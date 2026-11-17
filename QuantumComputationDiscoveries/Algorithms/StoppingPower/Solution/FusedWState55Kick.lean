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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.XorForestStageA128

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section WStateSharedBank114AndTwist114
set_option maxRecDepth 65536

set_option maxRecDepth 65536
namespace WStateSharedBank114AndTwist114
section
noncomputable section
local instance (priority := 1000000) instNeZeroTwoPowFusedW55 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
section Fused55WStateHdrAnd108Loader
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open QRegExt
open FusedVepCore288 (CleanUnitaryWp)
open SharedUnaryZeroTXUncInner3Axes288 (CleanUnitaryEquiv)
open Leaf4Twist162
theorem cleanUnitaryEquiv_of_cleanUnitaryWp {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    {rWork : QRegister m n} {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hw : CleanUnitaryWp rWork U d) :
    CleanUnitaryEquiv rWork U d := fun M ↦ by
  obtain ⟨M', hwp⟩ := hw.storeConst M
  refine ⟨M', hwp, ?_⟩
  have heq := hw.wp_eq M
  rwa [hwp] at heq
theorem cleanUnitaryWp_of_cleanUnitaryEquiv {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    {rWork : QRegister m n} {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hc : CleanUnitaryEquiv rWork U d) :
    CleanUnitaryWp rWork U d :=
  ⟨fun M ↦ ⟨(hc M).choose, (hc M).choose_spec.1⟩,
   fun M ↦ by rw [(hc M).choose_spec.1]; exact (hc M).choose_spec.2⟩
/-!
### Section 2b: Workspace Slicing (`55 + H + K + (6 + (K - 2)) ≤ mWExt`) & `dKickKoff55WState108KH`
-/
/-- Exact 3-axis Mode-1 `k_off` inner kick `.T` count with `55`-wire W-state shared header
and unified `108`-leaf `selectSwapXorBitLoop` loader (`-102 T` one-way = `-204 T/step` two-way
`-162 T` one-way = `-324 T/step` two-way at fixed workspace width):
`178 + 4 * H + 3 * (4 * (54 - H) + 4 * K + 64 + tZeroMuxSkip (48 - K))`. -/
def tKickKoff55WState_108KH (K H : ℕ) : ℕ :=
  178 + 4 * H + 3 * (4 * (54 - H) + 4 * K + 64 + tZeroMuxSkip (48 - K))
end Fused55WStateHdrAnd108Loader
end
end
end WStateSharedBank114AndTwist114
end WStateSharedBank114AndTwist114

noncomputable section SlimStageADepsE1
set_option maxRecDepth 131072

section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroAux0e1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.DynamicCircuit DynCircuitExt
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  concat_compose_selDataInAct concat_compose_selMeasInAct selDataInAct_disj_selMeasInAct)
open Operator QProg Matrix Real
open scoped Matrix BigOperators
namespace Xor32QftAnnihilationAndRawAdapter
open ZeroHypStageABToUFoldedPass123SegAndCompac (uHeadPhase80Mod4Eff)
open DyadicQft64Engine (wireHadamard6 bit5Flip6 stageDiag6)
open DyadicQft64WalkCircuit (rAxis654 axisProd654 axisProd654_mul stageH654_eq_axisProd
  stageD654_eq_axisProd bit5Flip654 bit5Flip654_eq_axisProd)
open DyadicQft64WalkCircuit220 (coreQftHadamardIdeal654)
open FullSysCatSegmentBridge (FullSysQft654Bundle fullSysCoreWires fullSysQftCoreUnitary
  coreElecBlock coreElecCosetB1Block)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open NuclearTwistRealizes (uXor32Core uXor32Core_inv)
open FusedPreDiagFromTwist288 (embed_bit5Flip654_eq_uXor32Core)
open HoistedSwapSelectBridge (unitaryConj)
open SchedBranchStitchGen (unitaryConj_eq_inv_mul)
open InterWalkRSum42Hoist (qreg_ext)
/-- 1D 6-qubit Karatsuba Hadamard butterfly unitary (`stageH 0 .. stageH 5`). -/
noncomputable abbrev uCoreHadamard6 : Unitary 64 := wireHadamard6 0 *
    (stageDiag6 1 * wireHadamard6 1) * (stageDiag6 2 * wireHadamard6 2) *
    (stageDiag6 3 * wireHadamard6 3) * (stageDiag6 4 * wireHadamard6 4) *
    (stageDiag6 5 * wireHadamard6 5)
/-- 6-qubit Pauli-`Z` phase gate on MSB wire `5 : Fin 6`. -/
noncomputable def bit5Phase6 : Unitary 64 :=
  (QRegister.singleton (5 : Fin 6) : QRegister 1 6).embedUnitary Qubit.Z
theorem qubit_Z_val_eq_diagonal : (Qubit.Z : 𝐔[Fin (2 ^ 1)]).1 = Matrix.diagonal
    (fun i : Fin 2 ↦ if i = 0 then (1 : ℂ) else -1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qubit.Z]
/-- `bit5Phase6` is a diagonal unitary. -/
theorem bit5Phase6_isDiag : ∃ d6 : Fin 64 → ℂ, bit5Phase6.1 = Matrix.diagonal d6 := by
  unfold bit5Phase6
  rw [QRegister.embedUnitary_val, qubit_Z_val_eq_diagonal, QRegister.embedMatrix_diagonal]
  exact ⟨_, rfl⟩
/-- `bit5Phase6` is an involution (`bit5Phase6 * bit5Phase6 = 1`). -/
@[simp] theorem bit5Phase6_sq : bit5Phase6 * bit5Phase6 = 1 := by
  unfold bit5Phase6
  rw [← QRegister.embedUnitary_mul, Qubit.Z_sq, QRegister.embedUnitary_one]
/-- Wire-5 Hadamard intertwines `bit5Flip6` (`X_5`) to `bit5Phase6` (`Z_5`). -/
theorem wireHadamard6_5_mul_bit5Flip6 :
    wireHadamard6 5 * bit5Flip6 = bit5Phase6 * wireHadamard6 5 := by
  unfold wireHadamard6 bit5Flip6 bit5Phase6
  rw [← QRegister.embedUnitary_mul, Qubit.H_mul_X_eq_Z_mul_H, QRegister.embedUnitary_mul]
/-- Every diagonal butterfly stage `stageDiag6 m` commutes with `bit5Phase6`. -/
theorem stageDiag6_comm_bit5Phase6 (m : Fin 6) :
    stageDiag6 m * bit5Phase6 = bit5Phase6 * stageDiag6 m := by
  apply Subtype.ext
  obtain ⟨d6, hd6⟩ := bit5Phase6_isDiag
  simp only [Submonoid.coe_mul, hd6, stageDiag6, Matrix.diagonal_mul_diagonal, mul_comm]
/-- Every wire Hadamard `wireHadamard6 m` with `m ≠ 5` commutes with `bit5Phase6`. -/
theorem wireHadamard6_comm_bit5Phase6_of_ne (m : Fin 6) (hm : m ≠ 5) :
    wireHadamard6 m * bit5Phase6 = bit5Phase6 * wireHadamard6 m :=
  Subtype.ext ((QRegister.singleton m).embedMatrix_comm_of_disjoint
    (QRegister.singleton 5) (QRegister.singleton_disjoint hm) Qubit.H.1 Qubit.Z.1)
theorem comm_mul_left {d : ℕ} {a b z : Unitary d}
    (ha : a * z = z * a) (hb : b * z = z * b) : (a * b) * z = z * (a * b) := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
/-- Exact 1D 6-qubit QFT butterfly intertwining `uCoreHadamard6 * bit5Flip6 = bit5Phase6 *
  uCoreHadamard6`. -/
theorem uCoreHadamard6_mul_bit5Flip6 :
    uCoreHadamard6 * bit5Flip6 = bit5Phase6 * uCoreHadamard6 := by
  let P4 : Unitary 64 := wireHadamard6 0 * (stageDiag6 1 * wireHadamard6 1) *
      (stageDiag6 2 * wireHadamard6 2) * (stageDiag6 3 * wireHadamard6 3) *
      (stageDiag6 4 * wireHadamard6 4)
  have hP4 : P4 * bit5Phase6 = bit5Phase6 * P4 := comm_mul_left (comm_mul_left (comm_mul_left
      (comm_mul_left (wireHadamard6_comm_bit5Phase6_of_ne 0 (by decide)) (comm_mul_left
      (stageDiag6_comm_bit5Phase6 1) (wireHadamard6_comm_bit5Phase6_of_ne 1 (by decide))))
      (comm_mul_left (stageDiag6_comm_bit5Phase6 2) (wireHadamard6_comm_bit5Phase6_of_ne 2
      (by decide)))) (comm_mul_left (stageDiag6_comm_bit5Phase6 3)
      (wireHadamard6_comm_bit5Phase6_of_ne 3 (by decide)))) (comm_mul_left
      (stageDiag6_comm_bit5Phase6 4) (wireHadamard6_comm_bit5Phase6_of_ne 4 (by decide)))
  change (P4 * (stageDiag6 5 * wireHadamard6 5)) * bit5Flip6 =
    bit5Phase6 * (P4 * (stageDiag6 5 * wireHadamard6 5))
  calc (P4 * (stageDiag6 5 * wireHadamard6 5)) * bit5Flip6
    _ = P4 * (stageDiag6 5 * (wireHadamard6 5 * bit5Flip6)) := by simp only [mul_assoc]
    _ = P4 * ((stageDiag6 5 * bit5Phase6) * wireHadamard6 5) := by
          rw [wireHadamard6_5_mul_bit5Flip6]; simp only [mul_assoc]
    _ = (P4 * bit5Phase6) * (stageDiag6 5 * wireHadamard6 5) := by
          rw [stageDiag6_comm_bit5Phase6 5]; simp only [mul_assoc]
    _ = bit5Phase6 * (P4 * (stageDiag6 5 * wireHadamard6 5)) := by
          rw [hP4]; simp only [mul_assoc]
/-- 654-axis Pauli-`Z` phase product on `(3924 + 3)` QFT wires. -/
noncomputable def bit5Phase654 : Unitary (2 ^ (3924 + 3)) := axisProd654 (fun _ ↦ bit5Phase6)
@[simp] theorem bit5Phase654_sq : bit5Phase654 * bit5Phase654 = 1 := by
  unfold bit5Phase654
  rw [axisProd654_mul]
  simp only [bit5Phase6_sq, axisProd654, QRegister.embedUnitary_one,
    List.ofFn_const, List.prod_replicate, one_pow]
/-- `coreQftHadamardIdeal654` factors as the 654-axis product of `uCoreHadamard6`. -/
theorem coreQftHadamardIdeal654_eq_axisProd :
    coreQftHadamardIdeal654 = axisProd654 (fun _ ↦ uCoreHadamard6) := by
  unfold coreQftHadamardIdeal654
  rw[stageH654_eq_axisProd, stageD654_eq_axisProd, stageH654_eq_axisProd,
      stageD654_eq_axisProd, stageH654_eq_axisProd, stageD654_eq_axisProd,
      stageH654_eq_axisProd, stageD654_eq_axisProd, stageH654_eq_axisProd,
      stageD654_eq_axisProd, stageH654_eq_axisProd, axisProd654_mul, axisProd654_mul,
      axisProd654_mul, axisProd654_mul, axisProd654_mul, axisProd654_mul, axisProd654_mul,
      axisProd654_mul, axisProd654_mul, axisProd654_mul]
/-- Exact 654-axis QFT butterfly intertwining `coreQftHadamardIdeal654 * bit5Flip654 =
  bit5Phase654 * coreQftHadamardIdeal654`. -/
theorem coreQftHadamardIdeal654_mul_bit5Flip654 :
    coreQftHadamardIdeal654 * bit5Flip654 = bit5Phase654 * coreQftHadamardIdeal654 := by
  rw [coreQftHadamardIdeal654_eq_axisProd, bit5Flip654_eq_axisProd, axisProd654_mul]
  simp only [uCoreHadamard6_mul_bit5Flip6]
  rw [← axisProd654_mul]
  rfl
/-- Purely low-`3924` electron bit-5 Pauli-`Z` phase product (`2 ^ 3924`). -/
noncomputable def zLow3924 : Unitary (2 ^ 3924) :=
  (List.ofFn fun a : Fin 654 ↦
    (QRegister.block (6 * a.val) 6 (by have := a.isLt; omega)).embedUnitary bit5Phase6).prod
/-- Core-level 654-axis Pauli-`Z` phase unitary (`Z_elec654`) on `fullSysCoreWires mPayload`. -/
noncomputable def zElec654Core {mPayload : ℕ} (hm6 : 6 ≤ mPayload) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := (coreElecCosetB1Block hm6).embedUnitary bit5Phase654
@[simp] theorem zElec654Core_sq {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    zElec654Core hm6 * zElec654Core hm6 = 1 := by
  unfold zElec654Core
  rw [← QRegister.embedUnitary_mul, bit5Phase654_sq, QRegister.embedUnitary_one]
theorem embedUnitary_list_prod {k N : ℕ} (r : QRegister k N) :
    ∀ l : List (Unitary (2 ^ k)), r.embedUnitary l.prod = (l.map r.embedUnitary).prod
  | [] => by simp
  | u :: s => by simp [embedUnitary_list_prod r s, QRegister.embedUnitary_mul]
theorem coreElecCosetB1Block_compose_rAxis654 {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (a : Fin 654) :
    (coreElecCosetB1Block hm6).compose (rAxis654 a) =
      (coreElecBlock mPayload).compose
        (QRegister.block (6 * a.val) 6 (by have := a.isLt; omega)) := by
  apply qreg_ext; intro j
  have hj : 6 * a.val + j.val < 3924 := by have := a.isLt; have := j.isLt; omega
  have hcast : rAxis654 a j = Fin.castAdd 3 ⟨6 * a.val + j.val, hj⟩ := Fin.ext rfl
  change (coreElecCosetB1Block hm6) (rAxis654 a j) =
    (coreElecBlock mPayload) (QRegister.block (6 * a.val) 6 _ j)
  rw [hcast, QRegister.concat_apply_left]
  apply Fin.ext
  simp only [coreElecBlock, QRegister.block_apply_val]
/-- `zElec654Core hm6` is supported purely on the low `3,924` electron wires (`coreElecBlock
  mPayload`). -/
theorem zElec654Core_eq_coreElecBlock_embed {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    zElec654Core hm6 = (coreElecBlock mPayload).embedUnitary zLow3924 := by
  unfold zElec654Core bit5Phase654 axisProd654 zLow3924
  rw [embedUnitary_list_prod, embedUnitary_list_prod, List.map_ofFn, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext a
  simp only [Function.comp_apply, ← QRegister.embedUnitary_compose,
    coreElecCosetB1Block_compose_rAxis654]
theorem exists_diagonal_list_prod {K : ℕ} :
    ∀ (l : List (Unitary K)),
      (∀ u ∈ l, ∃ d : Fin K → ℂ, u.1 = Matrix.diagonal d) →
      ∃ d : Fin K → ℂ, l.prod.1 = Matrix.diagonal d
  | [], _ => ⟨1, Matrix.diagonal_one.symm⟩
  | u :: s, h => by
      obtain ⟨d1, hd1⟩ := h u List.mem_cons_self
      obtain ⟨d2, hd2⟩ := exists_diagonal_list_prod s (fun v hv ↦ h v (List.mem_cons_of_mem u hv))
      exact ⟨fun x ↦ d1 x * d2 x, by
        rw [List.prod_cons, Submonoid.coe_mul, hd1, hd2, Matrix.diagonal_mul_diagonal]⟩
/-- `zLow3924` is a diagonal unitary (`∃ d0, zLow3924.1 = Matrix.diagonal d0`). -/
theorem zLow3924_isDiag : ∃ d0 : Fin (2 ^ 3924) → ℂ, zLow3924.1 = Matrix.diagonal d0 := by
  unfold zLow3924
  refine exists_diagonal_list_prod _ fun u hu ↦ ?_
  rw [List.mem_ofFn] at hu
  rcases hu with ⟨a, rfl⟩
  obtain ⟨d6, hd6⟩ := bit5Phase6_isDiag
  rw [QRegister.embedUnitary_val, hd6, QRegister.embedMatrix_diagonal]
  exact ⟨_, rfl⟩
/-- Core QFT intertwining `fullSysQftCoreUnitary hm6 qft * uXor32Core mPayload = zElec654Core hm6
  * fullSysQftCoreUnitary hm6 qft`. -/
theorem fullSysQftCoreUnitary_mul_uXor32Core {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (qft : FullSysQft654Bundle) (hQft : qft.uQft654 = coreQftHadamardIdeal654) :
    fullSysQftCoreUnitary hm6 qft * uXor32Core mPayload =
      zElec654Core hm6 * fullSysQftCoreUnitary hm6 qft := by
  unfold fullSysQftCoreUnitary zElec654Core
  rw [← embed_bit5Flip654_eq_uXor32Core hm6, ← QRegister.embedUnitary_mul,
    hQft, coreQftHadamardIdeal654_mul_bit5Flip654, QRegister.embedUnitary_mul]
/-- General low-`3924` commutation lemma: any basis-ket permutation fixing wires `< 3924` commutes
with `(QRegister.block 0 3924 hn).embedUnitary zLow3924`. -/
theorem perm_comm_embedLow3924_zLow {n : ℕ} (hn : 3924 ≤ n) (U : Unitary (2 ^ n))
    (perm : BitAssignment n → BitAssignment n) (hKet : ∀ β, U.1.mulVec
    (MeasureBranchHadamardSem.ket β) =
    MeasureBranchHadamardSem.ket (perm β)) (hFixLow : ∀ (β :
    BitAssignment n) (i : Fin 3924), perm β (QRegister.block 0 3924 hn i) = β (QRegister.block
    0 3924 hn i)) : U * (QRegister.block 0 3924 hn).embedUnitary zLow3924 =
    (QRegister.block 0 3924 hn).embedUnitary zLow3924 * U := by
  let rLow : QRegister 3924 n := QRegister.block 0 3924 hn
  obtain ⟨d0, hd0⟩ := zLow3924_isDiag
  apply Subtype.ext
  simp only [Submonoid.coe_mul, QRegister.embedUnitary_val, hd0, QRegister.embedMatrix_diagonal]
  refine PosPostPrep80MergedVep.perm_comm_diagonal_of_ket
    U.1 perm hKet _ fun β ↦ congrArg d0 ?_
  apply (basisBitsEquiv 3924).injective
  funext i
  change basisBits 3924 (rLow.extractIndex ((basisBitsEquiv n).symm (perm β))) i =
    basisBits 3924 (rLow.extractIndex ((basisBitsEquiv n).symm β)) i
  rw [rLow.basisBits_extractIndex, rLow.basisBits_extractIndex]
  have h1 := congrFun ((basisBitsEquiv n).apply_symm_apply (perm β)) (rLow i)
  have h2 := congrFun ((basisBitsEquiv n).apply_symm_apply β) (rLow i)
  change basisBits n ((basisBitsEquiv n).symm (perm β)) (rLow i) = perm β (rLow i) at h1
  change basisBits n ((basisBitsEquiv n).symm β) (rLow i) = β (rLow i) at h2
  rw [h1, h2, hFixLow β i]
theorem diag_comm_embedLow3924_zLow {n : ℕ} (hn : 3924 ≤ n)
    (U : Unitary (2 ^ n)) (dU : Fin (2 ^ n) → ℂ) (hU : U.1 = Matrix.diagonal dU) :
    U * (QRegister.block 0 3924 hn).embedUnitary zLow3924 =
      (QRegister.block 0 3924 hn).embedUnitary zLow3924 * U := by
  obtain ⟨d0, hd0⟩ := zLow3924_isDiag
  apply Subtype.ext
  simp only [Submonoid.coe_mul, QRegister.embedUnitary_val, hU, hd0,
    QRegister.embedMatrix_diagonal, Matrix.diagonal_mul_diagonal, mul_comm]
theorem castUnitaryPow2_comm_embedLow3924_zLow {a b : ℕ} (h : a = b) (ha : 3924 ≤ a)
    (hb : 3924 ≤ b) (U : Unitary (2 ^ a)) (hComm : U * (QRegister.block 0 3924
    ha).embedUnitary zLow3924 = (QRegister.block 0 3924 ha).embedUnitary zLow3924 * U) :
    PosSlots24SemanticBridge.castUnitaryPow2 h U *
    (QRegister.block 0 3924 hb).embedUnitary zLow3924 =
    (QRegister.block 0 3924 hb).embedUnitary zLow3924 *
    PosSlots24SemanticBridge.castUnitaryPow2 h U := by
  cases h
  exact hComm
/-- `3924 ≤ posCoreWires` (`posCoreWires = 4034`). -/
theorem h3924_posCore :
    3924 ≤ PosSlots24BranchConcrete.posCoreWires := by
  dsimp [PosSlots24BranchConcrete.posCoreWires]
  omega
/-- `3924 ≤ fullSysCoreWires 80` (`fullSysCoreWires 80 = 4034`). -/
theorem h3924_core80 : 3924 ≤ fullSysCoreWires 80 := by
  rw [PosSlots24SemanticBridge.pos24_coreWires80_eq]
  exact h3924_posCore
theorem diagZ8_comm_embedLow3924_zLow {n : ℕ} (hn : 3924 ≤ n) (p : BitAssignment n → ZMod 8) :
    PosHeadMod4_15476.diagZ8UnitaryN p *
    (QRegister.block 0 3924 hn).embedUnitary zLow3924 =
    (QRegister.block 0 3924 hn).embedUnitary zLow3924 *
    PosHeadMod4_15476.diagZ8UnitaryN p :=
    diag_comm_embedLow3924_zLow hn
    (PosHeadMod4_15476.diagZ8UnitaryN p) (fun x : Fin (2 ^ n) ↦
    ZeroAncillaUSP.omega8 ^ (p (basisBits n x)).val) rfl
/-- `uSwapCore3967` (acting on high wires `3967` and `4029`) commutes with `zElec654Core`. -/
theorem uSwapCore3967_comm_zElec654Core :
    PosPostPrep80MergedVep.uSwapCore3967 * zElec654Core
    (by decide : 6 ≤ 80) = zElec654Core (by decide : 6 ≤ 80) *
    PosPostPrep80MergedVep.uSwapCore3967 := by
  rw [zElec654Core_eq_coreElecBlock_embed]
  refine perm_comm_embedLow3924_zLow h3924_core80
    PosPostPrep80MergedVep.uSwapCore3967
    PosPostPrep80MergedVep.swapCore3967Fn
    PosPostPrep80MergedVep.uSwapCore3967_mulVec_ket fun β i ↦ ?_
  unfold PosPostPrep80MergedVep.swapCore3967Fn
  let w : Wire (fullSysCoreWires 80) := QRegister.block 0 3924 h3924_core80 i
  have h1 : w ≠ PosPostPrep80MergedVep.wCore3967 := by
    intro h; have hv := congrArg Fin.val h
    simp only [w, QRegister.block_apply_val,
      PosPostPrep80MergedVep.wCore3967] at hv
    have := i.isLt; omega
  have h2 : w ≠ PosPostPrep80MergedVep.wCore4029 := by
    intro h; have hv := congrArg Fin.val h
    simp only [w, QRegister.block_apply_val,
      PosPostPrep80MergedVep.wCore4029] at hv
    have := i.isLt; omega
  exact congrArg β (Equiv.swap_apply_of_ne_of_ne h1 h2)
/-- `uHeadPhaseMod4` (`monomialZ8UnitaryN` on wire `3985` times `diagZ8UnitaryN`) commutes with
`(QRegister.block 0 3924 h3924_posCore).embedUnitary zLow3924`. -/
theorem uHeadPhaseMod4_comm_zLow3924 :
    PosHeadMod4_15476.uHeadPhaseMod4 *
        (QRegister.block 0 3924 h3924_posCore).embedUnitary zLow3924 =
      (QRegister.block 0 3924 h3924_posCore).embedUnitary zLow3924 *
        PosHeadMod4_15476.uHeadPhaseMod4 := by
  unfold PosHeadMod4_15476.uHeadPhaseMod4
    PosHeadMod4_15476.monomialZ8UnitaryN
  refine comm_mul_left ?_ (diagZ8_comm_embedLow3924_zLow h3924_posCore _)
  let wTh := PosSlots24BranchConcrete.wHeadThresh
    (QRegExt.ofFin PosSlots24BranchConcrete.posCoreWires)
  have hwTh_val : wTh.val = 3985 := rfl
  refine perm_comm_embedLow3924_zLow h3924_posCore
    (permutationUnitary (PosHeadMod4_15476.permThClean wTh
      PosHeadMod4_15476.headEnBoolSpec))
    (PosHeadMod4_15476.flipThClean wTh
      PosHeadMod4_15476.headEnBoolSpec)
    (fun β ↦ by
      rw [PosSlots24BranchConcrete.mbh_ket_eq_ket,
        PosSlots24BranchConcrete.mbh_ket_eq_ket]
      exact PosHeadMod4_15476.ket_permThClean wTh _ β)
    fun β i ↦ ?_
  have hne : QRegister.block 0 3924 h3924_posCore i ≠ wTh := by
    intro h; have hv := congrArg Fin.val h
    rw [QRegister.block_apply_val, hwTh_val] at hv
    have := i.isLt; omega
  unfold PosHeadMod4_15476.flipThClean
    PosHeadMod4_15476.flipTh
  split_ifs
  · exact Function.update_of_ne hne _ _
  · rfl
/-- `uHeadPhase80Mod4Eff` commutes unconditionally (`0` hypotheses) with `zElec654Core`. -/
theorem uHeadPhase80Mod4Eff_comm_zElec654Core : uHeadPhase80Mod4Eff * zElec654Core
    (by decide : 6 ≤ 80) = zElec654Core (by decide : 6 ≤ 80) * uHeadPhase80Mod4Eff := by
  have hS := uSwapCore3967_comm_zElec654Core
  have hCast : PosSlots24SemanticBridge.castUnitaryPow2
      PosSlots24SemanticBridge.pos24_coreWires80_eq.symm
      PosHeadMod4_15476.uHeadPhaseMod4 * zElec654Core
      (by decide : 6 ≤ 80) = zElec654Core (by decide : 6 ≤ 80) *
      PosSlots24SemanticBridge.castUnitaryPow2
      PosSlots24SemanticBridge.pos24_coreWires80_eq.symm
      PosHeadMod4_15476.uHeadPhaseMod4 := by
    rw [zElec654Core_eq_coreElecBlock_embed]
    exact castUnitaryPow2_comm_embedLow3924_zLow
      PosSlots24SemanticBridge.pos24_coreWires80_eq.symm
      h3924_posCore h3924_core80 _ uHeadPhaseMod4_comm_zLow3924
  unfold uHeadPhase80Mod4Eff
  exact comm_mul_left (comm_mul_left hS hCast) hS
/-- General `uXor32Core` QFT-conjugation annihilation lemma for any core unitary `D` commuting
  with `zElec654Core`. -/
theorem uXor32Core_conj_unitaryConj_qft_of_comm_zElec {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (qft : FullSysQft654Bundle) (hQft : qft.uQft654 = coreQftHadamardIdeal654)
    (D : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (hDZ : D * zElec654Core hm6 = zElec654Core hm6 * D) : uXor32Core mPayload * unitaryConj
    (fullSysQftCoreUnitary hm6 qft) D * uXor32Core mPayload = unitaryConj
    (fullSysQftCoreUnitary hm6 qft) D := by
  let Q := fullSysQftCoreUnitary hm6 qft
  let X := uXor32Core mPayload
  let Z := zElec654Core hm6
  have hQX : Q * X = Z * Q := fullSysQftCoreUnitary_mul_uXor32Core hm6 qft hQft
  have hXInv : X⁻¹ = X := uXor32Core_inv mPayload
  have hZ2 : Z * Z = 1 := zElec654Core_sq hm6
  have hZInv : Z⁻¹ = Z := inv_eq_of_mul_eq_one_right hZ2
  have hXQInv : X * Q⁻¹ = Q⁻¹ * Z := by
    have h := congrArg Inv.inv hQX
    simpa only [_root_.mul_inv_rev, hXInv, hZInv] using h
  have hZD : Z * D = D * Z := hDZ.symm
  change X * unitaryConj Q D * X = unitaryConj Q D
  simp only [unitaryConj_eq_inv_mul]
  calc X * (Q⁻¹ * D * Q) * X
    _ = (X * Q⁻¹) * D * (Q * X) := by simp only [mul_assoc]
    _ = Q⁻¹ * ((Z * D) * (Z * Q)) := by rw [hXQInv, hQX]; simp only [mul_assoc]
    _ = Q⁻¹ * (D * ((Z * Z) * Q)) := by rw [hZD]; simp only [mul_assoc]
    _ = Q⁻¹ * D * Q := by rw [hZ2, one_mul, mul_assoc]
section HpowXor32Core80
attribute [local irreducible] HPow.hPow
/-- Zero-hypothesis annihilation `uXor32Core 80 * unitaryConj Q uHeadPhase80Mod4Eff * uXor32Core
  80 = unitaryConj Q uHeadPhase80Mod4Eff`. -/
theorem uXor32Core80_conj_qft_uHeadPhase80Mod4Eff : uXor32Core 80 * unitaryConj
    (fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128)
    uHeadPhase80Mod4Eff * uXor32Core 80 = unitaryConj (fullSysQftCoreUnitary
    (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128) uHeadPhase80Mod4Eff :=
    uXor32Core_conj_unitaryConj_qft_of_comm_zElec (by decide : 6 ≤ 80)
    coreQftHadamardPrunedBundle128
    SelStitchHelper.coreQftHadamardPrunedBundle128_eq_ideal654
    uHeadPhase80Mod4Eff uHeadPhase80Mod4Eff_comm_zElec654Core
end HpowXor32Core80
end Xor32QftAnnihilationAndRawAdapter
namespace BoothOpt_Anchor218CachedTrueSwapOuter
open ElecHadTrueSwapLocalCompClosure (uLensSwap)
open ZeroHypCatState48StageABMidCoreReductionAn (catState48)
open ZeroHypStageABToUFoldedPass123SegAndCompac (uHeadPhase80Mod4Eff)
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open QRegExt
section Part1E_PebbledAnchor218
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open InterWalkRSum42Hoist (kFull80 rCoreFull)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (coinBarrelFastOnDataLens)
/-- Selector embedding `k₁ + 18` into `k₂ + 18` via `sel : QRegister k₁ k₂` on the data block
and identity on the `18`-wire measurement block. -/
def selLiftAct {k₁ k₂ : ℕ} (sel : QRegister k₁ k₂) : QRegister (k₁ + 18) (k₂ + 18) :=
  ((selDataInAct k₂).compose sel).concat (selMeasInAct k₂)
    ((selDataInAct_disj_selMeasInAct k₂).compose_left sel)
/-- Canonical `kFull80` active-anchor `Slot18Lens` (`coinBarrelFastOnDataLens (le_refl 80)
  rCoreFull`). -/
noncomputable def L_anchor : Slot18Lens kFull80 :=
  coinBarrelFastOnDataLens (le_refl 80) rCoreFull
end Part1E_PebbledAnchor218
section Part2_AnchorFrameAndPass13
open DyadicQft64 (dyadicTurn dyadicTurn_add dyadicDiagUnitary dyadicDiagUnitary_inv
  embedUnitary_dyadicDiagUnitary_mulVec_basisKet sList sDagList wireListSum wireListSum_cons
  phasePerm_sList phasePerm_sDagList count_sList_toff count_sList_t count_sDagList_toff
  count_sDagList_t)
open HoistedSwapSelectBridge (unitaryConj)
open HoistBorrow42ProjBridge (RealizesOnProj)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires coreElecCosetB1Block coreCosetB1Block
  disjointWires_concat_left)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSegOrig rSegFull PreservesFeature E_rawStream42
  E_rawStream42_eq_streamProjOp embedAct0_comm_streamOp qreg_ext qreg_block_apply
  embedUnitary_inv_symm)
open NuclearTwistMulKickAndBridge288 (count_dyn_seq)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm)
open PartnerAndAnchorSlot18LensAndMidBA (mkSlot18LensOfSlotReg)
open ElecHadTrueSwapLocalCompClosure (extractPair liftPairIdx extractPair_liftPairIdx lensSwapEquiv)
open PureCnotLensLoadAndZeroHypTrueSwap (uLensSwap_mul_self_eq_one)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 P_slot0_eq_diagonal)
open CoinDispatchedBarrel288 (swapElec0Bits swapElec0Bits_self swapElec0Bits_high coinBarrelIdxFast
  coinBarrelIdxFast_congr_high coinBarrelIdxFast_swap_inv coinBarrelBitFnFast coinBarrelPermFast
  uBarrelFast uBarrelFast_mul_self)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open PosSlots24Barrel3Pass (permUnitary_apply)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (SameOutside embedMatrix_apply_sameOutside
  h3924_le_fullSysCoreWires rFullSysElecSlot rFullSysElecSlot_val coinBarrelFastOnDataLens
  coinBarrelFastOnDataLens_tbl coinBarrelFastOnDataLens_updSlot)
open ButterflyBarrelSlot0Conj (spectatorElecReg ActsAsIdOnSpectatorWires PreservesHigh3924On)
open Barrel3PassSelectStitch (hm6_80 rCoreSeg uTrailCliffordXor80)
open SelStitchHelper (comm_pCoinSlack010Core_of_comm_coin3)
open PosMomSelectSandwich (slotBitProj)
open SelectHoistLemmas (commutesWithReg_rCtrl3InSeg_rCoreSeg commutesWithReg_rPGIdleOrig_rCoreSeg)
open Leaf4Ext48TopStitch (CommutesWithReg rCtrl3InCore rPGIdleOrig)
open SelectHoistLemmas (rCtrl3InSeg pCoinSlack010Seg rSegFull_eq_rAct0_compose_rSegOrig)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
open SingleBarrel8StepClean (qftCoreUnitary80 qftCliffordCore80 mul_catState48_comp)
open NuclearTwistRealizes (embedUnitary_idReg_eq uXor32Core uXor32Core_inv)
open Xor32QftAnnihilationAndRawAdapter (uXor32Core80_conj_qft_uHeadPhase80Mod4Eff)
open FusedPreDiagFromTwist288 (preDiagCliffordExp128 uPreDiagClifford654 uPreDiagCliffordCore
  preDiagCliffordLocalCircuit preDiagCliffordInvLocalCircuit count_preDiagCliffordLocal_toff
  count_preDiagCliffordLocal_t count_preDiagCliffordInvLocal_toff count_preDiagCliffordInvLocal_t
  preDiagCliffordLocalCircuit_eval preDiagCliffordInvLocalCircuit_eval)
/-- First 18-wire electron slot (`slot[0]`) inside `fullSysCoreWires 80`. -/
def rSlot0InCore : QRegister 18 (fullSysCoreWires 80) := rFullSysElecSlot (le_refl 80) 0
/-- First 18-wire electron slot (`slot[0]`) of `rCoreFull` inside `kFull80`. -/
def rSlot0InFull : QRegister 18 kFull80 := rCoreFull.compose rSlot0InCore
/-- Zero-gate register re-indexing that replaces `rSlot0` inside `rData` by `rAnchor18`
while keeping all other `kData - 18` wires of `rData` unchanged. -/
noncomputable def rDataSubstSlot0 {kData n : ℕ}
    (rSlot0 : QRegister 18 kData)
    (rData : QRegister kData n) (rAnchor18 : QRegister 18 n)
    (hDA : rData.DisjointWires rAnchor18) : QRegister kData n where
  wires :=
    { toFun := fun i ↦
        if h : ∃ j : Fin 18, rSlot0 j = i then rAnchor18 h.choose else rData i
      inj' := by
        intro i₁ i₂ heq
        dsimp only at heq
        by_cases h₁ : ∃ j : Fin 18, rSlot0 j = i₁ <;> by_cases h₂ : ∃ j : Fin 18, rSlot0 j = i₂
        · rw [dite_eq_left h₁, dite_eq_left h₂] at heq
          rw [← h₁.choose_spec, ← h₂.choose_spec, rAnchor18.wires.injective heq]
        · rw [dite_eq_left h₁, dite_eq_right h₂] at heq
          exact absurd heq.symm (hDA.ne i₂ h₁.choose)
        · rw [dite_eq_right h₁, dite_eq_left h₂] at heq
          exact absurd heq (hDA.ne i₁ h₂.choose)
        · rw [dite_eq_right h₁, dite_eq_right h₂] at heq
          exact rData.wires.injective heq }
/-- Canonical `kFull80` register re-indexing replacing `rCoreFull`'s `slot[0]` (`18` wires)
with `rAnchor18` (`0` gates). -/
noncomputable abbrev rActAnchorSubst {n : ℕ} (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (hAA : rAct.DisjointWires rAnchor18) : QRegister kFull80 n :=
    rDataSubstSlot0 rSlot0InFull rAct rAnchor18 hAA
theorem rDataSubstSlot0_apply_slot0 {kData n : ℕ} (rSlot0 : QRegister 18 kData)
    (rData : QRegister kData n) (rAnchor18 : QRegister 18 n)
    (hDA : rData.DisjointWires rAnchor18) (j : Fin 18) : rDataSubstSlot0 rSlot0 rData
    rAnchor18 hDA (rSlot0 j) = rAnchor18 j := by
  have h : ∃ j' : Fin 18, rSlot0 j' = rSlot0 j := ⟨j, rfl⟩
  change (if h' : ∃ j' : Fin 18, rSlot0 j' = rSlot0 j then rAnchor18 h'.choose else _) = _
  rw [dite_eq_left h]
  exact congrArg rAnchor18 (rSlot0.wires.injective h.choose_spec)
theorem rDataSubstSlot0_apply_of_not_mem {kData n : ℕ} (rSlot0 : QRegister 18 kData)
    (rData : QRegister kData n) (rAnchor18 : QRegister 18 n)
    (hDA : rData.DisjointWires rAnchor18) {i : Fin kData} (hi : i ∉ Set.range rSlot0.wires) :
    rDataSubstSlot0 rSlot0 rData rAnchor18 hDA i = rData i := by
  change (if h' : ∃ j' : Fin 18, rSlot0 j' = i then rAnchor18 h'.choose else rData i) = rData i
  exact dite_eq_right hi
theorem rDataSubstSlot0_disj_of_disj {kData mW n : ℕ} (rSlot0 : QRegister 18 kData)
    {rData : QRegister kData n} {rAnchor18 : QRegister 18 n} {rW : QRegister mW n}
    (hDA : rData.DisjointWires rAnchor18) (hDW : rData.DisjointWires rW)
    (hAW : rAnchor18.DisjointWires rW) :
    (rDataSubstSlot0 rSlot0 rData rAnchor18 hDA).DisjointWires rW := by
  rw [QRegister.disjoint_iff]; intro i w
  change (if h : ∃ j : Fin 18, rSlot0 j = i then rAnchor18 h.choose else rData i) ≠ rW w
  split_ifs with h
  · exact hAW.ne h.choose w
  · exact hDW.ne i w
theorem rActAnchorSubst_disj_of_disj {mW n : ℕ} {rAct : QRegister kFull80 n}
    {rAnchor18 : QRegister 18 n} {rW : QRegister mW n} (hAA : rAct.DisjointWires rAnchor18)
    (hAWk : rAct.DisjointWires rW) (hAnWk : rAnchor18.DisjointWires rW) :
    (rActAnchorSubst rAct rAnchor18 hAA).DisjointWires rW := rDataSubstSlot0_disj_of_disj
    rSlot0InFull hAA hAWk hAnWk
/-- Selector inside `kData + 18` mapping `rSlot0` to `selMeasInAct kData` and all other wires to
  `selDataInAct kData`. -/
noncomputable def selSubstSlot0 {kData : ℕ} (rSlot0 : QRegister 18 kData) :
    QRegister kData (kData + 18) :=
  rDataSubstSlot0 rSlot0 (selDataInAct kData) (selMeasInAct kData) (selDataInAct_disj_selMeasInAct
    kData)
theorem concat_compose_selSubstSlot0 {kData n : ℕ} (rSlot0 : QRegister 18 kData)
    (rData : QRegister kData n) (rAnchor18 : QRegister 18 n)
    (hDA : rData.DisjointWires rAnchor18) : (rData.concat rAnchor18 hDA).compose
    (selSubstSlot0 rSlot0) = rDataSubstSlot0 rSlot0 rData rAnchor18 hDA := by
  apply qreg_ext; intro i
  rw [QRegister.compose_apply]
  by_cases h : ∃ j : Fin 18, rSlot0 j = i
  · obtain ⟨j, rfl⟩ := h
    rw [selSubstSlot0, rDataSubstSlot0_apply_slot0, rDataSubstSlot0_apply_slot0]
    exact congrArg (fun r ↦ r j) (concat_compose_selMeasInAct rData rAnchor18 hDA)
  · rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem _ _ _ _ h,
        rDataSubstSlot0_apply_of_not_mem _ _ _ _ h]
    exact congrArg (fun r ↦ r i) (concat_compose_selDataInAct rData rAnchor18 hDA)
/-- Constant `Slot18Lens kData` addressing a fixed `18`-wire subregister `rSlot0 : QRegister 18
  kData`. -/
noncomputable def L_slot0Of {kData : ℕ} (rSlot0 : QRegister 18 kData) : Slot18Lens kData :=
  mkSlot18LensOfSlotReg (fun _ ↦ rSlot0) (fun _ _ ↦ rfl)
@[simp]
theorem L_slot0Of_tbl {kData : ℕ} (rSlot0 : QRegister 18 kData) (d : Fin (2 ^ kData)) :
    (L_slot0Of rSlot0).tbl d = rSlot0.extractIndex d := rfl
@[simp] theorem L_slot0Of_updSlot {kData : ℕ} (rSlot0 : QRegister 18 kData)
    (d : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) :
    (L_slot0Of rSlot0).updSlot d v = rSlot0.replaceIndex d v := rfl
/-- Constant `slot[0]` lens on `kFull80` (`rSlot0InFull`). -/
noncomputable def L_slot0 : Slot18Lens kFull80 := L_slot0Of rSlot0InFull
/-- `18`-pair swap unitary on `kFull80 + 18` between `rCoreFull`'s `slot[0]` and `selMeasInAct
  kFull80`. -/
noncomputable def uSlot0MeasSwap : Unitary (2 ^ (kFull80 + 18)) := uLensSwap L_slot0
/-- `uBarrelFast (le_refl 80)` embedded on `(selDataInAct kFull80).compose rCoreFull` inside
  `kFull80 + 18`. -/
noncomputable def uBarrelFastAct : Unitary (2 ^ (kFull80 + 18)) :=
  ((selDataInAct kFull80).compose rCoreFull).embedUnitary (uBarrelFast (le_refl 80))
/-- `218`-slot true-swap unitary `uLensSwap L_anchor` on `kFull80 + 18`. -/
noncomputable def uAnchorLensSwap : Unitary (2 ^ (kFull80 + 18)) := uLensSwap L_anchor
/-- `18`-wire `|0^{18}⟩` projector on `selMeasInAct kFull80` inside `kFull80 + 18`. -/
noncomputable def P_anc0 : Operator (2 ^ (kFull80 + 18)) :=
  (selMeasInAct kFull80).basisOutcomeProjector 0
/-- Anchor-frame unitary on `kFull80 + 18` conjugating `(selDataInAct kFull80).embedUnitary U`
by `uBarrelFastAct * uSlot0MeasSwap`. -/
noncomputable def uAnchorFrame (U : Unitary (2 ^ kFull80)) : Unitary (2 ^ (kFull80 + 18)) :=
  (uBarrelFastAct * uSlot0MeasSwap) * (selDataInAct kFull80).embedUnitary U *
    (uSlot0MeasSwap * uBarrelFastAct)
theorem uSlot0MeasSwap_mul_self : uSlot0MeasSwap * uSlot0MeasSwap = 1 :=
  uLensSwap_mul_self_eq_one L_slot0
theorem uBarrelFastAct_mul_self : uBarrelFastAct * uBarrelFastAct = 1 := by
  dsimp only [uBarrelFastAct]
  rw [← QRegister.embedUnitary_mul, uBarrelFast_mul_self, QRegister.embedUnitary_one]
theorem uAnchorLensSwap_mul_self : uAnchorLensSwap * uAnchorLensSwap = 1 :=
  uLensSwap_mul_self_eq_one L_anchor
theorem uAnchorFrame_mul (U₂ U₁ : Unitary (2 ^ kFull80)) :
    uAnchorFrame U₂ * uAnchorFrame U₁ = uAnchorFrame (U₂ * U₁) := by
  dsimp only [uAnchorFrame]
  have hmid : (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap) = 1 := by
    calc (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap)
        = uSlot0MeasSwap * (uBarrelFastAct * uBarrelFastAct) * uSlot0MeasSwap := by
          simp only [mul_assoc]
      _ = uSlot0MeasSwap * uSlot0MeasSwap := by rw [uBarrelFastAct_mul_self, mul_one]
      _ = 1 := uSlot0MeasSwap_mul_self
  calc ((uBarrelFastAct * uSlot0MeasSwap) * (selDataInAct kFull80).embedUnitary U₂ *
          (uSlot0MeasSwap * uBarrelFastAct)) *
        ((uBarrelFastAct * uSlot0MeasSwap) * (selDataInAct kFull80).embedUnitary U₁ *
          (uSlot0MeasSwap * uBarrelFastAct))
      = (uBarrelFastAct * uSlot0MeasSwap) * (selDataInAct kFull80).embedUnitary U₂ *
          ((uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap)) *
          (selDataInAct kFull80).embedUnitary U₁ * (uSlot0MeasSwap * uBarrelFastAct) := by
          simp only [mul_assoc]
    _ = uAnchorFrame (U₂ * U₁) := by
          unfold uAnchorFrame
          rw [hmid, mul_one, QRegister.embedUnitary_mul]
          simp only [mul_assoc]
theorem permUnitary_inv_conj_apply_part2 {D : ℕ} (σ : Equiv.Perm (Fin D))
    (hInvol : ∀ x, σ (σ x) = x) (M : Operator D) (u' u : Fin D) :
    ((Operator.permutationUnitary σ).1 * M * (Operator.permutationUnitary σ).1) u' u =
      M (σ u') (σ u) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (σ u')]
  · have h1 : u' = σ (σ u') := (hInvol u').symm
    rw [permUnitary_apply, ite_eq_left h1, one_mul, Matrix.mul_apply, Finset.sum_eq_single (σ u)]
    · rw [permUnitary_apply, ite_eq_left rfl, mul_one]
    · intro k _ hk; rw [permUnitary_apply, ite_eq_right hk, mul_zero]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  · intro k _ hk
    have hne : u' ≠ σ k := fun h ↦ hk (by rw [h, hInvol])
    rw [permUnitary_apply, ite_eq_right hne, zero_mul]
  · intro h; exact False.elim (h (Finset.mem_univ _))
theorem permUnitary_conj_diagonal_part2 {D : ℕ} (σ : Equiv.Perm (Fin D))
    (hInvol : ∀ x, σ (σ x) = x) (d : Fin D → ℂ) :
    (Operator.permutationUnitary σ).1 * Matrix.diagonal d * (Operator.permutationUnitary σ).1 =
      Matrix.diagonal (fun x ↦ d (σ x)) := by
  ext x y
  rw [permUnitary_inv_conj_apply_part2 σ hInvol (Matrix.diagonal d) x y,
      Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : σ x ≠ σ y := fun h ↦ hxy (σ.injective h)
    simp [hxy, hne]
theorem permutationUnitary_mul_part2 {D : ℕ} (e₁ e₂ : Equiv.Perm (Fin D)) :
    Operator.permutationUnitary e₁ * Operator.permutationUnitary e₂ =
      Operator.permutationUnitary (e₂.trans e₁) := by
  apply Subtype.ext; ext x y
  change (∑ k : Fin D, (Operator.permutationUnitary e₁).1 x k * (Operator.permutationUnitary
    e₂).1 k y) = (Operator.permutationUnitary (e₂.trans e₁)).1 x y
  rw [Finset.sum_eq_single (e₂ y)]
  · rw [permUnitary_apply, permUnitary_apply, permUnitary_apply, ite_eq_left rfl, mul_one,
      Equiv.trans_apply]
  · intro k _ hk; rw [permUnitary_apply, permUnitary_apply, ite_eq_right hk, mul_zero]
  · intro h; exact False.elim (h (Finset.mem_univ _))
/-- Lifts `σ : Equiv.Perm (Fin (2 ^ k))` along `r : QRegister k N` to `Equiv.Perm (Fin (2 ^ N))`. -/
noncomputable def liftRegPerm {k N : ℕ} (r : QRegister k N) (σ : Equiv.Perm (Fin (2 ^ k))) :
    Equiv.Perm (Fin (2 ^ N)) where
  toFun z := r.replaceIndex z (σ (r.extractIndex z))
  invFun z := r.replaceIndex z (σ.symm (r.extractIndex z))
  left_inv z := eq_of_basisBits_eq fun w ↦ by
    by_cases hw : w ∈ Set.range r.wires
    · obtain ⟨i, rfl⟩ := hw
      rw [QRegister.basisBits_replaceIndex_apply, QRegister.extractIndex_replaceIndex,
          σ.symm_apply_apply, QRegister.basisBits_extractIndex]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
  right_inv z := eq_of_basisBits_eq fun w ↦ by
    by_cases hw : w ∈ Set.range r.wires
    · obtain ⟨i, rfl⟩ := hw
      rw [QRegister.basisBits_replaceIndex_apply, QRegister.extractIndex_replaceIndex,
          σ.apply_symm_apply, QRegister.basisBits_extractIndex]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
@[simp] theorem liftRegPerm_apply {k N : ℕ} (r : QRegister k N) (σ : Equiv.Perm (Fin (2 ^ k)))
    (z : Fin (2 ^ N)) : liftRegPerm r σ z = r.replaceIndex z (σ (r.extractIndex z)) := rfl
theorem embedMatrix_permutationUnitary_eq {k N : ℕ} (r : QRegister k N)
    (σ : Equiv.Perm (Fin (2 ^ k))) : r.embedMatrix (Operator.permutationUnitary σ).1 =
    (Operator.permutationUnitary (liftRegPerm r σ)).1 := by
  ext x y
  rw [embedMatrix_apply_sameOutside, permUnitary_apply, permUnitary_apply]
  by_cases hS : SameOutside (Set.range r.wires) y x
  · rw [ite_eq_left hS]
    have hiff : r.extractIndex x = σ (r.extractIndex y) ↔ x = liftRegPerm r σ y := by
      constructor
      · intro hex; apply eq_of_basisBits_eq; intro w
        change basisBits N x w = basisBits N (r.replaceIndex y (σ (r.extractIndex y))) w
        by_cases hw : w ∈ Set.range r.wires
        · obtain ⟨i, rfl⟩ := hw
          rw [QRegister.basisBits_replaceIndex_apply, ← hex, QRegister.basisBits_extractIndex]
        · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw, hS w hw]
      · rintro rfl; exact QRegister.extractIndex_replaceIndex r y _
    exact if_congr hiff rfl rfl
  · rw [ite_eq_right hS]
    have hne : x ≠ liftRegPerm r σ y := by
      rintro rfl
      exact hS fun w hw ↦ QRegister.basisBits_replaceIndex_of_not_mem r y _ w hw
    rw [ite_eq_right hne]
theorem embedUnitary_permutationUnitary_eq {k N : ℕ} (r : QRegister k N)
    (σ : Equiv.Perm (Fin (2 ^ k))) : r.embedUnitary (Operator.permutationUnitary σ) =
    Operator.permutationUnitary (liftRegPerm r σ) := Subtype.ext
    (embedMatrix_permutationUnitary_eq r σ)
theorem extractPair_inj {kData : ℕ} {z₁ z₂ : Fin (2 ^ (kData + 18))}
    (h : extractPair z₁ = extractPair z₂) : z₁ = z₂ := by
  obtain ⟨hd, hm⟩ := Prod.mk.inj (by unfold extractPair at h; exact h)
  apply eq_of_basisBits_eq; intro w
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) w
  · rw [← selDataInAct_apply i, ← QRegister.basisBits_extractIndex,
        ← QRegister.basisBits_extractIndex, hd]
  · rw [← selMeasInAct_apply j, ← QRegister.basisBits_extractIndex,
        ← QRegister.basisBits_extractIndex, hm]
theorem extractPair_lensSwapEquiv {kData : ℕ} (L : Slot18Lens kData)
    (z : Fin (2 ^ (kData + 18))) :
    extractPair (lensSwapEquiv L z) = lensSwapPerm L (extractPair z) := by
  change extractPair (liftPairIdx (lensSwapPerm L) z) = _
  exact extractPair_liftPairIdx (lensSwapPerm L) z
theorem lensSwapEquiv_involutive {kData : ℕ} (L : Slot18Lens kData)
    (z : Fin (2 ^ (kData + 18))) : lensSwapEquiv L (lensSwapEquiv L z) = z := by
  apply extractPair_inj
  rw [extractPair_lensSwapEquiv, extractPair_lensSwapEquiv]
  dsimp only [lensSwapPerm]
  exact Prod.ext (by rw [L.get_put, L.put_put, L.put_get]) (L.get_put _ _)
theorem basisBits_lensSwapEquiv_L_slot0Of_meas {kData : ℕ}
    (rSlot0 : QRegister 18 kData) (z : Fin (2 ^ (kData + 18))) (j : Fin 18) :
    basisBits (kData + 18) (lensSwapEquiv (L_slot0Of rSlot0) z) (selMeasInAct kData j) =
      basisBits (kData + 18) z (selDataInAct kData (rSlot0 j)) := by
  have hM : (selMeasInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) z) =
      rSlot0.extractIndex ((selDataInAct kData).extractIndex z) := (congrArg Prod.snd
      (extractPair_lensSwapEquiv (L_slot0Of rSlot0) z)).trans (L_slot0Of_tbl rSlot0 _)
  rw [← QRegister.basisBits_extractIndex (selMeasInAct kData) _ j, hM,
      QRegister.basisBits_extractIndex rSlot0 _ j,
      QRegister.basisBits_extractIndex (selDataInAct kData) z (rSlot0 j)]
theorem embedMatrix_selSubstSlot0_eq {kData : ℕ} (rSlot0 : QRegister 18 kData)
    (M : Operator (2 ^ kData)) : (selSubstSlot0 rSlot0).embedMatrix M =
    (uLensSwap (L_slot0Of rSlot0)).1 * (selDataInAct kData).embedMatrix M *
    (uLensSwap (L_slot0Of rSlot0)).1 := by
  have hEx : ∀ z : Fin (2 ^ (kData + 18)),
      (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) z) =
        (selSubstSlot0 rSlot0).extractIndex z := fun z ↦ by
    have hPair : (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) z) =
        rSlot0.replaceIndex ((selDataInAct kData).extractIndex z)
        ((selMeasInAct kData).extractIndex z) := (congrArg Prod.fst (extractPair_lensSwapEquiv
        (L_slot0Of rSlot0) z)).trans (L_slot0Of_updSlot rSlot0 _ _)
    rw [hPair]
    apply eq_of_basisBits_eq; intro i
    rw [QRegister.basisBits_extractIndex (selSubstSlot0 rSlot0) z i]
    by_cases hi : i ∈ Set.range rSlot0.wires
    · obtain ⟨j, rfl⟩ := hi
      rw [QRegister.basisBits_replaceIndex_apply, selSubstSlot0, rDataSubstSlot0_apply_slot0]
      exact QRegister.basisBits_extractIndex (selMeasInAct kData) z j
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hi,
          selSubstSlot0, rDataSubstSlot0_apply_of_not_mem _ _ _ _ hi]
      exact QRegister.basisBits_extractIndex (selDataInAct kData) z i
  have hSame : ∀ x y : Fin (2 ^ (kData + 18)),
      SameOutside (Set.range (selSubstSlot0 rSlot0).wires) y x ↔
        SameOutside (Set.range (selDataInAct kData).wires)
          (lensSwapEquiv (L_slot0Of rSlot0) y) (lensSwapEquiv (L_slot0Of rSlot0) x) := fun x y ↦ by
    constructor
    · intro hOut w; revert w
      refine Fin.addCases (fun i hw ↦ False.elim (hw ⟨i, selDataInAct_apply i⟩)) (fun j hw ↦ ?_)
      have hjNot : selDataInAct kData (rSlot0 j) ∉ Set.range (selSubstSlot0 rSlot0).wires := by
        rintro ⟨k, hk⟩
        by_cases hk0 : k ∈ Set.range rSlot0.wires
        · obtain ⟨j', rfl⟩ := hk0
          rw [selSubstSlot0, rDataSubstSlot0_apply_slot0] at hk
          exact (selDataInAct_disj_selMeasInAct kData).ne (rSlot0 j) j' hk.symm
        · rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem _ _ _ _ hk0] at hk
          exact hk0 ⟨j, (selDataInAct kData).wires.injective hk.symm⟩
      rw[← selMeasInAct_apply j, basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0 y j,
          basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0 x j]
      exact hOut _ hjNot
    · intro hOut w; revert w
      refine Fin.addCases (fun i hw ↦ ?_) (fun j hw ↦ ?_)
      · by_cases hi : i ∈ Set.range rSlot0.wires
        · obtain ⟨j, rfl⟩ := hi
          have hjNot : selMeasInAct kData j ∉ Set.range (selDataInAct kData).wires :=
            fun ⟨k, hk⟩ ↦ (selDataInAct_disj_selMeasInAct kData).ne k j hk
          have h1 := hOut (selMeasInAct kData j) hjNot
          rw[basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0 y j,
              basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0 x j, selDataInAct_apply] at h1
          exact h1
        · exact False.elim (hw ⟨i, by
            rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem _ _ _ _ hi, selDataInAct_apply]⟩)
      · exact False.elim (hw ⟨rSlot0 j, by
          rw [selSubstSlot0, rDataSubstSlot0_apply_slot0, selMeasInAct_apply]⟩)
  ext x y
  dsimp only [uLensSwap]
  rw [permUnitary_inv_conj_apply_part2 (lensSwapEquiv (L_slot0Of rSlot0))
        (lensSwapEquiv_involutive (L_slot0Of rSlot0)) _ x y,
      embedMatrix_apply_sameOutside, embedMatrix_apply_sameOutside, hEx x, hEx y]
  by_cases hS : SameOutside (Set.range (selSubstSlot0 rSlot0).wires) y x
  · rw [ite_eq_left hS, ite_eq_left ((hSame x y).mp hS)]
  · rw [ite_eq_right hS, ite_eq_right (fun h ↦ hS ((hSame x y).mpr h))]
theorem embedUnitary_rDataSubstSlot0_eq {kData n : ℕ} (rSlot0 : QRegister 18 kData)
    (rData : QRegister kData n) (rAnchor18 : QRegister 18 n)
    (hDA : rData.DisjointWires rAnchor18) (U : Unitary (2 ^ kData)) :
    (rDataSubstSlot0 rSlot0 rData rAnchor18 hDA).embedUnitary U =
    (rData.concat rAnchor18 hDA).embedUnitary (uLensSwap (L_slot0Of rSlot0) * (selDataInAct
    kData).embedUnitary U * uLensSwap (L_slot0Of rSlot0)) := by
  apply Subtype.ext
  rw [← concat_compose_selSubstSlot0 rSlot0 rData rAnchor18 hDA,
      QRegister.embedUnitary_val, QRegister.embedMatrix_compose, embedMatrix_selSubstSlot0_eq]
  simp only [QRegister.embedUnitary_val, Submonoid.coe_mul, QRegister.embedMatrix_mul,
    Matrix.mul_assoc]
theorem extractPair_liftRegPerm_data {kSub kData : ℕ} (r : QRegister kSub kData)
    (σ : Equiv.Perm (Fin (2 ^ kSub))) (z : Fin (2 ^ (kData + 18))) : extractPair
    (liftRegPerm ((selDataInAct kData).compose r) σ z) = (r.replaceIndex (extractPair z).1 (σ
    (r.extractIndex (extractPair z).1)), (extractPair z).2) := by
  have hDisj : (selMeasInAct kData).DisjointWires ((selDataInAct kData).compose r) :=
    (QRegister.disjoint_comm.mp (selDataInAct_disj_selMeasInAct kData)).compose_right r
  rw [liftRegPerm_apply, QRegister.extractIndex_compose (selDataInAct kData) r z]
  dsimp only [extractPair]
  refine Prod.ext ?_ ?_
  · apply eq_of_basisBits_eq; intro i
    rw [QRegister.basisBits_extractIndex (selDataInAct kData)]
    by_cases hi : i ∈ Set.range r.wires
    · obtain ⟨j, rfl⟩ := hi
      rw [← QRegister.compose_apply (selDataInAct kData) r j,
          QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
    · have hnot : selDataInAct kData i ∉ Set.range ((selDataInAct kData).compose r).wires :=
        fun ⟨j, hj⟩ ↦ hi ⟨j, (selDataInAct kData).wires.injective hj⟩
      rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hi,
          QRegister.basisBits_extractIndex]
  · exact QRegister.extractIndex_replaceIndex_of_disjoint
      (selMeasInAct kData) ((selDataInAct kData).compose r) hDisj z _
theorem basisBits_coinBarrelPermFast_eq {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (c : Fin (2 ^ (fullSysCoreWires mPayload))) :
    basisBits (fullSysCoreWires mPayload) (coinBarrelPermFast hmPay c) =
      coinBarrelBitFnFast hmPay (basisBits (fullSysCoreWires mPayload) c) := by
  unfold coinBarrelPermFast
  change (basisBitsEquiv (fullSysCoreWires mPayload))
    ((basisBitsEquiv (fullSysCoreWires mPayload)).symm
      (coinBarrelBitFnFast hmPay (basisBits (fullSysCoreWires mPayload) c))) = _
  exact (basisBitsEquiv (fullSysCoreWires mPayload)).apply_symm_apply _
theorem swapElec0Bits_rSlot0Core_eq {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (e : Fin 218)
    (β : BitAssignment (fullSysCoreWires mPayload)) (j : Fin 18) :
    swapElec0Bits e β (rFullSysElecSlot hmPay 0 j) = β (rFullSysElecSlot hmPay e j) := by
  have hj0 : (rFullSysElecSlot hmPay 0 j).val = j.val := by
    rw [rFullSysElecSlot_val]; simp
  by_cases he0 : e.val = 0
  · have he : e = 0 := Fin.ext he0
    unfold swapElec0Bits
    rw [ite_eq_left he0, he]
  · unfold swapElec0Bits
    rw [ite_eq_right he0]
    have hjlt : (rFullSysElecSlot hmPay 0 j).val < 18 := by rw [hj0]; exact j.isLt
    rw [dite_eq_left hjlt]
    exact congrArg β (Fin.ext (by
      dsimp only; rw [rFullSysElecSlot_val, rFullSysElecSlot_val]; omega))
theorem compose_replaceIndex_eq_replaceIndex_replaceIndex {k₁ k₂ k₃ : ℕ}
    (r₁ : QRegister k₂ k₃) (r₂ : QRegister k₁ k₂) (d : Fin (2 ^ k₃)) (m : Fin (2 ^ k₁)) :
    (r₁.compose r₂).replaceIndex d m = r₁.replaceIndex d
    (r₂.replaceIndex (r₁.extractIndex d) m) := by
  apply eq_of_basisBits_eq; intro w
  by_cases hw1 : w ∈ Set.range r₁.wires
  · obtain ⟨u, rfl⟩ := hw1
    rw [QRegister.basisBits_replaceIndex_apply]
    by_cases hu2 : u ∈ Set.range r₂.wires
    · obtain ⟨j, rfl⟩ := hu2
      rw [QRegister.basisBits_replaceIndex_apply]
      exact QRegister.basisBits_replaceIndex_apply (r₁.compose r₂) d m j
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hu2,
          QRegister.basisBits_extractIndex,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _
            (fun ⟨j, hj⟩ ↦ hu2 ⟨j, r₁.wires.injective hj⟩)]
  · rw[QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw1,
      QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ hw1 ⟨r₂ j, hj⟩)]
theorem uLensSwap_coinBarrelFastOnDataLens_eq {mPayload kData : ℕ} (hmPay : 80 ≤ mPayload)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) :
    uLensSwap (coinBarrelFastOnDataLens hmPay selCore) =
      ((selDataInAct kData).compose selCore).embedUnitary (uBarrelFast hmPay) *
        uLensSwap (L_slot0Of (selCore.compose (rFullSysElecSlot hmPay 0))) *
        ((selDataInAct kData).compose selCore).embedUnitary (uBarrelFast hmPay) := by
  let rSlot0Core := rFullSysElecSlot hmPay 0
  let rSlot0Full := selCore.compose rSlot0Core
  let L := coinBarrelFastOnDataLens hmPay selCore
  let permBar := liftRegPerm ((selDataInAct kData).compose selCore) (coinBarrelPermFast hmPay)
  have hBar : ((selDataInAct kData).compose selCore).embedUnitary (uBarrelFast hmPay) =
      Operator.permutationUnitary permBar := embedUnitary_permutationUnitary_eq
      ((selDataInAct kData).compose selCore) (coinBarrelPermFast hmPay)
  change Operator.permutationUnitary (lensSwapEquiv L) = _
  rw [hBar]
  change Operator.permutationUnitary (lensSwapEquiv L) = Operator.permutationUnitary permBar *
    Operator.permutationUnitary (lensSwapEquiv (L_slot0Of rSlot0Full)) *
    Operator.permutationUnitary permBar
  rw [permutationUnitary_mul_part2, permutationUnitary_mul_part2]
  apply congrArg Operator.permutationUnitary
  ext1 z
  change lensSwapEquiv L z = permBar (lensSwapEquiv (L_slot0Of rSlot0Full) (permBar z))
  apply extractPair_inj
  rw [extractPair_lensSwapEquiv, extractPair_liftRegPerm_data,
      extractPair_lensSwapEquiv, extractPair_liftRegPerm_data]
  let d := (extractPair z).1
  let m := (extractPair z).2
  let c := selCore.extractIndex d
  let e : Fin 218 := coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) c)
  let c₁ := coinBarrelPermFast hmPay c
  let d₁ := selCore.replaceIndex d c₁
  have hd₁_core : selCore.extractIndex d₁ = c₁ := QRegister.extractIndex_replaceIndex selCore d c₁
  have hSlot0_ex : rSlot0Full.extractIndex d₁ = L.tbl d := by
    have h1 : rSlot0Full.extractIndex d₁ = rSlot0Core.extractIndex c₁ := by
      dsimp only [rSlot0Full]
      rw [QRegister.extractIndex_compose, hd₁_core]
    have h2 : L.tbl d = (rFullSysElecSlot hmPay e).extractIndex c := by
      dsimp only [L]
      rw [coinBarrelFastOnDataLens_tbl, QRegister.extractIndex_compose]
      rfl
    rw [h1, h2]
    apply eq_of_basisBits_eq; intro j
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        basisBits_coinBarrelPermFast_eq hmPay]
    exact swapElec0Bits_rSlot0Core_eq hmPay e (basisBits (fullSysCoreWires mPayload) c) j
  let c₂ := rSlot0Core.replaceIndex c₁ m
  have hd₂_eq : rSlot0Full.replaceIndex d₁ m = selCore.replaceIndex d c₂ := by
    apply eq_of_basisBits_eq; intro w
    by_cases hwC : w ∈ Set.range selCore.wires
    · obtain ⟨u, rfl⟩ := hwC
      rw [QRegister.basisBits_replaceIndex_apply]
      by_cases hu0 : u ∈ Set.range rSlot0Core.wires
      · obtain ⟨j, rfl⟩ := hu0
        change basisBits kData (rSlot0Full.replaceIndex d₁ m) (rSlot0Full j) = _
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
      · have hnot : selCore u ∉ Set.range rSlot0Full.wires :=
          fun ⟨j, hj⟩ ↦ hu0 ⟨j, selCore.wires.injective hj⟩
        rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
            QRegister.basisBits_replaceIndex_apply,
            QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hu0]
    · have hnot : w ∉ Set.range rSlot0Full.wires := fun ⟨j, hj⟩ ↦ hwC ⟨rSlot0Core j, hj⟩
      rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwC,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwC]
  have hc₂_idx : coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) c₂) = e := by
    have hRep : coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) c₂) =
        coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) c₁) :=
      BoothOpt_03_CoinBarrelIdxFastTrueSwap.coinBarrelIdxFast_replaceIndex_elecSlot
        hmPay 0 c₁ m
    rw [hRep, basisBits_coinBarrelPermFast_eq hmPay]
    exact coinBarrelIdxFast_swap_inv hmPay e (basisBits (fullSysCoreWires mPayload) c)
  dsimp only [lensSwapPerm, L_slot0Of_tbl, L_slot0Of_updSlot]
  change (L.updSlot d m, L.tbl d) = (selCore.replaceIndex (rSlot0Full.replaceIndex d₁ m)
    (coinBarrelPermFast hmPay (selCore.extractIndex (rSlot0Full.replaceIndex d₁ m))),
    rSlot0Full.extractIndex d₁)
  rw [hSlot0_ex, hd₂_eq, QRegister.extractIndex_replaceIndex, QRegister.replaceIndex_replaceIndex]
  refine Prod.ext ?_ ?_
  · have hUpd : L.updSlot d m =
        selCore.replaceIndex d ((rFullSysElecSlot hmPay e).replaceIndex c m) := by
      dsimp only [L]
      rw [coinBarrelFastOnDataLens_updSlot, compose_replaceIndex_eq_replaceIndex_replaceIndex]
      rfl
    rw [hUpd]
    apply congrArg (selCore.replaceIndex d)
    apply eq_of_basisBits_eq; intro w
    rw [basisBits_coinBarrelPermFast_eq hmPay]
    dsimp only [coinBarrelBitFnFast]
    rw [hc₂_idx]
    have hInv : basisBits (fullSysCoreWires mPayload) c₂ = swapElec0Bits e (basisBits
        (fullSysCoreWires mPayload) ((rFullSysElecSlot hmPay e).replaceIndex c m)) := by
      funext u
      have hu0_iff : u ∈ Set.range rSlot0Core.wires ↔ u.val < 18 := by
        constructor
        · rintro ⟨j, rfl⟩; dsimp only [rSlot0Core]; rw [rFullSysElecSlot_val]; have := j.isLt; omega
        · intro hlt; exact ⟨⟨u.val, hlt⟩, Fin.ext (by
            dsimp only [rSlot0Core]; rw [rFullSysElecSlot_val]; simp)⟩
      by_cases he0 : e.val = 0
      · have he : e = 0 := Fin.ext he0
        unfold swapElec0Bits; rw [ite_eq_left he0]
        by_cases hu0 : u.val < 18
        · obtain ⟨j, rfl⟩ := hu0_iff.mpr hu0
          rw [he]; dsimp only [rSlot0Core]
          rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
        · have hnot : u ∉ Set.range rSlot0Core.wires := fun h ↦ hu0 (hu0_iff.mp h)
          have hnotE : u ∉ Set.range (rFullSysElecSlot hmPay e).wires := by
            rw [he]; exact hnot
          rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
              QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotE,
              basisBits_coinBarrelPermFast_eq hmPay]
          unfold coinBarrelBitFnFast swapElec0Bits
          rw [ite_eq_left he0]
      · unfold swapElec0Bits; rw [ite_eq_right he0]
        by_cases hu0 : u.val < 18
        · rw [dite_eq_left hu0]
          have hSlot : (⟨18 * e.val + u.val,
              by have := e.isLt; have := h3924_le_fullSysCoreWires hmPay; omega⟩ :
                Fin (fullSysCoreWires mPayload)) =
              rFullSysElecSlot hmPay e ⟨u.val, hu0⟩ :=
            Fin.ext (by dsimp only; rw [rFullSysElecSlot_val])
          rw [hSlot, QRegister.basisBits_replaceIndex_apply]
          have hu_eq : u = rSlot0Core ⟨u.val, hu0⟩ :=
            Fin.ext (by dsimp only [rSlot0Core]; rw [rFullSysElecSlot_val]; simp)
          conv_lhs => rw [hu_eq]
          rw [QRegister.basisBits_replaceIndex_apply]
        · rw [dite_eq_right hu0]
          have hnot0 : u ∉ Set.range rSlot0Core.wires := fun h ↦ hu0 (hu0_iff.mp h)
          rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot0,
              basisBits_coinBarrelPermFast_eq hmPay]
          change swapElec0Bits e (basisBits (fullSysCoreWires mPayload) c) u = _
          by_cases hue : 18 * e.val ≤ u.val ∧ u.val < 18 * e.val + 18
          · rw [dite_eq_left hue]
            have hnotE : (⟨u.val - 18 * e.val,
                by have := h3924_le_fullSysCoreWires hmPay; omega⟩ :
                  Fin (fullSysCoreWires mPayload)) ∉
                Set.range (rFullSysElecSlot hmPay e).wires := by
              rintro ⟨j, hj⟩
              have hv := congrArg Fin.val hj
              dsimp only at hv
              rw [rFullSysElecSlot_val] at hv
              have := j.isLt; omega
            rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotE]
            unfold swapElec0Bits; rw [ite_eq_right he0, dite_eq_right hu0, dite_eq_left hue]
          · rw [dite_eq_right hue]
            have hnotE : u ∉ Set.range (rFullSysElecSlot hmPay e).wires := by
              rintro ⟨j, rfl⟩
              rw [rFullSysElecSlot_val] at hue
              have := j.isLt; omega
            rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotE]
            unfold swapElec0Bits; rw [ite_eq_right he0, dite_eq_right hu0, dite_eq_right hue]
    rw [hInv, swapElec0Bits_self]
  · rfl
/-- Key factorization `σ_e = τ_e * σ_0 * τ_e` across all basis states (covering both `e = 0` and
  `e ≠ 0`). -/
theorem uAnchorLensSwap_eq_uBarrelFastAct_conj :
    uAnchorLensSwap = uBarrelFastAct * uSlot0MeasSwap * uBarrelFastAct :=
  uLensSwap_coinBarrelFastOnDataLens_eq (le_refl 80) rCoreFull
theorem uAnchorLensSwap_mul_uBarrelFastAct_mul_uSlot0MeasSwap :
    uAnchorLensSwap * (uBarrelFastAct * uSlot0MeasSwap) = uBarrelFastAct := by
  rw [uAnchorLensSwap_eq_uBarrelFastAct_conj]
  calc (uBarrelFastAct * uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap)
      = uBarrelFastAct * uSlot0MeasSwap * (uBarrelFastAct * uBarrelFastAct) * uSlot0MeasSwap := by
          simp only [mul_assoc]
    _ = uBarrelFastAct * (uSlot0MeasSwap * uSlot0MeasSwap) := by
          rw [uBarrelFastAct_mul_self, mul_one, mul_assoc]
    _ = uBarrelFastAct := by rw [uSlot0MeasSwap_mul_self, mul_one]
theorem uSlot0MeasSwap_mul_uBarrelFastAct_mul_uAnchorLensSwap :
    (uSlot0MeasSwap * uBarrelFastAct) * uAnchorLensSwap = uBarrelFastAct := by
  rw [uAnchorLensSwap_eq_uBarrelFastAct_conj]
  calc (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap * uBarrelFastAct)
      = uSlot0MeasSwap * (uBarrelFastAct * uBarrelFastAct) * uSlot0MeasSwap * uBarrelFastAct := by
          simp only [mul_assoc]
    _ = (uSlot0MeasSwap * uSlot0MeasSwap) * uBarrelFastAct := by
          rw [uBarrelFastAct_mul_self, mul_one]
    _ = uBarrelFastAct := by rw [uSlot0MeasSwap_mul_self, one_mul]
theorem uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct :
    uBarrelFastAct * uSlot0MeasSwap = uAnchorLensSwap * uBarrelFastAct := by
  calc uBarrelFastAct * uSlot0MeasSwap
      = (uAnchorLensSwap * uAnchorLensSwap) * (uBarrelFastAct * uSlot0MeasSwap) := by
          rw [uAnchorLensSwap_mul_self, one_mul]
    _ = uAnchorLensSwap * (uAnchorLensSwap * (uBarrelFastAct * uSlot0MeasSwap)) := by
          simp only [mul_assoc]
    _ = uAnchorLensSwap * uBarrelFastAct := by
          rw [uAnchorLensSwap_mul_uBarrelFastAct_mul_uSlot0MeasSwap]
theorem uSlot0MeasSwap_mul_uBarrelFastAct_eq_uBarrelFastAct_mul_uAnchorLensSwap :
    uSlot0MeasSwap * uBarrelFastAct = uBarrelFastAct * uAnchorLensSwap := by
  calc uSlot0MeasSwap * uBarrelFastAct
      = (uSlot0MeasSwap * uBarrelFastAct) * (uAnchorLensSwap * uAnchorLensSwap) := by
          rw [uAnchorLensSwap_mul_self, mul_one]
    _ = ((uSlot0MeasSwap * uBarrelFastAct) * uAnchorLensSwap) * uAnchorLensSwap := by
          simp only [mul_assoc]
    _ = uBarrelFastAct * uAnchorLensSwap := by
          rw [uSlot0MeasSwap_mul_uBarrelFastAct_mul_uAnchorLensSwap]
theorem uLensSwap_mul_P_anc0_gen {kData : ℕ} (L : Slot18Lens kData) : (uLensSwap L).1 *
    (selMeasInAct kData).basisOutcomeProjector 0 = P_slot0 L * (uLensSwap L).1 := by
  have hInv : (uLensSwap L).1 * (uLensSwap L).1 = 1 := by
    rw [← Submonoid.coe_mul, uLensSwap_mul_self_eq_one, OneMemClass.coe_one]
  dsimp only [P_slot0]
  rw [Matrix.mul_assoc _ _ (uLensSwap L).1, hInv, Matrix.mul_one]
theorem uAnchorLensSwap_mul_P_anc0 : uAnchorLensSwap.1 * P_anc0 = P_slot0 L_anchor *
    uAnchorLensSwap.1 := uLensSwap_mul_P_anc0_gen L_anchor
theorem uBarrelFastAct_mul_uSlot0MeasSwap_mul_P_anc0 : (uBarrelFastAct * uSlot0MeasSwap).1 *
    P_anc0 = P_slot0 L_anchor * (uBarrelFastAct * uSlot0MeasSwap).1 := by
  have hComm : uBarrelFastAct.1 * P_anc0 = P_anc0 * uBarrelFastAct.1 := by
    dsimp only [uBarrelFastAct, P_anc0]
    rw [QRegister.embedUnitary_val]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint ((selDataInAct
      kFull80).compose
      rCoreFull)) (selMeasInAct kFull80)
      ((selDataInAct_disj_selMeasInAct kFull80).compose_left rCoreFull) _ 0
  rw [uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct,
      Submonoid.coe_mul, Matrix.mul_assoc, hComm, ← Matrix.mul_assoc,
      uAnchorLensSwap_mul_P_anc0, Matrix.mul_assoc]
theorem P_slot0_mul_self_gen {kData : ℕ} (L : Slot18Lens kData) :
    P_slot0 L * P_slot0 L = P_slot0 L := by
  rw [P_slot0_eq_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext z; split_ifs <;> simp
theorem P_slot0_mul_uBarrelFastAct_mul_uSlot0MeasSwap_mul_P_anc0 :
    P_slot0 L_anchor * ((uBarrelFastAct * uSlot0MeasSwap).1 * P_anc0) =
      (uBarrelFastAct * uSlot0MeasSwap).1 * P_anc0 := by
  rw [uBarrelFastAct_mul_uSlot0MeasSwap_mul_P_anc0, ← Matrix.mul_assoc,
      P_slot0_mul_self_gen L_anchor]
theorem commutesWithReg_entry_eq_zero_of_ne {k N : ℕ} {r : QRegister k N}
    {M : Operator (2 ^ N)} (hComm : CommutesWithReg r M) {x y : Fin (2 ^ N)}
    (hne : r.extractIndex x ≠ r.extractIndex y) : M x y = 0 := by
  let P : Operator (2 ^ k) := Matrix.diagonal fun s ↦ if s = r.extractIndex y then 1 else 0
  have hEq := congrFun (congrFun (hComm P) x) y
  have hDiag : r.embedMatrix P =
      Matrix.diagonal fun z ↦ if r.extractIndex z = r.extractIndex y then (1 : ℂ) else 0 := by
    ext a b; rw [embedMatrix_apply_sameOutside, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      have hS : SameOutside (Set.range r.wires) a a := fun _ _ ↦ rfl
      rw [ite_eq_left hS]; simp [P]
    · simp only [hab, ↓reduceIte]
      by_cases hS : SameOutside (Set.range r.wires) b a
      · rw [ite_eq_left hS]
        have hne_ex : r.extractIndex a ≠ r.extractIndex b := fun hex ↦ hab <|
          eq_of_basisBits_eq fun w ↦ by
            by_cases hw : w ∈ Set.range r.wires
            · obtain ⟨i, rfl⟩ := hw
              rw [← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex, hex]
            · exact hS w hw
        exact Matrix.diagonal_apply_ne _ hne_ex
      · rw [ite_eq_right hS]
  rw [hDiag, Matrix.mul_diagonal, Matrix.diagonal_mul, ite_eq_left rfl, ite_eq_right hne,
      mul_one, zero_mul] at hEq
  exact hEq
theorem commutesWithReg_entry_replaceIndex_eq {k N : ℕ} {r : QRegister k N}
    {M : Operator (2 ^ N)} (hComm : CommutesWithReg r M) {x y : Fin (2 ^ N)} (v : Fin (2 ^ k))
    (hEx : r.extractIndex x = r.extractIndex y) : M (r.replaceIndex x v) (r.replaceIndex y v)
    = M x y := by
  let s₀ := r.extractIndex y
  let σ : Equiv.Perm (Fin (2 ^ k)) := Equiv.swap v s₀
  have hInv : ∀ z, liftRegPerm r σ (liftRegPerm r σ z) = z := fun z ↦ by
    rw [liftRegPerm_apply, liftRegPerm_apply, QRegister.extractIndex_replaceIndex,
        Equiv.swap_apply_self, QRegister.replaceIndex_replaceIndex]
    exact eq_of_basisBits_eq fun w ↦ by
      by_cases hw : w ∈ Set.range r.wires
      · obtain ⟨i, rfl⟩ := hw
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
      · exact QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw
  have hU : (Operator.permutationUnitary (liftRegPerm r σ)).1 * M *
      (Operator.permutationUnitary (liftRegPerm r σ)).1 = M := by
    have h1 := hComm (Operator.permutationUnitary σ).1
    rw [embedMatrix_permutationUnitary_eq] at h1
    have hSq : (Operator.permutationUnitary (liftRegPerm r σ)).1 *
        (Operator.permutationUnitary (liftRegPerm r σ)).1 = 1 := by
      rw [← Submonoid.coe_mul, permutationUnitary_mul_part2]
      have hId : (liftRegPerm r σ).trans (liftRegPerm r σ) = Equiv.refl _ := by
        ext1 z; exact hInv z
      rw [hId]; ext a b; rw [permUnitary_apply, Matrix.one_apply]
      by_cases hab : a = b <;> simp [hab]
    calc (Operator.permutationUnitary (liftRegPerm r σ)).1 * M *
          (Operator.permutationUnitary (liftRegPerm r σ)).1
        = (Operator.permutationUnitary (liftRegPerm r σ)).1 *
            ((Operator.permutationUnitary (liftRegPerm r σ)).1 * M) := by
          rw [Matrix.mul_assoc, ← h1]
      _ = M := by rw [← Matrix.mul_assoc, hSq, Matrix.one_mul]
  have hApp := congrFun (congrFun hU (r.replaceIndex x v)) (r.replaceIndex y v)
  rw [permUnitary_inv_conj_apply_part2 (liftRegPerm r σ) hInv M] at hApp
  have hLx : liftRegPerm r σ (r.replaceIndex x v) = x := by
    dsimp only [s₀, σ]
    rw [liftRegPerm_apply, QRegister.extractIndex_replaceIndex, Equiv.swap_apply_left,
        QRegister.replaceIndex_replaceIndex, ← hEx]
    exact PartnerAndAnchorSlot18LensAndMidBA.replaceIndex_extractIndex r x
  have hLy : liftRegPerm r σ (r.replaceIndex y v) = y := by
    dsimp only [s₀, σ]
    rw [liftRegPerm_apply, QRegister.extractIndex_replaceIndex, Equiv.swap_apply_left,
        QRegister.replaceIndex_replaceIndex]
    exact PartnerAndAnchorSlot18LensAndMidBA.replaceIndex_extractIndex r y
  rw [hLx, hLy] at hApp
  exact hApp.symm
theorem uLensSwap_slot0_conj_eq_gen {mPayload kData : ℕ} (hmPay : 80 ≤ mPayload)
    (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (U : Unitary (2 ^ kData))
    (hSpec : ActsAsIdOnSpectatorWires selCore U)
    (hHigh : PreservesHigh3924On selCore U) :
    let uBar := ((selDataInAct kData).compose selCore).embedUnitary (uBarrelFast hmPay)
    let uS0 := uLensSwap (L_slot0Of (selCore.compose (rFullSysElecSlot hmPay 0)))
    uS0 * (selDataInAct kData).embedUnitary U * uS0 =
      (uBar * uS0) * (selDataInAct kData).embedUnitary U * (uS0 * uBar) := by
  intro uBar uS0
  let rSlot0Core := rFullSysElecSlot hmPay 0
  let rSlot0Full := selCore.compose rSlot0Core
  let L0 := L_slot0Of rSlot0Full
  let permBar := liftRegPerm ((selDataInAct kData).compose selCore) (coinBarrelPermFast hmPay)
  let permConj := ((lensSwapEquiv L0).trans permBar).trans (lensSwapEquiv L0)
  have hPermConj_inv : ∀ z, permConj (permConj z) = z := fun z ↦ by
    dsimp only [permConj, Equiv.trans_apply]
    have hBar_inv : ∀ w, permBar (permBar w) = w := fun w ↦ by
      dsimp only [permBar]
      rw [liftRegPerm_apply, liftRegPerm_apply, QRegister.extractIndex_replaceIndex,
          CoinDispatchedBarrel288.coinBarrelPermFast_apply_self,
          QRegister.replaceIndex_replaceIndex]
      exact PartnerAndAnchorSlot18LensAndMidBA.replaceIndex_extractIndex _ w
    rw [lensSwapEquiv_involutive, hBar_inv, lensSwapEquiv_involutive]
  have hConjug : Operator.permutationUnitary permConj * (selDataInAct kData).embedUnitary U *
      Operator.permutationUnitary permConj = (selDataInAct kData).embedUnitary U := by
    apply Subtype.ext; ext x y
    change ((Operator.permutationUnitary permConj).1 * (selDataInAct kData).embedMatrix U.1 *
      (Operator.permutationUnitary permConj).1) x y = ((selDataInAct kData).embedMatrix U.1) x y
    rw [permUnitary_inv_conj_apply_part2 permConj hPermConj_inv]
    let eOf : Fin (2 ^ kData) → Fin 218 := fun d ↦
      coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) (selCore.extractIndex d))
    have hSameMeas : ∀ a b : Fin (2 ^ (kData + 18)),
        SameOutside (Set.range (selDataInAct kData).wires) b a ↔
          (extractPair a).2 = (extractPair b).2 := fun a b ↦ by
      constructor
      · intro hS; dsimp only [extractPair]; apply eq_of_basisBits_eq; intro j
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        exact hS (selMeasInAct kData j)
          (fun ⟨i, hi⟩ ↦ (selDataInAct_disj_selMeasInAct kData).ne i j hi)
      · intro hm w; revert w
        refine Fin.addCases (fun i hw ↦ False.elim (hw ⟨i, selDataInAct_apply i⟩)) (fun j _ ↦ ?_)
        have hm' : (selMeasInAct kData).extractIndex a = (selMeasInAct kData).extractIndex b := hm
        rw [← selMeasInAct_apply j,
            ← QRegister.basisBits_extractIndex (selMeasInAct kData) b j,
            ← QRegister.basisBits_extractIndex (selMeasInAct kData) a j, hm']
    have hPermConj_pair : ∀ z : Fin (2 ^ (kData + 18)),
        if (eOf (extractPair z).1).val = 0 then permConj z = z
        else extractPair (permConj z) =
          ((selCore.compose (rFullSysElecSlot hmPay (eOf (extractPair z).1))).replaceIndex
              (extractPair z).1 (extractPair z).2,
           (selCore.compose (rFullSysElecSlot hmPay (eOf (extractPair z).1))).extractIndex
              (extractPair z).1) := fun z ↦ by
      let d := (extractPair z).1
      let m := (extractPair z).2
      let c := selCore.extractIndex d
      let e := eOf d
      change if e.val = 0 then permConj z = z else extractPair (permConj z) =
        ((selCore.compose (rFullSysElecSlot hmPay e)).replaceIndex d m, (selCore.compose
        (rFullSysElecSlot hmPay e)).extractIndex d)
      have hStep1 : extractPair (lensSwapEquiv L0 z) =
          (selCore.replaceIndex d (rSlot0Core.replaceIndex c m), rSlot0Core.extractIndex c) := by
        rw [extractPair_lensSwapEquiv]
        dsimp only [lensSwapPerm, L0, L_slot0Of_tbl, L_slot0Of_updSlot, rSlot0Full]
        refine Prod.ext ?_ ?_
        · exact compose_replaceIndex_eq_replaceIndex_replaceIndex selCore rSlot0Core d m
        · exact QRegister.extractIndex_compose selCore rSlot0Core d
      have he_c1 : coinBarrelIdxFast hmPay
          (basisBits (fullSysCoreWires mPayload) (rSlot0Core.replaceIndex c m)) = e :=
        BoothOpt_03_CoinBarrelIdxFastTrueSwap.coinBarrelIdxFast_replaceIndex_elecSlot
          hmPay 0 c m
      have hStep2 : extractPair (permBar (lensSwapEquiv L0 z)) =
          (selCore.replaceIndex d (coinBarrelPermFast hmPay (rSlot0Core.replaceIndex c m)),
           rSlot0Core.extractIndex c) := by
        rw [extractPair_liftRegPerm_data, hStep1, QRegister.extractIndex_replaceIndex,
            QRegister.replaceIndex_replaceIndex]
      have hStep3 : extractPair (permConj z) = (selCore.replaceIndex d
          (rSlot0Core.replaceIndex (coinBarrelPermFast hmPay (rSlot0Core.replaceIndex c m))
          (rSlot0Core.extractIndex c)), rSlot0Core.extractIndex (coinBarrelPermFast hmPay
          (rSlot0Core.replaceIndex c m))) := by
        change extractPair (lensSwapEquiv L0 (permBar (lensSwapEquiv L0 z))) = _
        rw [extractPair_lensSwapEquiv, hStep2]
        dsimp only [lensSwapPerm, L0, L_slot0Of_tbl, L_slot0Of_updSlot, rSlot0Full]
        refine Prod.ext ?_ ?_
        · rw [compose_replaceIndex_eq_replaceIndex_replaceIndex,
            QRegister.extractIndex_replaceIndex,
              QRegister.replaceIndex_replaceIndex]
        · rw [QRegister.extractIndex_compose, QRegister.extractIndex_replaceIndex]
      by_cases he0 : e.val = 0
      · rw [ite_eq_left he0]
        apply extractPair_inj; rw [hStep3]
        have hPermId : coinBarrelPermFast hmPay (rSlot0Core.replaceIndex c m) =
            rSlot0Core.replaceIndex c m := by
          apply eq_of_basisBits_eq; intro w
          rw [basisBits_coinBarrelPermFast_eq hmPay]
          unfold coinBarrelBitFnFast
          rw [he_c1]
          unfold swapElec0Bits; rw [ite_eq_left he0]
        rw [hPermId, QRegister.extractIndex_replaceIndex, QRegister.replaceIndex_replaceIndex,
            PartnerAndAnchorSlot18LensAndMidBA.replaceIndex_extractIndex,
            PartnerAndAnchorSlot18LensAndMidBA.replaceIndex_extractIndex]
      · rw [ite_eq_right he0, hStep3]
        refine Prod.ext ?_ ?_
        · apply eq_of_basisBits_eq; intro w
          by_cases hwC : w ∈ Set.range selCore.wires
          · obtain ⟨u, rfl⟩ := hwC
            rw [QRegister.basisBits_replaceIndex_apply]
            have hu0_iff : u ∈ Set.range rSlot0Core.wires ↔ u.val < 18 := by
              constructor
              · rintro ⟨j, rfl⟩; dsimp only [rSlot0Core]; rw [rFullSysElecSlot_val]; have := j.isLt;
                  omega
              · intro hlt; exact ⟨⟨u.val, hlt⟩, Fin.ext (by
                  dsimp only [rSlot0Core]; rw [rFullSysElecSlot_val]; simp)⟩
            by_cases hu0 : u.val < 18
            · obtain ⟨j, rfl⟩ := hu0_iff.mpr hu0
              have hnotE : selCore (rSlot0Core j) ∉
                  Set.range (selCore.compose (rFullSysElecSlot hmPay e)).wires := by
                rintro ⟨j', hj'⟩
                have hv := congrArg Fin.val (selCore.wires.injective hj')
                dsimp only [rSlot0Core] at hv
                rw [rFullSysElecSlot_val, rFullSysElecSlot_val] at hv
                have := j.isLt; omega
              rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex,
                  QRegister.basisBits_extractIndex,
                  QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotE]
            · have hnot0 : u ∉ Set.range rSlot0Core.wires := fun h ↦ hu0 (hu0_iff.mp h)
              rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot0,
                  basisBits_coinBarrelPermFast_eq hmPay]
              unfold coinBarrelBitFnFast; rw [he_c1]
              unfold swapElec0Bits; rw [ite_eq_right he0, dite_eq_right hu0]
              by_cases hue : 18 * e.val ≤ u.val ∧ u.val < 18 * e.val + 18
              · rw [dite_eq_left hue]
                let j : Fin 18 := ⟨u.val - 18 * e.val, by omega⟩
                have hSlot0 : (⟨u.val - 18 * e.val,
                    by have := h3924_le_fullSysCoreWires hmPay; omega⟩ :
                      Fin (fullSysCoreWires mPayload)) = rSlot0Core j :=
                  Fin.ext (by dsimp only [rSlot0Core]; rw [rFullSysElecSlot_val]; simp [j])
                have hSlotE : selCore u = (selCore.compose (rFullSysElecSlot hmPay e)) j :=
                  congrArg selCore (Fin.ext (by rw [rFullSysElecSlot_val]; dsimp [j]; omega))
                rw [hSlot0, QRegister.basisBits_replaceIndex_apply, hSlotE,
                    QRegister.basisBits_replaceIndex_apply]
              · rw [dite_eq_right hue]
                have hnotE : selCore u ∉
                    Set.range (selCore.compose (rFullSysElecSlot hmPay e)).wires := by
                  rintro ⟨j, hj⟩
                  have hv := congrArg Fin.val (selCore.wires.injective hj)
                  rw [rFullSysElecSlot_val] at hv
                  have := j.isLt; omega
                rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot0,
                    QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotE,
                    QRegister.basisBits_extractIndex]
          · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwC,
                QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _
                  (fun ⟨j, hj⟩ ↦ hwC ⟨rFullSysElecSlot hmPay e j, hj⟩)]
        · apply eq_of_basisBits_eq; intro j
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
              basisBits_coinBarrelPermFast_eq hmPay]
          unfold coinBarrelBitFnFast; rw [he_c1, swapElec0Bits_rSlot0Core_eq hmPay]
          have hnot0 : rFullSysElecSlot hmPay e j ∉ Set.range rSlot0Core.wires := by
            rintro ⟨j', hj'⟩
            have hv := congrArg Fin.val hj'
            dsimp only [rSlot0Core] at hv
            rw [rFullSysElecSlot_val, rFullSysElecSlot_val] at hv
            have := j'.isLt; omega
          rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot0,
              QRegister.basisBits_extractIndex]
          rfl
    have hEntryZero : ∀ a b : Fin (2 ^ kData), eOf a ≠ eOf b → U.1 a b = 0 := fun a b hne ↦ by
      by_contra hnz
      apply hne
      refine coinBarrelIdxFast_congr_high hmPay fun w hw ↦ ?_
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      exact hHigh.entry_eq hnz w hw
    let dx := (extractPair x).1; let mx := (extractPair x).2
    let dy := (extractPair y).1; let my := (extractPair y).2
    by_cases hex : eOf dx = eOf dy
    · let e := eOf dx
      by_cases he0 : e.val = 0
      · have hx_eq : permConj x = x := by
          have hp := hPermConj_pair x
          change if e.val = 0 then permConj x = x else _ at hp
          rw [ite_eq_left he0] at hp; exact hp
        have hy_eq : permConj y = y := by
          have hp := hPermConj_pair y
          change if (eOf dy).val = 0 then permConj y = y else _ at hp
          rw [← hex, ite_eq_left he0] at hp; exact hp
        rw [hx_eq, hy_eq]
      · have hx_p : extractPair (permConj x) =
            ((selCore.compose (rFullSysElecSlot hmPay e)).replaceIndex dx mx,
             (selCore.compose (rFullSysElecSlot hmPay e)).extractIndex dx) := by
          have hp := hPermConj_pair x
          change if e.val = 0 then _ else extractPair (permConj x) = ((selCore.compose
            (rFullSysElecSlot hmPay e)).replaceIndex dx mx, (selCore.compose
            (rFullSysElecSlot hmPay e)).extractIndex dx) at hp
          rw [ite_eq_right he0] at hp; exact hp
        have hy_p : extractPair (permConj y) =
            ((selCore.compose (rFullSysElecSlot hmPay e)).replaceIndex dy my,
             (selCore.compose (rFullSysElecSlot hmPay e)).extractIndex dy) := by
          have hp := hPermConj_pair y
          change if (eOf dy).val = 0 then _ else extractPair (permConj y) = ((selCore.compose
            (rFullSysElecSlot hmPay (eOf dy))).replaceIndex dy my, (selCore.compose
            (rFullSysElecSlot hmPay (eOf dy))).extractIndex dy) at hp
          rw [← hex, ite_eq_right he0] at hp; exact hp
        let rSlotE := selCore.compose (rFullSysElecSlot hmPay e)
        have hCommSlotE : CommutesWithReg rSlotE U.1 := by
          let selE : QRegister 18 3906 := QRegister.block (18 * (e.val - 1)) 18
            (by have := e.isLt; omega)
          have hComp : (spectatorElecReg selCore).compose selE = rSlotE := by
            apply qreg_ext; intro j
            change (spectatorElecReg selCore).wires (selE.wires j) =
              selCore.wires ((rFullSysElecSlot hmPay e).wires j)
            dsimp only [spectatorElecReg, selE]
            rw [QRegister.slice_apply]
            apply congrArg selCore.wires
            apply Fin.ext
            rw [qreg_block_apply]
            dsimp only [e]
            rw [rFullSysElecSlot_val]
            have he_pos : 0 < (eOf dx).val := Nat.pos_of_ne_zero he0
            omega
          intro A
          rw [← hComp, QRegister.embedMatrix_compose]
          exact hSpec (selE.embedMatrix A)
        have hx1 : (selDataInAct kData).extractIndex (permConj x) = rSlotE.replaceIndex dx mx :=
          congrArg Prod.fst hx_p
        have hx2 : (extractPair (permConj x)).2 = rSlotE.extractIndex dx := by
          rw [hx_p]
        have hy1 : (selDataInAct kData).extractIndex (permConj y) = rSlotE.replaceIndex dy my :=
          congrArg Prod.fst hy_p
        have hy2 : (extractPair (permConj y)).2 = rSlotE.extractIndex dy := by
          rw [hy_p]
        have hEqU : U.1 ((selDataInAct kData).extractIndex (permConj x))
            ((selDataInAct kData).extractIndex (permConj y)) = U.1 (rSlotE.replaceIndex dx mx)
            (rSlotE.replaceIndex dy my) := congrArg₂ (fun a b ↦ U.1 a b) hx1 hy1
        rw [embedMatrix_apply_sameOutside, embedMatrix_apply_sameOutside]
        by_cases hSP : SameOutside (Set.range (selDataInAct kData).wires) (permConj y) (permConj x)
        · rw [ite_eq_left hSP, hEqU]
          have hExSlot : rSlotE.extractIndex dx = rSlotE.extractIndex dy := by
            have h2 := (hSameMeas (permConj x) (permConj y)).mp hSP
            rwa [hx2, hy2] at h2
          by_cases hS : SameOutside (Set.range (selDataInAct kData).wires) y x
          · rw [ite_eq_left hS]
            have hm : mx = my := (hSameMeas x y).mp hS
            rw [hm]
            exact commutesWithReg_entry_replaceIndex_eq hCommSlotE my hExSlot
          · rw [ite_eq_right hS]
            have hm : mx ≠ my := fun h ↦ hS ((hSameMeas x y).mpr h)
            refine commutesWithReg_entry_eq_zero_of_ne hCommSlotE ?_
            rwa [QRegister.extractIndex_replaceIndex, QRegister.extractIndex_replaceIndex]
        · rw [ite_eq_right hSP]
          have hExSlot : rSlotE.extractIndex dx ≠ rSlotE.extractIndex dy := fun h ↦
            hSP ((hSameMeas (permConj x) (permConj y)).mpr (by rw [hx2, hy2]; exact h))
          by_cases hS : SameOutside (Set.range (selDataInAct kData).wires) y x
          · rw [ite_eq_left hS]
            exact (commutesWithReg_entry_eq_zero_of_ne hCommSlotE hExSlot).symm
          · rw [ite_eq_right hS]
    · have he_px : eOf ((extractPair (permConj x)).1) = eOf dx := by
        by_cases he0 : (eOf dx).val = 0
        · have hp := hPermConj_pair x
          change if (eOf dx).val = 0 then permConj x = x else _ at hp
          rw [ite_eq_left he0] at hp; rw [hp]
        · have hp := hPermConj_pair x
          change if (eOf dx).val = 0 then _ else extractPair (permConj x) = ((selCore.compose
            (rFullSysElecSlot hmPay (eOf dx))).replaceIndex dx mx, (selCore.compose
            (rFullSysElecSlot hmPay (eOf dx))).extractIndex dx) at hp
          rw [ite_eq_right he0] at hp
          rw [congrArg Prod.fst hp]
          refine coinBarrelIdxFast_congr_high hmPay fun w hw ↦ ?_
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
          refine QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ ?_
          rintro ⟨j, hj⟩
          have hv := congrArg Fin.val (selCore.wires.injective hj)
          rw [rFullSysElecSlot_val] at hv
          have := (eOf dx).isLt; have := j.isLt; omega
      have he_py : eOf ((extractPair (permConj y)).1) = eOf dy := by
        by_cases he0 : (eOf dy).val = 0
        · have hp := hPermConj_pair y
          change if (eOf dy).val = 0 then permConj y = y else _ at hp
          rw [ite_eq_left he0] at hp; rw [hp]
        · have hp := hPermConj_pair y
          change if (eOf dy).val = 0 then _ else extractPair (permConj y) = ((selCore.compose
            (rFullSysElecSlot hmPay (eOf dy))).replaceIndex dy my, (selCore.compose
            (rFullSysElecSlot hmPay (eOf dy))).extractIndex dy) at hp
          rw [ite_eq_right he0] at hp
          rw [congrArg Prod.fst hp]
          refine coinBarrelIdxFast_congr_high hmPay fun w hw ↦ ?_
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
          refine QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ ?_
          rintro ⟨j, hj⟩
          have hv := congrArg Fin.val (selCore.wires.injective hj)
          rw [rFullSysElecSlot_val] at hv
          have := (eOf dy).isLt; have := j.isLt; omega
      have hZ1 : U.1 ((selDataInAct kData).extractIndex (permConj x))
          ((selDataInAct kData).extractIndex (permConj y)) = 0 :=
        hEntryZero _ _ (by
          change eOf (extractPair (permConj x)).1 ≠ eOf (extractPair (permConj y)).1
          rw [he_px, he_py]; exact hex)
      have hZ2 : U.1 ((selDataInAct kData).extractIndex x)
          ((selDataInAct kData).extractIndex y) = 0 := hEntryZero dx dy hex
      rw [embedMatrix_apply_sameOutside, embedMatrix_apply_sameOutside, hZ1, hZ2]
      simp only [ite_self]
  have hPiEq : Operator.permutationUnitary permConj = uS0 * uBar * uS0 := by
    have hBar : uBar = Operator.permutationUnitary permBar :=
      embedUnitary_permutationUnitary_eq ((selDataInAct kData).compose selCore)
        (coinBarrelPermFast hmPay)
    change Operator.permutationUnitary permConj = Operator.permutationUnitary
      (lensSwapEquiv L0) * uBar * Operator.permutationUnitary (lensSwapEquiv L0)
    rw [hBar, permutationUnitary_mul_part2, permutationUnitary_mul_part2]
    apply congrArg Operator.permutationUnitary
    ext1 z; rfl
  rw [hPiEq] at hConjug
  have hS0_sq : uS0 * uS0 = 1 := uLensSwap_mul_self_eq_one L0
  calc uS0 * (selDataInAct kData).embedUnitary U * uS0
      = uS0 * ((uS0 * uBar * uS0) * (selDataInAct kData).embedUnitary U * (uS0 * uBar * uS0)) *
        uS0 := by
          conv_lhs => rw [← hConjug]
    _ = (uS0 * uS0) * uBar * uS0 * (selDataInAct kData).embedUnitary U *
          uS0 * uBar * (uS0 * uS0) := by simp only [mul_assoc]
    _ = (uBar * uS0) * (selDataInAct kData).embedUnitary U * (uS0 * uBar) := by
          rw [hS0_sq, one_mul, mul_one]; simp only [mul_assoc]
/-- Slot-0 swap conjugation coincides with `uAnchorFrame U` whenever `U` acts as the identity on
spectator electron slots `1..217` and preserves high core wires `≥ 3924`. -/
theorem uSlot0MeasSwap_conj_eq_uAnchorFrame (U : Unitary (2 ^ kFull80))
    (hSpec : ActsAsIdOnSpectatorWires rCoreFull U) (hHigh : PreservesHigh3924On rCoreFull U) :
    uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U * uSlot0MeasSwap = uAnchorFrame U
    := uLensSwap_slot0_conj_eq_gen (le_refl 80) rCoreFull U hSpec hHigh
theorem actsAsIdOnSpectatorWires_embed {mPayload kSub kData : ℕ}
    (rEmb : QRegister kSub kData)
    (selCoreSub : QRegister (fullSysCoreWires mPayload) kSub)
    {U₀ : Unitary (2 ^ kSub)}
    (hSpec : ActsAsIdOnSpectatorWires selCoreSub U₀) :
    ActsAsIdOnSpectatorWires (rEmb.compose selCoreSub) (rEmb.embedUnitary U₀) := fun A ↦ by
  have hSlice : spectatorElecReg (rEmb.compose selCoreSub) =
      rEmb.compose (spectatorElecReg selCoreSub) := by
    apply qreg_ext; intro i; rfl
  rw [hSlice, QRegister.embedMatrix_compose, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, hSpec A, QRegister.embedMatrix_mul]
theorem preservesHigh3924On_embed {mPayload kSub kData : ℕ}
    (rEmb : QRegister kSub kData)
    (selCoreSub : QRegister (fullSysCoreWires mPayload) kSub)
    {U₀ : Unitary (2 ^ kSub)}
    (hHigh : PreservesHigh3924On selCoreSub U₀) :
    PreservesHigh3924On (rEmb.compose selCoreSub) (rEmb.embedUnitary U₀) := fun w hw b ↦ by
  have hSing : (QRegister.singleton ((rEmb.compose selCoreSub) w)).basisOutcomeProjector b =
      rEmb.embedMatrix ((QRegister.singleton (selCoreSub w)).basisOutcomeProjector b) := by
    ext x y
    rw [QRegister.basisOutcomeProjector_eq_diagonal, embedMatrix_apply_sameOutside]
    by_cases hxy : x = y
    · subst hxy
      have hS : SameOutside (Set.range rEmb.wires) x x := fun _ _ ↦ rfl
      rw [ite_eq_left hS, QRegister.basisOutcomeProjector_eq_diagonal,
          Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      have hEx : (QRegister.singleton ((rEmb.compose selCoreSub) w)).extractIndex x =
          (QRegister.singleton (selCoreSub w)).extractIndex (rEmb.extractIndex x) := by
        apply eq_of_basisBits_eq; intro j
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
            QRegister.singleton_apply, QRegister.singleton_apply, QRegister.compose_apply,
            QRegister.basisBits_extractIndex]
      rw [hEx]
    · rw [Matrix.diagonal_apply_ne _ hxy]
      by_cases hS : SameOutside (Set.range rEmb.wires) y x
      · rw [ite_eq_left hS, QRegister.basisOutcomeProjector_eq_diagonal]
        have hne : rEmb.extractIndex x ≠ rEmb.extractIndex y := fun hex ↦ hxy <|
          eq_of_basisBits_eq fun u ↦ by
            by_cases hu : u ∈ Set.range rEmb.wires
            · obtain ⟨i, rfl⟩ := hu
              rw [← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex, hex]
            · exact hS u hu
        exact (Matrix.diagonal_apply_ne _ hne).symm
      · rw [ite_eq_right hS]
  rw [hSing, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hHigh w hw b,
      QRegister.embedMatrix_mul]
theorem realizesOnProj_mul_right
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E : Operator (2 ^ n)} (B : Operator (2 ^ n)) {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (h : RealizesOnProj E U d) : RealizesOnProj (E * B) U d := fun M ↦ by
  obtain ⟨M', hwp, hproj⟩ := h M
  refine ⟨M', hwp, ?_⟩
  calc (E * B)ᴴ * M'.1.1 * (E * B)
      = Bᴴ * (Eᴴ * M'.1.1 * E) * B := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Bᴴ * (Eᴴ * (U.1ᴴ * M.1.1 * U.1) * E) * B := by rw [hproj]
    _ = (E * B)ᴴ * (U.1ᴴ * M.1.1 * U.1) * (E * B) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
theorem realizesOnProj_congr_unitary
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hEq : U₁.1 * E = U₂.1 * E) (h : RealizesOnProj E U₁ d) : RealizesOnProj E U₂ d := fun M ↦ by
  obtain ⟨M', hwp, hproj⟩ := h M
  refine ⟨M', hwp, hproj.trans ?_⟩
  calc Eᴴ * (U₁.1ᴴ * M.1.1 * U₁.1) * E
      = (U₁.1 * E)ᴴ * M.1.1 * (U₁.1 * E) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (U₂.1 * E)ᴴ * M.1.1 * (U₂.1 * E) := by rw [hEq]
    _ = Eᴴ * (U₂.1ᴴ * M.1.1 * U₂.1) * E := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
theorem embedMatrix_diagonal_part2 {k N : ℕ} (r : QRegister k N) (d : Fin (2 ^ k) → ℂ) :
    r.embedMatrix (Matrix.diagonal d) = Matrix.diagonal (fun x ↦ d (r.extractIndex x)) := by
  ext x y
  rw [embedMatrix_apply_sameOutside]
  by_cases hxy : x = y
  · subst hxy
    have hS : SameOutside (Set.range r.wires) x x := fun _ _ ↦ rfl
    rw [ite_eq_left hS, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    by_cases hS : SameOutside (Set.range r.wires) y x
    · rw [ite_eq_left hS]
      have hne : r.extractIndex x ≠ r.extractIndex y := fun hex ↦ hxy <|
        eq_of_basisBits_eq fun w ↦ by
          by_cases hw : w ∈ Set.range r.wires
          · obtain ⟨i, rfl⟩ := hw
            rw [← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex, hex]
          · exact hS w hw
      exact Matrix.diagonal_apply_ne _ hne
    · rw [ite_eq_right hS]
/-- `K`-wire `SDag^{\otimes K}` unitary matching the `-32` dyadic electron weight of
  `uPreDiagClifford654`. -/
noncomputable def uSDagK (K : ℕ) : Unitary (2 ^ K) :=
  dyadicDiagUnitary K 7 (fun γ ↦ -32 * ∑ j : Fin K, ((γ j).val : ℤ))
/-- `18`-wire `SDag^{\otimes 18}` unitary matching the `-32` dyadic electron weight of
  `uPreDiagClifford654`. -/
noncomputable abbrev uSDag18 : Unitary (2 ^ 18) := uSDagK 18
/-- `K`-wire `S†` static Clifford circuit. -/
def cSDagK (K : ℕ) : Circuit K := sDagList (List.ofFn (id : Fin K → Wire K))
/-- `K`-wire `S` static Clifford circuit. -/
def cSK (K : ℕ) : Circuit K := sList (List.ofFn (id : Fin K → Wire K))
/-- `18`-wire `S†` static Clifford circuit. -/
abbrev cSDag18 : Circuit 18 := cSDagK 18
/-- `18`-wire `S` static Clifford circuit. -/
abbrev cS18 : Circuit 18 := cSK 18
theorem dyadicDiagUnitary_mulVec_basisKet_part2 {K B : ℕ} (e : BitAssignment K → ℤ)
    (β : BitAssignment K) : (dyadicDiagUnitary K B e).1.mulVec (basisKet β) = dyadicTurn B
    (e β) • basisKet β := by
  have hx := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg K) B e β
  rw [embedUnitary_idReg_eq] at hx
  exact hx
theorem wireListSum_ofFn_id_part2 {K : ℕ} (β : BitAssignment K) :
    (wireListSum (List.ofFn (id : Fin K → Wire K)) β : ℤ) = ∑ j : Fin K, ((β j).val : ℤ) := by
  have haux : ∀ l : List (Wire K), (wireListSum l β : ℤ) =
      (l.map fun w ↦ ((β w).val : ℤ)).sum := fun l ↦ by
    induction l with
    | nil => rfl
    | cons w ws ih => rw [wireListSum_cons]; push_cast; rw [ih]; rfl
  rw [haux, List.map_ofFn, List.sum_ofFn]; rfl
theorem cSDagK_eval (K : ℕ) : (cSDagK K).eval = uSDagK K := by
  apply Subtype.ext; apply matrix_ext_basisKet; intro β
  have hev := (phasePerm_sDagList (List.ofFn (id : Fin K → Wire K))).evolve β
  dsimp only [id_eq] at hev
  rw [cSDagK, uSDagK, hev, dyadicDiagUnitary_mulVec_basisKet_part2, wireListSum_ofFn_id_part2]
theorem cSK_eval (K : ℕ) : (cSK K).eval = (uSDagK K)⁻¹ := by
  rw [uSDagK, dyadicDiagUnitary_inv]
  apply Subtype.ext; apply matrix_ext_basisKet; intro β
  have hev := (phasePerm_sList (List.ofFn (id : Fin K → Wire K))).evolve β
  dsimp only [id_eq] at hev
  rw [cSK, hev, dyadicDiagUnitary_mulVec_basisKet_part2, wireListSum_ofFn_id_part2]
  apply congrArg (· • basisKet β)
  apply congrArg (dyadicTurn 7)
  ring
theorem coreElecCosetB1Block_elec_val {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (i : Fin 3924) :
    (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩).val = i.val := by
  have heq : (⟨i.val, by have := i.isLt; omega⟩ : Fin (3924 + 3)) = Fin.castAdd 3 i := Fin.ext rfl
  rw [heq, coreElecCosetB1Block, QRegister.concat_apply_left]
  simp [FullSysCatSegmentBridge.coreElecBlock]
theorem coreElecCosetB1Block_coset_ge {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (w : Fin 3) :
    3924 ≤ (coreElecCosetB1Block hm6 ⟨3924 + w.val, by have := w.isLt; omega⟩).val := by
  have heq : (⟨3924 + w.val, by have := w.isLt; omega⟩ : Fin (3924 + 3)) = Fin.natAdd 3924 w :=
    Fin.ext rfl
  rw [heq, coreElecCosetB1Block, QRegister.concat_apply_right]
  simp [FullSysCatSegmentBridge.coreCosetB1Block]
  omega
theorem preDiagCliffordExp128_swapElec0Bits {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (e : Fin 218)
    (β : BitAssignment (fullSysCoreWires mPayload)) :
    preDiagCliffordExp128 (fun k ↦ swapElec0Bits e β (coreElecCosetB1Block hm6 k)) =
      preDiagCliffordExp128 (fun k ↦ β (coreElecCosetB1Block hm6 k)) := by
  dsimp only [preDiagCliffordExp128]
  have hCos : (∑ w : Fin 3,
      ((swapElec0Bits e β (coreElecCosetB1Block hm6 ⟨3924 + w.val, by
        have := w.isLt; omega⟩)).val : ℤ)) =
      ∑ w : Fin 3, ((β (coreElecCosetB1Block hm6 ⟨3924 + w.val, by
        have := w.isLt; omega⟩)).val : ℤ) :=
    Finset.sum_congr rfl fun w _ ↦ by
      rw [swapElec0Bits_high e β _ (coreElecCosetB1Block_coset_ge hm6 w)]
  have hElec : (∑ i : Fin 3924,
      ((swapElec0Bits e β (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩)).val : ℤ)) =
      ∑ i : Fin 3924, ((β (coreElecCosetB1Block hm6 ⟨i.val, by
        have := i.isLt; omega⟩)).val : ℤ) := by
    by_cases he0 : e.val = 0
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      unfold swapElec0Bits; rw [ite_eq_left he0]
    · let f : Fin 3924 → Fin 3924 := fun i ↦
        if hi : i.val < 18 then ⟨18 * e.val + i.val, by have := e.isLt; omega⟩
        else if hie : 18 * e.val ≤ i.val ∧ i.val < 18 * e.val + 18 then
          ⟨i.val - 18 * e.val, by omega⟩
        else i
      have hf_inv : Function.Involutive f := fun i ↦ by
        dsimp only [f]
        by_cases hi : i.val < 18
        · rw [dite_eq_left hi]
          have h1 : ¬ (18 * e.val + i.val < 18) := by omega
          have h2 : 18 * e.val ≤ 18 * e.val + i.val ∧ 18 * e.val + i.val < 18 * e.val + 18 := by
            omega
          rw [dite_eq_right h1, dite_eq_left h2]
          exact Fin.ext (by dsimp; omega)
        · rw [dite_eq_right hi]
          by_cases hie : 18 * e.val ≤ i.val ∧ i.val < 18 * e.val + 18
          · rw [dite_eq_left hie]
            have h1 : i.val - 18 * e.val < 18 := by omega
            rw [dite_eq_left h1]
            exact Fin.ext (by dsimp; omega)
          · rw [dite_eq_right hie, dite_eq_right hi, dite_eq_right hie]
      let permE : Equiv.Perm (Fin 3924) := Equiv.ofBijective f hf_inv.bijective
      have hPt : ∀ i : Fin 3924,
          swapElec0Bits e β (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩) =
            β (coreElecCosetB1Block hm6 ⟨(permE i).val, (permE i).isLt.trans (by
              omega)⟩) := fun i ↦ by
        have hvi := coreElecCosetB1Block_elec_val hm6 i
        unfold swapElec0Bits; rw [ite_eq_right he0]
        by_cases hi : i.val < 18
        · have hi' : (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩).val < 18 := by
            rw [hvi]; exact hi
          rw [dite_eq_left hi']
          have hPermEi : (permE i).val = 18 * e.val + i.val := by
            change (f i).val = _; dsimp only [f]; rw [dite_eq_left hi]
          exact congrArg β (Fin.ext (by
            dsimp only; rw [coreElecCosetB1Block_elec_val hm6 (permE i), hPermEi, hvi]))
        · have hi' : ¬ ((coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩).val < 18) := by
            rw [hvi]; exact hi
          rw [dite_eq_right hi']
          by_cases hie : 18 * e.val ≤ i.val ∧ i.val < 18 * e.val + 18
          · have hie' : 18 * e.val ≤ (coreElecCosetB1Block hm6 ⟨i.val, by
              have := i.isLt; omega⟩).val ∧
                (coreElecCosetB1Block hm6 ⟨i.val, by
                  have := i.isLt; omega⟩).val < 18 * e.val + 18 := by
              rw [hvi]; exact hie
            rw [dite_eq_left hie']
            have hPermEi : (permE i).val = i.val - 18 * e.val := by
              change (f i).val = _; dsimp only [f]; rw [dite_eq_right hi, dite_eq_left hie]
            exact congrArg β (Fin.ext (by
              dsimp only; rw [coreElecCosetB1Block_elec_val hm6 (permE i), hPermEi, hvi]))
          · have hie' : ¬ (18 * e.val ≤ (coreElecCosetB1Block hm6 ⟨i.val, by
              have := i.isLt; omega⟩).val ∧
                (coreElecCosetB1Block hm6 ⟨i.val, by
                  have := i.isLt; omega⟩).val < 18 * e.val + 18) := by
              rw [hvi]; exact hie
            rw [dite_eq_right hie']
            have hPermEi : permE i = i := by
              change f i = i; dsimp only [f]; rw [dite_eq_right hi, dite_eq_right hie]
            simp only [hPermEi]
      simp_rw [hPt]
      exact Equiv.sum_comp permE (fun j : Fin 3924 ↦
        ((β (coreElecCosetB1Block hm6 ⟨j.val, j.isLt.trans (by omega)⟩)).val : ℤ))
  rw [hCos, hElec]
theorem embedUnitary_dyadicDiagUnitary_val_part2 {k n : ℕ} (r : QRegister k n) (B : ℕ)
    (e : BitAssignment k → ℤ) : (r.embedUnitary (dyadicDiagUnitary k B e)).1 = r.embedMatrix
    (Matrix.diagonal (fun x : Fin (2 ^ k) ↦ dyadicTurn B (e (basisBits k x)))) := rfl
theorem uPreDiagCliffordCore_eq_diagonal_gen {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    (uPreDiagCliffordCore hm6).1 = Matrix.diagonal (fun c : Fin (2 ^ (fullSysCoreWires
    mPayload)) ↦ dyadicTurn 7 (preDiagCliffordExp128 (fun k ↦ basisBits (fullSysCoreWires
    mPayload) c (coreElecCosetB1Block hm6 k)))) := by
  rw [uPreDiagCliffordCore, uPreDiagClifford654, embedUnitary_dyadicDiagUnitary_val_part2,
      embedMatrix_diagonal_part2]
  apply congrArg Matrix.diagonal; funext c
  have hBits : basisBits (3924 + 3) ((coreElecCosetB1Block hm6).extractIndex c) =
      fun k ↦ basisBits (fullSysCoreWires mPayload) c (coreElecCosetB1Block hm6 k) :=
    funext fun k ↦ QRegister.basisBits_extractIndex (coreElecCosetB1Block hm6) c k
  rw [hBits]
theorem uPreDiagCliffordCore_inv_eq_diagonal_gen {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    ((uPreDiagCliffordCore hm6)⁻¹).1 = Matrix.diagonal (fun c : Fin (2 ^ (fullSysCoreWires
    mPayload)) ↦ dyadicTurn 7 (-preDiagCliffordExp128 (fun k ↦ basisBits (fullSysCoreWires
    mPayload) c (coreElecCosetB1Block hm6 k)))) := by
  rw [uPreDiagCliffordCore, embedUnitary_inv_symm, uPreDiagClifford654, dyadicDiagUnitary_inv,
      embedUnitary_dyadicDiagUnitary_val_part2, embedMatrix_diagonal_part2]
  apply congrArg Matrix.diagonal; funext c
  have hBits : basisBits (3924 + 3) ((coreElecCosetB1Block hm6).extractIndex c) =
      fun k ↦ basisBits (fullSysCoreWires mPayload) c (coreElecCosetB1Block hm6 k) :=
    funext fun k ↦ QRegister.basisBits_extractIndex (coreElecCosetB1Block hm6) c k
  rw [hBits]
theorem uPreDiagCliffordCore_eq_diagonal : (uPreDiagCliffordCore hm6_80).1 = Matrix.diagonal
    (fun c : Fin (2 ^ (fullSysCoreWires 80)) ↦ dyadicTurn 7 (preDiagCliffordExp128 (fun k ↦
    basisBits (fullSysCoreWires 80) c (coreElecCosetB1Block hm6_80 k)))) :=
    uPreDiagCliffordCore_eq_diagonal_gen hm6_80
theorem uPreDiagCliffordCore_inv_eq_diagonal : ((uPreDiagCliffordCore hm6_80)⁻¹).1 =
    Matrix.diagonal (fun c : Fin (2 ^ (fullSysCoreWires 80)) ↦ dyadicTurn 7
    (-preDiagCliffordExp128 (fun k ↦ basisBits (fullSysCoreWires 80) c (coreElecCosetB1Block
    hm6_80 k)))) := uPreDiagCliffordCore_inv_eq_diagonal_gen hm6_80
theorem uBarrelFast_conj_uPreDiagCliffordCore_gen {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (hm6 : 6 ≤ mPayload) : uBarrelFast hmPay * uPreDiagCliffordCore hm6 * uBarrelFast hmPay =
    uPreDiagCliffordCore hm6 := by
  apply Subtype.ext
  change (Operator.permutationUnitary (coinBarrelPermFast hmPay)).1 *
      (uPreDiagCliffordCore hm6).1 *
      (Operator.permutationUnitary (coinBarrelPermFast hmPay)).1 = _
  rw [uPreDiagCliffordCore_eq_diagonal_gen hm6,
      permUnitary_conj_diagonal_part2 (coinBarrelPermFast hmPay)
        (CoinDispatchedBarrel288.coinBarrelPermFast_apply_self hmPay)]
  apply congrArg Matrix.diagonal; funext c
  simp only [basisBits_coinBarrelPermFast_eq hmPay]
  unfold coinBarrelBitFnFast
  rw [preDiagCliffordExp128_swapElec0Bits hm6]
theorem uBarrelFast_conj_uPreDiagCliffordCore_inv_gen {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (hm6 : 6 ≤ mPayload) : uBarrelFast hmPay * (uPreDiagCliffordCore hm6)⁻¹ * uBarrelFast
    hmPay = (uPreDiagCliffordCore hm6)⁻¹ := by
  apply Subtype.ext
  change (Operator.permutationUnitary (coinBarrelPermFast hmPay)).1 *
      ((uPreDiagCliffordCore hm6)⁻¹).1 *
      (Operator.permutationUnitary (coinBarrelPermFast hmPay)).1 = _
  rw [uPreDiagCliffordCore_inv_eq_diagonal_gen hm6,
      permUnitary_conj_diagonal_part2 (coinBarrelPermFast hmPay)
        (CoinDispatchedBarrel288.coinBarrelPermFast_apply_self hmPay)]
  apply congrArg Matrix.diagonal; funext c
  simp only [basisBits_coinBarrelPermFast_eq hmPay]
  unfold coinBarrelBitFnFast
  rw [preDiagCliffordExp128_swapElec0Bits hm6]
theorem uBarrelFast_conj_uPreDiagCliffordCore : uBarrelFast (le_refl 80) *
    uPreDiagCliffordCore hm6_80 * uBarrelFast (le_refl 80) = uPreDiagCliffordCore hm6_80 :=
    uBarrelFast_conj_uPreDiagCliffordCore_gen (le_refl 80) hm6_80
theorem uBarrelFast_conj_uPreDiagCliffordCore_inv :
    uBarrelFast (le_refl 80) * (uPreDiagCliffordCore hm6_80)⁻¹ * uBarrelFast (le_refl 80) =
      (uPreDiagCliffordCore hm6_80)⁻¹ :=
  uBarrelFast_conj_uPreDiagCliffordCore_inv_gen (le_refl 80) hm6_80
theorem uAnchorFrame_of_uBarrelFast_conj_eq (V : Unitary (2 ^ (fullSysCoreWires 80))) (hConj
    : uBarrelFast (le_refl 80) * V * uBarrelFast (le_refl 80) = V) : uAnchorFrame
    (rCoreFull.embedUnitary V) = uAnchorLensSwap * (selDataInAct kFull80).embedUnitary
    (rCoreFull.embedUnitary V) * uAnchorLensSwap := by
  have hAct : uBarrelFastAct * (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary V) *
      uBarrelFastAct = (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary V) := by
    dsimp only [uBarrelFastAct]
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul,
        ← QRegister.embedUnitary_mul, hConj]
  dsimp only [uAnchorFrame]
  rw [uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct,
      uSlot0MeasSwap_mul_uBarrelFastAct_eq_uBarrelFastAct_mul_uAnchorLensSwap]
  calc (uAnchorLensSwap * uBarrelFastAct) *
          (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary V) *
          (uBarrelFastAct * uAnchorLensSwap)
      = uAnchorLensSwap *
          (uBarrelFastAct * (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary V) *
            uBarrelFastAct) *
          uAnchorLensSwap := by simp only [mul_assoc]
    _ = _ := by rw [hAct]
theorem preDiagExp_updSlot_of_tbl_zero_gen {mPayload kData : ℕ}
    (hmPay : 80 ≤ mPayload) (hm6 : 6 ≤ mPayload)
    (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (z : Fin (2 ^ (kData + 18)))
    (hZero : (coinBarrelFastOnDataLens hmPay selCore).tbl ((selDataInAct kData).extractIndex z) =
      0) :
    let L := coinBarrelFastOnDataLens hmPay selCore
    let c := selCore.extractIndex ((selDataInAct kData).extractIndex z)
    let c' := selCore.extractIndex ((selDataInAct kData).extractIndex (lensSwapEquiv L z))
    let m := (selMeasInAct kData).extractIndex z
    preDiagCliffordExp128 (fun k ↦
      basisBits (fullSysCoreWires mPayload) c' (coreElecCosetB1Block hm6 k)) =
      preDiagCliffordExp128 (fun k ↦
        basisBits (fullSysCoreWires mPayload) c (coreElecCosetB1Block hm6 k)) +
        (-32 * ∑ j : Fin 18, ((basisBits 18 m j).val : ℤ)) := by
  intro L c c' m
  let d := (selDataInAct kData).extractIndex z
  let e : Fin 218 := coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) c)
  have hc' : c' = (rFullSysElecSlot hmPay e).replaceIndex c m := by
    have h1 : (selDataInAct kData).extractIndex (lensSwapEquiv L z) =
        L.updSlot d m := congrArg Prod.fst (extractPair_lensSwapEquiv L z)
    have h2 : L.updSlot d m =
        selCore.replaceIndex d ((rFullSysElecSlot hmPay e).replaceIndex c m) := by
      dsimp only [L]
      rw [coinBarrelFastOnDataLens_updSlot, compose_replaceIndex_eq_replaceIndex_replaceIndex]
      rfl
    dsimp only [c']
    rw [h1, h2, QRegister.extractIndex_replaceIndex]
  have hSlot0 : ∀ j : Fin 18,
    basisBits (fullSysCoreWires mPayload) c (rFullSysElecSlot hmPay e j) = 0 := by
    intro j
    have hTbl : L.tbl d = (rFullSysElecSlot hmPay e).extractIndex c := by
      dsimp only [L]
      rw [coinBarrelFastOnDataLens_tbl, QRegister.extractIndex_compose]
      rfl
    rw [← QRegister.basisBits_extractIndex (rFullSysElecSlot hmPay e) c j, ← hTbl, hZero]
    simp [-Nat.reducePow, basisBits_eq_div_mod]
  dsimp only [preDiagCliffordExp128]
  rw [hc']
  have hCos : (∑ w : Fin 3,
      ((basisBits (fullSysCoreWires mPayload) ((rFullSysElecSlot hmPay e).replaceIndex c m)
        (coreElecCosetB1Block hm6 ⟨3924 + w.val, by have := w.isLt; omega⟩)).val : ℤ)) =
      ∑ w : Fin 3, ((basisBits (fullSysCoreWires mPayload) c
        (coreElecCosetB1Block hm6 ⟨3924 + w.val, by have := w.isLt; omega⟩)).val : ℤ) :=
    Finset.sum_congr rfl fun w _ ↦ by
      rw [QRegister.basisBits_replaceIndex_of_not_mem]
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hge := coreElecCosetB1Block_coset_ge hm6 w
      rw [rFullSysElecSlot_val] at hv
      have := e.isLt; have := j.isLt; omega
  have hElec : (∑ i : Fin 3924,
      ((basisBits (fullSysCoreWires mPayload) ((rFullSysElecSlot hmPay e).replaceIndex c m)
        (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩)).val : ℤ)) =
      (∑ i : Fin 3924, ((basisBits (fullSysCoreWires mPayload) c
        (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩)).val : ℤ)) +
      ∑ j : Fin 18, ((basisBits 18 m j).val : ℤ) := by
    let g : Fin 3924 → ℤ := fun i ↦
      if h : 18 * e.val ≤ i.val ∧ i.val < 18 * e.val + 18 then
        ((basisBits 18 m ⟨i.val - 18 * e.val, by omega⟩).val : ℤ)
      else 0
    have hSplit : ∀ i : Fin 3924,
        ((basisBits (fullSysCoreWires mPayload) ((rFullSysElecSlot hmPay e).replaceIndex c m)
          (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩)).val : ℤ) =
        ((basisBits (fullSysCoreWires mPayload) c
          (coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩)).val : ℤ) + g i := fun i ↦ by
      have hvi := coreElecCosetB1Block_elec_val hm6 i
      dsimp only [g]
      by_cases h : 18 * e.val ≤ i.val ∧ i.val < 18 * e.val + 18
      · rw [dite_eq_left h]
        let j : Fin 18 := ⟨i.val - 18 * e.val, by omega⟩
        have hEqW : coreElecCosetB1Block hm6 ⟨i.val, by have := i.isLt; omega⟩ =
            rFullSysElecSlot hmPay e j :=
          Fin.ext (by rw [hvi, rFullSysElecSlot_val]; dsimp [j]; omega)
        rw [hEqW, QRegister.basisBits_replaceIndex_apply, hSlot0 j]
        simp [j]
      · rw [dite_eq_right h, add_zero, QRegister.basisBits_replaceIndex_of_not_mem]
        rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        rw [rFullSysElecSlot_val, hvi] at hv
        have := j.isLt; omega
    simp_rw [hSplit, Finset.sum_add_distrib]
    apply congrArg (_ + ·)
    let emb : Fin 18 ↪ Fin 3924 :=
      { toFun := fun j ↦ ⟨18 * e.val + j.val, by have := e.isLt; have := j.isLt; omega⟩
        inj' := fun j₁ j₂ h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega) }
    have hge : (∑ j : Fin 18, ((basisBits 18 m j).val : ℤ)) = ∑ j : Fin 18, g (emb j) :=
      Finset.sum_congr rfl fun j _ ↦ by
        have hemb : (emb j).val = 18 * e.val + j.val := rfl
        dsimp only [g]
        rw [dite_eq_left (by rw [hemb]; have := j.isLt; omega)]
        exact congrArg (fun k ↦ ((basisBits 18 m k).val : ℤ))
          (Fin.ext (by dsimp only; rw [hemb]; omega)).symm
    rw [hge, ← Finset.sum_map Finset.univ emb g]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hiNot ↦ ?_
    · dsimp only [g]
      split_ifs with h
      · exfalso; apply hiNot
        rw [Finset.mem_map]
        exact ⟨⟨i.val - 18 * e.val, by omega⟩, Finset.mem_univ _,
          Fin.ext (by dsimp [emb]; omega)⟩
      · rfl
  rw [hCos, hElec]; ring
theorem embedUnitary_uSDagK_eq_diagonal {K n : ℕ} (r : QRegister K n) :
    (r.embedUnitary (uSDagK K)).1 = Matrix.diagonal (fun z : Fin (2 ^ n) ↦
      dyadicTurn 7 (-32 * ∑ j : Fin K, ((basisBits K (r.extractIndex z) j).val : ℤ))) := by
  rw [uSDagK, embedUnitary_dyadicDiagUnitary_val_part2, embedMatrix_diagonal_part2]
theorem embedUnitary_uSDagK_inv_eq_diagonal {K n : ℕ} (r : QRegister K n) :
    (r.embedUnitary (uSDagK K)⁻¹).1 = Matrix.diagonal (fun z : Fin (2 ^ n) ↦
      dyadicTurn 7 (-(-32 * ∑ j : Fin K, ((basisBits K (r.extractIndex z) j).val : ℤ)))) := by
  rw [uSDagK, dyadicDiagUnitary_inv, embedUnitary_dyadicDiagUnitary_val_part2,
    embedMatrix_diagonal_part2]
theorem uLensSwap_conj_uPreDiagCliffordCore_eq_diagonal_gen {mPayload kData : ℕ}
    (hmPay : 80 ≤ mPayload) (hm6 : 6 ≤ mPayload)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) :
    let L := coinBarrelFastOnDataLens hmPay selCore
    (uLensSwap L *
      (selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6)) *
      uLensSwap L).1 =
      Matrix.diagonal (fun z : Fin (2 ^ (kData + 18)) ↦
        dyadicTurn 7 (preDiagCliffordExp128 (fun k ↦
          basisBits (fullSysCoreWires mPayload)
            (selCore.extractIndex ((selDataInAct kData).extractIndex (lensSwapEquiv L z)))
            (coreElecCosetB1Block hm6 k)))) := by
  intro L
  simp only [Submonoid.coe_mul]
  change (Operator.permutationUnitary (lensSwapEquiv L)).1 *
      ((selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6))).1 *
      (Operator.permutationUnitary (lensSwapEquiv L)).1 = _
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      uPreDiagCliffordCore_eq_diagonal_gen hm6,
      embedMatrix_diagonal_part2, embedMatrix_diagonal_part2,
      permUnitary_conj_diagonal_part2 (lensSwapEquiv L) (lensSwapEquiv_involutive L)]
theorem uLensSwap_conj_uPreDiagCliffordCore_inv_eq_diagonal_gen {mPayload kData : ℕ}
    (hmPay : 80 ≤ mPayload) (hm6 : 6 ≤ mPayload)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) :
    let L := coinBarrelFastOnDataLens hmPay selCore
    (uLensSwap L *
      (selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6)⁻¹) *
      uLensSwap L).1 =
      Matrix.diagonal (fun z : Fin (2 ^ (kData + 18)) ↦
        dyadicTurn 7 (-preDiagCliffordExp128 (fun k ↦
          basisBits (fullSysCoreWires mPayload)
            (selCore.extractIndex ((selDataInAct kData).extractIndex (lensSwapEquiv L z)))
            (coreElecCosetB1Block hm6 k)))) := by
  intro L
  simp only [Submonoid.coe_mul]
  change (Operator.permutationUnitary (lensSwapEquiv L)).1 *
      ((selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6)⁻¹)).1 *
      (Operator.permutationUnitary (lensSwapEquiv L)).1 = _
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      uPreDiagCliffordCore_inv_eq_diagonal_gen hm6,
      embedMatrix_diagonal_part2, embedMatrix_diagonal_part2,
      permUnitary_conj_diagonal_part2 (lensSwapEquiv L) (lensSwapEquiv_involutive L)]
theorem uPreDiagCliffordAnchorLoc_mul_P_slot0_gen {mPayload kData : ℕ}
    (hmPay : 80 ≤ mPayload) (hm6 : 6 ≤ mPayload)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) :
    let L := coinBarrelFastOnDataLens hmPay selCore
    ((selMeasInAct kData).embedUnitary uSDag18 *
      (selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6))).1 *
      P_slot0 L =
    (uLensSwap L *
      (selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6)) *
      uLensSwap L).1 * P_slot0 L := by
  intro L
  dsimp only [uSDag18]
  rw[Submonoid.coe_mul, embedUnitary_uSDagK_eq_diagonal, QRegister.embedUnitary_val,
      QRegister.embedUnitary_val, uPreDiagCliffordCore_eq_diagonal_gen hm6,
      embedMatrix_diagonal_part2, embedMatrix_diagonal_part2,
      uLensSwap_conj_uPreDiagCliffordCore_eq_diagonal_gen hmPay hm6 selCore,
      P_slot0_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext z
  by_cases hZero : L.tbl ((selDataInAct kData).extractIndex z) = 0
  · rw [ite_eq_left hZero, mul_one, mul_one]
    have hExp := preDiagExp_updSlot_of_tbl_zero_gen hmPay hm6 selCore z hZero
    rw [hExp, ← dyadicTurn_add]
    exact mul_comm _ _
  · rw [ite_eq_right hZero, mul_zero, mul_zero]
theorem uPreDiagCliffordAnchorInvLoc_mul_P_slot0_gen {mPayload kData : ℕ}
    (hmPay : 80 ≤ mPayload) (hm6 : 6 ≤ mPayload)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) :
    let L := coinBarrelFastOnDataLens hmPay selCore
    ((selMeasInAct kData).embedUnitary uSDag18⁻¹ *
      (selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6)⁻¹)).1 *
      P_slot0 L =
    (uLensSwap L *
      (selDataInAct kData).embedUnitary (selCore.embedUnitary (uPreDiagCliffordCore hm6)⁻¹) *
      uLensSwap L).1 * P_slot0 L := by
  intro L
  dsimp only [uSDag18]
  rw[Submonoid.coe_mul, embedUnitary_uSDagK_inv_eq_diagonal, QRegister.embedUnitary_val,
      QRegister.embedUnitary_val, uPreDiagCliffordCore_inv_eq_diagonal_gen hm6,
      embedMatrix_diagonal_part2, embedMatrix_diagonal_part2,
      uLensSwap_conj_uPreDiagCliffordCore_inv_eq_diagonal_gen hmPay hm6 selCore,
      P_slot0_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext z
  by_cases hZero : L.tbl ((selDataInAct kData).extractIndex z) = 0
  · rw [ite_eq_left hZero, mul_one, mul_one]
    have hExp := preDiagExp_updSlot_of_tbl_zero_gen hmPay hm6 selCore z hZero
    have hNeg : -preDiagCliffordExp128 (fun k ↦ basisBits (fullSysCoreWires mPayload)
        (selCore.extractIndex ((selDataInAct kData).extractIndex (lensSwapEquiv L z)))
        (coreElecCosetB1Block hm6 k)) = -(-32 * ∑ j : Fin 18, ((basisBits 18 ((selMeasInAct
        kData).extractIndex z) j).val : ℤ)) + -preDiagCliffordExp128 (fun k ↦ basisBits
        (fullSysCoreWires mPayload) (selCore.extractIndex ((selDataInAct kData).extractIndex
        z)) (coreElecCosetB1Block hm6 k)) := by
      rw [hExp]; ring
    rw [hNeg, dyadicTurn_add]
  · rw [ite_eq_right hZero, mul_zero, mul_zero]
noncomputable def uPreDiagCliffordAnchorLoc : Unitary (2 ^ (kFull80 + 18)) :=
  (selMeasInAct kFull80).embedUnitary uSDag18 *
    (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))
noncomputable def uPreDiagCliffordAnchorInvLoc : Unitary (2 ^ (kFull80 + 18)) :=
  (selMeasInAct kFull80).embedUnitary uSDag18⁻¹ *
    (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹)
theorem uPreDiagCliffordAnchorLoc_mul_P_slot0 :
    uPreDiagCliffordAnchorLoc.1 * P_slot0 L_anchor =
      (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))).1 * P_slot0 L_anchor :=
        by
  rw [uAnchorFrame_of_uBarrelFast_conj_eq (uPreDiagCliffordCore hm6_80)
        uBarrelFast_conj_uPreDiagCliffordCore]
  exact uPreDiagCliffordAnchorLoc_mul_P_slot0_gen (le_refl 80) hm6_80 rCoreFull
theorem uPreDiagCliffordAnchorInvLoc_mul_P_slot0 :
    uPreDiagCliffordAnchorInvLoc.1 * P_slot0 L_anchor =
      (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹)).1 *
        P_slot0 L_anchor := by
  rw [uAnchorFrame_of_uBarrelFast_conj_eq (uPreDiagCliffordCore hm6_80)⁻¹
        uBarrelFast_conj_uPreDiagCliffordCore_inv]
  exact uPreDiagCliffordAnchorInvLoc_mul_P_slot0_gen (le_refl 80) hm6_80 rCoreFull
/-- `0-T`, `0-TOFF` static Clifford circuit applying `S†` on `rCore[0..3924)`, `Z` on the 3 coset
  wires,
and `S†` on `rAnchor18`. -/
def cPreDiagCliffordAnchor {n : ℕ} (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) :
    Circuit n :=
  preDiagCliffordLocalCircuit.onRegister ((rAct.compose rCoreFull).compose (coreElecCosetB1Block
    hm6_80)) ;;ᶜ
    cSDag18.onRegister rAnchor18
/-- `0-T`, `0-TOFF` static Clifford circuit applying `S` on `rCore[0..3924)`, `Z` on the 3 coset
  wires,
and `S` on `rAnchor18`. -/
def cPreDiagCliffordAnchorInv {n : ℕ} (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) :
    Circuit n :=
  preDiagCliffordInvLocalCircuit.onRegister ((rAct.compose rCoreFull).compose (coreElecCosetB1Block
    hm6_80)) ;;ᶜ
    cS18.onRegister rAnchor18
/-- `0-T`, `0-TOFF` dynamic circuit applying `uPreDiagCliffordCore` in the `rAnchor18` frame on
  `P_slot0 L_anchor`. -/
def dPreDiagCliffordAnchor {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) : DynamicCircuit Var n :=
  .circuit (cPreDiagCliffordAnchor rAct rAnchor18)
/-- `0-T`, `0-TOFF` dynamic circuit applying `uPreDiagCliffordCore⁻¹` in the `rAnchor18` frame on
  `P_slot0 L_anchor`. -/
def dPreDiagCliffordAnchorInv {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) : DynamicCircuit Var n :=
  .circuit (cPreDiagCliffordAnchorInv rAct rAnchor18)
/-- `0-T`, `0-TOFF` wrapper conjugating any `qftCoreUnitary80`-framed Stage-A anchor circuit by
  `dPreDiagCliffordAnchor`. -/
def dWrapPreDiagCliffordAnchor {Var : Type} {n : ℕ} (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (dStageARaw : DynamicCircuit Var n) : DynamicCircuit Var n :=
    .seq (dPreDiagCliffordAnchor rAct rAnchor18)
    (.seq dStageARaw (dPreDiagCliffordAnchorInv rAct rAnchor18))
@[simp] theorem dPreDiagCliffordAnchor_count_toff {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) :
    (dPreDiagCliffordAnchor (Var := Var) rAct rAnchor18).count TOFF = 0 := by
  unfold dPreDiagCliffordAnchor cPreDiagCliffordAnchor cSDag18 cSDagK
  simp only [DynamicCircuit.count, Circuit.count_seq, Circuit.count_onRegister,
    count_preDiagCliffordLocal_toff, count_sDagList_toff]
@[simp] theorem dPreDiagCliffordAnchor_count_t {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) :
    (dPreDiagCliffordAnchor (Var := Var) rAct rAnchor18).count T = 0 := by
  unfold dPreDiagCliffordAnchor cPreDiagCliffordAnchor cSDag18 cSDagK
  simp only [DynamicCircuit.count, Circuit.count_seq, Circuit.count_onRegister,
    count_preDiagCliffordLocal_t, count_sDagList_t]
@[simp] theorem dPreDiagCliffordAnchorInv_count_toff {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) :
    (dPreDiagCliffordAnchorInv (Var := Var) rAct rAnchor18).count TOFF = 0 := by
  unfold dPreDiagCliffordAnchorInv cPreDiagCliffordAnchorInv cS18 cSK
  simp only [DynamicCircuit.count, Circuit.count_seq, Circuit.count_onRegister,
    count_preDiagCliffordInvLocal_toff, count_sList_toff]
@[simp] theorem dPreDiagCliffordAnchorInv_count_t {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) :
    (dPreDiagCliffordAnchorInv (Var := Var) rAct rAnchor18).count T = 0 := by
  unfold dPreDiagCliffordAnchorInv cPreDiagCliffordAnchorInv cS18 cSK
  simp only [DynamicCircuit.count, Circuit.count_seq, Circuit.count_onRegister,
    count_preDiagCliffordInvLocal_t, count_sList_t]
theorem dWrapPreDiagCliffordAnchor_count_toff {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    {dStageARaw : DynamicCircuit Var n} (hToff : dStageARaw.count TOFF = 0) :
    (dWrapPreDiagCliffordAnchor rAct rAnchor18 dStageARaw).count TOFF = 0 := by
  unfold dWrapPreDiagCliffordAnchor
  simp only [count_dyn_seq, dPreDiagCliffordAnchor_count_toff, dPreDiagCliffordAnchorInv_count_toff,
    hToff, add_zero]
@[simp] theorem dWrapPreDiagCliffordAnchor_count_t {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (dStageARaw : DynamicCircuit Var n) :
    (dWrapPreDiagCliffordAnchor rAct rAnchor18 dStageARaw).count T = dStageARaw.count T := by
  unfold dWrapPreDiagCliffordAnchor
  simp only [count_dyn_seq, dPreDiagCliffordAnchor_count_t, dPreDiagCliffordAnchorInv_count_t,
    zero_add, add_zero]
theorem cPreDiagCliffordAnchor_eval {n : ℕ} (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (hAA : rAct.DisjointWires rAnchor18) :
    (cPreDiagCliffordAnchor rAct rAnchor18).eval = (rAct.concat rAnchor18 hAA).embedUnitary
    uPreDiagCliffordAnchorLoc := by
  unfold cPreDiagCliffordAnchor uPreDiagCliffordAnchorLoc cSDag18 uSDag18
  rw [Circuit.eval_seq, Circuit.eval_onRegister, Circuit.eval_onRegister,
      preDiagCliffordLocalCircuit_eval, cSDagK_eval, QRegister.embedUnitary_mul]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [← QRegister.embedUnitary_compose]
    exact congrArg (·.embedUnitary (uSDagK 18)) (concat_compose_selMeasInAct rAct rAnchor18
      hAA).symm
  · rw [← QRegister.embedUnitary_compose, concat_compose_selDataInAct,
        uPreDiagCliffordCore, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose, QRegister.compose_assoc]
theorem cPreDiagCliffordAnchorInv_eval {n : ℕ} (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (hAA : rAct.DisjointWires rAnchor18) :
    (cPreDiagCliffordAnchorInv rAct rAnchor18).eval = (rAct.concat rAnchor18 hAA).embedUnitary
    uPreDiagCliffordAnchorInvLoc := by
  unfold cPreDiagCliffordAnchorInv uPreDiagCliffordAnchorInvLoc cS18 uSDag18
  rw [Circuit.eval_seq, Circuit.eval_onRegister, Circuit.eval_onRegister,
      preDiagCliffordInvLocalCircuit_eval, cSK_eval, QRegister.embedUnitary_mul]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [← QRegister.embedUnitary_compose]
    exact congrArg (·.embedUnitary (uSDagK 18)⁻¹) (concat_compose_selMeasInAct rAct rAnchor18
      hAA).symm
  · rw [← QRegister.embedUnitary_compose, concat_compose_selDataInAct,
        uPreDiagCliffordCore, embedUnitary_inv_symm, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose, QRegister.compose_assoc]
theorem dPreDiagCliffordAnchor_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister kFull80 n} {rAnchor18 : QRegister 18 n} {rWork : QRegister mWork n}
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAncW : rAnchor18.DisjointWires rWork)
    (A : Operator (2 ^ (kFull80 + 18))) :
    RealizesOnProj
      ((rAct.concat rAnchor18 hAA).embedMatrix (P_slot0 L_anchor * A) *
        rWork.basisOutcomeProjector 0)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))))
      (dPreDiagCliffordAnchor (Var := Var) rAct rAnchor18) := by
  let rActAnc := rAct.concat rAnchor18 hAA
  have hAAW : rActAnc.DisjointWires rWork := disjointWires_concat_left hAA hAW hAncW
  have hClean := RealizesOnProj.of_clean_embed hAAW (P_slot0 L_anchor * A)
    (DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var)
      rActAnc rWork _ _ (cPreDiagCliffordAnchor_eval rAct rAnchor18 hAA))
  refine realizesOnProj_congr_unitary ?_ hClean
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rActAnc.embedMatrix_mul, ← rActAnc.embedMatrix_mul,
      ← Matrix.mul_assoc uPreDiagCliffordAnchorLoc.1,
      uPreDiagCliffordAnchorLoc_mul_P_slot0, Matrix.mul_assoc]
theorem dPreDiagCliffordAnchorInv_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister kFull80 n} {rAnchor18 : QRegister 18 n} {rWork : QRegister mWork n}
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAncW : rAnchor18.DisjointWires rWork)
    (A : Operator (2 ^ (kFull80 + 18))) :
    RealizesOnProj
      ((rAct.concat rAnchor18 hAA).embedMatrix (P_slot0 L_anchor * A) *
        rWork.basisOutcomeProjector 0)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹)))
      (dPreDiagCliffordAnchorInv (Var := Var) rAct rAnchor18) := by
  let rActAnc := rAct.concat rAnchor18 hAA
  have hAAW : rActAnc.DisjointWires rWork := disjointWires_concat_left hAA hAW hAncW
  have hClean := RealizesOnProj.of_clean_embed hAAW (P_slot0 L_anchor * A)
    (DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var)
      rActAnc rWork _ _ (cPreDiagCliffordAnchorInv_eval rAct rAnchor18 hAA))
  refine realizesOnProj_congr_unitary ?_ hClean
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rActAnc.embedMatrix_mul, ← rActAnc.embedMatrix_mul,
      ← Matrix.mul_assoc uPreDiagCliffordAnchorInvLoc.1,
      uPreDiagCliffordAnchorInvLoc_mul_P_slot0, Matrix.mul_assoc]
theorem embedIntertwineOp {k m n : ℕ} {rA : QRegister k n} {rW : QRegister m n}
    (hDisj : rA.DisjointWires rW) {U : Unitary (2 ^ k)} {E₁ E₂ V : Operator (2 ^ k)}
    (h : U.1 * E₁ = E₂ * V) :
    (rA.embedUnitary U).1 * (rA.embedMatrix E₁ * rW.basisOutcomeProjector 0) =
      (rA.embedMatrix E₂ * rW.basisOutcomeProjector 0) * rA.embedMatrix V := by
  have hComm : rA.embedMatrix V * rW.basisOutcomeProjector 0 = rW.basisOutcomeProjector 0 *
      rA.embedMatrix V :=
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rA) rW hDisj V 0
  rw [QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← rA.embedMatrix_mul, h,
      rA.embedMatrix_mul, Matrix.mul_assoc, hComm, ← Matrix.mul_assoc]
/-- Full-width (`kFull80`) conjugation of a `qftCoreUnitary80`-framed Stage-A unitary by
  `uPreDiagCliffordCore`. -/
noncomputable def uWrapPreDiagCliffordFull (uRawFull : Unitary (2 ^ kFull80)) : Unitary (2 ^
    kFull80) :=
  rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹ *
    (uRawFull * rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))
/-- Segment-level (`fullSysBEWires 80 + 48`) conjugation of a `qftCoreUnitary80`-framed Stage-A
  unitary by `uPreDiagCliffordCore`. -/
noncomputable def uWrapPreDiagCliffordSeg (uRawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48)))
    : Unitary (2 ^ (fullSysBEWires 80 + 48)) := rCoreSeg.embedUnitary
    (uPreDiagCliffordCore hm6_80)⁻¹ *
    (uRawSeg * rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80))
theorem dWrapPreDiagCliffordAnchor_realizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kFull80 n} {rAnchor18 : QRegister 18 n}
    {rWork : QRegister mWork n} (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAncW : rAnchor18.DisjointWires rWork)
    {E_loc V_D V_raw : Operator (2 ^ (kFull80 + 18))}
    (hPSlot0 : P_slot0 L_anchor * E_loc = E_loc) (hDE : (uAnchorFrame (rCoreFull.embedUnitary
    (uPreDiagCliffordCore hm6_80))).1 * E_loc = E_loc * V_D)
    {uRawFull : Unitary (2 ^ kFull80)} {dStageARaw : DynamicCircuit Var n}
    (hInterRaw : (uAnchorFrame uRawFull).1 * E_loc = E_loc * V_raw) (hRealRaw : RealizesOnProj
    ((rAct.concat rAnchor18 hAA).embedMatrix E_loc * rWork.basisOutcomeProjector 0)
    ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame uRawFull)) dStageARaw) :
    RealizesOnProj ((rAct.concat rAnchor18 hAA).embedMatrix E_loc *
    rWork.basisOutcomeProjector 0) ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame
    (uWrapPreDiagCliffordFull uRawFull)))
    (dWrapPreDiagCliffordAnchor rAct rAnchor18 dStageARaw) := by
  let rActAnc := rAct.concat rAnchor18 hAA
  have hAAW : rActAnc.DisjointWires rWork := disjointWires_concat_left hAA hAW hAncW
  let D := uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))
  let DInv := uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹)
  have p1 : RealizesOnProj (rActAnc.embedMatrix E_loc * rWork.basisOutcomeProjector 0)
      (rActAnc.embedUnitary D) (dPreDiagCliffordAnchor (Var := Var) rAct rAnchor18) := by
    rw [← hPSlot0]
    exact dPreDiagCliffordAnchor_realizesOnProj hAA hAW hAncW E_loc
  have p3 : RealizesOnProj (rActAnc.embedMatrix E_loc * rWork.basisOutcomeProjector 0)
      (rActAnc.embedUnitary DInv) (dPreDiagCliffordAnchorInv (Var := Var) rAct rAnchor18) := by
    rw [← hPSlot0]
    exact dPreDiagCliffordAnchorInv_realizesOnProj hAA hAW hAncW E_loc
  have hCh := p1.seq_intertwine (embedIntertwineOp hAAW hDE)
    (hRealRaw.seq_intertwine (embedIntertwineOp hAAW hInterRaw) p3)
  have hComb : rActAnc.embedUnitary DInv * rActAnc.embedUnitary (uAnchorFrame uRawFull) *
        rActAnc.embedUnitary (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))) =
      rActAnc.embedUnitary (uAnchorFrame (uWrapPreDiagCliffordFull uRawFull)) := by
    rw [mul_assoc, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
    apply congrArg rActAnc.embedUnitary
    dsimp only [DInv, uWrapPreDiagCliffordFull]
    rw [uAnchorFrame_mul, uAnchorFrame_mul]
  unfold dWrapPreDiagCliffordAnchor
  rwa [hComb] at hCh
set_option exponentiation.threshold 8192 in
theorem unitaryConj_qftCliffordCore80_uHeadPhase80Mod4Eff_eq : unitaryConj qftCliffordCore80
    uHeadPhase80Mod4Eff = (uPreDiagCliffordCore hm6_80)⁻¹ * unitaryConj qftCoreUnitary80
    uHeadPhase80Mod4Eff * uPreDiagCliffordCore hm6_80 := by
  have hXorInv : (uXor32Core 80)⁻¹ = uXor32Core 80 := uXor32Core_inv 80
  have hAnn : uXor32Core 80 * unitaryConj qftCoreUnitary80 uHeadPhase80Mod4Eff * uXor32Core 80 =
      unitaryConj qftCoreUnitary80 uHeadPhase80Mod4Eff :=
    uXor32Core80_conj_qft_uHeadPhase80Mod4Eff
  unfold qftCliffordCore80 uTrailCliffordXor80 unitaryConj
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hXorInv]
  calc ((uPreDiagCliffordCore hm6_80)⁻¹ * uXor32Core 80 * qftCoreUnitary80⁻¹) *
          uHeadPhase80Mod4Eff *
          (qftCoreUnitary80 * (uXor32Core 80 * uPreDiagCliffordCore hm6_80))
      = (uPreDiagCliffordCore hm6_80)⁻¹ *
          (uXor32Core 80 * (qftCoreUnitary80⁻¹ * uHeadPhase80Mod4Eff * qftCoreUnitary80) *
            uXor32Core 80) *
          uPreDiagCliffordCore hm6_80 := by simp only [mul_assoc]
    _ = _ := by
          change (uPreDiagCliffordCore hm6_80)⁻¹ *
              (uXor32Core 80 * unitaryConj qftCoreUnitary80 uHeadPhase80Mod4Eff * uXor32Core 80) *
              uPreDiagCliffordCore hm6_80 = _
          rw [hAnn]; rfl
theorem uWrapPreDiagCliffordSeg_uHeadPhase80Mod4Eff_mul_catState48
    (uRawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))) (hRawCat : uRawSeg.1 * catState48 =
    (rCoreSeg.embedUnitary (unitaryConj qftCoreUnitary80 uHeadPhase80Mod4Eff)).1 * catState48)
    : (uWrapPreDiagCliffordSeg uRawSeg).1 * catState48 = (rCoreSeg.embedUnitary (unitaryConj
    qftCliffordCore80 uHeadPhase80Mod4Eff)).1 * catState48 := by
  have h1 := mul_catState48_comp
    (U2 := rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹)
    (V2 := (uPreDiagCliffordCore hm6_80)⁻¹) rfl
    (mul_catState48_comp hRawCat
      (U1 := rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80))
      (V1 := uPreDiagCliffordCore hm6_80) rfl)
  change (uWrapPreDiagCliffordSeg uRawSeg).1 * catState48 = _ at h1
  rw [h1, unitaryConj_qftCliffordCore80_uHeadPhase80Mod4Eff_eq, mul_assoc]
theorem uPreDiagCliffordCore_comm_E_rawStream42 :
    (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 * E_rawStream42 =
      E_rawStream42 * (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 := by
  rw [← rSegFull_compose_rCoreSeg_eq, rSegFull_eq_rAct0_compose_rSegOrig,
      QRegister.compose_assoc, QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      uPreDiagCliffordCore_eq_diagonal, embedMatrix_diagonal_part2, E_rawStream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp ((PreservesFeature.diagonal id _).id_imp _)
theorem uPreDiagCliffordCore_inv_comm_E_rawStream42 :
    (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 * E_rawStream42 =
      E_rawStream42 * (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 := by
  rw [← rSegFull_compose_rCoreSeg_eq, rSegFull_eq_rAct0_compose_rSegOrig,
      QRegister.compose_assoc, QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      uPreDiagCliffordCore_inv_eq_diagonal, embedMatrix_diagonal_part2,
        E_rawStream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp ((PreservesFeature.diagonal id _).id_imp _)
theorem uWrapPreDiagCliffordFull_intertwines_E_rawStream42 {uRawFull : Unitary (2 ^ kFull80)}
    {uRawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))} (hRaw : uRawFull.1 * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary uRawSeg).1) : (uWrapPreDiagCliffordFull uRawFull).1
    * E_rawStream42 = E_rawStream42 *
    (rSegFull.embedUnitary (uWrapPreDiagCliffordSeg uRawSeg)).1 := by
  have hSegEq : ∀ V : Unitary (2 ^ (fullSysCoreWires 80)),
      rSegFull.embedUnitary (rCoreSeg.embedUnitary V) = rCoreFull.embedUnitary V := fun V ↦ by
    rw [← QRegister.embedUnitary_compose, rSegFull_compose_rCoreSeg_eq]
  unfold uWrapPreDiagCliffordFull uWrapPreDiagCliffordSeg
  simp only [QRegister.embedUnitary_mul, hSegEq, Submonoid.coe_mul]
  calc ((rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          (uRawFull.1 * (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1)) * E_rawStream42
      = (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          (uRawFull.1 * ((rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 *
            E_rawStream42)) := by
          simp only [Matrix.mul_assoc]
    _ = (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          ((uRawFull.1 * E_rawStream42) *
            (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1) := by
          rw [uPreDiagCliffordCore_comm_E_rawStream42]; simp only [Matrix.mul_assoc]
    _ = ((rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 * E_rawStream42) *
          ((rSegFull.embedUnitary uRawSeg).1 *
            (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1) := by
          rw [hRaw]; simp only [Matrix.mul_assoc]
    _ = E_rawStream42 * ((rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          ((rSegFull.embedUnitary uRawSeg).1 *
            (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1)) := by
          rw [uPreDiagCliffordCore_inv_comm_E_rawStream42]; simp only [Matrix.mul_assoc]
theorem coreElecCosetB1Block_disj_rCtrl3InCore :
    (coreElecCosetB1Block hm6_80).DisjointWires rCtrl3InCore := by
  rw [QRegister.disjoint_iff]
  intro idx j
  have hj : (rCtrl3InCore j).val = 3951 + j.val := by
    simp [rCtrl3InCore]
  refine Fin.addCases (fun i hij ↦ ?_) (fun w hij ↦ ?_) idx
  · have hv := congrArg Fin.val hij
    have hi : (coreElecCosetB1Block hm6_80 (Fin.castAdd 3 i)).val = i.val := by
      have heq : Fin.castAdd 3 i = ⟨i.val, by have := i.isLt; omega⟩ := Fin.ext rfl
      rw [heq]; exact coreElecCosetB1Block_elec_val hm6_80 i
    rw [hi, hj] at hv; have := i.isLt; omega
  · have hv := congrArg Fin.val hij
    have hw : 3954 ≤ (coreElecCosetB1Block hm6_80 (Fin.natAdd 3924 w)).val := by
      rw [coreElecCosetB1Block, QRegister.concat_apply_right]
      simp [coreCosetB1Block]
    rw [hj] at hv; have := j.isLt; omega
theorem uPreDiagCliffordCore_comm_rCtrl3InSeg :
    CommutesWithReg rCtrl3InSeg (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)).1 := by
  refine commutesWithReg_rCtrl3InSeg_rCoreSeg ?_
  rw [uPreDiagCliffordCore, QRegister.embedUnitary_val]
  exact CommutesWithReg.of_disjoint coreElecCosetB1Block_disj_rCtrl3InCore _
theorem uPreDiagCliffordCore_inv_comm_rCtrl3InSeg :
    CommutesWithReg rCtrl3InSeg (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 := by
  refine commutesWithReg_rCtrl3InSeg_rCoreSeg ?_
  rw [uPreDiagCliffordCore, embedUnitary_inv_symm, QRegister.embedUnitary_val]
  exact CommutesWithReg.of_disjoint coreElecCosetB1Block_disj_rCtrl3InCore _
theorem uWrapPreDiagCliffordSeg_comm_rCtrl3InSeg
    {uRawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))}
    (hRaw : CommutesWithReg rCtrl3InSeg uRawSeg.1) :
    CommutesWithReg rCtrl3InSeg (uWrapPreDiagCliffordSeg uRawSeg).1 := by
  unfold uWrapPreDiagCliffordSeg
  simp only [Submonoid.coe_mul]
  exact uPreDiagCliffordCore_inv_comm_rCtrl3InSeg.mul (hRaw.mul
    uPreDiagCliffordCore_comm_rCtrl3InSeg)
theorem uWrapPreDiagCliffordSeg_comm_rPGIdleOrig {k_idle : ℕ} (hk48 : k_idle ≤ 48)
    {uRawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))}
    (hRaw : CommutesWithReg (rPGIdleOrig k_idle hk48) (rSegOrig.embedUnitary uRawSeg).1) :
    CommutesWithReg (rPGIdleOrig k_idle hk48)
      (rSegOrig.embedUnitary (uWrapPreDiagCliffordSeg uRawSeg)).1 := by
  unfold uWrapPreDiagCliffordSeg
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact (commutesWithReg_rPGIdleOrig_rCoreSeg k_idle hk48 _).mul
    (hRaw.mul (commutesWithReg_rPGIdleOrig_rCoreSeg k_idle hk48 _))
theorem diagonal_comm_slotBitProj_gen {N : ℕ} (d : Fin (2 ^ N) → ℂ) (w : Wire N) (b : Fin 2) :
    Matrix.diagonal d * slotBitProj w b = slotBitProj w b * Matrix.diagonal d := by
  unfold slotBitProj
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext x; exact mul_comm _ _
theorem uWrapPreDiagCliffordSeg_mul_pCoinSlack010Seg
    {uRawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))}
    (hRaw : uRawSeg.1 * pCoinSlack010Seg = pCoinSlack010Seg) :
    (uWrapPreDiagCliffordSeg uRawSeg).1 * pCoinSlack010Seg = pCoinSlack010Seg := by
  have hDiagComm : ∀ U : Unitary (2 ^ (fullSysCoreWires 80)), (∃ d, U.1 = Matrix.diagonal d)
      → (rCoreSeg.embedUnitary U).1 * pCoinSlack010Seg = pCoinSlack010Seg *
      (rCoreSeg.embedUnitary U).1 := by
    rintro U ⟨d, hd⟩
    unfold pCoinSlack010Seg
    rw [QRegister.embedUnitary_val, ← rCoreSeg.embedMatrix_mul, ← rCoreSeg.embedMatrix_mul]
    apply congrArg rCoreSeg.embedMatrix
    have hSlot : ∀ (w : Wire (fullSysCoreWires 80)) (b : Fin 2),
        U.1 * slotBitProj w b = slotBitProj w b * U.1 := fun w b ↦ by
      rw [hd]
      exact diagonal_comm_slotBitProj_gen d w b
    exact comm_pCoinSlack010Core_of_comm_coin3 (hSlot _ _) (hSlot _ _) (hSlot _ _)
  have hD : (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)).1 * pCoinSlack010Seg =
      pCoinSlack010Seg * (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)).1 :=
    hDiagComm _ ⟨_, uPreDiagCliffordCore_eq_diagonal⟩
  unfold uWrapPreDiagCliffordSeg
  simp only [Submonoid.coe_mul]
  calc ((rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          (uRawSeg.1 * (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)).1)) * pCoinSlack010Seg
      = (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          (uRawSeg.1 * ((rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)).1 *
            pCoinSlack010Seg)) := by
          simp only [Matrix.mul_assoc]
    _ = (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          ((uRawSeg.1 * pCoinSlack010Seg) *
            (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)).1) := by
          rw [hD]; simp only [Matrix.mul_assoc]
    _ = ((rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹).1 *
          (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)).1) * pCoinSlack010Seg := by
          rw [hRaw, ← hD]; simp only [Matrix.mul_assoc]
    _ = pCoinSlack010Seg := by
          rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, inv_mul_cancel,
              QRegister.embedUnitary_one, OneMemClass.coe_one, Matrix.one_mul]
end Part2_AnchorFrameAndPass13
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge (fullSysBEWires)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSegOrig rSegFull E_rawStream42)
open ZeroHypSlot0CommAndHMidClosure (P_slot0)
open CoinDispatchedBarrel288 (uBarrelFast)
open Leaf4Ext48TopStitch (CommutesWithReg rCtrl3InCore rPGIdleOrig)
open SelectHoistLemmas (rCtrl3InSeg pCoinSlack010Seg)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
open Barrel3PassSelectStitch (hm6_80 rCoreSeg)
open HeldStreamFoldedPass123Bridge (E_rawCtrl3Ext E_rawSegExt)
open BarrelPass2AndHeld3PassSelectStitch (rawStream_core_intertwine_to_rawCtrl3Ext_and_rawSegExt)
open SingleBarrel8StepClean (qftCoreUnitary80 qftCliffordCore80)
open FusedPreDiagFromTwist288 (uPreDiagCliffordCore)
/-- Local `kFull80 + 18` active-anchor subspace operator `(τ_e · σ_0) · (E_ext ⊗
  |0^{18}⟩⟨0^{18}|)`. -/
noncomputable def E_anchorLoc (E_ext : Operator (2 ^ kFull80)) : Operator (2 ^ (kFull80 + 18)) :=
  (uBarrelFastAct * uSlot0MeasSwap).1 * ((selDataInAct kFull80).embedMatrix E_ext * P_anc0)
/-- Full-system active-anchor subspace operator on `(rAct, rAnchor18, rWork)` (`rWork` in
  `|0^{mWork}⟩`). -/
noncomputable def E_anchor {mWork n : ℕ} (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) : Operator (2 ^ n) :=
  (rAct.concat rAnchor18 hAA).embedMatrix (E_anchorLoc E_ext) * rWork.basisOutcomeProjector 0
theorem selDataInAct_embedMatrix_comm_P_anc0 (M : Operator (2 ^ kFull80)) :
    (selDataInAct kFull80).embedMatrix M * P_anc0 =
      P_anc0 * (selDataInAct kFull80).embedMatrix M :=
  (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selDataInAct kFull80))
    (selMeasInAct kFull80) (selDataInAct_disj_selMeasInAct kFull80) M 0
theorem P_slot0_mul_E_anchorLoc (E_ext : Operator (2 ^ kFull80)) :
    P_slot0 L_anchor * E_anchorLoc E_ext = E_anchorLoc E_ext := by
  unfold E_anchorLoc
  rw [selDataInAct_embedMatrix_comm_P_anc0 E_ext,
      ← Matrix.mul_assoc (uBarrelFastAct * uSlot0MeasSwap).1,
      ← Matrix.mul_assoc (P_slot0 L_anchor),
      P_slot0_mul_uBarrelFastAct_mul_uSlot0MeasSwap_mul_P_anc0]
theorem uBarrelFastAct_eq_embedData_rCoreFull :
    uBarrelFastAct =
      (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))) := by
  unfold uBarrelFastAct
  exact QRegister.embedUnitary_compose (selDataInAct kFull80) rCoreFull _
theorem uAnchorFrame_intertwines_E_anchorLoc {U : Unitary (2 ^ kFull80)}
    {E_ext V : Operator (2 ^ kFull80)} (hUE : U.1 * E_ext = E_ext * V) : (uAnchorFrame U).1 *
    E_anchorLoc E_ext = E_anchorLoc E_ext * (selDataInAct kFull80).embedMatrix V := by
  have hmid : (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap) = 1 := by
    calc (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap)
        = uSlot0MeasSwap * (uBarrelFastAct * uBarrelFastAct) * uSlot0MeasSwap := by
          simp only [mul_assoc]
      _ = uSlot0MeasSwap * uSlot0MeasSwap := by rw [uBarrelFastAct_mul_self, mul_one]
      _ = 1 := uSlot0MeasSwap_mul_self
  have hmidM : (uSlot0MeasSwap * uBarrelFastAct).1 * (uBarrelFastAct * uSlot0MeasSwap).1 = 1 := by
    rw [← Submonoid.coe_mul, hmid, OneMemClass.coe_one]
  unfold uAnchorFrame E_anchorLoc
  simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
  calc (((uBarrelFastAct.1 * uSlot0MeasSwap.1) * (selDataInAct kFull80).embedMatrix U.1) *
          (uSlot0MeasSwap.1 * uBarrelFastAct.1)) *
          ((uBarrelFastAct.1 * uSlot0MeasSwap.1) * ((selDataInAct kFull80).embedMatrix E_ext *
            P_anc0))
      = (uBarrelFastAct.1 * uSlot0MeasSwap.1) * (selDataInAct kFull80).embedMatrix U.1 *
          ((uSlot0MeasSwap * uBarrelFastAct).1 * (uBarrelFastAct * uSlot0MeasSwap).1) *
          ((selDataInAct kFull80).embedMatrix E_ext * P_anc0) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (uBarrelFastAct.1 * uSlot0MeasSwap.1) *
          (((selDataInAct kFull80).embedMatrix U.1 * (selDataInAct kFull80).embedMatrix E_ext) *
            P_anc0) := by
          rw [hmidM, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (uBarrelFastAct.1 * uSlot0MeasSwap.1) *
          ((selDataInAct kFull80).embedMatrix E_ext * ((selDataInAct kFull80).embedMatrix V *
            P_anc0)) := by
          rw [← (selDataInAct kFull80).embedMatrix_mul, hUE, (selDataInAct kFull80).embedMatrix_mul]
          simp only [Matrix.mul_assoc]
    _ = ((uBarrelFastAct.1 * uSlot0MeasSwap.1) *
          ((selDataInAct kFull80).embedMatrix E_ext * P_anc0)) *
          (selDataInAct kFull80).embedMatrix V := by
          rw [selDataInAct_embedMatrix_comm_P_anc0 V]; simp only [Matrix.mul_assoc]
theorem uPreDiagCliffordCore_comm_E_rawCtrl3Ext_and_E_rawSegExt {k_idle : ℕ} (hk : k_idle ≤ 48) :
    (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 * E_rawCtrl3Ext k_idle hk =
      E_rawCtrl3Ext k_idle hk * (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 ∧
    (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 * E_rawSegExt k_idle hk =
      E_rawSegExt k_idle hk * (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 := by
  have hDFull : rSegFull.embedUnitary (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80)) =
      rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80) := by
    rw [← QRegister.embedUnitary_compose, rSegFull_compose_rCoreSeg_eq]
  have hRaw : (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 * E_rawStream42 =
      E_rawStream42 *
        (rSegFull.embedUnitary (rCoreSeg.embedUnitary (uPreDiagCliffordCore hm6_80))).1 := by
    rw [hDFull]; exact uPreDiagCliffordCore_comm_E_rawStream42
  have hCtrl3 : CommutesWithReg rCtrl3InCore (uPreDiagCliffordCore hm6_80).1 := by
    rw [uPreDiagCliffordCore, QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint coreElecCosetB1Block_disj_rCtrl3InCore _
  have hPair := rawStream_core_intertwine_to_rawCtrl3Ext_and_rawSegExt hk
    (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)).1 (uPreDiagCliffordCore hm6_80)
    hRaw hCtrl3
  rwa [hDFull] at hPair
/-- Anchor-frame Stage-A input bundle at `(mWork = 179, k_idle = 11)` (`rAnchor18` + `161` clean
  wires). -/
structure StageAAnchorInput179_11 (tACtrl tACat : Fin 10 → ℕ) where
  uStageASeg : Fin 10 → Unitary (2 ^ (fullSysBEWires 80 + 48))
  uStageACtrlFull : Fin 10 → Unitary (2 ^ kFull80)
  uStageACatFull : Fin 10 → Unitary (2 ^ kFull80)
  hACtrlRaw : ∀ j, (uStageACtrlFull j).1 * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary (uStageASeg j)).1
  hACatRaw : ∀ j, (uStageACatFull j).1 * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary (uStageASeg j)).1
  hACtrl3 : ∀ j, CommutesWithReg rCtrl3InSeg (uStageASeg j).1
  hAIdle11 : ∀ j, CommutesWithReg (rPGIdleOrig 11 (by
    decide)) (rSegOrig.embedUnitary (uStageASeg j)).1
  hASlack010 : ∀ j, (uStageASeg j).1 * pCoinSlack010Seg = pCoinSlack010Seg
  hACat48 : ∀ j, (uStageASeg j).1 * catState48 =
    (rCoreSeg.embedUnitary (unitaryConj qftCliffordCore80 uHeadPhase80Mod4Eff)).1 * catState48
/-- Raw `qftCoreUnitary80`-framed Stage-A anchor input bundle (`no uTrailCliffordXor80`),
upgradable at `+0 T` to `StageAAnchorInput179_11` via `.toStageAAnchorInput179_11`. -/
structure StageARawQftAnchorInput179_11 (tACtrl tACat : Fin 10 → ℕ) where
  uRawASeg : Fin 10 → Unitary (2 ^ (fullSysBEWires 80 + 48))
  uRawACtrlFull : Fin 10 → Unitary (2 ^ kFull80)
  uRawACatFull : Fin 10 → Unitary (2 ^ kFull80)
  hRawACtrl : ∀ j, (uRawACtrlFull j).1 * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary (uRawASeg j)).1
  hRawACat : ∀ j, (uRawACatFull j).1 * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary (uRawASeg j)).1
  hRawACtrl3 : ∀ j, CommutesWithReg rCtrl3InSeg (uRawASeg j).1
  hRawAIdle11 : ∀ j, CommutesWithReg (rPGIdleOrig 11 (by
    decide)) (rSegOrig.embedUnitary (uRawASeg j)).1
  hRawASlack010 : ∀ j, (uRawASeg j).1 * pCoinSlack010Seg = pCoinSlack010Seg
  hRawACat48 : ∀ j, (uRawASeg j).1 * catState48 =
    (rCoreSeg.embedUnitary (unitaryConj qftCoreUnitary80 uHeadPhase80Mod4Eff)).1 * catState48
/-- `+0 T` upgrade from raw `qftCoreUnitary80`-framed Stage A (`StageARawQftAnchorInput179_11`) to
`qftCliffordCore80`-framed `StageAAnchorInput179_11` via `dWrapPreDiagCliffordAnchor` + XOR32
annihilation. -/
noncomputable def StageARawQftAnchorInput179_11.toStageAAnchorInput179_11
    {tACtrl tACat : Fin 10 → ℕ} (raw : StageARawQftAnchorInput179_11 tACtrl tACat) :
    StageAAnchorInput179_11 tACtrl tACat where
  uStageASeg j := uWrapPreDiagCliffordSeg (raw.uRawASeg j)
  uStageACtrlFull j := uWrapPreDiagCliffordFull (raw.uRawACtrlFull j)
  uStageACatFull j := uWrapPreDiagCliffordFull (raw.uRawACatFull j)
  hACtrlRaw j := uWrapPreDiagCliffordFull_intertwines_E_rawStream42 (raw.hRawACtrl j)
  hACatRaw j := uWrapPreDiagCliffordFull_intertwines_E_rawStream42 (raw.hRawACat j)
  hACtrl3 j := uWrapPreDiagCliffordSeg_comm_rCtrl3InSeg (raw.hRawACtrl3 j)
  hAIdle11 j := uWrapPreDiagCliffordSeg_comm_rPGIdleOrig (by decide) (raw.hRawAIdle11 j)
  hASlack010 j := uWrapPreDiagCliffordSeg_mul_pCoinSlack010Seg (raw.hRawASlack010 j)
  hACat48 j := uWrapPreDiagCliffordSeg_uHeadPhase80Mod4Eff_mul_catState48 _ (raw.hRawACat48 j)
end BoothOpt_Anchor218CachedTrueSwapOuter
end SharedScope
end SlimStageADepsE1

noncomputable section SlimStageADepsE2
set_option maxRecDepth 131072

section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroAux0e2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.DynamicCircuit DynCircuitExt
open Circuit hiding TOFF
open Operator QProg Matrix Real
open scoped Matrix BigOperators
namespace TrailXorAndRepairedStageAExactEq
open SpecsAux.DyadicSubgridToeplitz128 (anchorSubTarget1D)
open SpecsAux.PhaseGradCatalystCore (hadamardAll)
open ZeroAncillaUSP (omega8)
open HoistedSwapSelectBridge (unitaryConj embedUnitary_inv_eq)
open CanonRank7Circuit (fineCoordOfReg21)
open Dyadic128CoulombMath (SubGridCoord64)
open MeasureBranchHadamardSem (ket matrix_ext_ket)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysQftCoreUnitary)
open KaratsubaQft64Matrix (omega128 omega128_zero omega128_add star_mul_omega128_self bitRev6)
open DyadicQft64WalkCircuit (u18GridEquiv block6_extractIndex_u18 disjoint_block_sep
  list_prod_comm_of_all)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open PosSlots24BranchConcrete (posCoreWires rElecSlot wSlot0Core wSlot1Core wSlot2Core wSubReject
  wIsHead rNucIdx rAnchorIdx rCosetB0 wHeadThresh rHeadFine21 axisBitRev6 slotSubGridCoord64
  parity3OfReg)
open PosSlots24SemanticBridge (pos24_6_le_80 pos24_coreWires80_eq castUnitaryPow2)
open PosPostPrep80MergedVep (wCore3967 wCore4029 uSwapCore3967)
open PosHeadMod4_15476 (omega8_zmod8_add diagZ8UnitaryN ket_diagZ8UnitaryN flipTh flipThClean
  flipThClean_apply_ne monomialZ8UnitaryN ket_monomialZ8UnitaryN embedUnitary_monomialZ8UnitaryN
  headEnBoolSpec headHitSetSpec headPhaseMod4Z8Spec uHeadPhaseMod4
  headEnBoolSpec_update_wHeadThresh)
open NuclearTwistRealizes (embedUnitary_idReg_eq)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open HeadMod4Wide178 (pointAxisPhaseExp128)
open StageAPosHeadConjugatedCircuit (rSpectatorElec3906InCore rSpectatorElec3906
  cSpectatorHadamard3906 cSpectatorHadamard3906_eval uSpectatorHadamard3906 uCoreHadamard18
  uHadamard18 pointDiagUnitary18 rSpectatorSlot elecProd217 uQft217 uHad217 pointDiag217)
open OriginZeroHeadMod4Reduction (pointPhaseUnitary18Z8 rElec0InCore zeroSlot0Bits
  headHitSetOrigin0Spec headPhaseMod4Origin0Z8Spec uHeadPhaseMod4Origin0
  uHeadPhaseMod4Origin0_eq_monomialZ8 uHeadPhaseMod4Origin0ConjH_comm_rElec0
  embedUnitary_comm_of_disjoint_local elecProd217_inv uSpectatorPhase217
  uQft217_conj_uSpectatorPhase217_eq_pointDiag217_conj_origin0 cHadamard6 cHadamard18
  cHadamard18_eval)
open OriginZeroHeadMod4Circuit14900 (uQft0 fullQft218 fullQft218_conj_eq_uQft0_conj_uQft217_conj)
open Origin0Head34RealizesAndLeaf2Spec (headEnBoolSpec_zeroSlot0Bits)
open DoubleDutyFoldedRealizesBridge (selPosCoreInCore80)
open ZeroHypStageABToUFoldedPass123SegAndCompac (rElec18InCore
  fullSysQftCoreUnitary_coreQftHadamardPrunedBundle128 uHeadPhase80Mod4Eff
  monomialZ8UnitaryN_comm_diagonal_of_invariant)
open SpecsAux SpecsAux.SpecMirror
open scoped Circuit.Notation
section Part1_RepairedOrigin0HeadAndQft218Conjugation
/-- Boolean flag `β (wSlot0Core (QRegister.ofFin posCoreWires)) == 1` on `posCoreWires`. -/
def headS0Bool (β : BitAssignment posCoreWires) : Bool :=
  β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1
/-- Target 3D subgrid coordinate `yTarget : SubGridCoord64` tested by `headHitSetSpec` on
  `posCoreWires`:
equals `⟨(dHead w).val / 2, _⟩` when `s0 = false`, and
`(anchorSubTarget1D (y0 w) (if b0 w then 1 else 0) (dHead w)).1` when `s0 = true`. -/
def headTargetCoord64 (β : BitAssignment posCoreWires) : SubGridCoord64 :=
  let rCore := QRegExt.ofFin posCoreWires
  let s0 := headS0Bool β
  let dHead := fineCoordOfReg21 (rHeadFine21 rCore) β
  let y0 := slotSubGridCoord64 (rElecSlot rCore 0) β
  let b0 := parity3OfReg (rCosetB0 rCore) β
  fun w ↦
    if Bool.not s0 then ⟨(dHead w).val / 2, by have := (dHead w).isLt; omega⟩
    else (anchorSubTarget1D (y0 w) (if b0 w then 1 else 0) (dHead w)).1
/-- Bit-reversed 18-bit target point `Fin (2 ^ 18)` corresponding to `headTargetCoord64 β`. -/
def headTargetPoint18 (β : BitAssignment posCoreWires) : Fin (2 ^ 18) :=
  u18GridEquiv.symm (fun w ↦ bitRev6 (headTargetCoord64 β w))
theorem u18GridEquiv_headTargetPoint18 (β : BitAssignment posCoreWires) (w : Fin 3) :
    u18GridEquiv (headTargetPoint18 β) w = bitRev6 (headTargetCoord64 β w) := by
  unfold headTargetPoint18
  rw [Equiv.apply_symm_apply]
/-- Repaired origin-`0` hit set on `posCoreWires`: tests spectator slots `1 .. 217` against the
origin `0 : SubGridCoord64` (`fun _ ↦ 0`), while preserving the exact slot-`0` (`e = 0`) test
`Bool.not s0 && decide (slotSubGridCoord64 (rElecSlot rCore 0) β = headTargetCoord64 β)`
because Electron `0` is NOT conjugated by `uQft217`. -/
noncomputable def headHitSetOrigin0RepairedSpec (β : BitAssignment posCoreWires) : Finset (Fin 218)
    :=
  let rCore := QRegExt.ofFin posCoreWires
  Finset.univ.filter fun e : Fin 218 ↦
    if e.val = 0 then
      Bool.not (headS0Bool β) &&
        decide (slotSubGridCoord64 (rElecSlot rCore 0) β = headTargetCoord64 β)
    else
      decide (slotSubGridCoord64 (rElecSlot rCore e) β = fun _ ↦ 0)
/-- `ZMod 8` phase exponent of the repaired origin-`0` Mod-4 Head Phase Oracle on `posCoreWires`. -/
noncomputable def headPhaseMod4Origin0RepairedZ8Spec (β : BitAssignment posCoreWires) : ZMod 8 :=
  let rCore := QRegExt.ofFin posCoreWires
  if Bool.not (headEnBoolSpec β) then 0
  else
    let s0Z8 : ZMod 8 := if headS0Bool β then 4 else 0
    let tZ8 : ZMod 8 := if β (wHeadThresh rCore) == 1 then 4 else 0
    s0Z8 + ((headHitSetOrigin0RepairedSpec β).card : ZMod 8) * (2 + tZ8)
/-- Repaired origin-`0` Mod-4 Head Phase Unitary on `posCoreWires`. -/
noncomputable def uHeadPhaseMod4Origin0Repaired : Unitary (2 ^ posCoreWires) :=
  monomialZ8UnitaryN (wHeadThresh (QRegExt.ofFin posCoreWires))
    headEnBoolSpec headPhaseMod4Origin0RepairedZ8Spec
/-- Slot-`0` miss predicate `c_miss(β)`: true iff `headEnBoolSpec β = true`, `s0 = false`,
and Electron `0` misses `headTargetCoord64 β` (`y_0 ≠ dHead / 2`). -/
noncomputable def headSlot0MissBool (β : BitAssignment posCoreWires) : Bool :=
  headEnBoolSpec β && Bool.not (headS0Bool β) &&
    decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β ≠ headTargetCoord64 β)
/-- Right-side (`D_pre`) `ZMod 8` diagonal phase exponent `(6 + 4*t) mod 8` on `headSlot0MissBool
  β`,
compensating the unconditional `e = 0` hit in `headHitSetOrigin0Spec` before `wHeadThresh` flips. -/
noncomputable def headOrigin0Slot0MissPreZ8Spec (β : BitAssignment posCoreWires) : ZMod 8 :=
    if headSlot0MissBool β then 6 + (if β (wHeadThresh (QRegExt.ofFin posCoreWires)) == 1
    then 4 else 0) else 0
/-- Left-side (`D_post`) `ZMod 8` diagonal phase exponent `(2 + 4*t_out) mod 8` on
  `headSlot0MissBool β`,
compensating the unconditional `e = 0` hit in `headHitSetOrigin0Spec` after `wHeadThresh` flips. -/
noncomputable def headOrigin0Slot0MissPostZ8Spec (β : BitAssignment posCoreWires) : ZMod 8 :=
    if headSlot0MissBool β then 2 + (if β (wHeadThresh (QRegExt.ofFin posCoreWires)) == 1
    then 4 else 0) else 0
/-- Right-side (`D_pre`) diagonal unitary on `posCoreWires`:
`uHeadPhaseMod4Origin0Repaired = uHeadPhaseMod4Origin0 * uHeadOrigin0Slot0MissPre`. -/
noncomputable def uHeadOrigin0Slot0MissPre : Unitary (2 ^ posCoreWires) :=
  diagZ8UnitaryN headOrigin0Slot0MissPreZ8Spec
/-- Left-side (`D_post`) diagonal unitary on `posCoreWires`:
`uHeadPhaseMod4Origin0Repaired = uHeadOrigin0Slot0MissPost * uHeadPhaseMod4Origin0`. -/
noncomputable def uHeadOrigin0Slot0MissPost : Unitary (2 ^ posCoreWires) :=
  diagZ8UnitaryN headOrigin0Slot0MissPostZ8Spec
theorem zeroSlot0Bits_idem_local (β : BitAssignment posCoreWires) :
    zeroSlot0Bits (zeroSlot0Bits β) = zeroSlot0Bits β := by
  funext w
  unfold zeroSlot0Bits
  split_ifs <;> rfl
theorem zeroSlot0Bits_high (β : BitAssignment posCoreWires) {w : Wire posCoreWires}
    (hw : 18 ≤ w.val) : zeroSlot0Bits β w = β w := by
  unfold zeroSlot0Bits
  exact ite_eq_right (by omega)
theorem zeroSlot0Bits_slot0_coord_eq_zero (β : BitAssignment posCoreWires) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) (zeroSlot0Bits β) =
      fun _ ↦ 0 := by
  funext w
  apply Fin.ext
  change bitsVal (fun j : Fin 6 ↦ zeroSlot0Bits β
    (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w j)) = 0
  unfold bitsVal
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hlt : (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w j).val < 18 := by
    have hw := w.isLt; have hj := j.isLt
    have hv : (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w j).val =
        18 * 0 + (6 * w.val + (5 - j.val)) :=
      PosSlots24UnbarreledWide.rElecSlot_ofFin_val 0 ⟨6 * w.val + (5 - j.val), by omega⟩
    omega
  have hz : zeroSlot0Bits β (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w j) = 0 := by
    unfold zeroSlot0Bits
    exact ite_eq_left hlt
  simp [hz]
theorem zeroSlot0Bits_spectator_coord_eq (β : BitAssignment posCoreWires) (e : Fin 217) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e.succ) (zeroSlot0Bits β) =
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e.succ) β := by
  funext w
  apply Fin.ext
  change bitsVal (fun j : Fin 6 ↦ zeroSlot0Bits β (axisBitRev6 (rElecSlot (QRegExt.ofFin
    posCoreWires) e.succ) w j)) = bitsVal (fun j : Fin 6 ↦ β (axisBitRev6 (rElecSlot
    (QRegExt.ofFin posCoreWires) e.succ) w j))
  unfold bitsVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hge : 18 ≤ (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e.succ) w j).val := by
    have he := e.isLt; have hw := w.isLt; have hj := j.isLt
    have hv : (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e.succ) w j).val =
        18 * (e.val + 1) + (6 * w.val + (5 - j.val)) :=
      PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ ⟨6 * w.val + (5 - j.val), by omega⟩
    omega
  dsimp only
  rw [zeroSlot0Bits_high β hge]
theorem fin218_filter_card_split (p : Fin 218 → Bool) :
    (Finset.univ.filter fun e : Fin 218 ↦ p e).card = (if p 0 then 1 else 0) +
    (Finset.univ.filter fun e : Fin 217 ↦ p e.succ).card := by
  have hSum : ∀ {m : ℕ} (q : Fin m → Bool),
      (Finset.univ.filter fun i : Fin m ↦ q i).card =
        ∑ i : Fin m, if q i then 1 else 0 := fun q ↦ by
    rw [Finset.card_filter]
  rw [hSum p, Fin.sum_univ_succ, ← hSum (fun e : Fin 217 ↦ p e.succ)]
theorem zmod8_repaired_eq_add_missPre : ∀ (en s0 eq th : Bool) (N : ZMod 8), (if Bool.not en
    then (0 : ZMod 8) else (if s0 then 4 else 0) + (((if (Bool.not s0 && eq) then 1 else 0 :
    ℕ) : ZMod 8) + N) * (2 + (if th then 4 else 0))) = (if Bool.not en then (0 : ZMod 8) else
    (if s0 then 4 else 0) + (((if Bool.not s0 then 1 else 0 : ℕ) : ZMod 8) + N) * (2 + (if th
    then 4 else 0))) + (if (en && Bool.not s0 && Bool.not eq) then 6 + (if th then 4 else 0)
    else 0) := by
  decide
/-- Exact `ZMod 8` phase identity:
`headPhaseMod4Origin0RepairedZ8Spec β = headPhaseMod4Origin0Z8Spec β + headOrigin0Slot0MissPreZ8Spec
β`. -/
theorem headPhaseMod4Origin0RepairedZ8Spec_eq_add_missPre (β : BitAssignment posCoreWires) :
    headPhaseMod4Origin0RepairedZ8Spec β =
      headPhaseMod4Origin0Z8Spec β + headOrigin0Slot0MissPreZ8Spec β := by
  have hEn0 : headEnBoolSpec (zeroSlot0Bits β) = headEnBoolSpec β :=
    headEnBoolSpec_zeroSlot0Bits β
  have hS0_0 :
      (zeroSlot0Bits β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) = headS0Bool β := by
    unfold headS0Bool
    rw [zeroSlot0Bits_high β (by decide : 18 ≤ (wSlot0Core (QRegExt.ofFin posCoreWires)).val)]
  have hTh_0 : (zeroSlot0Bits β (wHeadThresh (QRegExt.ofFin posCoreWires)) == 1) =
      (β (wHeadThresh (QRegExt.ofFin posCoreWires)) == 1) := by
    rw [zeroSlot0Bits_high β (by decide : 18 ≤ (wHeadThresh (QRegExt.ofFin posCoreWires)).val)]
  have hHit0 : (headHitSetOrigin0Spec (zeroSlot0Bits β)).card =
      (if Bool.not (headS0Bool β) then 1 else 0) + (Finset.univ.filter fun e : Fin 217 ↦
      decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e.succ) β = fun _ ↦
      0)).card := by
    unfold headHitSetOrigin0Spec
    rw [zeroSlot0Bits_idem_local]
    dsimp only
    rw [hS0_0, fin218_filter_card_split]
    have h0 : ((Bool.not (headS0Bool β) || decide ((0 : Fin 218).val ≠ 0)) &&
        decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0)
          (zeroSlot0Bits β) = fun _ ↦ 0)) =
      Bool.not (headS0Bool β) := by
      rw [zeroSlot0Bits_slot0_coord_eq_zero]
      simp
    rw [h0]
    exact congrArg ((if Bool.not (headS0Bool β) then 1 else 0) + ·)
      (congrArg Finset.card (Finset.filter_congr fun e _ ↦ by
        rw [zeroSlot0Bits_spectator_coord_eq β e]
        have hne : decide (e.succ.val ≠ 0) = true :=
          decide_eq_true (fun h ↦ Fin.succ_ne_zero e (Fin.ext h))
        rw [hne, Bool.or_true, Bool.true_and]))
  have hHitRep : (headHitSetOrigin0RepairedSpec β).card = (if (Bool.not (headS0Bool β) &&
      decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β =
      headTargetCoord64 β)) then 1 else 0) + (Finset.univ.filter fun e : Fin 217 ↦ decide
      (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e.succ) β = fun _ ↦
      0)).card := by
    unfold headHitSetOrigin0RepairedSpec
    dsimp only
    rw [fin218_filter_card_split]
    simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.succ_ne_zero]
  have hNeDec : decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β ≠
      headTargetCoord64 β) = Bool.not (decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin
      posCoreWires) 0) β = headTargetCoord64 β)) := by
    by_cases h : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β =
        headTargetCoord64 β <;> simp [h]
  unfold headPhaseMod4Origin0RepairedZ8Spec headPhaseMod4Origin0Z8Spec
    headOrigin0Slot0MissPreZ8Spec headSlot0MissBool
  dsimp only
  simp only [hEn0, hS0_0, hTh_0, hHit0, hHitRep, hNeDec, Nat.cast_add]
  exact zmod8_repaired_eq_add_missPre
    (headEnBoolSpec β)
    (headS0Bool β)
    (decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β = headTargetCoord64 β))
    (β (wHeadThresh (QRegExt.ofFin posCoreWires)) == 1)
    (((Finset.univ.filter fun e : Fin 217 ↦
      decide (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e.succ) β =
        fun _ ↦ 0)).card : ℕ) : ZMod 8)
theorem headTargetCoord64_congr_outside_spec_and_wTh {β₁ β₂ : BitAssignment posCoreWires} (hS0
    : β₁ (wSlot0Core (QRegExt.ofFin posCoreWires)) = β₂ (wSlot0Core (QRegExt.ofFin
    posCoreWires))) (hFine : ∀ q : Fin 21, β₁ (rHeadFine21 (QRegExt.ofFin posCoreWires) q) =
    β₂ (rHeadFine21 (QRegExt.ofFin posCoreWires) q)) (hElec0 : ∀ q : Fin 18, β₁ (rElecSlot
    (QRegExt.ofFin posCoreWires) 0 q) = β₂ (rElecSlot (QRegExt.ofFin posCoreWires) 0 q))
    (hB0 : ∀ q : Fin 3, β₁ (rCosetB0 (QRegExt.ofFin posCoreWires) q) = β₂ (rCosetB0
    (QRegExt.ofFin posCoreWires) q)) : slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₁ = slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₂ ∧ headTargetCoord64 β₁ = headTargetCoord64
    β₂ := by
  let rCore := QRegExt.ofFin posCoreWires
  have hy0 : slotSubGridCoord64 (rElecSlot rCore 0) β₁ =
      slotSubGridCoord64 (rElecSlot rCore 0) β₂ := by
    funext w; apply Fin.ext
    change bitsVal (fun j : Fin 6 ↦ β₁ (axisBitRev6 (rElecSlot rCore 0) w j)) =
      bitsVal (fun j : Fin 6 ↦ β₂ (axisBitRev6 (rElecSlot rCore 0) w j))
    unfold bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hq := hElec0 ⟨6 * w.val + (5 - j.val), by omega⟩
    exact congrArg (·.val * 2 ^ j.val) hq
  have hd : fineCoordOfReg21 (rHeadFine21 rCore) β₁ =
      fineCoordOfReg21 (rHeadFine21 rCore) β₂ := by
    funext w; apply Fin.ext
    change regVal ((rHeadFine21 rCore).slice (7 * w.val) 7 _) β₁ =
      regVal ((rHeadFine21 rCore).slice (7 * w.val) 7 _) β₂
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hq := hFine ⟨7 * w.val + j.val, by omega⟩
    exact congrArg (·.val * 2 ^ j.val) hq
  have hb0 : parity3OfReg (rCosetB0 rCore) β₁ = parity3OfReg (rCosetB0 rCore) β₂ := by
    funext w
    change (β₁ (rCosetB0 rCore w) == 1) = (β₂ (rCosetB0 rCore w) == 1)
    rw [hB0 w]
  have hs0 : headS0Bool β₁ = headS0Bool β₂ := by
    unfold headS0Bool; rw [hS0]
  refine ⟨hy0, ?_⟩
  funext w; apply Fin.ext
  unfold headTargetCoord64
  dsimp only [rCore] at hy0 hd hb0 ⊢
  rw [hs0]
  cases headS0Bool β₂
  · simp only [Bool.not_false, ↓reduceIte]; rw [hd]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [hd, hy0, hb0]
theorem headEn_and_miss_congr_ne_wHeadThresh {β₁ β₂ : BitAssignment posCoreWires} (hne : ∀ w :
    Wire posCoreWires, w ≠ wHeadThresh (QRegExt.ofFin posCoreWires) → β₁ w = β₂ w) :
    headEnBoolSpec β₁ = headEnBoolSpec β₂ ∧ slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₁ = slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₂ ∧ headTargetCoord64 β₁ = headTargetCoord64
    β₂ ∧ headSlot0MissBool β₁ = headSlot0MissBool β₂ := by
  let rCore := QRegExt.ofFin posCoreWires
  let wTh := wHeadThresh rCore
  have hUpd : Function.update β₁ wTh 0 = Function.update β₂ wTh 0 := by
    funext w
    by_cases hw : w = wTh
    · subst hw; simp
    · simp [Function.update_of_ne hw, hne w hw]
  have hEn : headEnBoolSpec β₁ = headEnBoolSpec β₂ := by
    rw [← headEnBoolSpec_update_wHeadThresh β₁ 0, hUpd, headEnBoolSpec_update_wHeadThresh β₂ 0]
  have hS0 : β₁ (wSlot0Core rCore) = β₂ (wSlot0Core rCore) := hne _ (by decide)
  have hFine : ∀ q : Fin 21, β₁ (rHeadFine21 rCore q) = β₂ (rHeadFine21 rCore q) :=
    fun q ↦ hne _ (by revert q; decide)
  have hElec0 : ∀ q : Fin 18, β₁ (rElecSlot rCore 0 q) = β₂ (rElecSlot rCore 0 q) :=
    fun q ↦ hne _ (by revert q; decide)
  have hB0 : ∀ q : Fin 3, β₁ (rCosetB0 rCore q) = β₂ (rCosetB0 rCore q) :=
    fun q ↦ hne _ (by revert q; decide)
  obtain ⟨hy0, hTgt⟩ := headTargetCoord64_congr_outside_spec_and_wTh hS0 hFine hElec0 hB0
  have hs0b : headS0Bool β₁ = headS0Bool β₂ := by unfold headS0Bool; rw [hS0]
  have hMiss : headSlot0MissBool β₁ = headSlot0MissBool β₂ := by
    unfold headSlot0MissBool
    rw [hEn, hs0b, hy0, hTgt]
  exact ⟨hEn, hy0, hTgt, hMiss⟩
theorem zmod2_post_eq_pre_z8 : ∀ v : ZMod 2, ((2 : ZMod 8) + if v + 1 == 1 then 4 else 0) =
    ((6 : ZMod 8) + if v == 1 then 4 else 0) := by
  decide
/-- Pulling `headOrigin0Slot0MissPostZ8Spec` through `flipThClean` yields
  `headOrigin0Slot0MissPreZ8Spec`. -/
theorem headOrigin0Slot0MissPostZ8Spec_flipThClean_eq_missPre (β : BitAssignment posCoreWires)
    : headOrigin0Slot0MissPostZ8Spec (flipThClean (wHeadThresh (QRegExt.ofFin posCoreWires))
    headEnBoolSpec β) = headOrigin0Slot0MissPreZ8Spec β := by
  let rCore := QRegExt.ofFin posCoreWires
  let wTh := wHeadThresh rCore
  have hInv := headEn_and_miss_congr_ne_wHeadThresh (β₁ := flipThClean wTh headEnBoolSpec β) (β₂ :=
    β)
    (fun w hw ↦ flipThClean_apply_ne wTh headEnBoolSpec β hw)
  unfold headOrigin0Slot0MissPostZ8Spec headOrigin0Slot0MissPreZ8Spec
  rw [hInv.2.2.2]
  by_cases hMiss : headSlot0MissBool β = true
  · rw [ite_eq_left hMiss, ite_eq_left hMiss]
    have hEnTrue : headEnBoolSpec β = true := by
      unfold headSlot0MissBool at hMiss
      revert hMiss
      cases headEnBoolSpec β <;> simp
    have hFlipTh : flipThClean wTh headEnBoolSpec β wTh = β wTh + 1 := by
      unfold flipThClean flipTh
      rw [headEnBoolSpec_update_wHeadThresh β 0, ite_eq_left hEnTrue, Function.update_self]
    rw [hFlipTh]
    exact zmod2_post_eq_pre_z8 (β wTh)
  · simp [hMiss]
theorem rSpectatorElec3906InCore_val (idx : Fin 3906) :
    (rSpectatorElec3906InCore idx).val = 18 + idx.val := by
  simp [rSpectatorElec3906InCore]
theorem agreeOutside_rSpectatorElec3906InCore_nonSpec {x y : Fin (2 ^ posCoreWires)}
    (hOut : rSpectatorElec3906InCore.AgreeOutside x y) {w : Wire posCoreWires}
    (hw : w.val < 18 ∨ 3924 ≤ w.val) : basisBits posCoreWires x w = basisBits posCoreWires y w
    := by
  refine hOut w ?_
  rintro ⟨i, hi⟩
  have hv : 18 + i.val = w.val := by
    rw [← rSpectatorElec3906InCore_val i]
    exact congrArg Fin.val hi
  have := i.isLt
  omega
theorem headEnBoolSpec_congr_high {β₁ β₂ : BitAssignment posCoreWires}
    (hHigh : ∀ w : Wire posCoreWires, 3924 ≤ w.val → β₁ w = β₂ w) : headEnBoolSpec β₁ =
    headEnBoolSpec β₂ := by
  let rCore := QRegExt.ofFin posCoreWires
  have hS2 : β₁ (wSlot2Core rCore) = β₂ (wSlot2Core rCore) := hHigh _ (by decide)
  have hS1 : β₁ (wSlot1Core rCore) = β₂ (wSlot1Core rCore) := hHigh _ (by decide)
  have hS0 : β₁ (wSlot0Core rCore) = β₂ (wSlot0Core rCore) := hHigh _ (by decide)
  have hSR : β₁ (wSubReject rCore) = β₂ (wSubReject rCore) := hHigh _ (by decide)
  have hIH : β₁ (wIsHead rCore) = β₂ (wIsHead rCore) := hHigh _ (by decide)
  have hNuc : regVal (rNucIdx rCore) β₁ = regVal (rNucIdx rCore) β₂ := by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only
    rw [hHigh _ (by revert i; decide)]
  have hAnc : regVal (rAnchorIdx rCore) β₁ = regVal (rAnchorIdx rCore) β₂ := by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only
    rw [hHigh _ (by revert i; decide)]
  unfold headEnBoolSpec
  dsimp only [rCore] at hS2 hS1 hS0 hSR hIH hNuc hAnc ⊢
  rw [hS2, hS1, hS0, hSR, hIH, hNuc, hAnc]
theorem nonSpec_invariants_of_agreeOutside_rSpectator3906
    {x y : Fin (2 ^ posCoreWires)}
    (hOut : rSpectatorElec3906InCore.AgreeOutside x y) :
    let βx := basisBits posCoreWires x
    let βy := basisBits posCoreWires y
    let rCore := QRegExt.ofFin posCoreWires
    headEnBoolSpec βx = headEnBoolSpec βy ∧
    headS0Bool βx = headS0Bool βy ∧
    βx (wHeadThresh rCore) = βy (wHeadThresh rCore) ∧
    slotSubGridCoord64 (rElecSlot rCore 0) βx = slotSubGridCoord64 (rElecSlot rCore 0) βy ∧
    headTargetCoord64 βx = headTargetCoord64 βy ∧
    headSlot0MissBool βx = headSlot0MissBool βy ∧
    headOrigin0Slot0MissPreZ8Spec βx = headOrigin0Slot0MissPreZ8Spec βy ∧
    headOrigin0Slot0MissPostZ8Spec βx = headOrigin0Slot0MissPostZ8Spec βy := by
  intro βx βy rCore
  have hHigh : ∀ (w : Wire posCoreWires), 3924 ≤ w.val → βx w = βy w :=
    fun w hw ↦ agreeOutside_rSpectatorElec3906InCore_nonSpec hOut (Or.inr hw)
  have hLow : ∀ (w : Wire posCoreWires), w.val < 18 → βx w = βy w :=
    fun w hw ↦ agreeOutside_rSpectatorElec3906InCore_nonSpec hOut (Or.inl hw)
  have hEn : headEnBoolSpec βx = headEnBoolSpec βy := headEnBoolSpec_congr_high hHigh
  have hS0Val : βx (wSlot0Core rCore) = βy (wSlot0Core rCore) := hHigh _ (by decide)
  have hTh : βx (wHeadThresh rCore) = βy (wHeadThresh rCore) := hHigh _ (by decide)
  have hFine : ∀ q : Fin 21, βx (rHeadFine21 rCore q) = βy (rHeadFine21 rCore q) :=
    fun q ↦ hHigh _ (by revert q; decide)
  have hElec0 : ∀ q : Fin 18, βx (rElecSlot rCore 0 q) = βy (rElecSlot rCore 0 q) :=
    fun q ↦ hLow _ (by
      have := q.isLt
      have hv := PosSlots24UnbarreledWide.rElecSlot_ofFin_val 0 q
      dsimp only [rCore]
      omega)
  have hB0 : ∀ q : Fin 3, βx (rCosetB0 rCore q) = βy (rCosetB0 rCore q) :=
    fun q ↦ hHigh _ (by revert q; decide)
  obtain ⟨hy0, hTgt⟩ := headTargetCoord64_congr_outside_spec_and_wTh hS0Val hFine hElec0 hB0
  have hS0 : headS0Bool βx = headS0Bool βy := by unfold headS0Bool; rw [hS0Val]
  have hMiss : headSlot0MissBool βx = headSlot0MissBool βy := by
    unfold headSlot0MissBool; rw [hEn, hS0, hy0, hTgt]
  have hPre : headOrigin0Slot0MissPreZ8Spec βx = headOrigin0Slot0MissPreZ8Spec βy := by
    unfold headOrigin0Slot0MissPreZ8Spec; rw [hMiss, hTh]
  have hPost : headOrigin0Slot0MissPostZ8Spec βx = headOrigin0Slot0MissPostZ8Spec βy := by
    unfold headOrigin0Slot0MissPostZ8Spec; rw [hMiss, hTh]
  exact ⟨hEn, hS0, hTh, hy0, hTgt, hMiss, hPre, hPost⟩
def rHigh110InCore : QRegister 110 posCoreWires := QRegister.block 3924 110 (by decide)
theorem rHigh110InCore_61_eq_wHeadThresh :
    rHigh110InCore ⟨61, by decide⟩ = wHeadThresh (QRegExt.ofFin posCoreWires) := by decide
theorem wHeadThresh_val_eq_3985 :
    (wHeadThresh (QRegExt.ofFin posCoreWires)).val = 3985 := by decide
theorem w_sub_3924_lt_110 (w : Wire posCoreWires) (hw : 3924 ≤ w.val) :
    w.val - 3924 < 110 := by
  have := w.isLt; dsimp [posCoreWires] at this; omega
theorem rHigh110InCore_val (k : Fin 110) : (rHigh110InCore k).val = 3924 + k.val := by
  simp [rHigh110InCore]
theorem rElec0InCore_disj_rHigh110InCore : rElec0InCore.DisjointWires rHigh110InCore :=
    disjoint_block_sep (by decide)
theorem matrix_ext_of_ket_local {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n,
      A.mulVec (OctahedralOrbit.ket β) = B.mulVec (OctahedralOrbit.ket β)) : A = B := by
  refine matrix_ext_ket fun β ↦ ?_
  have hEq : ket β = OctahedralOrbit.ket β := by
    funext x; simp [ket, OctahedralOrbit.ket, basisState]
  rw [hEq]
  exact h β
/-- **Right-Side (`D_pre`) Exact Factorization of `uHeadPhaseMod4Origin0Repaired` (`0`
  Hypotheses)**:
`uHeadPhaseMod4Origin0Repaired = uHeadPhaseMod4Origin0 * uHeadOrigin0Slot0MissPre`. -/
theorem uHeadPhaseMod4Origin0Repaired_eq_mul_missPre : uHeadPhaseMod4Origin0Repaired =
    uHeadPhaseMod4Origin0 * uHeadOrigin0Slot0MissPre := by
  apply Subtype.ext
  apply matrix_ext_of_ket_local
  intro β
  let wTh := wHeadThresh (QRegExt.ofFin posCoreWires)
  have hEnEq : (fun γ : BitAssignment posCoreWires ↦ headEnBoolSpec (zeroSlot0Bits γ)) =
      headEnBoolSpec := funext headEnBoolSpec_zeroSlot0Bits
  have h0 : uHeadPhaseMod4Origin0 =
    monomialZ8UnitaryN wTh headEnBoolSpec headPhaseMod4Origin0Z8Spec := by
    rw [uHeadPhaseMod4Origin0_eq_monomialZ8, hEnEq]
  rw [h0]
  unfold uHeadPhaseMod4Origin0Repaired uHeadOrigin0Slot0MissPre
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [ket_diagZ8UnitaryN, Matrix.mulVec_smul, ket_monomialZ8UnitaryN, ket_monomialZ8UnitaryN,
      smul_smul, mul_comm (omega8 ^ _), ← omega8_zmod8_add,
      headPhaseMod4Origin0RepairedZ8Spec_eq_add_missPre]
/-- **Left-Side (`D_post`) Exact Factorization of `uHeadPhaseMod4Origin0Repaired` (`0`
  Hypotheses)**:
`uHeadPhaseMod4Origin0Repaired = uHeadOrigin0Slot0MissPost * uHeadPhaseMod4Origin0`. -/
theorem uHeadPhaseMod4Origin0Repaired_eq_missPost_mul : uHeadPhaseMod4Origin0Repaired =
    uHeadOrigin0Slot0MissPost * uHeadPhaseMod4Origin0 := by
  apply Subtype.ext
  apply matrix_ext_of_ket_local
  intro β
  let wTh := wHeadThresh (QRegExt.ofFin posCoreWires)
  have hEnEq : (fun γ : BitAssignment posCoreWires ↦ headEnBoolSpec (zeroSlot0Bits γ)) =
      headEnBoolSpec := funext headEnBoolSpec_zeroSlot0Bits
  have h0 : uHeadPhaseMod4Origin0 =
    monomialZ8UnitaryN wTh headEnBoolSpec headPhaseMod4Origin0Z8Spec := by
    rw [uHeadPhaseMod4Origin0_eq_monomialZ8, hEnEq]
  rw [h0]
  unfold uHeadPhaseMod4Origin0Repaired uHeadOrigin0Slot0MissPost
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [ket_monomialZ8UnitaryN, ket_monomialZ8UnitaryN, Matrix.mulVec_smul, ket_diagZ8UnitaryN,
      smul_smul, headOrigin0Slot0MissPostZ8Spec_flipThClean_eq_missPre,
      mul_comm (omega8 ^ (headPhaseMod4Origin0Z8Spec β).val),
      ← omega8_zmod8_add, add_comm (headOrigin0Slot0MissPreZ8Spec β),
      ← headPhaseMod4Origin0RepairedZ8Spec_eq_add_missPre]
theorem list_prod_reverse_of_comm {G : Type*} [Monoid G] :
    ∀ (L : List G), (∀ a ∈ L, ∀ b ∈ L, a * b = b * a) → L.reverse.prod = L.prod
  | [], _ => rfl
  | x :: xs, hcomm => by
      simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
      rw [list_prod_reverse_of_comm xs (fun a ha b hb ↦
        hcomm a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))]
      exact list_prod_comm_of_all xs x
        (fun y hy ↦ hcomm y (List.mem_cons_of_mem x hy) x List.mem_cons_self)
theorem prod_ofFn_chunk {G : Type*} [Monoid G] :
    ∀ (m k : ℕ) (f : Fin (m * k) → G),
      (List.ofFn f).prod =
        (List.ofFn fun i : Fin m ↦
          (List.ofFn fun j : Fin k ↦ f ⟨i.val * k + j.val, by
            have hi := i.isLt; have hj := j.isLt
            calc i.val * k + j.val < i.val * k + k := Nat.add_lt_add_left hj _
              _ = (i.val + 1) * k := (Nat.succ_mul i.val k).symm
              _ ≤ m * k := Nat.mul_le_mul_right k hi⟩).prod).prod
  | 0, k, f => by simp
  | m + 1, k, f => by
      have hj_lt : ∀ j : Fin k, j.val < (m + 1) * k := fun j ↦ by
        have := j.isLt; rw [Nat.succ_mul]; omega
      have hidx_lt : ∀ idx : Fin (m * k), k + idx.val < (m + 1) * k := fun idx ↦ by
        have := idx.isLt; rw [Nat.succ_mul]; omega
      have hSplit : List.ofFn f = (List.ofFn fun j : Fin k ↦ f ⟨j.val, hj_lt j⟩) ++
          (List.ofFn fun idx : Fin (m * k) ↦ f ⟨k + idx.val, hidx_lt idx⟩) := by
        apply List.ext_getElem
        · simp [Nat.succ_mul, Nat.add_comm]
        · intro n hn1 hn2
          rw [List.getElem_ofFn]
          by_cases hnk : n < k
          · rw [List.getElem_append_left (by simp [hnk]), List.getElem_ofFn]
          · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
            simp only [List.length_ofFn]
            exact congrArg f (Fin.ext (by dsimp; omega))
      rw [hSplit, List.prod_append, List.ofFn_succ, List.prod_cons,
          prod_ofFn_chunk m k (fun idx ↦ f ⟨k + idx.val, hidx_lt idx⟩)]
      refine congrArg₂ (· * ·) ?_ ?_
      · refine congrArg List.prod (congrArg List.ofFn (funext fun j ↦ ?_))
        exact congrArg f (Fin.ext (by simp))
      · refine congrArg List.prod (congrArg List.ofFn (funext fun i ↦ ?_))
        refine congrArg List.prod (congrArg List.ofFn (funext fun j ↦ ?_))
        exact congrArg f (Fin.ext (by dsimp; ring))
theorem circuit_onRegister_comp {a b c : ℕ} (r1 : QRegister a b) (r2 : QRegister b c) :
    ∀ (ckt : Circuit a), (ckt.onRegister r1).onRegister r2 = ckt.onRegister (r2.compose r1)
  | .identity => rfl
  | .gate g r => by simp only [Circuit.onRegister, QRegister.compose_assoc]
  | .seq c1 c2 => by
      simp only [Circuit.onRegister, circuit_onRegister_comp r1 r2 c1,
        circuit_onRegister_comp r1 r2 c2]
theorem hadamardAll_eval_symbolic {b n : ℕ} (r : QRegister b n) :
    (hadamardAll r).eval =
      (List.ofFn fun i : Fin b ↦
        (QRegister.singleton (r i)).embedUnitary PrimitiveGate.H.eval).prod := by
  unfold hadamardAll
  rw [Circuit.eval_sequence, List.map_ofFn, Function.comp_def]
  exact list_prod_reverse_of_comm
    (List.ofFn fun i : Fin b ↦ (QRegister.singleton (r i)).embedUnitary PrimitiveGate.H.eval)
    (fun a ha x hx ↦ by
      rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
      rcases List.mem_ofFn.mp hx with ⟨j, rfl⟩
      by_cases hij : r i = r j
      · rw [hij]
      · refine embedUnitary_comm_of_disjoint_local (QRegister.singleton (r i)) (QRegister.singleton
          (r j)) ?_ _ _
        rw [QRegister.disjoint_iff]
        intro _ _ heq
        exact hij heq)
theorem hadamardAll_chunk18_symbolic {m n : ℕ} (rM : QRegister (m * 18) n) :
    (hadamardAll rM).eval =
      (List.ofFn fun e : Fin m ↦
        (rM.compose (QRegister.block (e.val * 18) 18 (by
          have he := e.isLt
          calc e.val * 18 + 18 = (e.val + 1) * 18 := (Nat.succ_mul e.val 18).symm
            _ ≤ m * 18 := Nat.mul_le_mul_right 18 he))).embedUnitary uHadamard18).prod := by
  let hWire (w : Wire n) : Unitary (2 ^ n) :=
    (QRegister.singleton w).embedUnitary PrimitiveGate.H.eval
  have hHad6 : ∀ (r6 : QRegister 6 n),
      (cHadamard6.onRegister r6).eval = (List.ofFn fun j : Fin 6 ↦ hWire (r6 j)).prod := by
    intro r6
    dsimp only [cHadamard6, Circuit.H, Circuit.single]
    simp only [Circuit.onRegister, Circuit.eval_seq, Circuit.eval_gate,
      List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, _root_.mul_assoc]
    have hs : ∀ j : Fin 6, r6.compose (QRegister.singleton j) = QRegister.singleton (r6 j) :=
      fun _ ↦ qreg_ext fun _ ↦ rfl
    simp only [hs, hWire]
    rfl
  have hHad18 : ∀ (r18 : QRegister 18 n),
      r18.embedUnitary uHadamard18 = (List.ofFn fun q : Fin 18 ↦ hWire (r18 q)).prod := by
    intro r18
    rw [← cHadamard18_eval, ← Circuit.eval_onRegister]
    dsimp only [cHadamard18]
    have hOnSeq : ∀ (a b : Circuit 18),
      (a ;;ᶜ b).onRegister r18 = a.onRegister r18 ;;ᶜ b.onRegister r18 :=
      fun _ _ ↦ rfl
    rw[hOnSeq, hOnSeq, Circuit.eval_seq, Circuit.eval_seq, circuit_onRegister_comp,
        circuit_onRegister_comp, circuit_onRegister_comp, hHad6, hHad6, hHad6]
    have hChunk18 := prod_ofFn_chunk 3 6 (fun q : Fin (3 * 6) ↦ hWire (r18 q))
    rw [hChunk18]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      ← _root_.mul_assoc]
    have hb0 : ∀ j : Fin 6, r18.compose (QRegister.block 0 6 (by
      decide)) j = r18 ⟨0 * 6 + j.val, by omega⟩ :=
      fun j ↦ congrArg r18 (Fin.ext (by simp))
    have hb1 : ∀ j : Fin 6, r18.compose (QRegister.block 6 6 (by
      decide)) j = r18 ⟨1 * 6 + j.val, by omega⟩ :=
      fun j ↦ congrArg r18 (Fin.ext (by simp))
    have hb2 : ∀ j : Fin 6, r18.compose (QRegister.block 12 6 (by
      decide)) j = r18 ⟨2 * 6 + j.val, by omega⟩ :=
      fun j ↦ congrArg r18 (Fin.ext (by simp))
    simp only [hb0, hb1, hb2, Fin.val_zero, Fin.val_succ, zero_add, Nat.reduceAdd, _root_.mul_assoc]
  rw [hadamardAll_eval_symbolic rM, prod_ofFn_chunk m 18]
  refine congrArg List.prod (congrArg List.ofFn (funext fun e ↦ ?_))
  rw [hHad18]
  refine congrArg List.prod (congrArg List.ofFn (funext fun q ↦ congrArg hWire ?_))
  exact congrArg rM (Fin.ext (by simp))
/-- **Exact Equality of the Two 3,906-Wire Spectator Hadamard Walls (`0` Hypotheses)**:
`uSpectatorHadamard3906` (`hadamardAll` on `[18 .. 3924)`) is identically equal to
`uHad217` (`elecProd217 (fun _ ↦ uHadamard18)`). -/
theorem uSpectatorHadamard3906_eq_uHad217 : uSpectatorHadamard3906 = uHad217 := by
  let rId := QRegExt.idReg posCoreWires
  have hL : (cSpectatorHadamard3906 rId).eval = uSpectatorHadamard3906 := by
    rw [cSpectatorHadamard3906_eval, embedUnitary_idReg_eq]
  rw [← hL]
  dsimp only [cSpectatorHadamard3906]
  have hChunk := hadamardAll_chunk18_symbolic (m := 217) (rSpectatorElec3906 rId)
  rw [hChunk]
  unfold uHad217 elecProd217
  refine congrArg List.prod (congrArg List.ofFn (funext fun e ↦ ?_))
  have he18 : e.val * 18 + 18 ≤ 217 * 18 := by
    have he := e.isLt
    calc e.val * 18 + 18 = (e.val + 1) * 18 := (Nat.succ_mul e.val 18).symm
      _ ≤ 217 * 18 := Nat.mul_le_mul_right 18 he
  have hReg : (rSpectatorElec3906 rId).compose (QRegister.block (e.val * 18) 18 he18) =
      rSpectatorSlot e := by
    apply qreg_ext; intro q; apply Fin.ext
    have h1 : ((rSpectatorElec3906 rId).compose (QRegister.block (e.val * 18) 18 he18) q).val =
        18 + (e.val * 18 + q.val) := by
      change (rSpectatorElec3906InCore ⟨e.val * 18 + q.val, by have := q.isLt; omega⟩).val =
        18 + (e.val * 18 + q.val)
      exact rSpectatorElec3906InCore_val _
    have h2 : (rSpectatorSlot e q).val = 18 * (e.val + 1) + q.val :=
      PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ q
    rw [h1, h2]
    ring
  rw [hReg]
theorem rSpectatorSlot_agreeOutside_imp_rSpectator3906 (e : Fin 217)
    {x y : Fin (2 ^ posCoreWires)} (hOut : (rSpectatorSlot e).AgreeOutside x y) :
    rSpectatorElec3906InCore.AgreeOutside x y := by
  intro w hw
  refine hOut w ?_
  rintro ⟨q, rfl⟩
  refine hw ⟨⟨18 * e.val + q.val, by have := e.isLt; have := q.isLt; omega⟩, ?_⟩
  apply Fin.ext
  have h1 := rSpectatorElec3906InCore_val ⟨18 * e.val + q.val, by
    have := e.isLt; have := q.isLt; omega⟩
  have h2 : (rSpectatorSlot e q).val = 18 * (e.val + 1) + q.val :=
    PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ q
  rw [h1, h2]
  ring
theorem list_unitary_prod_comm_mat {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) :
    ∀ (L : List (Unitary D)),
      (∀ u ∈ L, u.1 * M = M * u.1) →
      (L.prod).1 * M = M * (L.prod).1
  | [], _ => by simp
  | u :: us, h => by
      simp only [List.prod_cons, Submonoid.coe_mul]
      calc u.1 * (us.prod).1 * M
          = u.1 * ((us.prod).1 * M) := by simp only [Matrix.mul_assoc]
        _ = u.1 * (M * (us.prod).1) := by
            rw [list_unitary_prod_comm_mat M us (fun v hv ↦ h v (List.mem_cons_of_mem u hv))]
        _ = (u.1 * M) * (us.prod).1 := by simp only [Matrix.mul_assoc]
        _ = M * (u.1 * (us.prod).1) := by
            rw [h u List.mem_cons_self]; simp only [Matrix.mul_assoc]
theorem elecProd217_comm_diagonal_of_agreeOutside (U_e : Fin 217 → Unitary (2 ^ 18))
    (f : Fin (2 ^ posCoreWires) → ℂ) (hf : ∀ x y : Fin (2 ^ posCoreWires),
    rSpectatorElec3906InCore.AgreeOutside x y → f x = f y) : (elecProd217 U_e).1 *
    Matrix.diagonal f = Matrix.diagonal f * (elecProd217 U_e).1 := by
  unfold elecProd217
  refine list_unitary_prod_comm_mat (Matrix.diagonal f) _ fun u hu ↦ ?_
  rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩
  rw [QRegister.embedUnitary_val]
  exact embedMatrix_comm_diagonal_of_outside (rSpectatorSlot e) (U_e e).1 f
    (fun x y hOut ↦ hf x y (rSpectatorSlot_agreeOutside_imp_rSpectator3906 e hOut))
/-- Both `uHeadOrigin0Slot0MissPre` (`D_pre`) and `uHeadOrigin0Slot0MissPost` (`D_post`) commute
with `elecProd217 U_e` for any 217-electron family `U_e` (including `uSpectatorHadamard3906 =
uHad217`,
`uQft217`, `pointDiag217 z`, and their inverses). -/
theorem elecProd217_comm_slot0MissPre_and_Post (U_e : Fin 217 → Unitary (2 ^ 18)) :
    elecProd217 U_e * uHeadOrigin0Slot0MissPre = uHeadOrigin0Slot0MissPre * elecProd217 U_e ∧
    elecProd217 U_e * uHeadOrigin0Slot0MissPost = uHeadOrigin0Slot0MissPost * elecProd217 U_e
    := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · exact elecProd217_comm_diagonal_of_agreeOutside U_e _ fun x y hOut ↦
      congrArg (fun z : ZMod 8 ↦ omega8 ^ z.val)
        (nonSpec_invariants_of_agreeOutside_rSpectator3906 hOut).2.2.2.2.2.2.1
  · exact elecProd217_comm_diagonal_of_agreeOutside U_e _ fun x y hOut ↦
      congrArg (fun z : ZMod 8 ↦ omega8 ^ z.val)
        (nonSpec_invariants_of_agreeOutside_rSpectator3906 hOut).2.2.2.2.2.2.2
/-- `uSpectatorHadamard3906` and `(uSpectatorHadamard3906)⁻¹` commute with `D_pre` and `D_post`. -/
theorem uSpectatorHadamard3906_comm_slot0MissPre_and_Post : uSpectatorHadamard3906 *
    uHeadOrigin0Slot0MissPre = uHeadOrigin0Slot0MissPre * uSpectatorHadamard3906 ∧
    (uSpectatorHadamard3906)⁻¹ * uHeadOrigin0Slot0MissPre = uHeadOrigin0Slot0MissPre *
    (uSpectatorHadamard3906)⁻¹ ∧ uSpectatorHadamard3906 * uHeadOrigin0Slot0MissPost =
    uHeadOrigin0Slot0MissPost * uSpectatorHadamard3906 ∧ (uSpectatorHadamard3906)⁻¹ *
    uHeadOrigin0Slot0MissPost = uHeadOrigin0Slot0MissPost * (uSpectatorHadamard3906)⁻¹ := by
  rw [uSpectatorHadamard3906_eq_uHad217]
  dsimp only [uHad217]
  rw [elecProd217_inv]
  have h1 := elecProd217_comm_slot0MissPre_and_Post (fun _ ↦ uHadamard18)
  have h2 := elecProd217_comm_slot0MissPre_and_Post (fun _ ↦ (uHadamard18)⁻¹)
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩
/-- **Hadamard-Conjugated `D_pre` and `D_post` Factorizations of `uHeadPhaseMod4Origin0Repaired`
  (`0` Hypotheses)**:
Conjugating `uHeadPhaseMod4Origin0Repaired` by `uSpectatorHadamard3906` (`= uHad217`) factors
cleanly into
`((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906) *
uHeadOrigin0Slot0MissPre`
and `uHeadOrigin0Slot0MissPost * ((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 *
uSpectatorHadamard3906)`. -/
theorem uSpectatorHadamard3906_conj_repaired_eq_missPre_and_missPost :
    let M0_rep :=
      (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0Repaired * uSpectatorHadamard3906
    let M0_orig := (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906
    M0_rep = M0_orig * uHeadOrigin0Slot0MissPre ∧
    M0_rep = uHeadOrigin0Slot0MissPost * M0_orig := by
  intro M0_rep M0_orig
  obtain ⟨hHPre, hHInvPre, _, hHInvPost⟩ := uSpectatorHadamard3906_comm_slot0MissPre_and_Post
  refine ⟨?_, ?_⟩
  · dsimp only [M0_rep, M0_orig]
    rw [uHeadPhaseMod4Origin0Repaired_eq_mul_missPre]
    calc (uSpectatorHadamard3906)⁻¹ * (uHeadPhaseMod4Origin0 * uHeadOrigin0Slot0MissPre) *
      uSpectatorHadamard3906
        = (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 *
            (uHeadOrigin0Slot0MissPre * uSpectatorHadamard3906) := by simp only [_root_.mul_assoc]
      _ = ((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906) *
            uHeadOrigin0Slot0MissPre := by rw [← hHPre]; simp only [_root_.mul_assoc]
  · dsimp only [M0_rep, M0_orig]
    rw [uHeadPhaseMod4Origin0Repaired_eq_missPost_mul]
    calc (uSpectatorHadamard3906)⁻¹ * (uHeadOrigin0Slot0MissPost * uHeadPhaseMod4Origin0) *
      uSpectatorHadamard3906
        = ((uSpectatorHadamard3906)⁻¹ * uHeadOrigin0Slot0MissPost) *
            uHeadPhaseMod4Origin0 * uSpectatorHadamard3906 := by simp only [_root_.mul_assoc]
      _ = uHeadOrigin0Slot0MissPost *
            ((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906) := by
          rw [hHInvPost]; simp only [_root_.mul_assoc]
theorem unitary_inv_comm_of_comm {D : ℕ} {U V : Unitary D}
    (h : U * V = V * U) : U⁻¹ * V = V * U⁻¹ := by
  calc U⁻¹ * V = U⁻¹ * (V * U) * U⁻¹ := by simp only [_root_.mul_assoc, mul_inv_cancel, mul_one]
    _ = U⁻¹ * (U * V) * U⁻¹ := by rw [← h]
    _ = V * U⁻¹ := by simp only [← _root_.mul_assoc, inv_mul_cancel, one_mul]
theorem unitary_inv_mul_eq_of_mul_eq_and_comm {D : ℕ} {U V : Unitary D} {P : Operator D}
    (hFwd : U.1 * P = V.1 * P) (_hU : U.1 * P = P * U.1) (hV : V.1 * P = P * V.1) :
    (U⁻¹).1 * P = (V⁻¹).1 * P := by
  have hVV : V.1 * (V⁻¹).1 = 1 := V.2.2
  have hVV' : (V⁻¹).1 * V.1 = 1 := V.2.1
  have hUU : (U⁻¹).1 * U.1 = 1 := U.2.1
  have hVInv : P * (V⁻¹).1 = (V⁻¹).1 * P := by
    calc P * (V⁻¹).1 = ((V⁻¹).1 * V.1) * P * (V⁻¹).1 := by rw [hVV', Matrix.one_mul]
      _ = (V⁻¹).1 * (V.1 * P) * (V⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = (V⁻¹).1 * (P * V.1) * (V⁻¹).1 := by rw [hV]
      _ = (V⁻¹).1 * P * (V.1 * (V⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = (V⁻¹).1 * P := by rw [hVV, Matrix.mul_one]
  calc (U⁻¹).1 * P = (U⁻¹).1 * P * (V.1 * (V⁻¹).1) := by rw [hVV, Matrix.mul_one]
    _ = (U⁻¹).1 * (P * V.1) * (V⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = (U⁻¹).1 * (U.1 * P) * (V⁻¹).1 := by rw [← hV, ← hFwd]
    _ = ((U⁻¹).1 * U.1) * P * (V⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = (V⁻¹).1 * P := by rw [hUU, Matrix.one_mul, hVInv]
theorem smul_diagonal_local {D : ℕ} (c : ℂ) (d : Fin D → ℂ) :
    c • Matrix.diagonal d = Matrix.diagonal (fun x ↦ c * d x) := by
  ext i j
  by_cases h : i = j <;> simp [h]
theorem diagonal_mem_unitary_of_star_mul_self {D : ℕ} (f : Fin D → ℂ)
    (hf : ∀ i : Fin D, star (f i) * f i = 1) :
    Matrix.diagonal f ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hct : star (Matrix.diagonal f) = Matrix.diagonal (fun i ↦ star (f i)) := by
    rw [Matrix.star_eq_conjTranspose]
    ext i j
    rw [Matrix.conjTranspose_apply]
    by_cases h : i = j
    · subst h; simp
    · have hji : j ≠ i := Ne.symm h
      simp [h, hji]
  rw [hct, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact hf i
  · simp [h]
/-- Diagonal entry of `uControlledPointDiag217` on `posCoreWires`: applies the 3-axis 217-spectator
Karatsuba point-QFT diagonal phase controlled on `bitRev6 (headTargetCoord64 (basisBits posCoreWires
x) w)`. -/
noncomputable def controlledPointDiag217Entry (x : Fin (2 ^ posCoreWires)) : ℂ :=
  let β := basisBits posCoreWires x
  ∏ w : Fin 3,
    omega128 (∑ e : Fin 217,
      pointAxisPhaseExp128
        (bitRev6 (headTargetCoord64 β w))
        (u18GridEquiv ((rSpectatorSlot e).extractIndex x) w))
/-- Controlled 217-spectator point-QFT diagonal unitary on `posCoreWires`. -/
noncomputable def uControlledPointDiag217 : Unitary (2 ^ posCoreWires) :=
  ⟨Matrix.diagonal controlledPointDiag217Entry,
    diagonal_mem_unitary_of_star_mul_self controlledPointDiag217Entry fun i ↦ by
      dsimp only [controlledPointDiag217Entry]
      rw [star_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun w _ ↦ star_mul_omega128_self _⟩
theorem uControlledPointDiag217_val :
    uControlledPointDiag217.1 = Matrix.diagonal controlledPointDiag217Entry := rfl
theorem diagZ8UnitaryN_val_local {n : ℕ} (p : BitAssignment n → ZMod 8) :
    (diagZ8UnitaryN p).1 = Matrix.diagonal (fun x : Fin (2 ^ n) ↦
      omega8 ^ (p (basisBits n x)).val) := rfl
/-- Because both `uControlledPointDiag217` and `D_pre` / `D_post` are diagonal in the computational
  basis,
`uControlledPointDiag217` and its inverse commute with both `uHeadOrigin0Slot0MissPre` and
`uHeadOrigin0Slot0MissPost`. -/
theorem uControlledPointDiag217_comm_slot0MissPre_and_Post : uControlledPointDiag217 *
    uHeadOrigin0Slot0MissPre = uHeadOrigin0Slot0MissPre * uControlledPointDiag217 ∧
    (uControlledPointDiag217)⁻¹ * uHeadOrigin0Slot0MissPre = uHeadOrigin0Slot0MissPre *
    (uControlledPointDiag217)⁻¹ ∧ uControlledPointDiag217 * uHeadOrigin0Slot0MissPost =
    uHeadOrigin0Slot0MissPost * uControlledPointDiag217 ∧ (uControlledPointDiag217)⁻¹ *
    uHeadOrigin0Slot0MissPost = uHeadOrigin0Slot0MissPost * (uControlledPointDiag217)⁻¹ := by
  have hDiagComm : ∀ (f g : Fin (2 ^ posCoreWires) → ℂ),
      Matrix.diagonal f * Matrix.diagonal g = Matrix.diagonal g * Matrix.diagonal f := fun f g ↦ by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hPre : uControlledPointDiag217 * uHeadOrigin0Slot0MissPre =
      uHeadOrigin0Slot0MissPre * uControlledPointDiag217 := by
    apply Subtype.ext
    unfold uHeadOrigin0Slot0MissPre
    rw [Submonoid.coe_mul, Submonoid.coe_mul, uControlledPointDiag217_val, diagZ8UnitaryN_val_local]
    exact hDiagComm _ _
  have hPost : uControlledPointDiag217 * uHeadOrigin0Slot0MissPost =
      uHeadOrigin0Slot0MissPost * uControlledPointDiag217 := by
    apply Subtype.ext
    unfold uHeadOrigin0Slot0MissPost
    rw [Submonoid.coe_mul, Submonoid.coe_mul, uControlledPointDiag217_val, diagZ8UnitaryN_val_local]
    exact hDiagComm _ _
  exact ⟨hPre, unitary_inv_comm_of_comm hPre, hPost, unitary_inv_comm_of_comm hPost⟩
theorem embedMatrix_diagonal_local {k n : ℕ} (r : QRegister k n) (d : Fin (2 ^ k) → ℂ) :
    r.embedMatrix (Matrix.diagonal d) = Matrix.diagonal
    (fun x : Fin (2 ^ n) ↦ d (r.extractIndex x)) := by
  ext x y
  rw [QRegister.embedMatrix_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [ite_eq_right hxy]
    by_cases hEnv : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
    · have hneExt : r.extractIndex x ≠ r.extractIndex y := by
        intro hExt
        refine hxy ((basisBitsEquiv n).injective (funext fun w ↦ ?_))
        by_cases hw : w ∈ Set.range r.wires
        · rcases hw with ⟨idx, rfl⟩
          have hx := r.basisBits_extractIndex x idx
          have hy := r.basisBits_extractIndex y idx
          change basisBits n x (r idx) = basisBits n y (r idx)
          rw [← hx, ← hy, hExt]
        · exact (r.basisSplit_environment_eq_iff x y).mp hEnv w hw
      simp [hEnv, hneExt]
    · simp [hEnv]
theorem list_unitary_val_prod {D : ℕ} :
    ∀ (L : List (Unitary D)), (L.prod).1 = (L.map Subtype.val).prod
  | [] => rfl
  | u :: us => by simp [List.prod_cons, Submonoid.coe_mul, list_unitary_val_prod us]
theorem list_ofFn_diagonal_prod {D : ℕ} :
    ∀ {m : ℕ} (g : Fin m → Fin D → ℂ),
      (List.ofFn fun i : Fin m ↦ Matrix.diagonal (g i)).prod =
        Matrix.diagonal (fun x : Fin D ↦ ∏ i : Fin m, g i x)
  | 0, _ => by simp [Matrix.diagonal_one]
  | m + 1, g => by
      rw[List.ofFn_succ, List.prod_cons, list_ofFn_diagonal_prod (fun i : Fin m ↦ g i.succ),
          Matrix.diagonal_mul_diagonal]
      congr 1; funext x
      rw [Fin.prod_univ_succ]
theorem omega128_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    omega128 (∑ i ∈ s, f i) = ∏ i ∈ s, omega128 (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [omega128_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, omega128_add, ih]
theorem prod_ite_omega8_eq_card_mul {m : ℕ} (p : Fin m → Prop) [DecidablePred p] (k : ZMod 8) :
    (∏ i : Fin m, if p i then omega8 ^ k.val else (1 : ℂ)) =
      omega8 ^ (((Finset.univ.filter fun i : Fin m ↦ decide (p i)).card : ZMod 8) * k).val := by
  have hGen : ∀ (s : Finset (Fin m)), (∏ i ∈ s, if p i then omega8 ^ k.val else (1 : ℂ)) =
      omega8 ^ (((s.filter fun i : Fin m ↦ decide (p i)).card : ZMod 8) * k).val := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
        rw [Finset.prod_cons, Finset.filter_cons, ih]
        by_cases hpa : p a
        · have hd : decide (p a) = true := decide_eq_true hpa
          rw [ite_eq_left hpa, ite_eq_left hd, Finset.card_cons,
              Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm _ k, omega8_zmod8_add]
        · have hd : decide (p a) = false := decide_eq_false hpa
          simp [hpa]
  exact hGen Finset.univ
theorem bitRev6_involutive_local : ∀ a : Fin 64, bitRev6 (bitRev6 a) = a := by decide
theorem bitRev6_val_eq_bitsVal_rev :
    ∀ a : Fin 64, (bitRev6 a).val = bitsVal (fun j : Fin 6 ↦ basisBits 6 a ⟨5 - j.val, by omega⟩) :=
      by
  decide
theorem u18GridEquiv_zero_eq : ∀ w : Fin 3, u18GridEquiv 0 w = 0 := by decide
theorem bitRev6_zero_eq : bitRev6 0 = 0 := by decide
/-- Exact coordinate bridge: `slotSubGridCoord64 r18 (basisBits n x) w = bitRev6 (u18GridEquiv
  (r18.extractIndex x) w)`. -/
theorem slotSubGridCoord64_eq_bitRev6_u18GridEquiv {n : ℕ} (r18 : QRegister 18 n)
    (x : Fin (2 ^ n)) (w : Fin 3) : slotSubGridCoord64 r18 (basisBits n x) w = bitRev6
    (u18GridEquiv (r18.extractIndex x) w) := by
  apply Fin.ext
  have hw : 6 * w.val + 6 ≤ 18 := by have := w.isLt; omega
  let r6 : QRegister 6 18 := QRegister.block (6 * w.val) 6 hw
  have hu : u18GridEquiv (r18.extractIndex x) w = r6.extractIndex (r18.extractIndex x) :=
    (block6_extractIndex_u18 w hw (r18.extractIndex x)).symm
  rw [hu, bitRev6_val_eq_bitsVal_rev]
  change bitsVal (fun j : Fin 6 ↦ basisBits n x (axisBitRev6 r18 w j)) =
    bitsVal (fun j : Fin 6 ↦
      basisBits 6 (r6.extractIndex (r18.extractIndex x)) ⟨5 - j.val, by omega⟩)
  unfold bitsVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  rw [QRegister.basisBits_extractIndex r6, QRegister.basisBits_extractIndex r18]
  have hidx : r6 ⟨5 - j.val, by omega⟩ = ⟨6 * w.val + (5 - j.val), by have := w.isLt; omega⟩ := by
    ext; simp [r6]
  rw [hidx]
  rfl
theorem slotSubGridCoord64_eq_iff_extractIndex {n : ℕ} (r18 : QRegister 18 n)
    (x : Fin (2 ^ n)) (c : SubGridCoord64) : slotSubGridCoord64 r18 (basisBits n x) = c ↔
    r18.extractIndex x = u18GridEquiv.symm (fun w ↦ bitRev6 (c w)) := by
  constructor
  · intro h
    apply u18GridEquiv.injective
    rw [Equiv.apply_symm_apply]
    funext w
    rw [← h, slotSubGridCoord64_eq_bitRev6_u18GridEquiv, bitRev6_involutive_local]
  · intro h
    funext w
    rw [slotSubGridCoord64_eq_bitRev6_u18GridEquiv, h, Equiv.apply_symm_apply,
      bitRev6_involutive_local]
theorem slotSubGridCoord64_eq_zero_iff_extractIndex {n : ℕ} (r18 : QRegister 18 n)
    (x : Fin (2 ^ n)) : slotSubGridCoord64 r18 (basisBits n x) = (fun _ ↦ 0) ↔
    r18.extractIndex x = 0 := by
  rw [slotSubGridCoord64_eq_iff_extractIndex]
  have hz : u18GridEquiv.symm (fun _ : Fin 3 ↦ bitRev6 0) = 0 := by
    apply u18GridEquiv.injective
    rw [Equiv.apply_symm_apply]
    funext w
    rw [bitRev6_zero_eq, u18GridEquiv_zero_eq]
  rw [hz]
open Classical in
noncomputable def pEnvSpec (y : Fin (2 ^ posCoreWires)) : Operator (2 ^ posCoreWires) :=
  Matrix.diagonal fun x ↦ if rSpectatorElec3906InCore.AgreeOutside x y then (1 : ℂ) else 0
open Classical in
theorem matrix_eq_of_mul_pEnvSpec {A B : Operator (2 ^ posCoreWires)}
    (h : ∀ y : Fin (2 ^ posCoreWires), A * pEnvSpec y = B * pEnvSpec y) : A = B := by
  ext x y
  have hyy : rSpectatorElec3906InCore.AgreeOutside y y := fun _ _ ↦ rfl
  have hxy := congrFun (congrFun (h y) x) y
  simpa [pEnvSpec, Matrix.mul_diagonal, hyy] using hxy
open Classical in
theorem elecProd217_comm_pEnvSpec
    (U_e : Fin 217 → Unitary (2 ^ 18)) (y : Fin (2 ^ posCoreWires)) :
    (elecProd217 U_e).1 * pEnvSpec y = pEnvSpec y * (elecProd217 U_e).1 := by
  unfold pEnvSpec
  refine elecProd217_comm_diagonal_of_agreeOutside U_e _ fun x₁ x₂ h12 ↦ ?_
  have hIff : rSpectatorElec3906InCore.AgreeOutside x₁ y ↔
      rSpectatorElec3906InCore.AgreeOutside x₂ y := ⟨fun h1y w hw ↦ (h12 w hw).symm.trans (h1y
      w hw), fun h2y w hw ↦ (h12 w hw).trans (h2y w hw)⟩
  simp only [hIff]
theorem pointDiag217_eq_diagonal (z : Fin (2 ^ 18)) : (pointDiag217 z).1 = Matrix.diagonal fun
    x : Fin (2 ^ posCoreWires) ↦ ∏ w : Fin 3, omega128 (∑ e : Fin 217, pointAxisPhaseExp128
    (u18GridEquiv z w) (u18GridEquiv ((rSpectatorSlot e).extractIndex x) w)) := by
  dsimp only [pointDiag217, elecProd217]
  rw [list_unitary_val_prod, List.map_ofFn, Function.comp_def]
  have hFn : (fun e : Fin 217 ↦
    Subtype.val ((rSpectatorSlot e).embedUnitary (pointDiagUnitary18 z))) =
      fun e : Fin 217 ↦ Matrix.diagonal (fun x : Fin (2 ^ posCoreWires) ↦
        ∏ w : Fin 3, omega128 (pointAxisPhaseExp128 (u18GridEquiv z w)
          (u18GridEquiv ((rSpectatorSlot e).extractIndex x) w))) := by
    funext e
    rw [QRegister.embedUnitary_val]
    exact embedMatrix_diagonal_local (rSpectatorSlot e) _
  rw [hFn, list_ofFn_diagonal_prod]
  congr 1; funext x
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun w _ ↦ (omega128_finset_sum Finset.univ _).symm
theorem uSpectatorPhase217_eq_diagonal (k : ZMod 8) (z : Fin (2 ^ 18)) :
    (uSpectatorPhase217 k z).1 = Matrix.diagonal fun x : Fin (2 ^ posCoreWires) ↦ omega8 ^
    (((Finset.univ.filter fun e : Fin 217 ↦ decide ((rSpectatorSlot e).extractIndex x =
    z)).card : ZMod 8) * k).val := by
  dsimp only [uSpectatorPhase217, elecProd217]
  rw [list_unitary_val_prod, List.map_ofFn, Function.comp_def]
  have hFn : (fun e : Fin 217 ↦
    Subtype.val ((rSpectatorSlot e).embedUnitary (pointPhaseUnitary18Z8 k z))) =
      fun e : Fin 217 ↦ Matrix.diagonal (fun x : Fin (2 ^ posCoreWires) ↦
        if (rSpectatorSlot e).extractIndex x = z then omega8 ^ k.val else 1) := by
    funext e
    rw [QRegister.embedUnitary_val]
    exact embedMatrix_diagonal_local (rSpectatorSlot e) _
  rw [hFn, list_ofFn_diagonal_prod]
  congr 1; funext x
  exact prod_ite_omega8_eq_card_mul (fun e : Fin 217 ↦ (rSpectatorSlot e).extractIndex x = z) k
open Classical in
theorem uControlledPointDiag217_mul_pEnvSpec (y : Fin (2 ^ posCoreWires)) :
    let z := headTargetPoint18 (basisBits posCoreWires y)
    uControlledPointDiag217.1 * pEnvSpec y = (pointDiag217 z).1 * pEnvSpec y ∧
    (uControlledPointDiag217⁻¹).1 * pEnvSpec y = ((pointDiag217 z)⁻¹).1 * pEnvSpec y := by
  intro z
  have hEntry : ∀ x : Fin (2 ^ posCoreWires), rSpectatorElec3906InCore.AgreeOutside x y →
      controlledPointDiag217Entry x = ∏ w : Fin 3, omega128 (∑ e : Fin 217,
      pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv ((rSpectatorSlot e).extractIndex
      x) w)) := by
    intro x hOut
    dsimp only [controlledPointDiag217Entry, z]
    have hTgt := (nonSpec_invariants_of_agreeOutside_rSpectator3906 hOut).2.2.2.2.1
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [hTgt, u18GridEquiv_headTargetPoint18]
  have hFwd : uControlledPointDiag217.1 * pEnvSpec y = (pointDiag217 z).1 * pEnvSpec y := by
    rw [uControlledPointDiag217_val, pointDiag217_eq_diagonal z]
    unfold pEnvSpec
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x
    by_cases hOut : rSpectatorElec3906InCore.AgreeOutside x y
    · simp [hOut, hEntry x hOut]
    · simp [hOut]
  have hCPDComm : uControlledPointDiag217.1 * pEnvSpec y = pEnvSpec y * uControlledPointDiag217.1 :=
    by
    rw [uControlledPointDiag217_val]
    unfold pEnvSpec
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hPDComm : (pointDiag217 z).1 * pEnvSpec y = pEnvSpec y * (pointDiag217 z).1 :=
    elecProd217_comm_pEnvSpec _ y
  exact ⟨hFwd, unitary_inv_mul_eq_of_mul_eq_and_comm hFwd hCPDComm hPDComm⟩
open Classical in
theorem diag_headPhase_eq_repairedOrigin0_conj : (uQft217)⁻¹ * diagZ8UnitaryN
    headPhaseMod4Z8Spec * uQft217 = (uControlledPointDiag217)⁻¹ * ((uHad217)⁻¹ *
    diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec * uHad217) * uControlledPointDiag217
    := by
  apply Subtype.ext
  apply matrix_eq_of_mul_pEnvSpec
  intro y
  let rCore := QRegExt.ofFin posCoreWires
  let βy := basisBits posCoreWires y
  let z := headTargetPoint18 βy
  let k : ZMod 8 := if Bool.not (headEnBoolSpec βy) then 0
    else 2 + (if βy (wHeadThresh rCore) == 1 then 4 else 0)
  let baseZ8 : ZMod 8 := if Bool.not (headEnBoolSpec βy) then 0 else
      (if headS0Bool βy then 4 else 0) + (if (Bool.not (headS0Bool βy) && decide
      (slotSubGridCoord64 (rElecSlot rCore 0) βy = headTargetCoord64 βy)) then 1 else 0) * k
  let c0 : ℂ := omega8 ^ baseZ8.val
  have hDiagOrig : (diagZ8UnitaryN headPhaseMod4Z8Spec).1 * pEnvSpec y =
      c0 • ((uSpectatorPhase217 k z).1 * pEnvSpec y) := by
    change Matrix.diagonal _ * pEnvSpec y = c0 • ((uSpectatorPhase217 k z).1 * pEnvSpec y)
    rw [uSpectatorPhase217_eq_diagonal k z]
    unfold pEnvSpec
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, smul_diagonal_local]
    congr 1; funext x
    by_cases hOut : rSpectatorElec3906InCore.AgreeOutside x y
    · obtain ⟨hEn, hS0, hTh, hy0, hTgt, _, _, _⟩ :=
        nonSpec_invariants_of_agreeOutside_rSpectator3906 hOut
      let βx := basisBits posCoreWires x
      have hCard : (headHitSetSpec βx).card =
          (if (Bool.not (headS0Bool βy) &&
            decide (slotSubGridCoord64 (rElecSlot rCore 0) βy = headTargetCoord64 βy)) then 1 else
              0) +
          (Finset.univ.filter fun e : Fin 217 ↦
            decide ((rSpectatorSlot e).extractIndex x = z)).card := by
        unfold headHitSetSpec
        rw [fin218_filter_card_split]
        have hs0x : (βx (wSlot0Core rCore) == 1) = headS0Bool βy := hS0
        have hyTgtEq : (let s0 := βx (wSlot0Core rCore) == 1
            let dHead := fineCoordOfReg21 (rHeadFine21 rCore) βx
            let y0 := slotSubGridCoord64 (rElecSlot rCore 0) βx
            let b0 := parity3OfReg (rCosetB0 rCore) βx
            (fun w ↦ if Bool.not s0 then ⟨(dHead w).val / 2, by omega⟩
              else (anchorSubTarget1D (y0 w) (if b0 w then 1 else
                0) (dHead w)).1 : SubGridCoord64)) =
            headTargetCoord64 βy := hTgt
        rw [hyTgtEq, hs0x, hy0]
        simp only [Fin.val_zero, ne_eq, not_true_eq_false, decide_false, Bool.or_false]
        refine congrArg ((if (Bool.not (headS0Bool βy) &&
            decide (slotSubGridCoord64 (rElecSlot rCore 0) βy = headTargetCoord64 βy)) then 1 else
              0) + ·)
          (congrArg Finset.card (Finset.filter_congr fun e _ ↦ ?_))
        have hne : decide (e.succ.val ≠ 0) = true :=
          decide_eq_true (fun h ↦ Fin.succ_ne_zero e (Fin.ext h))
        rw [hne, Bool.or_true, Bool.true_and, decide_eq_true_eq, decide_eq_true_eq]
        exact slotSubGridCoord64_eq_iff_extractIndex (rSpectatorSlot e) x (headTargetCoord64 βy)
      simp only [hOut, ↓reduceIte, mul_one]
      change omega8 ^ (headPhaseMod4Z8Spec βx).val = c0 * _
      unfold headPhaseMod4Z8Spec
      dsimp only [c0, baseZ8, k, βx, βy, rCore] at hEn hS0 hTh hCard ⊢
      have hs0x : (basisBits posCoreWires x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) =
          headS0Bool (basisBits posCoreWires y) := hS0
      simp only [hEn, hs0x, hTh, hCard]
      cases hEnY : headEnBoolSpec (basisBits posCoreWires y)
      · simp only [Bool.not_false, ↓reduceIte, ZMod.val_zero, _root_.pow_zero, mul_zero, mul_one]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.cast_add]
        rw [← omega8_zmod8_add]
        exact congrArg (fun u : ZMod 8 ↦ omega8 ^ u.val) (by split_ifs <;> ring)
    · simp only [hOut, ↓reduceIte, mul_zero]
  have hDiagRep : (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * pEnvSpec y =
      c0 • ((uSpectatorPhase217 k 0).1 * pEnvSpec y) := by
    change Matrix.diagonal _ * pEnvSpec y = c0 • ((uSpectatorPhase217 k 0).1 * pEnvSpec y)
    rw [uSpectatorPhase217_eq_diagonal k 0]
    unfold pEnvSpec
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, smul_diagonal_local]
    congr 1; funext x
    by_cases hOut : rSpectatorElec3906InCore.AgreeOutside x y
    · obtain ⟨hEn, hS0, hTh, hy0, hTgt, _, _, _⟩ :=
        nonSpec_invariants_of_agreeOutside_rSpectator3906 hOut
      let βx := basisBits posCoreWires x
      have hCard : (headHitSetOrigin0RepairedSpec βx).card =
          (if (Bool.not (headS0Bool βy) &&
            decide (slotSubGridCoord64 (rElecSlot rCore 0) βy = headTargetCoord64 βy)) then 1 else
              0) +
          (Finset.univ.filter fun e : Fin 217 ↦
            decide ((rSpectatorSlot e).extractIndex x = 0)).card := by
        unfold headHitSetOrigin0RepairedSpec
        rw [fin218_filter_card_split]
        dsimp only [βx, βy, rCore] at hS0 hy0 hTgt ⊢
        rw [hS0, hy0, hTgt]
        simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.succ_ne_zero]
        refine congrArg ((if (Bool.not (headS0Bool βy) &&
            decide (slotSubGridCoord64 (rElecSlot rCore 0) βy = headTargetCoord64 βy)) then 1 else
              0) + ·)
          (congrArg Finset.card (Finset.filter_congr fun e _ ↦ ?_))
        rw [decide_eq_true_eq, decide_eq_true_eq]
        exact slotSubGridCoord64_eq_zero_iff_extractIndex (rSpectatorSlot e) x
      simp only [hOut, ↓reduceIte, mul_one]
      change omega8 ^ (headPhaseMod4Origin0RepairedZ8Spec βx).val = c0 * _
      unfold headPhaseMod4Origin0RepairedZ8Spec
      dsimp only [c0, baseZ8, k, βx, βy, rCore] at hEn hS0 hTh hCard ⊢
      simp only [hEn, hS0, hTh, hCard]
      cases hEnY : headEnBoolSpec (basisBits posCoreWires y)
      · simp only [Bool.not_false, ↓reduceIte, ZMod.val_zero, _root_.pow_zero, mul_zero, mul_one]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.cast_add]
        rw [← omega8_zmod8_add]
        exact congrArg (fun u : ZMod 8 ↦ omega8 ^ u.val) (by split_ifs <;> ring)
    · simp only [hOut, ↓reduceIte, mul_zero]
  have hQftComm : uQft217.1 * pEnvSpec y = pEnvSpec y * uQft217.1 :=
    elecProd217_comm_pEnvSpec _ y
  have hHadComm : uHad217.1 * pEnvSpec y = pEnvSpec y * uHad217.1 :=
    elecProd217_comm_pEnvSpec _ y
  have hPDComm : (pointDiag217 z).1 * pEnvSpec y = pEnvSpec y * (pointDiag217 z).1 :=
    elecProd217_comm_pEnvSpec _ y
  obtain ⟨hCtrlFwd, hCtrlInv⟩ := uControlledPointDiag217_mul_pEnvSpec y
  have hCPDComm : uControlledPointDiag217.1 * pEnvSpec y = pEnvSpec y * uControlledPointDiag217.1 :=
    by
    change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hBase := congrArg (fun U : Unitary (2 ^ posCoreWires) ↦ c0 • (U.1 * pEnvSpec y))
    (uQft217_conj_uSpectatorPhase217_eq_pointDiag217_conj_origin0 k z)
  dsimp only [Submonoid.coe_mul] at hBase ⊢
  calc (uQft217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Z8Spec).1 * uQft217.1 * pEnvSpec y
      = (uQft217⁻¹).1 * ((diagZ8UnitaryN headPhaseMod4Z8Spec).1 * pEnvSpec y) * uQft217.1 := by
          simp only [Matrix.mul_assoc]; rw [hQftComm]
    _ = c0 • (((uQft217⁻¹).1 * (uSpectatorPhase217 k z).1 * uQft217.1) * pEnvSpec y) := by
          rw [hDiagOrig, Matrix.mul_smul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]; rw [← hQftComm]
    _ = c0 • ((((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 * (uSpectatorPhase217 k 0).1 * uHad217.1) *
          (pointDiag217 z).1) * pEnvSpec y) := hBase
    _ = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 *
          (c0 • ((uSpectatorPhase217 k 0).1 * pEnvSpec y)) * uHad217.1) * (pointDiag217 z).1 := by
          simp only [Matrix.smul_mul, Matrix.mul_smul]
          refine congrArg (c0 • ·) ?_
          calc ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 * (uSpectatorPhase217 k 0).1 * uHad217.1) *
                  (pointDiag217 z).1 * pEnvSpec y
              = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 * (uSpectatorPhase217 k 0).1 * uHad217.1) *
                  ((pointDiag217 z).1 * pEnvSpec y) := by simp only [Matrix.mul_assoc]
            _ = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 * (uSpectatorPhase217 k 0).1 *
                  (uHad217.1 * pEnvSpec y)) * (pointDiag217 z).1 := by
                  rw [hPDComm]; simp only [Matrix.mul_assoc]
            _ = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 *
                  ((uSpectatorPhase217 k 0).1 * pEnvSpec y) * uHad217.1) * (pointDiag217 z).1 := by
                  rw [hHadComm]; simp only [Matrix.mul_assoc]
    _ = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 *
          (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * uHad217.1) *
          ((pointDiag217 z).1 * pEnvSpec y) := by
          rw [← hDiagRep]
          calc ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 *
                  ((diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * pEnvSpec y) *
                    uHad217.1) *
                  (pointDiag217 z).1
              = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 *
                  (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * (pEnvSpec y *
                    uHad217.1)) *
                  (pointDiag217 z).1 := by simp only [Matrix.mul_assoc]
            _ = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 *
                  (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * uHad217.1) *
                  (pEnvSpec y * (pointDiag217 z).1) := by
                  rw [← hHadComm]; simp only [Matrix.mul_assoc]
            _ = ((pointDiag217 z)⁻¹).1 * ((uHad217⁻¹).1 *
                  (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * uHad217.1) *
                  ((pointDiag217 z).1 * pEnvSpec y) := by
                  rw [← hPDComm]
    _ = (uControlledPointDiag217⁻¹).1 *
          ((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * uHad217.1) *
          uControlledPointDiag217.1 * pEnvSpec y := by
          rw [← hCtrlFwd]
          have hMidComm : ((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
            uHad217.1) *
              pEnvSpec y =
            pEnvSpec y * ((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
              uHad217.1) := by
            have hHadInvComm : (uHad217⁻¹).1 * pEnvSpec y = pEnvSpec y * (uHad217⁻¹).1 := by
              dsimp only [uHad217]; rw [elecProd217_inv]; exact elecProd217_comm_pEnvSpec _ y
            have hDComm : (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * pEnvSpec y =
                pEnvSpec y * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 := by
              change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
              rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
              exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
            calc (uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 * uHad217.1 *
              pEnvSpec y
                = (uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    (pEnvSpec y * uHad217.1) := by simp only [Matrix.mul_assoc]; rw [hHadComm]
              _ = (uHad217⁻¹).1 * (pEnvSpec y *
                (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1) *
                    uHad217.1 := by
                      simp only [← Matrix.mul_assoc];
                      rw [Matrix.mul_assoc (uHad217⁻¹).1, hDComm, ← Matrix.mul_assoc]
              _ = pEnvSpec y * ((uHad217⁻¹).1 *
                (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    uHad217.1) := by simp only [← Matrix.mul_assoc]; rw [hHadInvComm]
          calc ((pointDiag217 z)⁻¹).1 *
                  ((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    uHad217.1) *
                  (uControlledPointDiag217.1 * pEnvSpec y)
              = ((pointDiag217 z)⁻¹).1 *
                  (((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    uHad217.1) *
                    pEnvSpec y) * uControlledPointDiag217.1 := by
                  rw [hCPDComm]; simp only [Matrix.mul_assoc]
            _ = (((pointDiag217 z)⁻¹).1 * pEnvSpec y) *
                  ((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    uHad217.1) *
                  uControlledPointDiag217.1 := by
                  rw [hMidComm]; simp only [Matrix.mul_assoc]
            _ = ((uControlledPointDiag217⁻¹).1 * pEnvSpec y) *
                  ((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    uHad217.1) *
                  uControlledPointDiag217.1 := by rw [hCtrlInv]
            _ = (uControlledPointDiag217⁻¹).1 *
                  (((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    uHad217.1) *
                    pEnvSpec y) * uControlledPointDiag217.1 := by
                  rw [hMidComm]; simp only [Matrix.mul_assoc]
            _ = (uControlledPointDiag217⁻¹).1 *
                  ((uHad217⁻¹).1 * (diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec).1 *
                    uHad217.1) *
                  uControlledPointDiag217.1 * pEnvSpec y := by
                  simp only [Matrix.mul_assoc]; rw [← hCPDComm]
noncomputable def uFlipHeadThresh : Unitary (2 ^ posCoreWires) :=
  monomialZ8UnitaryN (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec (fun _ ↦ 0)
theorem monomialZ8_eq_uFlip_mul_diag (p : BitAssignment posCoreWires → ZMod 8) :
    monomialZ8UnitaryN (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec p =
      uFlipHeadThresh * diagZ8UnitaryN p := by
  apply Subtype.ext
  apply matrix_ext_of_ket_local
  intro β
  unfold uFlipHeadThresh
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [ket_diagZ8UnitaryN, Matrix.mulVec_smul, ket_monomialZ8UnitaryN, ket_monomialZ8UnitaryN]
  simp
theorem uFlipHeadThresh_eq_embed_high110 :
    uFlipHeadThresh =
      rHigh110InCore.embedUnitary
        (monomialZ8UnitaryN ⟨61, by decide⟩
          (fun γ : BitAssignment 110 ↦
            headEnBoolSpec (fun w ↦
              if h : 3924 ≤ w.val then
                γ ⟨w.val - 3924, w_sub_3924_lt_110 w h⟩
              else 0))
          (fun _ ↦ 0)) := by
  unfold uFlipHeadThresh
  rw [embedUnitary_monomialZ8UnitaryN, rHigh110InCore_61_eq_wHeadThresh]
  have hd : (fun β : BitAssignment posCoreWires ↦ headEnBoolSpec (fun w ↦ if h : 3924 ≤ w.val
      then β (rHigh110InCore ⟨w.val - 3924, w_sub_3924_lt_110 w h⟩) else 0)) = headEnBoolSpec
      := by
    funext β
    refine headEnBoolSpec_congr_high fun w hw3924 ↦ ?_
    rw [dite_eq_left hw3924]
    refine congrArg β (Fin.ext ?_)
    rw [rHigh110InCore_val]
    dsimp only
    omega
  rw [hd]
theorem uFlipHeadThresh_comm_qft_had_and_ctrlDiag : uQft0 * uFlipHeadThresh = uFlipHeadThresh
    * uQft0 ∧ uQft217 * uFlipHeadThresh = uFlipHeadThresh * uQft217 ∧ (uQft217)⁻¹ *
    uFlipHeadThresh = uFlipHeadThresh * (uQft217)⁻¹ ∧ uHad217 * uFlipHeadThresh =
    uFlipHeadThresh * uHad217 ∧ (uHad217)⁻¹ * uFlipHeadThresh = uFlipHeadThresh * (uHad217)⁻¹
    ∧ uControlledPointDiag217 * uFlipHeadThresh = uFlipHeadThresh * uControlledPointDiag217 ∧
    (uControlledPointDiag217)⁻¹ * uFlipHeadThresh = uFlipHeadThresh *
    (uControlledPointDiag217)⁻¹ := by
  have hQ0 : uQft0 * uFlipHeadThresh = uFlipHeadThresh * uQft0 := by
    rw [uFlipHeadThresh_eq_embed_high110]
    exact embedUnitary_comm_of_disjoint_local rElec0InCore rHigh110InCore
      rElec0InCore_disj_rHigh110InCore _ _
  have hProd : ∀ U_e : Fin 217 → Unitary (2 ^ 18),
      elecProd217 U_e * uFlipHeadThresh = uFlipHeadThresh * elecProd217 U_e := fun U_e ↦ by
    apply Subtype.ext
    unfold elecProd217
    refine list_unitary_prod_comm_mat uFlipHeadThresh.1 _ fun u hu ↦ ?_
    rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩
    have hEq : (rSpectatorSlot e).embedUnitary (U_e e) * uFlipHeadThresh =
        uFlipHeadThresh * (rSpectatorSlot e).embedUnitary (U_e e) := by
      rw [uFlipHeadThresh_eq_embed_high110]
      refine embedUnitary_comm_of_disjoint_local (rSpectatorSlot e) rHigh110InCore ?_ _ _
      rw [QRegister.disjoint_iff]
      intro q k hqk
      have h1 : (rSpectatorSlot e q).val = 18 * (e.val + 1) + q.val :=
        PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ q
      have h2 : (rHigh110InCore k).val = 3924 + k.val := rHigh110InCore_val k
      have hv := congrArg Fin.val hqk
      rw [h1, h2] at hv
      have := e.isLt; have := q.isLt
      omega
    simpa only [Submonoid.coe_mul] using congrArg Subtype.val hEq
  have hDiag : ∀ f : Fin (2 ^ posCoreWires) → ℂ, (∀ x y : Fin (2 ^ posCoreWires), (∀ w : Wire
      posCoreWires, w ≠ wHeadThresh (QRegExt.ofFin posCoreWires) → basisBits posCoreWires x
      w = basisBits posCoreWires y w) → f x = f y) → Matrix.diagonal f * uFlipHeadThresh.1 =
      uFlipHeadThresh.1 * Matrix.diagonal f := fun f hInv ↦
      (monomialZ8UnitaryN_comm_diagonal_of_invariant _ _ _ f hInv).symm
  have hEntryInv : ∀ x y : Fin (2 ^ posCoreWires), (∀ w : Wire posCoreWires, w ≠ wHeadThresh
      (QRegExt.ofFin posCoreWires) → basisBits posCoreWires x w = basisBits posCoreWires y
      w) → controlledPointDiag217Entry x = controlledPointDiag217Entry y := by
    intro x y hxy
    have hTgt := (headEn_and_miss_congr_ne_wHeadThresh hxy).2.2.1
    have hExt : ∀ e : Fin 217,
      (rSpectatorSlot e).extractIndex x = (rSpectatorSlot e).extractIndex y := fun e ↦ by
      apply (basisBitsEquiv 18).injective
      funext q
      change basisBits 18 ((rSpectatorSlot e).extractIndex x) q =
        basisBits 18 ((rSpectatorSlot e).extractIndex y) q
      rw [(rSpectatorSlot e).basisBits_extractIndex, (rSpectatorSlot e).basisBits_extractIndex]
      refine hxy _ (fun h ↦ ?_)
      have hv := congrArg Fin.val h
      have h1 := PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ q
      change (rSpectatorSlot e q).val = _ at h1
      rw [h1, wHeadThresh_val_eq_3985] at hv
      have := e.isLt; have := q.isLt
      omega
    dsimp only [controlledPointDiag217Entry]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [hTgt]
    exact congrArg omega128 (Finset.sum_congr rfl fun e _ ↦ by rw [hExt e])
  have hCPD : uControlledPointDiag217 * uFlipHeadThresh = uFlipHeadThresh *
    uControlledPointDiag217 :=
    Subtype.ext (hDiag controlledPointDiag217Entry hEntryInv)
  refine ⟨hQ0, hProd _, ?_, hProd _, ?_, hCPD, unitary_inv_comm_of_comm hCPD⟩
  · dsimp only [uQft217]; rw [elecProd217_inv]; exact hProd _
  · dsimp only [uHad217]; rw [elecProd217_inv]; exact hProd _
/-- **217-Electron QFT Conjugation of `uHeadPhaseMod4` onto `uHeadPhaseMod4Origin0Repaired` (`0`
  Hypotheses)**:
Proves exact matrix equality on all of `2 ^ posCoreWires` (`0` hypotheses):
`(uQft217)⁻¹ * uHeadPhaseMod4 * uQft217` equals conjugating
`(uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0Repaired * uSpectatorHadamard3906`
by `uControlledPointDiag217`! -/
theorem uQft217_conj_uHeadPhaseMod4_eq_repairedOrigin0_zeroHyp : (uQft217)⁻¹ * uHeadPhaseMod4
    * uQft217 = (uControlledPointDiag217)⁻¹ * ((uSpectatorHadamard3906)⁻¹ *
    uHeadPhaseMod4Origin0Repaired * uSpectatorHadamard3906) * uControlledPointDiag217 := by
  obtain ⟨_, _, hQftInv, _, hHadInv, _, hCPDInv⟩ := uFlipHeadThresh_comm_qft_had_and_ctrlDiag
  rw [uSpectatorHadamard3906_eq_uHad217]
  have hOrig : uHeadPhaseMod4 = uFlipHeadThresh * diagZ8UnitaryN headPhaseMod4Z8Spec :=
    monomialZ8_eq_uFlip_mul_diag headPhaseMod4Z8Spec
  have hRep : uHeadPhaseMod4Origin0Repaired =
      uFlipHeadThresh * diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec :=
    monomialZ8_eq_uFlip_mul_diag headPhaseMod4Origin0RepairedZ8Spec
  rw [hOrig, hRep]
  calc (uQft217)⁻¹ * (uFlipHeadThresh * diagZ8UnitaryN headPhaseMod4Z8Spec) * uQft217
      = ((uQft217)⁻¹ * uFlipHeadThresh) * diagZ8UnitaryN headPhaseMod4Z8Spec * uQft217 := by
          simp only [_root_.mul_assoc]
    _ = uFlipHeadThresh * ((uQft217)⁻¹ * diagZ8UnitaryN headPhaseMod4Z8Spec * uQft217) := by
          rw [hQftInv]; simp only [_root_.mul_assoc]
    _ = uFlipHeadThresh *
          ((uControlledPointDiag217)⁻¹ *
            ((uHad217)⁻¹ * diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec * uHad217) *
            uControlledPointDiag217) := by
          rw [diag_headPhase_eq_repairedOrigin0_conj]
    _ = ((uControlledPointDiag217)⁻¹ * uFlipHeadThresh) *
          ((uHad217)⁻¹ * diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec * uHad217) *
          uControlledPointDiag217 := by
          rw [hCPDInv]; simp only [_root_.mul_assoc]
    _ = (uControlledPointDiag217)⁻¹ *
          (((uHad217)⁻¹ * uFlipHeadThresh) *
            diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec * uHad217) *
          uControlledPointDiag217 := by
          rw [hHadInv]; simp only [_root_.mul_assoc]
    _ = (uControlledPointDiag217)⁻¹ *
          ((uHad217)⁻¹ * (uFlipHeadThresh * diagZ8UnitaryN headPhaseMod4Origin0RepairedZ8Spec) *
            uHad217) *
          uControlledPointDiag217 := by
          simp only [_root_.mul_assoc]
theorem unitary_conj_mul_local {D : ℕ} (U A B : Unitary D) :
    U⁻¹ * (A * B) * U = (U⁻¹ * A * U) * (U⁻¹ * B * U) := by
  apply Subtype.ext
  have hU : U.1 * (U⁻¹).1 = 1 := U.2.2
  calc (U⁻¹).1 * (A.1 * B.1) * U.1
      = (U⁻¹).1 * A.1 * (U.1 * (U⁻¹).1) * B.1 * U.1 := by
          rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = ((U⁻¹).1 * A.1 * U.1) * ((U⁻¹).1 * B.1 * U.1) := by
          simp only [Matrix.mul_assoc]
/-- **Full 218-Electron QFT Conjugation of `uHeadPhaseMod4`
  (`fullQft218_conj_uHeadPhaseMod4_eq_repairedOrigin0_zeroHyp`,
`0` Hypotheses)**:
Exports all three canonical forms of `(fullQft218)⁻¹ * uHeadPhaseMod4 * fullQft218` on
`posCoreWires`:
1. Conjugated `uHeadPhaseMod4Origin0Repaired` sandwiched by `uControlledPointDiag217` and `uQft0`,
2. Right-side (`D_pre`) split form where `M0_orig := (uSpectatorHadamard3906)⁻¹ *
uHeadPhaseMod4Origin0 * uSpectatorHadamard3906`
   absorbs `uQft0` (`uQft0⁻¹ * M0_orig * uQft0 = M0_orig`) and `D_pre` sits either inside or outside
   `uControlledPointDiag217`, and
3. Left-side (`D_post`) split form where `M0_orig` absorbs `uQft0` and `D_post` sits either inside
or outside `uControlledPointDiag217`! -/
theorem fullQft218_conj_uHeadPhaseMod4_eq_repairedOrigin0_zeroHyp :
    let M0_rep :=
      (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0Repaired * uSpectatorHadamard3906
    let M0_orig := (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906
    let Phi := uControlledPointDiag217
    fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      uQft0⁻¹ * (Phi⁻¹ * M0_rep * Phi) * uQft0 ∧
    fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      uQft0⁻¹ * ((Phi⁻¹ * M0_orig * Phi) * uHeadOrigin0Slot0MissPre) * uQft0 ∧
    fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      uQft0⁻¹ * (uHeadOrigin0Slot0MissPost * (Phi⁻¹ * M0_orig * Phi)) * uQft0 ∧
    fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      ((uQft0⁻¹ * Phi⁻¹ * uQft0) * M0_orig * (uQft0⁻¹ * Phi * uQft0)) *
        (uQft0⁻¹ * uHeadOrigin0Slot0MissPre * uQft0) ∧
    fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      (uQft0⁻¹ * uHeadOrigin0Slot0MissPost * uQft0) *
        ((uQft0⁻¹ * Phi⁻¹ * uQft0) * M0_orig * (uQft0⁻¹ * Phi * uQft0)) := by
  intro M0_rep M0_orig Phi
  have h1 : fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      uQft0⁻¹ * (Phi⁻¹ * M0_rep * Phi) * uQft0 := by
    dsimp only [fullQft218]
    rw [fullQft218_conj_eq_uQft0_conj_uQft217_conj,
        uQft217_conj_uHeadPhaseMod4_eq_repairedOrigin0_zeroHyp]
  obtain ⟨hRepPre, hRepPost⟩ := uSpectatorHadamard3906_conj_repaired_eq_missPre_and_missPost
  obtain ⟨hPhiPre, _, _, hPhiInvPost⟩ := uControlledPointDiag217_comm_slot0MissPre_and_Post
  have h2 : fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      uQft0⁻¹ * ((Phi⁻¹ * M0_orig * Phi) * uHeadOrigin0Slot0MissPre) * uQft0 := by
    rw [h1]
    refine congrArg (fun X ↦ uQft0⁻¹ * X * uQft0) ?_
    dsimp only [M0_rep, M0_orig, Phi] at hRepPre ⊢
    rw [hRepPre]
    calc (uControlledPointDiag217)⁻¹ * (M0_orig * uHeadOrigin0Slot0MissPre) *
      uControlledPointDiag217
        = (uControlledPointDiag217)⁻¹ * M0_orig *
            (uHeadOrigin0Slot0MissPre * uControlledPointDiag217) := by simp only [_root_.mul_assoc]
      _ = ((uControlledPointDiag217)⁻¹ * M0_orig * uControlledPointDiag217) *
            uHeadOrigin0Slot0MissPre := by rw [← hPhiPre]; simp only [_root_.mul_assoc]
  have h3 : fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      uQft0⁻¹ * (uHeadOrigin0Slot0MissPost * (Phi⁻¹ * M0_orig * Phi)) * uQft0 := by
    rw [h1]
    refine congrArg (fun X ↦ uQft0⁻¹ * X * uQft0) ?_
    dsimp only [M0_rep, M0_orig, Phi] at hRepPost ⊢
    rw [hRepPost]
    calc (uControlledPointDiag217)⁻¹ * (uHeadOrigin0Slot0MissPost * M0_orig) *
      uControlledPointDiag217
        = ((uControlledPointDiag217)⁻¹ * uHeadOrigin0Slot0MissPost) *
            M0_orig * uControlledPointDiag217 := by simp only [_root_.mul_assoc]
      _ = uHeadOrigin0Slot0MissPost *
            ((uControlledPointDiag217)⁻¹ * M0_orig * uControlledPointDiag217) := by
          rw [hPhiInvPost]; simp only [_root_.mul_assoc]
  have hQ0_M0 : uQft0⁻¹ * M0_orig * uQft0 = M0_orig := by
    have hComm : uQft0 * M0_orig = M0_orig * uQft0 :=
      uHeadPhaseMod4Origin0ConjH_comm_rElec0 uCoreHadamard18
    calc uQft0⁻¹ * M0_orig * uQft0
        = uQft0⁻¹ * (M0_orig * uQft0) := by simp only [_root_.mul_assoc]
      _ = (uQft0⁻¹ * uQft0) * M0_orig := by rw [← hComm]; simp only [_root_.mul_assoc]
      _ = M0_orig := by rw [inv_mul_cancel, one_mul]
  have h4 : fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      ((uQft0⁻¹ * Phi⁻¹ * uQft0) * M0_orig * (uQft0⁻¹ * Phi * uQft0)) *
        (uQft0⁻¹ * uHeadOrigin0Slot0MissPre * uQft0) := by
    rw [h2, unitary_conj_mul_local uQft0 (Phi⁻¹ * M0_orig * Phi) uHeadOrigin0Slot0MissPre,
        unitary_conj_mul_local uQft0 (Phi⁻¹ * M0_orig) Phi,
        unitary_conj_mul_local uQft0 Phi⁻¹ M0_orig, hQ0_M0]
  have h5 : fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218 =
      (uQft0⁻¹ * uHeadOrigin0Slot0MissPost * uQft0) *
        ((uQft0⁻¹ * Phi⁻¹ * uQft0) * M0_orig * (uQft0⁻¹ * Phi * uQft0)) := by
    rw [h3, unitary_conj_mul_local uQft0 uHeadOrigin0Slot0MissPost (Phi⁻¹ * M0_orig * Phi),
        unitary_conj_mul_local uQft0 (Phi⁻¹ * M0_orig) Phi,
        unitary_conj_mul_local uQft0 Phi⁻¹ M0_orig, hQ0_M0]
  exact ⟨h1, h2, h3, h4, h5⟩
end Part1_RepairedOrigin0HeadAndQft218Conjugation
section Part2_USwapCore3967AndHeadPhase80Mod4Eff
theorem block0_embedUnitary_eq_castUnitaryPow2 {a b : ℕ} (h : a = b) (hle : 0 + a ≤ b)
    (U : Unitary (2 ^ a)) :
    (QRegister.block 0 a hle).embedUnitary U = castUnitaryPow2 h U := by
  subst h
  unfold castUnitaryPow2
  have hid : QRegister.block 0 a hle = QRegExt.idReg a := by
    apply qreg_ext; intro i; apply Fin.ext
    simp [QRegExt.idReg]
  rw [hid, embedUnitary_idReg_eq]
/-- `selPosCoreInCore80.embedUnitary U` coincides identically with `castUnitaryPow2
  pos24_coreWires80_eq.symm U`. -/
theorem selPosCoreInCore80_embedUnitary_eq_castUnitaryPow2 (U : Unitary (2 ^ posCoreWires)) :
    selPosCoreInCore80.embedUnitary U = castUnitaryPow2 pos24_coreWires80_eq.symm U :=
  block0_embedUnitary_eq_castUnitaryPow2 pos24_coreWires80_eq.symm _ U
/-- 2-wire high-core register `(wCore3967, wCore4029)` supporting `uSwapCore3967`. -/
def rSwap2Core : QRegister 2 (fullSysCoreWires 80) where
  wires := ⟨fun i : Fin 2 ↦ if i.val = 0 then wCore3967 else wCore4029,
    fun a b hab ↦ by
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab PosPostPrep80MergedVep.wCore3967_ne_4029
      · exact absurd hab.symm PosPostPrep80MergedVep.wCore3967_ne_4029
      · rfl⟩
theorem rSwap2Core_ge_3924 : InterWalkRSum42Hoist.IsHigh3924Reg rSwap2Core := by
  intro i
  fin_cases i <;> decide
/-- `uSwapCore3967` equals `rSwap2Core.embedUnitary (cSwap2 0 1 _).eval`. -/
theorem uSwapCore3967_eq_embed_rSwap2Core : uSwapCore3967 = rSwap2Core.embedUnitary
    (PosPostPrep80MergedVep.cSwap2 0 1 (by decide)).eval := by
  have hOnReg : (PosPostPrep80MergedVep.cSwap2 0 1 (by decide)).onRegister rSwap2Core =
      PosPostPrep80MergedVep.cSwapCore3967 := by
    have h01 : rSwap2Core.compose (QRegister.pair 0 1 (by decide)) =
        QRegister.pair PosPostPrep80MergedVep.wCore3967 PosPostPrep80MergedVep.wCore4029
          PosPostPrep80MergedVep.wCore3967_ne_4029 := by
      apply qreg_ext; intro i; fin_cases i <;> simp [QRegister.pair, QRegister.compose, rSwap2Core]
    have h10 : rSwap2Core.compose (QRegister.pair 1 0 (Ne.symm (by decide))) =
        QRegister.pair PosPostPrep80MergedVep.wCore4029 PosPostPrep80MergedVep.wCore3967
          PosPostPrep80MergedVep.wCore3967_ne_4029.symm := by
      apply qreg_ext; intro i; fin_cases i <;> simp [QRegister.pair, QRegister.compose, rSwap2Core]
    dsimp only [PosPostPrep80MergedVep.cSwapCore3967, PosPostPrep80MergedVep.cSwap2,
      Circuit.CNOT, Circuit.onRegister]
    rw [h01, h10]
  rw [uSwapCore3967, PosPostPrep80MergedVep.lockPosPostVal_eq, ← hOnReg,
      Circuit.eval_onRegister]
/-- Any embedded unitary on `fullSysCoreWires 80` whose wires all lie in `[0 .. 3924)` commutes
  with `uSwapCore3967`. -/
theorem uSwapCore3967_comm_of_wires_lt_3924 {k : ℕ} (r : QRegister k (fullSysCoreWires 80))
    (hr : ∀ j : Fin k, (r j).val < 3924) (U : Unitary (2 ^ k)) : uSwapCore3967 *
    r.embedUnitary U = r.embedUnitary U * uSwapCore3967 := by
  rw [uSwapCore3967_eq_embed_rSwap2Core]
  refine embedUnitary_comm_of_disjoint_local rSwap2Core r ?_ _ U
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hi := rSwap2Core_ge_3924 i
  have hj := hr j
  have hv := congrArg Fin.val hij
  omega
/-- `uSwapCore3967` commutes with every 18-wire electron slot `rElec18InCore pos24_6_le_80 i` (`i
  : Fin 218`). -/
theorem uSwapCore3967_comm_rElec18InCore (i : Fin 218) (U : Unitary (2 ^ 18)) :
    uSwapCore3967 * (rElec18InCore pos24_6_le_80 i).embedUnitary U =
      (rElec18InCore pos24_6_le_80 i).embedUnitary U * uSwapCore3967 := by
  refine uSwapCore3967_comm_of_wires_lt_3924 (rElec18InCore pos24_6_le_80 i) (fun j ↦ ?_) U
  rw [ZeroHypStageABToUFoldedPass123SegAndCompac.rElec18InCore_apply_val]
  have := i.isLt; have := j.isLt
  omega
theorem unitary_list_prod_comm {D : ℕ} (A : Unitary D) :
    ∀ (L : List (Unitary D)), (∀ u ∈ L, A * u = u * A) → A * L.prod = L.prod * A
  | [], _ => by simp
  | u :: us, hcomm => by
      simp only [List.prod_cons, ← _root_.mul_assoc]
      rw [hcomm u List.mem_cons_self, _root_.mul_assoc,
          unitary_list_prod_comm A us (fun v hv ↦ hcomm v (List.mem_cons_of_mem u hv)),
          ← _root_.mul_assoc]
/-- `uSwapCore3967` commutes with the full 218-electron QFT `Q_{218}` and its inverse
  `Q_{218}⁻¹`. -/
theorem uSwapCore3967_comm_qftCore218 :
    let Q := fullSysQftCoreUnitary pos24_6_le_80 coreQftHadamardPrunedBundle128
    uSwapCore3967 * Q = Q * uSwapCore3967 ∧
    uSwapCore3967 * Q⁻¹ = Q⁻¹ * uSwapCore3967 := by
  intro Q
  have hFwd : uSwapCore3967 * Q = Q * uSwapCore3967 := by
    dsimp only [Q]
    rw [fullSysQftCoreUnitary_coreQftHadamardPrunedBundle128]
    refine unitary_list_prod_comm uSwapCore3967 _ fun u hu ↦ ?_
    rcases List.mem_ofFn.mp hu with ⟨i, rfl⟩
    exact uSwapCore3967_comm_rElec18InCore i uCoreHadamard18
  have hInv : uSwapCore3967 * Q⁻¹ = Q⁻¹ * uSwapCore3967 := by
    calc uSwapCore3967 * Q⁻¹
        = (Q⁻¹ * Q) * uSwapCore3967 * Q⁻¹ := by rw [inv_mul_cancel, one_mul]
      _ = Q⁻¹ * (Q * uSwapCore3967) * Q⁻¹ := by simp only [_root_.mul_assoc]
      _ = Q⁻¹ * uSwapCore3967 * (Q * Q⁻¹) := by rw [← hFwd]; simp only [_root_.mul_assoc]
      _ = Q⁻¹ * uSwapCore3967 := by rw [mul_inv_cancel, mul_one]
  exact ⟨hFwd, hInv⟩
theorem embedUnitary_list_prod {k N : ℕ} (r : QRegister k N) :
    ∀ (L : List (Unitary (2 ^ k))), r.embedUnitary L.prod = (L.map r.embedUnitary).prod
  | [] => by simp [r.embedUnitary_one]
  | u :: us => by simp [List.prod_cons, r.embedUnitary_mul, embedUnitary_list_prod r us]
/-- `fullSysQftCoreUnitary pos24_6_le_80 coreQftHadamardPrunedBundle128` equals
  `selPosCoreInCore80.embedUnitary fullQft218`. -/
theorem qftCore218_eq_selPosCoreInCore80_fullQft218 : fullSysQftCoreUnitary pos24_6_le_80
    coreQftHadamardPrunedBundle128 = selPosCoreInCore80.embedUnitary fullQft218 := by
  rw [fullSysQftCoreUnitary_coreQftHadamardPrunedBundle128]
  unfold fullQft218 uQft0 uQft217 elecProd217
  rw [List.ofFn_succ, List.prod_cons, selPosCoreInCore80.embedUnitary_mul,
      ← QRegister.embedUnitary_compose, embedUnitary_list_prod, List.map_ofFn]
  have h0 : selPosCoreInCore80.compose rElec0InCore = rElec18InCore pos24_6_le_80 0 := by
    apply qreg_ext; intro j; apply Fin.ext
    have hL : (selPosCoreInCore80 (rElec0InCore j)).val = (rElec0InCore j).val := by
      simp [selPosCoreInCore80]
    rw [QRegister.compose_apply, hL,
        ZeroHypStageABToUFoldedPass123SegAndCompac.rElec18InCore_apply_val]
    simp [rElec0InCore]
  have hSpec : (selPosCoreInCore80.embedUnitary ∘ fun e : Fin 217 ↦ (rSpectatorSlot
      e).embedUnitary uCoreHadamard18) = (fun e : Fin 217 ↦ (rElec18InCore pos24_6_le_80
      e.succ).embedUnitary uCoreHadamard18) := by
    funext e
    dsimp only [Function.comp_apply]
    rw [← QRegister.embedUnitary_compose]
    refine congrArg (fun r : QRegister 18 (fullSysCoreWires 80) ↦ r.embedUnitary uCoreHadamard18) ?_
    apply qreg_ext; intro j; apply Fin.ext
    have hL : (selPosCoreInCore80 (rSpectatorSlot e j)).val = (rSpectatorSlot e j).val := by
      simp [selPosCoreInCore80]
    rw [QRegister.compose_apply, hL]
    unfold rSpectatorSlot
    rw [PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ j,
        ZeroHypStageABToUFoldedPass123SegAndCompac.rElec18InCore_apply_val]
  rw [h0, hSpec]
/-- **Exact Zero-Hypothesis Reduction of `unitaryConj Q_{218} uHeadPhase80Mod4Eff` (`0`
  Hypotheses)**:
Factors `uSwapCore3967` outside `Q_{218}` and expresses the conjugated `uHeadPhaseMod4` in all 5
repaired / `D_pre` / `D_post` forms (`M0_rep`, `D_pre` inside `Q0`, `D_post` inside `Q0`,
`D_pre` outside `Q0`, `D_post` outside `Q0`). -/
theorem unitaryConj_qftCore218_uHeadPhase80Mod4Eff_eq_zeroHyp :
    let Q := fullSysQftCoreUnitary pos24_6_le_80 coreQftHadamardPrunedBundle128
    let H80 := castUnitaryPow2 pos24_coreWires80_eq.symm uHeadPhaseMod4
    let M0_rep :=
      (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0Repaired * uSpectatorHadamard3906
    let M0_orig := (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906
    let Phi := uControlledPointDiag217
    unitaryConj Q uHeadPhase80Mod4Eff =
      uSwapCore3967 * unitaryConj Q H80 * uSwapCore3967 ∧
    unitaryConj Q H80 =
      selPosCoreInCore80.embedUnitary (fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218) ∧
    unitaryConj Q uHeadPhase80Mod4Eff =
      uSwapCore3967 *
        selPosCoreInCore80.embedUnitary (uQft0⁻¹ * (Phi⁻¹ * M0_rep * Phi) * uQft0) *
        uSwapCore3967 ∧
    unitaryConj Q uHeadPhase80Mod4Eff =
      uSwapCore3967 *
        selPosCoreInCore80.embedUnitary
          (((uQft0⁻¹ * Phi⁻¹ * uQft0) * M0_orig * (uQft0⁻¹ * Phi * uQft0)) *
            (uQft0⁻¹ * uHeadOrigin0Slot0MissPre * uQft0)) *
        uSwapCore3967 ∧
    unitaryConj Q uHeadPhase80Mod4Eff =
      uSwapCore3967 *
        selPosCoreInCore80.embedUnitary
          ((uQft0⁻¹ * uHeadOrigin0Slot0MissPost * uQft0) *
            ((uQft0⁻¹ * Phi⁻¹ * uQft0) * M0_orig * (uQft0⁻¹ * Phi * uQft0))) *
        uSwapCore3967 := by
  intro Q H80 M0_rep M0_orig Phi
  obtain ⟨hSwQ, hSwQInv⟩ := uSwapCore3967_comm_qftCore218
  have hSwapOut : unitaryConj Q uHeadPhase80Mod4Eff =
      uSwapCore3967 * unitaryConj Q H80 * uSwapCore3967 := by
    dsimp only [Q, H80] at hSwQ hSwQInv ⊢
    unfold unitaryConj uHeadPhase80Mod4Eff
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, hSwQInv.symm]
    simp only [_root_.mul_assoc]
    rw [hSwQ]
  have hEmbed : unitaryConj Q H80 =
      selPosCoreInCore80.embedUnitary (fullQft218⁻¹ * uHeadPhaseMod4 * fullQft218) := by
    dsimp only [Q, H80]
    unfold unitaryConj
    rw[qftCore218_eq_selPosCoreInCore80_fullQft218,
        ← selPosCoreInCore80_embedUnitary_eq_castUnitaryPow2, ← embedUnitary_inv_eq,
        ← selPosCoreInCore80.embedUnitary_mul, ← selPosCoreInCore80.embedUnitary_mul,
        _root_.mul_assoc]
  obtain ⟨hf1, _, _, hf4, hf5⟩ := fullQft218_conj_uHeadPhaseMod4_eq_repairedOrigin0_zeroHyp
  refine ⟨hSwapOut, hEmbed, ?_, ?_, ?_⟩
  · rw [hSwapOut, hEmbed, hf1]
  · rw [hSwapOut, hEmbed, hf4]
  · rw [hSwapOut, hEmbed, hf5]
end Part2_USwapCore3967AndHeadPhase80Mod4Eff
theorem embedMatrix_diagonal_eq {k N : ℕ} (r : QRegister k N) (f : Fin (2 ^ k) → ℂ) :
    r.embedMatrix (Matrix.diagonal f) = Matrix.diagonal (fun x ↦ f (r.extractIndex x)) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [QRegister.embedMatrix_apply]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    by_cases hEnv : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
    · have hExtNe : r.extractIndex x ≠ r.extractIndex y := by
        intro hEq
        exact hxy (r.basisSplitEquiv.injective (Prod.ext hEq hEnv))
      simp [QRegister.embedMatrix_apply, hEnv, Matrix.diagonal_apply_ne _ hExtNe]
    · simp [QRegister.embedMatrix_apply, hEnv]
end TrailXorAndRepairedStageAExactEq
namespace StageBCachedSwapAndRawCancelBridge
open ZeroHypCatState48StageABMidCoreReductionAn (catState48)
open QRegExt
open CatalystPrep (U_cat_B_normalized)
open FullSysCatSegmentBridge (fullSysBEWires)
open PosMomSelectSandwich (slotBitProj)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply kActOrig kFull80 rAct0 rCoreOrig rSegOrig
  rPG48Orig rSegFull rPG48Full rSum0 hAct0_disj_Sum0 E_rawStream42 E_stream42 pSum42Zero
  E_rawStream42_eq_streamProjOp E_stream42_eq_streamProjOp embedAct0_comm_streamOp PreservesFeature
  IsHigh3924Reg FixesLow3924 h3924_core h3924_actOrig isLow3924Prefix_rCoreOrig
  fixesLow3924_embedMatrix_prefix fixesLow3924_embedMatrix_high)
open HoistInitStream1300And164 (uStreamFullOf)
open Barrel3PassSelectStitch (rCat80 rCoreSeg)
open Leaf4Stream162 (uHybridStream146 isSlot2StreamUnitary_146)
open Leaf4Ext48TopStitch (CommutesWithReg rPG48Full_val_eq rPGIdle rPGIdleOrig rUnusedCtrl3Orig
  rUnusedCtrl3Full)
open SelectHoistLemmas (rCtrl3InSeg pCoinSlack010Core pCoinSlack010Seg rSegFull_compose_rCtrl3InSeg
  rSegFull_eq_rAct0_compose_rSegOrig)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
/-! `E_rawStream42` is a partial isometry with initial projector `pSum42Zero`. -/
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
theorem E_rawStream42_conjTranspose_mul_self :
    E_rawStream42ᴴ * E_rawStream42 = pSum42Zero := by
  have hStr :=
    HeldStreamEStream42Interface.uStreamFullOf_012_mul_pSum42Zero_eq_E_rawStream42
      isSlot2StreamUnitary_146
  set U_str : Unitary (2 ^ kFull80) :=
    uStreamFullOf uHybridStream146 0 *
      (uStreamFullOf uHybridStream146 1 * uStreamFullOf uHybridStream146 2)
  have hU : U_str.1ᴴ * U_str.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp U_str.2
  have hP_sa : pSum42Zeroᴴ = pSum42Zero := QRegister.basisOutcomeProjector_conjTranspose rSum0 0
  have hP_idem : pSum42Zero * pSum42Zero = pSum42Zero :=
    QRegister.basisOutcomeProjector_mul_self rSum0 0
  calc E_rawStream42ᴴ * E_rawStream42
    _ = (U_str.1 * pSum42Zero)ᴴ * (U_str.1 * pSum42Zero) := by rw [← hStr]
    _ = pSum42Zeroᴴ * (U_str.1ᴴ * U_str.1) * pSum42Zero := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = pSum42Zero := by rw [hP_sa, hU, Matrix.mul_one, hP_idem]
/-- General left-cancellation of `rP.basisOutcomeProjector v₀` against any disjoint
  `r.embedMatrix`. -/
theorem eq_of_basisOutcomeProjector_mul_embed_disjoint {k m n : ℕ} (rP : QRegister m n)
    (r : QRegister k n) (hDisj : r.DisjointWires rP) (v₀ : Fin (2 ^ m))
    (A B : Operator (2 ^ k)) (h : rP.basisOutcomeProjector v₀ * r.embedMatrix A =
    rP.basisOutcomeProjector v₀ * r.embedMatrix B) : A = B := by
  ext x y
  have hi0 : rP.extractIndex (r.replaceIndex (rP.replaceIndex ⟨0, Nat.two_pow_pos n⟩ v₀) x) = v₀ :=
    by
    rw [QRegister.extractIndex_replaceIndex_of_disjoint rP r (QRegExt.disjointWires_symm hDisj),
        QRegister.extractIndex_replaceIndex]
  have henv : (r.basisSplitEquiv (r.replaceIndex (rP.replaceIndex ⟨0, Nat.two_pow_pos n⟩ v₀) x)).2 =
      (r.basisSplitEquiv (r.replaceIndex (rP.replaceIndex ⟨0, Nat.two_pow_pos n⟩ v₀) y)).2 := by
    rw [r.basisSplitEquiv_replaceIndex, r.basisSplitEquiv_replaceIndex]
  have hx : r.extractIndex (r.replaceIndex (rP.replaceIndex ⟨0, Nat.two_pow_pos n⟩ v₀) x) = x :=
    r.extractIndex_replaceIndex _ x
  have hy : r.extractIndex (r.replaceIndex (rP.replaceIndex ⟨0, Nat.two_pow_pos n⟩ v₀) y) = y :=
    r.extractIndex_replaceIndex _ y
  generalize r.replaceIndex (rP.replaceIndex ⟨0, Nat.two_pow_pos n⟩ v₀) x = i at hi0 henv hx
  generalize r.replaceIndex (rP.replaceIndex ⟨0, Nat.two_pow_pos n⟩ v₀) y = j at henv hy
  have hij := congrFun (congrFun h i) j
  rw[QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul, Matrix.diagonal_mul,
      ite_eq_left hi0, one_mul, one_mul, QRegister.embedMatrix_apply, QRegister.embedMatrix_apply,
      ite_eq_left henv, hx, hy, mul_one, mul_one] at hij
  exact hij
/-- Universal left-cancellation of `pSum42Zero` against any subregister disjoint from `rSum0`. -/
theorem eq_of_pSum42Zero_mul_embedDisjSum0_eq {k : ℕ} (r : QRegister k kFull80)
    (hDisj : r.DisjointWires rSum0) (A B : Operator (2 ^ k))
    (h : pSum42Zero * r.embedMatrix A = pSum42Zero * r.embedMatrix B) : A = B :=
    eq_of_basisOutcomeProjector_mul_embed_disjoint rSum0 r hDisj 0 A B h
/-- Universal left-cancellation of `E_rawStream42` against any subregister disjoint from `rSum0`. -/
theorem eq_of_E_rawStream42_mul_embedDisjSum0_eq {k : ℕ} (r : QRegister k kFull80)
    (hDisj : r.DisjointWires rSum0) (A B : Operator (2 ^ k)) (h : E_rawStream42 *
    r.embedMatrix A = E_rawStream42 * r.embedMatrix B) : A = B := by
  refine eq_of_pSum42Zero_mul_embedDisjSum0_eq r hDisj A B ?_
  have hMul : E_rawStream42ᴴ * (E_rawStream42 * r.embedMatrix A) = E_rawStream42ᴴ *
      (E_rawStream42 * r.embedMatrix B) := congrArg (fun M ↦ E_rawStream42ᴴ * M) h
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, E_rawStream42_conjTranspose_mul_self] at hMul
theorem rSegFull_disj_rSum0 : rSegFull.DisjointWires rSum0 := by
  rw [rSegFull_eq_rAct0_compose_rSegOrig]
  exact hAct0_disj_Sum0.compose_left rSegOrig
/-- Left-cancellation of `E_rawStream42` against `rSegFull.embedMatrix`. -/
theorem eq_of_E_rawStream42_mul_embedSegFull_eq
    (A B : Operator (2 ^ (fullSysBEWires 80 + 48))) (h : E_rawStream42 * rSegFull.embedMatrix
    A = E_rawStream42 * rSegFull.embedMatrix B) : A = B :=
    eq_of_E_rawStream42_mul_embedDisjSum0_eq rSegFull rSegFull_disj_rSum0 A B h
/-- Left-cancellation of `E_rawStream42` against `rAct0.embedMatrix`. -/
theorem eq_of_E_rawStream42_mul_embedAct0_eq (A B : Operator (2 ^ kActOrig)) (h :
    E_rawStream42 * rAct0.embedMatrix A = E_rawStream42 * rAct0.embedMatrix B) : A = B :=
    eq_of_E_rawStream42_mul_embedDisjSum0_eq rAct0 hAct0_disj_Sum0 A B h
theorem embedAct0_high_comm_E_rawStream42 {k : ℕ} {rSub : QRegister k kActOrig}
    (hr : IsHigh3924Reg rSub) (M : Operator (2 ^ k)) : (rAct0.compose rSub).embedMatrix M *
    E_rawStream42 = E_rawStream42 * (rAct0.compose rSub).embedMatrix M := by
  rw [QRegister.embedMatrix_compose rAct0 rSub, E_rawStream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp (fixesLow3924_embedMatrix_high h3924_actOrig hr
    M).preservesRawStream42
theorem embedAct0_high_comm_E_stream42 {k : ℕ} {rSub : QRegister k kActOrig}
    (hr : IsHigh3924Reg rSub) (M : Operator (2 ^ k)) : (rAct0.compose rSub).embedMatrix M *
    E_stream42 = E_stream42 * (rAct0.compose rSub).embedMatrix M := by
  rw [QRegister.embedMatrix_compose rAct0 rSub, E_stream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp (fixesLow3924_embedMatrix_high h3924_actOrig hr
    M).preservesHoistStream42
theorem isHigh3924Reg_rPG48Orig : IsHigh3924Reg rPG48Orig := by
  intro j
  have hFull := rPG48Full_val_eq j
  have hEq : (rPG48Full j).val = (rPG48Orig j).val := by
    change (rAct0 (rPG48Orig j)).val = (rPG48Orig j).val
    simp [rAct0]
  omega
theorem rSegOrig_compose_rCat80_eq_rPG48Orig : rSegOrig.compose rCat80 = rPG48Orig := by
  apply qreg_ext; intro j
  change rSegOrig (rCat80 j) = rSegOrig (InterWalkRSum42Hoist.rPG48Loc j)
  congr 1; apply Fin.ext
  simp [rCat80, InterWalkRSum42Hoist.rPG48Loc, SingleCatSpine.rTopCatSlice]
theorem basisOutcomeProjector_eq_embedMatrix_diag {m n : ℕ} (r : QRegister m n)
    (v : Fin (2 ^ m)) : r.basisOutcomeProjector v = r.embedMatrix (Matrix.diagonal (fun y :
    Fin (2 ^ m) ↦ if y = v then (1 : ℂ) else 0)) := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal,
      ZeroHypHMidBAndPureCnotSwapClosure.embedMatrix_diagonal_eq]
/-- `rSegFull.embedMatrix catState48` commutes with `E_rawStream42` and `E_stream42`. -/
theorem embedSegFull_catState48_comm_E_rawStream42_and_E_stream42 : rSegFull.embedMatrix
    catState48 * E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix catState48 ∧
    rSegFull.embedMatrix catState48 * E_stream42 = E_stream42 * rSegFull.embedMatrix
    catState48 := by
  let p0Loc : Operator (2 ^ 48) :=
    Matrix.diagonal (fun y : Fin (2 ^ 48) ↦ if y = 0 then (1 : ℂ) else 0)
  let catLoc : Operator (2 ^ 48) := (U_cat_B_normalized 48).1 * p0Loc
  have hCatEq : catState48 = rCat80.embedMatrix catLoc := by
    unfold catState48
    rw [QRegister.embedUnitary_val, basisOutcomeProjector_eq_embedMatrix_diag rCat80 0,
        ← QRegister.embedMatrix_mul]
  have hComp : rSegFull.embedMatrix catState48 =
      (rAct0.compose rPG48Orig).embedMatrix catLoc := by
    rw [hCatEq, ← QRegister.embedMatrix_compose rSegFull rCat80,
        rSegFull_eq_rAct0_compose_rSegOrig, QRegister.compose_assoc,
        rSegOrig_compose_rCat80_eq_rPG48Orig]
  rw [hComp]
  exact ⟨embedAct0_high_comm_E_rawStream42 isHigh3924Reg_rPG48Orig catLoc,
    embedAct0_high_comm_E_stream42 isHigh3924Reg_rPG48Orig catLoc⟩
/-- `rSegFull.embedMatrix pCoinSlack010Seg` commutes with `E_rawStream42` and `E_stream42`. -/
theorem embedSegFull_pCoinSlack010Seg_comm_E_rawStream42_and_E_stream42 : rSegFull.embedMatrix
    pCoinSlack010Seg * E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix pCoinSlack010Seg ∧
    rSegFull.embedMatrix pCoinSlack010Seg * E_stream42 = E_stream42 * rSegFull.embedMatrix
    pCoinSlack010Seg := by
  have hFixCore : FixesLow3924 h3924_core pCoinSlack010Core := by
    unfold pCoinSlack010Core slotBitProj
    exact ((PreservesFeature.diagonal _ _).mul (PreservesFeature.diagonal _ _)).mul
      (PreservesFeature.diagonal _ _)
  have hFixOrig : FixesLow3924 h3924_actOrig (rCoreOrig.embedMatrix pCoinSlack010Core) :=
    fixesLow3924_embedMatrix_prefix isLow3924Prefix_rCoreOrig hFixCore
  have hEmbedEq : rSegFull.embedMatrix pCoinSlack010Seg =
      rAct0.embedMatrix (rCoreOrig.embedMatrix pCoinSlack010Core) := by
    dsimp only [pCoinSlack010Seg]
    rw [← QRegister.embedMatrix_compose rSegFull rCoreSeg, rSegFull_compose_rCoreSeg_eq]
    exact QRegister.embedMatrix_compose rAct0 rCoreOrig pCoinSlack010Core
  rw [hEmbedEq]
  refine ⟨?_, ?_⟩
  · rw [E_rawStream42_eq_streamProjOp]
    exact embedAct0_comm_streamOp hFixOrig.preservesRawStream42
  · rw [E_stream42_eq_streamProjOp]
    exact embedAct0_comm_streamOp hFixOrig.preservesHoistStream42
/-- **1-Hop `catState48` Transfer (`seg_mul_catState48_eq_of_intertwineRaw`)**:
Transfers `U_Full * rSegFull.embedMatrix catState48 = U_NoCat * rSegFull.embedMatrix catState48`
and `U_NoCat * E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix TargetSeg` across
`U_Full * E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix U_Seg` directly to
`U_Seg * catState48 = TargetSeg * catState48`. -/
theorem seg_mul_catState48_eq_of_intertwineRaw (U_Full U_NoCat : Operator (2 ^ kFull80))
    (U_Seg TargetSeg : Operator (2 ^ (fullSysBEWires 80 + 48))) (hRaw : U_Full *
    E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix U_Seg) (hNoCatRaw : U_NoCat *
    E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix TargetSeg) (hCatFull : U_Full *
    rSegFull.embedMatrix catState48 = U_NoCat * rSegFull.embedMatrix catState48) : U_Seg *
    catState48 = TargetSeg * catState48 := by
  refine eq_of_E_rawStream42_mul_embedSegFull_eq _ _ ?_
  have hComm := embedSegFull_catState48_comm_E_rawStream42_and_E_stream42.1
  calc E_rawStream42 * rSegFull.embedMatrix (U_Seg * catState48)
    _ = (E_rawStream42 * rSegFull.embedMatrix U_Seg) * rSegFull.embedMatrix catState48 := by
        rw [QRegister.embedMatrix_mul, Matrix.mul_assoc]
    _ = U_Full * (E_rawStream42 * rSegFull.embedMatrix catState48) := by
        rw [← hRaw, Matrix.mul_assoc]
    _ = (U_Full * rSegFull.embedMatrix catState48) * E_rawStream42 := by
        rw [← hComm, Matrix.mul_assoc]
    _ = U_NoCat * (rSegFull.embedMatrix catState48 * E_rawStream42) := by
        rw [hCatFull, Matrix.mul_assoc]
    _ = (U_NoCat * E_rawStream42) * rSegFull.embedMatrix catState48 := by
        rw [hComm, Matrix.mul_assoc]
    _ = E_rawStream42 * rSegFull.embedMatrix (TargetSeg * catState48) := by
        rw [hNoCatRaw, Matrix.mul_assoc, ← QRegister.embedMatrix_mul]
/-- **1-Hop `pCoinSlack010Seg` Transfer (`seg_mul_pCoinSlack010Seg_eq_of_intertwineRaw`)**:
Transfers `U_Full * rSegFull.embedMatrix pCoinSlack010Seg = rSegFull.embedMatrix pCoinSlack010Seg`
across `U_Full * E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix U_Seg` to
`U_Seg * pCoinSlack010Seg = pCoinSlack010Seg`. -/
theorem seg_mul_pCoinSlack010Seg_eq_of_intertwineRaw (U_Full : Operator (2 ^ kFull80))
    (U_Seg : Operator (2 ^ (fullSysBEWires 80 + 48))) (hRaw : U_Full * E_rawStream42 =
    E_rawStream42 * rSegFull.embedMatrix U_Seg) (hSlackFull : U_Full * rSegFull.embedMatrix
    pCoinSlack010Seg = rSegFull.embedMatrix pCoinSlack010Seg) : U_Seg * pCoinSlack010Seg =
    pCoinSlack010Seg := by
  refine eq_of_E_rawStream42_mul_embedSegFull_eq _ _ ?_
  have hComm := embedSegFull_pCoinSlack010Seg_comm_E_rawStream42_and_E_stream42.1
  calc E_rawStream42 * rSegFull.embedMatrix (U_Seg * pCoinSlack010Seg)
    _ = (E_rawStream42 * rSegFull.embedMatrix U_Seg) * rSegFull.embedMatrix pCoinSlack010Seg := by
        rw [QRegister.embedMatrix_mul, Matrix.mul_assoc]
    _ = U_Full * (E_rawStream42 * rSegFull.embedMatrix pCoinSlack010Seg) := by
        rw [← hRaw, Matrix.mul_assoc]
    _ = (U_Full * rSegFull.embedMatrix pCoinSlack010Seg) * E_rawStream42 := by
        rw [← hComm, Matrix.mul_assoc]
    _ = E_rawStream42 * rSegFull.embedMatrix pCoinSlack010Seg := by
        rw [hSlackFull, hComm]
/-- **1-Hop `rCtrl3InSeg` Commutation Transfer (`commutesWithReg_rCtrl3InSeg_of_intertwineRaw`)**:
Transfers `CommutesWithReg rUnusedCtrl3Full U_Full` across `E_rawStream42` to
`CommutesWithReg rCtrl3InSeg U_Seg`. -/
theorem commutesWithReg_rCtrl3InSeg_of_intertwineRaw (U_Full : Operator (2 ^ kFull80))
    (U_Seg : Operator (2 ^ (fullSysBEWires 80 + 48))) (hRaw : U_Full * E_rawStream42 =
    E_rawStream42 * rSegFull.embedMatrix U_Seg)
    (hCtrlFull : CommutesWithReg rUnusedCtrl3Full U_Full) : CommutesWithReg rCtrl3InSeg U_Seg
    := by
  have hHighCtrl : IsHigh3924Reg rUnusedCtrl3Orig := fun i ↦ by
    simp [rUnusedCtrl3Orig]; omega
  intro B
  refine eq_of_E_rawStream42_mul_embedSegFull_eq _ _ ?_
  have hEmb : rSegFull.embedMatrix (rCtrl3InSeg.embedMatrix B) = rUnusedCtrl3Full.embedMatrix B :=
    by
    rw [← QRegister.embedMatrix_compose rSegFull rCtrl3InSeg, rSegFull_compose_rCtrl3InSeg]
  have hCommE : rUnusedCtrl3Full.embedMatrix B * E_rawStream42 = E_rawStream42 *
      rUnusedCtrl3Full.embedMatrix B := embedAct0_high_comm_E_rawStream42 hHighCtrl B
  calc E_rawStream42 * rSegFull.embedMatrix (U_Seg * rCtrl3InSeg.embedMatrix B)
    _ = (E_rawStream42 * rSegFull.embedMatrix U_Seg) * rUnusedCtrl3Full.embedMatrix B := by
        rw [QRegister.embedMatrix_mul, hEmb, Matrix.mul_assoc]
    _ = U_Full * (E_rawStream42 * rUnusedCtrl3Full.embedMatrix B) := by
        rw [← hRaw, Matrix.mul_assoc]
    _ = (U_Full * rUnusedCtrl3Full.embedMatrix B) * E_rawStream42 := by
        rw [← hCommE, Matrix.mul_assoc]
    _ = rUnusedCtrl3Full.embedMatrix B * (U_Full * E_rawStream42) := by
        rw [hCtrlFull B, Matrix.mul_assoc]
    _ = (rUnusedCtrl3Full.embedMatrix B * E_rawStream42) * rSegFull.embedMatrix U_Seg := by
        rw [hRaw, Matrix.mul_assoc]
    _ = E_rawStream42 * rSegFull.embedMatrix (rCtrl3InSeg.embedMatrix B * U_Seg) := by
        rw [hCommE, Matrix.mul_assoc, ← hEmb, ← QRegister.embedMatrix_mul]
/-- **1-Hop `rPGIdleOrig` Commutation Transfer (`commutesWithReg_rPGIdleOrig_of_intertwineRaw`)**:
Transfers `CommutesWithReg (rPGIdle k_idle hk) U_Full` across `E_rawStream42` to
`CommutesWithReg (rPGIdleOrig k_idle hk) (rSegOrig.embedMatrix U_Seg)`. -/
theorem commutesWithReg_rPGIdleOrig_of_intertwineRaw {k_idle : ℕ} (hk : k_idle ≤ 48)
    (U_Full : Operator (2 ^ kFull80)) (U_Seg : Operator (2 ^ (fullSysBEWires 80 + 48))) (hRaw
    : U_Full * E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix U_Seg)
    (hIdleFull : CommutesWithReg (rPGIdle k_idle hk) U_Full) : CommutesWithReg
    (rPGIdleOrig k_idle hk) (rSegOrig.embedMatrix U_Seg) := by
  have hHighIdle : IsHigh3924Reg (rPGIdleOrig k_idle hk) := fun i ↦ isHigh3924Reg_rPG48Orig _
  have hSegAct : rSegFull.embedMatrix U_Seg = rAct0.embedMatrix (rSegOrig.embedMatrix U_Seg) := by
    rw [rSegFull_eq_rAct0_compose_rSegOrig, QRegister.embedMatrix_compose]
  intro B
  refine eq_of_E_rawStream42_mul_embedAct0_eq _ _ ?_
  have hEmb : rAct0.embedMatrix ((rPGIdleOrig k_idle hk).embedMatrix B) =
      (rPGIdle k_idle hk).embedMatrix B :=
    (QRegister.embedMatrix_compose rAct0 (rPGIdleOrig k_idle hk) B).symm
  have hCommE : (rPGIdle k_idle hk).embedMatrix B * E_rawStream42 = E_rawStream42 *
      (rPGIdle k_idle hk).embedMatrix B := embedAct0_high_comm_E_rawStream42 hHighIdle B
  calc E_rawStream42 * rAct0.embedMatrix (rSegOrig.embedMatrix U_Seg *
    (rPGIdleOrig k_idle hk).embedMatrix B)
    _ = (E_rawStream42 * rSegFull.embedMatrix U_Seg) * (rPGIdle k_idle hk).embedMatrix B := by
        rw [QRegister.embedMatrix_mul, hEmb, ← hSegAct, Matrix.mul_assoc]
    _ = U_Full * (E_rawStream42 * (rPGIdle k_idle hk).embedMatrix B) := by
        rw [← hRaw, Matrix.mul_assoc]
    _ = (U_Full * (rPGIdle k_idle hk).embedMatrix B) * E_rawStream42 := by
        rw [← hCommE, Matrix.mul_assoc]
    _ = (rPGIdle k_idle hk).embedMatrix B * (U_Full * E_rawStream42) := by
        rw [hIdleFull B, Matrix.mul_assoc]
    _ = ((rPGIdle k_idle hk).embedMatrix B * E_rawStream42) * rSegFull.embedMatrix U_Seg := by
        rw [hRaw, Matrix.mul_assoc]
    _ = E_rawStream42 * rAct0.embedMatrix ((rPGIdleOrig k_idle hk).embedMatrix B *
      rSegOrig.embedMatrix U_Seg) := by
        rw [hCommE, hSegAct, Matrix.mul_assoc, ← hEmb, ← QRegister.embedMatrix_mul]
/-- Specialization of `commutesWithReg_rPGIdleOrig_of_intertwineRaw` at `k_idle = 12` for
  unitaries. -/
theorem commutesWithReg_rPGIdleOrig12_of_intertwineRaw (U_Full : Operator (2 ^ kFull80))
    (U_Seg : Unitary (2 ^ (fullSysBEWires 80 + 48))) (hRaw : U_Full * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary U_Seg).1)
    (hIdleFull : CommutesWithReg (rPGIdle 12 (by decide)) U_Full) : CommutesWithReg
    (rPGIdleOrig 12 (by decide)) (rSegOrig.embedUnitary U_Seg).1 := by
  rw [QRegister.embedUnitary_val] at hRaw ⊢
  exact commutesWithReg_rPGIdleOrig_of_intertwineRaw (by decide) U_Full U_Seg.1 hRaw hIdleFull
-- ----------------------------------------------------------------------------
-- Section 2B: Zero-Hypothesis `pCoinSlack010Core` Fixation
-- ----------------------------------------------------------------------------
end StageBCachedSwapAndRawCancelBridge
end SharedScope
end SlimStageADepsE2

noncomputable section SlimStageBOuterDepsA

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK10 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
  InterWalkRSum42Hoist.mActHoist
set_option exponentiation.threshold 8192
namespace Width136KIdle12ZeroPenaltyBridge
open HermitianMat
open scoped ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_concat_left)
open SingleCatSpine (rTopCatSlice)
open InterWalkRSum42Hoist (qreg_ext rCTFull rCoreFull rPG48Full hCoreFull_disj_PG48Full)
open Leaf1Pass1And3Width204 (compose_selCT4InCT_eq selCT4InCT)
open Leaf4Ext48TopStitch (rExt42IdleFull rCoreTopCatFull rCoreTopCatFull_disj_rExt42IdleFull)
open SelectStitch hiding rCoreTopCatInCT
open SelectPass13Gen (rT4Full)
section Part1Select136_12
set_option maxRecDepth 131072
/-- Disjointness of `rCoreFull`, `rTopCat7Full`, `rQFull`, and `rCT4Full` from `rExt42IdleFull
  12`. -/
theorem rCoreFull_disj_rExt42Idle12 :
    rCoreFull.DisjointWires (rExt42IdleFull 12 (by decide)) := by
  have hSub := (rCoreTopCatFull_disj_rExt42IdleFull 12 0 (by decide)).compose_left
    (QRegister.block 0 (fullSysCoreWires 80) (Nat.le_refl _))
  have hEq : (rCoreTopCatFull 0 (by decide)).compose
      (QRegister.block 0 (fullSysCoreWires 80) (Nat.le_refl _)) = rCoreFull := by
    apply qreg_ext; intro i
    have hi : (QRegister.block 0 (fullSysCoreWires 80) (Nat.le_refl _) :
        QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 0)) i = Fin.castAdd 0 i := by
      ext; simp [QRegister.block]
    change (rCoreTopCatFull 0 (by decide)) _ = rCoreFull i
    rw [hi, rCoreTopCatFull, QRegister.concat_apply_left]
  rwa [hEq] at hSub
theorem rTopCat7Full_disj_rExt42Idle12 :
    (rPG48Full.compose (rTopCatSlice 7 48 (by decide))).DisjointWires
      (rExt42IdleFull 12 (by decide)) := by
  have hSub := (rCoreTopCatFull_disj_rExt42IdleFull 12 7 (by decide)).compose_left
    (QRegister.block (fullSysCoreWires 80) 7 (Nat.le_refl _))
  have hEq : (rCoreTopCatFull 7 (by decide)).compose
      (QRegister.block (fullSysCoreWires 80) 7 (Nat.le_refl _)) =
      rPG48Full.compose (rTopCatSlice 7 48 (by decide)) := by
    apply qreg_ext; intro j
    have hj : (QRegister.block (fullSysCoreWires 80) 7 (Nat.le_refl _) :
        QRegister 7 (fullSysCoreWires 80 + 7)) j = Fin.natAdd (fullSysCoreWires 80) j := by
      ext; simp [QRegister.block]
    change (rCoreTopCatFull 7 (by decide)) _ = (rPG48Full.compose (rTopCatSlice 7 48 (by decide))) j
    rw [hj, rCoreTopCatFull, QRegister.concat_apply_right]
  rwa [hEq] at hSub
theorem rT4Full_disj_rExt42Idle12 :
    rT4Full.DisjointWires (rExt42IdleFull 12 (by decide)) := by
  have h47 : rT4Full = (rPG48Full.compose (rTopCatSlice 7 48 (by decide))).compose
      (QRegister.block 0 4 (by decide)) := by
    apply qreg_ext; intro j
    change rPG48Full _ = rPG48Full _
    exact congrArg rPG48Full (by fin_cases j <;> rfl)
  rw [h47]; exact rTopCat7Full_disj_rExt42Idle12.compose_left _
theorem rCT4Full_disj_rExt42Idle12 :
    (rCTFull.compose (selCT4InCT 80)).DisjointWires (rExt42IdleFull 12 (by decide)) := by
  have hEq : rCTFull.compose (selCT4InCT 80) =
      rCoreFull.concat rT4Full (hCoreFull_disj_PG48Full.compose_right _) :=
    compose_selCT4InCT_eq rCoreFull rPG48Full hCoreFull_disj_PG48Full
  rw [hEq]
  exact disjointWires_concat_left _ rCoreFull_disj_rExt42Idle12 rT4Full_disj_rExt42Idle12
end Part1Select136_12
end Width136KIdle12ZeroPenaltyBridge
namespace Pass1InnerAndIdx128Aux
open Pass1InnerAndIdx128
section Slot0LocalWState128
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open SpecsAux SpecsAux.SpecMirror
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open MomSlot0LocalAndMomCombine288
open MomSlots01Slot1ProjKinetic hiding padZeroBits phaseDiagUnitary ket matrix_ext_ket
open MeasureBranchHadamardSem (matrix_ext_ket)
open AnchorSwap0Split133 (p2d_ketPredProj p2d_ketPredProj_conjTranspose p2d_ketPredProj_mul_ket
  p2d_ketPredProj_mul_imp p2d_basisOutcomeProjector_zero_eq_ketPredProj
  p2d_RealizesConstCleanUnitary_mono_proj p2d_RealizesConstCleanUnitary_congr_unitary
  p2d_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace p2dEmptyReg p2dEmptyReg_disj)
open ParticleOneHotWState (DisjWUncond DiagCtxW toDynW toDynW_count_toff toDynW_count_t
  realizes_toDynW_pred_diagComplex)
open scoped ComplexOrder MatrixOrder Circuit.Notation
/-- Workspace wire count for `dSlot0LocalWState128` (`128` wires):
`32 (CSA) + 5 (tail decode) + 6 (muxA) + 6 (muxB) + 4 (mag5) + 32 (wStateTree 4) + 43 (wTh + 42
stream lt, reusing wTh for qEnc and muxBit) = 128`. -/
abbrev slot0LocalWorkWires128 : ℕ := 128
/-- `T`-gate count of `dSlot0LocalWState128`: `53 * 4 + 60 + 42 * 4 + 4 = 444 T` (`-44 T` below
  `488 T`). -/
abbrev slot0LocalTCost444 : ℕ := 444
/-- Sequential composition of two `DiagCtxW M` contexts. -/
def DiagCtxW_append {M : ℕ} : DiagCtxW M → DiagCtxW M → DiagCtxW M
  | .hole, K₂ => K₂
  | .cliffConj c K₁, K₂ => .cliffConj c (DiagCtxW_append K₁ K₂)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, K₂ =>
      .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (DiagCtxW_append K₁ K₂)
  | .wStateTree k wIdx wOut qEnc hd K₁, K₂ =>
      .wStateTree k wIdx wOut qEnc hd (DiagCtxW_append K₁ K₂)
theorem DiagCtxW_append_countT {M : ℕ} :
    ∀ (K₁ K₂ : DiagCtxW M),
      (DiagCtxW_append K₁ K₂).countT = K₁.countT + K₂.countT
  | .hole, _ => by simp [DiagCtxW_append, DiagCtxW.countT]
  | .cliffConj _ K₁, K₂ => by
      simp [DiagCtxW_append, DiagCtxW.countT, DiagCtxW_append_countT K₁ K₂]
  | .tempAnd _ _ _ _ _ _ K₁, K₂ => by
      simp only [DiagCtxW_append, DiagCtxW.countT, DiagCtxW_append_countT K₁ K₂]
      omega
  | .wStateTree _ _ _ _ _ K₁, K₂ => by
      simp only [DiagCtxW_append, DiagCtxW.countT, DiagCtxW_append_countT K₁ K₂]
      omega
theorem DiagCtxW_append_fwdBits {M : ℕ} :
    ∀ (K₁ K₂ : DiagCtxW M) (γ : BitAssignment M),
      (DiagCtxW_append K₁ K₂).fwdBits γ = K₂.fwdBits (K₁.fwdBits γ)
  | .hole, _, _ => rfl
  | .cliffConj c K₁, K₂, γ => DiagCtxW_append_fwdBits K₁ K₂ (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K₁, K₂, γ =>
      DiagCtxW_append_fwdBits K₁ K₂ (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ _ _ _ _ K₁, K₂, _γ =>
      DiagCtxW_append_fwdBits K₁ K₂ _
theorem DiagCtxW_append_validAt {M : ℕ} :
    ∀ (K₁ K₂ : DiagCtxW M) {γ : BitAssignment M},
      K₁.ValidAt γ → K₂.ValidAt (K₁.fwdBits γ) → (DiagCtxW_append K₁ K₂).ValidAt γ
  | .hole, _, _, _, hV₂ => hV₂
  | .cliffConj _ K₁, K₂, _, hV₁, hV₂ =>
      DiagCtxW_append_validAt K₁ K₂ hV₁ hV₂
  | .tempAnd _ _ _ _ _ _ K₁, K₂, _, ⟨h0, hV₁⟩, hV₂ =>
      ⟨h0, DiagCtxW_append_validAt K₁ K₂ hV₁ hV₂⟩
  | .wStateTree _ _ _ _ _ K₁, K₂, _, ⟨h0, hV₁⟩, hV₂ =>
      ⟨h0, DiagCtxW_append_validAt K₁ K₂ hV₁ hV₂⟩
/-- Every `f : TempPhaseProg M → TempPhaseProg M` satisfying `IsPurePhaseCtx f` lifts to a
`DiagCtxW M` preserving `countT`, `fwdBits`, and `ValidAt`. -/
theorem exists_diagCtxW_of_isPurePhaseCtx {M : ℕ} {f : TempPhaseProg M → TempPhaseProg M}
    (hf : IsPurePhaseCtx f) : ∃ K : DiagCtxW M, K.countT = 4 * (f .nil).countTempAnd ∧ (∀ q :
    Wire M, ∀ γ : BitAssignment M, K.fwdBits γ q = (f (.z q)).evalSign γ) ∧ (∀ (q : Wire M)
    (rem : ℕ) (γ : BitAssignment M), ValidCleanRem M rem (f (.z q)) → cleanRem M rem γ →
    K.ValidAt γ) := by
  induction hf with
  | id =>
      exact ⟨.hole, rfl, fun _ _ ↦ rfl, fun _ _ _ _ _ ↦ trivial⟩
  | @cliff c f₁ _ ih =>
      obtain ⟨K₁, hCount₁, hFwd₁, hVal₁⟩ := ih
      refine ⟨.cliffConj c K₁, ?_, fun q γ ↦ ?_, fun q rem γ hv hcl ↦ ?_⟩
      · simp [DiagCtxW.countT, withCliffAlloc, TempPhaseProg.countTempAnd, hCount₁]
      · dsimp only [DiagCtxW.fwdBits, withCliffAlloc, TempPhaseProg.evalSign,
          TempPhaseProg.evalBits]
        rw [zero_add, add_zero]
        exact hFwd₁ q (c.eval γ)
      · obtain ⟨remMid, _, _, ⟨_, _, hv₁, _, _⟩, hpres⟩ := hv
        exact hVal₁ q remMid (c.eval γ) hv₁ (hpres γ hcl)
  | @tempBit c₁ c₂ anc h₁₂ h₁a h₂a f₁ _ ih =>
      obtain ⟨K₁, hCount₁, hFwd₁, hVal₁⟩ := ih
      refine ⟨.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, ?_, fun q γ ↦ ?_, fun q rem γ hv hcl ↦ ?_⟩
      · simp only [DiagCtxW.countT, withTempBit, TempPhaseProg.countTempAnd, hCount₁]
        ring
      · dsimp only [DiagCtxW.fwdBits, withTempBit, TempPhaseProg.evalSign]
        exact hFwd₁ q (Function.update γ anc (γ anc + γ c₁ * γ c₂))
      · obtain ⟨hanc, hv₁, _⟩ := hv
        have hanc0 : γ anc = 0 := hcl anc hanc
        let γ₁ := Function.update γ anc (γ anc + γ c₁ * γ c₂)
        have hcl₁ : cleanRem M (M - (anc.val + 1)) γ₁ := fun w hw ↦ by
          have hw_gt : anc.val < w.val := by have := anc.isLt; omega
          dsimp only [γ₁]
          rw [Function.update_of_ne (wire_ne_of_gt hw_gt)]
          exact hcl w (by omega)
        exact ⟨hanc0, hVal₁ q (M - (anc.val + 1)) γ₁ hv₁ hcl₁⟩
/-- Single one-hot bit CNOT step into `outJ` when `b = true`. -/
def ohSingleBitCliff {M : ℕ} (ohCur : ℕ) (_hoh : ohCur + 32 ≤ M) (outJ : Wire M)
    (hout : ohCur + 32 ≤ outJ.val) (b : Bool) (m : Fin 32) : CliffProg M :=
  if b then
    .cnot ⟨ohCur + m.val, by omega⟩ outJ
      (wire_ne_of_lt (by dsimp; omega))
  else .nil
theorem ohSingleBitCliff_supportsBelow {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val) {bound : ℕ} (hb : outJ.val < bound)
    (b : Bool) (m : Fin 32) :
    (ohSingleBitCliff ohCur hoh outJ hout b m).SupportsBelow bound := by
  dsimp only [ohSingleBitCliff]
  split_ifs
  · exact ⟨by dsimp; omega, hb⟩
  · trivial
theorem ohSingleBitCliff_eval {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (b : Bool) (m : Fin 32) (γ : BitAssignment M) :
    (ohSingleBitCliff ohCur hoh outJ hout b m).eval γ =
      Function.update γ outJ (γ outJ + if b then γ ⟨ohCur + m.val, by omega⟩ else 0) := by
  dsimp only [ohSingleBitCliff]
  cases b
  · simp [CliffProg.eval]
  · simp [CliffProg.eval]
/-- Streams column `j` of `tbl : Fin 32 → ℕ` from the `32` one-hot wires `ohCur .. ohCur + 31`
into `outJ`. -/
def ohColLoop {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (tbl : Fin 32 → ℕ) (j : ℕ) : (n : ℕ) → n ≤ 32 → CliffProg M
  | 0, _ => .nil
  | n + 1, hn =>
      .seq (ohColLoop ohCur hoh outJ hout tbl j n (Nat.le_of_succ_le hn))
        (ohSingleBitCliff ohCur hoh outJ hout ((tbl ⟨n, hn⟩).testBit j) ⟨n, hn⟩)
theorem ohColLoop_supportsBelow {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val) {bound : ℕ} (hb : outJ.val < bound)
    (tbl : Fin 32 → ℕ) (j : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ 32),
      (ohColLoop ohCur hoh outJ hout tbl j n hn).SupportsBelow bound
  | 0, _ => trivial
  | n + 1, hn =>
      ⟨ohColLoop_supportsBelow ohCur hoh outJ hout hb tbl j n (Nat.le_of_succ_le hn),
       ohSingleBitCliff_supportsBelow ohCur hoh outJ hout hb _ _⟩
theorem ohColLoop_eval_prefix {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (tbl : Fin 32 → ℕ) (j : ℕ) (u : Fin 32) (γ : BitAssignment M)
    (hoh_val : ∀ m : Fin 32, γ ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0) :
    ∀ (n : ℕ) (hn : n ≤ 32),
      (ohColLoop ohCur hoh outJ hout tbl j n hn).eval γ =
        Function.update γ outJ
          (γ outJ + if u.val < n ∧ (tbl u).testBit j then 1 else 0)
  | 0, _ => by
      simp [ohColLoop, CliffProg.eval]
  | n + 1, hn => by
      dsimp only [ohColLoop, CliffProg.eval]
      rw [ohColLoop_eval_prefix ohCur hoh outJ hout tbl j u γ hoh_val n (Nat.le_of_succ_le hn),
          ohSingleBitCliff_eval]
      have hne_out : (⟨ohCur + n, by omega⟩ : Wire M) ≠ outJ :=
        wire_ne_of_lt (by dsimp; omega)
      rw [Function.update_self, Function.update_of_ne hne_out, Function.update_idem,
          hoh_val ⟨n, hn⟩]
      congr 1
      rw [add_assoc]
      congr 1
      by_cases hun : n = u.val
      · have hmeq : (⟨n, hn⟩ : Fin 32) = u := Fin.ext hun
        rw [hmeq]
        simp [hun]
      · have hiff : u.val < n + 1 ↔ u.val < n := by omega
        simp [hun, hiff]
theorem ohColLoop_eval_32 {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (tbl : Fin 32 → ℕ) (j : ℕ) (u : Fin 32) (γ : BitAssignment M)
    (hoh_val : ∀ m : Fin 32, γ ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0) :
    (ohColLoop ohCur hoh outJ hout tbl j 32 le_rfl).eval γ =
      Function.update γ outJ (γ outJ + if (tbl u).testBit j then 1 else 0) := by
  rw [ohColLoop_eval_prefix ohCur hoh outJ hout tbl j u γ hoh_val 32 le_rfl]
  simp [u.isLt]
theorem streamOh_lt32_M {ohCur cur W M : ℕ} (hoh : ohCur + 33 ≤ cur)
    (hcur : cur + (W + 1) + 1 ≤ M) : ohCur + 32 < M := by omega
theorem streamOh_le32_M {ohCur cur W M : ℕ} (hoh : ohCur + 33 ≤ cur)
    (hcur : cur + (W + 1) + 1 ≤ M) : ohCur + 32 ≤ M := by omega
theorem streamOh_cur_lt_M {cur W M : ℕ} (hcur : cur + (W + 1) + 1 ≤ M) : cur < M := by omega
theorem streamOh_cur2_le_M {cur W M : ℕ} (hcur : cur + (W + 1) + 1 ≤ M) :
    (cur + 1) + 1 ≤ M := by omega
theorem streamOh_a0_lt_cur1 {x ohCur cur : ℕ} (hoh : ohCur + 33 ≤ cur)
    (hx : x < ohCur) : x < cur + 1 := by omega
theorem streamOh_32_lt_cur1 {ohCur cur : ℕ} (hoh : ohCur + 33 ≤ cur) :
    ohCur + 32 < cur + 1 := by omega
theorem streamOh_32_lt_cur {ohCur cur : ℕ} (hoh : ohCur + 33 ≤ cur) :
    ohCur + 32 < cur := by omega
theorem streamOh_hcur_step {cur W M : ℕ} (hcur : cur + (W + 1) + 1 ≤ M) :
    (cur + 1) + W + 1 ≤ M := by omega
/-- Streams `W` threshold columns from the `32` one-hot wires `ohCur .. ohCur + 31` onto the shared
threshold wire `ohCur + 32` while stepping the ripple less-than comparator across `[cur .. cur + W +
1)`. -/
def withStreamOhLtCompLoop {M : ℕ} (ohCur : ℕ) (tbl : Fin 32 → ℕ) :
    (W j0 cur : ℕ) → (hoh : ohCur + 33 ≤ cur) → (hcur : cur + W + 1 ≤ M) →
    (a : Fin W → Wire M) → (ha : ∀ j, (a j).val < ohCur) →
    (body : TempPhaseProg M) → TempPhaseProg M
  | 0, _, _, _, _, _, _, body => body
  | W + 1, j0, cur, hoh, hcur, a, ha, body =>
      let wTh : Wire M := ⟨ohCur + 32, streamOh_lt32_M hoh hcur⟩
      let prev : Wire M := ⟨cur, streamOh_cur_lt_M hcur⟩
      let cCol := ohColLoop ohCur (streamOh_le32_M hoh hcur) wTh le_rfl tbl j0 32 le_rfl
      withCliffAlloc cCol
        (withLtStep (cur + 1) (streamOh_cur2_le_M hcur) (a 0) wTh prev
          (wire_ne_of_lt (Nat.lt_add_right 32 (ha 0)))
          (streamOh_a0_lt_cur1 hoh (ha 0))
          (streamOh_32_lt_cur1 hoh)
          (Nat.lt_succ_self cur)
          (wire_ne_of_lt (streamOh_32_lt_cur hoh))
          (withCliffAlloc cCol.inv
            (withStreamOhLtCompLoop ohCur tbl
              W (j0 + 1) (cur + 1) (Nat.le_succ_of_le hoh) (streamOh_hcur_step hcur)
              (fun j ↦ a j.succ) (fun j ↦ ha j.succ) body)))
@[simp] theorem withStreamOhLtCompLoop_countTempAnd {M : ℕ} (ohCur : ℕ) (tbl : Fin 32 → ℕ) :
    ∀ (W j0 cur : ℕ) (hoh : ohCur + 33 ≤ cur) (hcur : cur + W + 1 ≤ M)
      (a : Fin W → Wire M) (ha : ∀ j, (a j).val < ohCur)
      (body : TempPhaseProg M),
      (withStreamOhLtCompLoop ohCur tbl W j0 cur hoh hcur a ha body).countTempAnd =
        W + body.countTempAnd
  | 0, _, _, _, _, _, _, _ => by simp [withStreamOhLtCompLoop]
  | W + 1, j0, cur, hoh, hcur, a, ha, body => by
      simp only [withStreamOhLtCompLoop, withCliffAlloc_countTempAnd,
        withLtStep_countTempAnd, withStreamOhLtCompLoop_countTempAnd]
      omega
theorem isPurePhaseCtx_withStreamOhLtCompLoop {M : ℕ} (ohCur : ℕ) (tbl : Fin 32 → ℕ) :
    ∀ (W j0 cur : ℕ) (hoh : ohCur + 33 ≤ cur) (hcur : cur + W + 1 ≤ M)
      (a : Fin W → Wire M) (ha : ∀ j, (a j).val < ohCur)
      {f : TempPhaseProg M → TempPhaseProg M},
      IsPurePhaseCtx f →
      IsPurePhaseCtx (fun body ↦ withStreamOhLtCompLoop ohCur tbl W j0 cur hoh hcur a ha (f body))
  | 0, _, _, _, _, _, _, _, hf => hf
  | W + 1, j0, cur, _, _, _, _, _, hf => by
      dsimp only [withStreamOhLtCompLoop, withLtStep]
      exact .cliff (.cliff (.tempBit (.cliff (.cliff
        (isPurePhaseCtx_withStreamOhLtCompLoop ohCur tbl W (j0 + 1) (cur + 1) _ _ _ _ hf)))))
theorem
    _root_.QuantumComputation.Specs.StoppingPowerSolution.ScopedBlock.withStreamOhLtCompLoop_block
    {M : ℕ}
    (ohCur : ℕ) (tbl : Fin 32 → ℕ) (u : Fin 32) :
    ∀ (W j0 cur : ℕ) (hoh : ohCur + 33 ≤ cur) (hcur : cur + W + 1 ≤ M)
      (a : Fin W → Wire M) (ha : ∀ j, (a j).val < ohCur)
      (leaf body : TempPhaseProg M) (sBody : BitAssignment M → BitAssignment M),
      ScopedBlock M (M - (cur + W + 1)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - (cur + 1)) (fun β ↦ sBody (setup β)) leaf
          (withStreamOhLtCompLoop ohCur tbl W j0 cur hoh hcur a ha body) ∧
        ∀ β : BitAssignment M, cleanRem M (M - (cur + 1)) β →
          β ⟨ohCur + 32, by omega⟩ = 0 →
          (∀ m : Fin 32, β ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0) →
          cleanRem M (M - (cur + W + 1)) (setup β) ∧
          (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
          ((setup β ⟨cur + W, by omega⟩ = 1) ↔
            (bitsVal (fun j ↦ β (a j)) <
              bitsVal (fun j : Fin W ↦ if (tbl u).testBit (j0 + j.val) then (1 : ZMod 2) else 0) ∨
              (bitsVal (fun j ↦ β (a j)) =
                bitsVal (fun j : Fin W ↦ if (tbl u).testBit (j0 + j.val) then (1 : ZMod 2) else 0) ∧
                β ⟨cur, by omega⟩ = 1)))
  | 0, _, cur, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody, fun _ hβ _ _ ↦ ⟨hβ, fun _ _ ↦ rfl, by simp [bitsVal]⟩⟩
  | W + 1, j0, cur, hoh, hcur, a, ha, leaf, body, sBody, hBody => by
      have hoh32 : ohCur + 32 ≤ M := by omega
      let wTh : Wire M := ⟨ohCur + 32, by omega⟩
      let prev : Wire M := ⟨cur, by omega⟩
      let cCol := ohColLoop ohCur hoh32 wTh (by dsimp [wTh]; omega) tbl j0 32 le_rfl
      have hcCol_supp33 : cCol.SupportsBelow (ohCur + 33) :=
        ohColLoop_supportsBelow ohCur hoh32 wTh
          (by dsimp [wTh]; omega) (by dsimp [wTh]; omega) tbl j0 32 le_rfl
      have hcCol_supp : cCol.SupportsBelow (M - (M - (cur + 1))) :=
        cliff_supportsBelow_mono (by omega) hcCol_supp33
      have hcInv_supp : cCol.inv.SupportsBelow (M - (M - (cur + 2))) :=
        cliff_supportsBelow_mono (by omega) (CliffProg.inv_supportsBelow cCol hcCol_supp33)
      obtain ⟨setupInner, hInner, hSpecInner⟩ :=
        ScopedBlock.withStreamOhLtCompLoop_block ohCur tbl u
          W (j0 + 1) (cur + 1) (by omega) (by omega)
          (fun j ↦ a j.succ) (fun j ↦ ha j.succ)
          leaf body sBody (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBody)
      have hInv := ScopedBlock.withCliffAlloc_block (M := M)
        (rem := M - (cur + 2)) (remIn := M - (cur + 2)) (by omega) le_rfl cCol.inv hcInv_supp hInner
      have hStep := ScopedBlock.withLtStep_block (M := M) (cur + 1) (by omega) (a 0) wTh prev
        (wire_ne_of_lt (lt_trans (ha 0) (by dsimp [wTh]; omega)))
        (wire_ne_of_lt (lt_trans (ha 0) (by dsimp [prev]; omega)))
        (lt_trans (ha 0) (by omega)) (by dsimp [wTh]; omega) (by dsimp [prev]; omega)
        (wire_ne_of_lt (by dsimp [wTh, prev]; omega)) hInv
      have hCol := ScopedBlock.withCliffAlloc_block (M := M)
        (rem := M - (cur + 1)) (remIn := M - (cur + 1)) (by omega) le_rfl cCol hcCol_supp hStep
      let step1 : BitAssignment M → BitAssignment M :=
        fun β ↦ cCol.inv.eval (ltStepSetup (cur + 1) (by omega) (a 0) wTh prev (cCol.eval β))
      refine ⟨fun β ↦ setupInner (step1 β), hCol, fun β hβ hwTh0 hbasis ↦ ?_⟩
      let b0 : ZMod 2 := if (tbl u).testBit j0 then 1 else 0
      have hcCol_eval : cCol.eval β = Function.update β wTh b0 := by
        dsimp only [cCol]
        rw [ohColLoop_eval_32 ohCur hoh32 wTh (by dsimp [wTh]; omega) tbl j0 u β hbasis,
            hwTh0, zero_add]
      have hstep1_eq : step1 β =
          Function.update β ⟨cur + 1, by omega⟩
            (β prev + (β (a 0) + b0) * (b0 + β prev)) := by
        dsimp only [step1, ltStepSetup]
        rw [cliff_eval_update_outside cCol.inv (CliffProg.inv_supportsBelow cCol hcCol_supp33)
          (cCol.eval β) ⟨cur + 1, by omega⟩ (by dsimp; omega), CliffProg.inv_eval]
        congr 1; rw [hcCol_eval]
        have ha0_ne : a 0 ≠ wTh := wire_ne_of_lt (lt_trans (ha 0) (by dsimp [wTh]; omega))
        have hp_ne : prev ≠ wTh := wire_ne_of_gt (by dsimp [prev, wTh]; omega)
        rw [Function.update_self, Function.update_of_ne ha0_ne, Function.update_of_ne hp_ne]
      let β₁ := step1 β
      have hβ₁_clean : cleanRem M (M - (cur + 2)) β₁ := fun w hw ↦ by
        rw [show β₁ = _ from hstep1_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
        exact hβ w (by omega)
      have hβ₁_wTh : β₁ wTh = 0 := by
        rw [show β₁ = _ from hstep1_eq, Function.update_of_ne (wire_ne_of_lt (by
          dsimp [wTh]; omega))]
        exact hwTh0
      have hβ₁_basis : ∀ m : Fin 32,
          β₁ ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0 := fun m ↦ by
        rw [show β₁ = _ from hstep1_eq,
            Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))]
        exact hbasis m
      obtain ⟨hcl, hbelow, hlt_ih⟩ := hSpecInner β₁ hβ₁_clean hβ₁_wTh hβ₁_basis
      have hcur_eq : (⟨cur + 1 + W, by omega⟩ : Wire M) = ⟨cur + (W + 1), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have ha_eq : ∀ j : Fin W, β₁ (a j.succ) = β (a j.succ) := fun j ↦ by
        rw [show β₁ = _ from hstep1_eq]
        exact Function.update_of_ne (wire_ne_of_lt (by have := ha j.succ; dsimp; omega)) _ _
      have hbit1 : β₁ ⟨cur + 1, by omega⟩ = 1 ↔
          ((β (a 0)).val < b0.val ∨ ((β (a 0)).val = b0.val ∧ β prev = 1)) := by
        rw [show β₁ = _ from hstep1_eq, Function.update_self]
        exact ltStep_bit_iff (β (a 0)) b0 (β prev)
      have splitVal (f : Fin (W + 1) → ZMod 2) :
          bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦ f j.succ) := by
        rw [bitsVal, Fin.sum_univ_succ]
        simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Fin.val_succ, pow_succ]; ring
      have ha_bv : bitsVal (fun j : Fin W ↦ β₁ (a j.succ)) = bitsVal (fun j : Fin W ↦
        β (a j.succ)) :=
        congrArg bitsVal (funext ha_eq)
      let bVirt : Fin (W + 1) → ZMod 2 := fun j ↦ if (tbl u).testBit (j0 + j.val) then 1 else 0
      have hb_bv : bitsVal (fun j : Fin W ↦ if (tbl u).testBit (j0 + 1 + j.val) then (1 : ZMod
          2) else 0) = bitsVal (fun j : Fin W ↦ bVirt j.succ) := by
        refine congrArg bitsVal (funext fun j ↦ ?_)
        have htb : (tbl u).testBit (j0 + 1 + j.val) = (tbl u).testBit (j0 + (j.succ).val) :=
          congrArg (tbl u).testBit (by rw [Fin.val_succ]; omega)
        dsimp only [bVirt]; rw [htb]
      have hb0_val : (bVirt 0).val = b0.val := by
        have htb0 : (tbl u).testBit (j0 + (0 : Fin (W + 1)).val) = (tbl u).testBit j0 :=
          congrArg (tbl u).testBit (by rw [Fin.val_zero, Nat.add_zero])
        dsimp only [bVirt, b0]; rw [htb0]
      have hlt_ih' :
          setupInner β₁ ⟨cur + (W + 1), by omega⟩ = 1 ↔
            (bitsVal (fun j : Fin W ↦ β (a j.succ)) < bitsVal (fun j : Fin W ↦ bVirt j.succ) ∨
              (bitsVal (fun j : Fin W ↦ β (a j.succ)) = bitsVal (fun j : Fin W ↦ bVirt j.succ) ∧
                β₁ ⟨cur + 1, by omega⟩ = 1)) := by
        rw [← hcur_eq, hlt_ih, ha_bv, hb_bv]
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcl,
        fun w hw ↦ ?_, ?_⟩
      · dsimp only
        rw [hbelow w (by omega), show β₁ = _ from hstep1_eq]
        exact Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)) _ _
      · dsimp only
        have hp_eq : prev = ⟨cur, by omega⟩ := rfl
        rw [hp_eq] at hbit1
        have ha0 := ZMod.val_lt (β (a 0)); have hb0_lt := ZMod.val_lt b0
        change (setupInner β₁ ⟨cur + (W + 1), by omega⟩ = 1) ↔
          (bitsVal (fun j ↦ β (a j)) < bitsVal bVirt ∨
            (bitsVal (fun j ↦ β (a j)) = bitsVal bVirt ∧ β ⟨cur, by omega⟩ = 1))
        by_cases hp1 : β ⟨cur, by omega⟩ = 1
        · simp only [hp1, and_true] at hbit1 ⊢
          rw [hlt_ih', hbit1, splitVal (fun j ↦ β (a j)), splitVal bVirt, hb0_val]; omega
        · simp only [hp1, and_false, or_false] at hbit1 ⊢
          rw [hlt_ih', hbit1, splitVal (fun j ↦ β (a j)), splitVal bVirt, hb0_val]; omega
/-- `42`-step one-hot streaming less-than comparator (`42` `TempAnd`s = `168 T`, using `wTh = ⟨ohCur
  + 32⟩`
and `42` carry wires `ohCur + 33 .. ohCur + 74`). -/
def withOhStreamLtComp42 {M : ℕ} (ohCur : ℕ) (hcur : ohCur + 75 ≤ M)
    (tbl : Fin 32 → ℕ) (a : Fin 42 → Wire M) (ha : ∀ j, (a j).val < ohCur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  have hoh32 : ohCur + 32 ≤ M := by omega
  let wTh : Wire M := ⟨ohCur + 32, by omega⟩
  let cCol0 := ohColLoop ohCur hoh32 wTh (by dsimp [wTh]; omega) tbl 0 32 le_rfl
  withCliffAlloc cCol0
    (withLtStep0 (ohCur + 33) (by omega) (a 0) wTh
      (wire_ne_of_lt (lt_trans (ha 0) (by dsimp [wTh]; omega)))
      (lt_trans (ha 0) (by omega))
      (by dsimp [wTh]; omega)
      (withCliffAlloc cCol0.inv
        (withStreamOhLtCompLoop ohCur tbl 41 1 (ohCur + 33) le_rfl (by omega)
          (fun j ↦ a j.succ) (fun j ↦ ha j.succ) body)))
@[simp] theorem withOhStreamLtComp42_countTempAnd {M : ℕ} (ohCur : ℕ) (hcur : ohCur + 75 ≤ M)
    (tbl : Fin 32 → ℕ) (a : Fin 42 → Wire M) (ha : ∀ j, (a j).val < ohCur)
    (body : TempPhaseProg M) :
    (withOhStreamLtComp42 ohCur hcur tbl a ha body).countTempAnd = 42 + body.countTempAnd := by
  simp only [withOhStreamLtComp42, withCliffAlloc_countTempAnd,
    withLtStep0_countTempAnd, withStreamOhLtCompLoop_countTempAnd]
  omega
theorem isPurePhaseCtx_withOhStreamLtComp42 {M : ℕ} (ohCur : ℕ) (hcur : ohCur + 75 ≤ M)
    (tbl : Fin 32 → ℕ) (a : Fin 42 → Wire M) (ha : ∀ j, (a j).val < ohCur)
    {f : TempPhaseProg M → TempPhaseProg M} (hf : IsPurePhaseCtx f) :
    IsPurePhaseCtx (fun body ↦ withOhStreamLtComp42 ohCur hcur tbl a ha (f body)) := by
  dsimp only [withOhStreamLtComp42, withLtStep0]
  exact .cliff (.cliff (.tempBit (.cliff (.cliff
    (isPurePhaseCtx_withStreamOhLtCompLoop _ _ _ _ _ _ _ _ _ hf)))))
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.ScopedBlock.withOhStreamLtComp42_block
    {M : ℕ} (ohCur : ℕ) (hcur : ohCur + 75 ≤ M)
    (tbl : Fin 32 → ℕ) (a : Fin 42 → Wire M) (ha : ∀ j, (a j).val < ohCur)
    (u : Fin 32)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (ohCur + 75)) sBody leaf body) :
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - (ohCur + 33)) (fun β ↦ sBody (setup β)) leaf
        (withOhStreamLtComp42 ohCur hcur tbl a ha body) ∧
      ∀ β : BitAssignment M, cleanRem M (M - (ohCur + 33)) β →
        β ⟨ohCur + 32, by omega⟩ = 0 →
        (∀ m : Fin 32, β ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0) →
        cleanRem M (M - (ohCur + 75)) (setup β) ∧
        setup β ⟨ohCur + 32, by omega⟩ = 0 ∧
        (∀ w : Wire M, w.val < ohCur + 32 → setup β w = β w) ∧
        setup β ⟨ohCur + 74, by omega⟩ =
          if bitsVal (fun j : Fin 42 ↦ β (a j)) <
              bitsVal (fun j : Fin 42 ↦ if (tbl u).testBit j.val then (1 : ZMod 2) else 0)
          then 1 else 0 := by
  have hoh32 : ohCur + 32 ≤ M := by omega
  let wTh : Wire M := ⟨ohCur + 32, by omega⟩
  let cCol0 := ohColLoop ohCur hoh32 wTh (by dsimp [wTh]; omega) tbl 0 32 le_rfl
  have hcCol0_supp33 : cCol0.SupportsBelow (ohCur + 33) :=
    ohColLoop_supportsBelow ohCur hoh32 wTh (by
      dsimp [wTh]; omega) (by dsimp [wTh]; omega) tbl 0 32 le_rfl
  have hcCol0_supp : cCol0.SupportsBelow (M - (M - (ohCur + 33))) :=
    cliff_supportsBelow_mono (by omega) hcCol0_supp33
  have hcInv0_supp : cCol0.inv.SupportsBelow (M - (M - (ohCur + 34))) :=
    cliff_supportsBelow_mono (by omega) (CliffProg.inv_supportsBelow cCol0 hcCol0_supp33)
  let step0 : BitAssignment M → BitAssignment M :=
    fun γ ↦ cCol0.inv.eval (ltStep0Setup (ohCur + 33) (by omega) (a 0) wTh (cCol0.eval γ))
  obtain ⟨stStr, hBlkStr, hSpecStr⟩ :=
    ScopedBlock.withStreamOhLtCompLoop_block (M := M) ohCur tbl u
      41 1 (ohCur + 33) le_rfl (by omega)
      (fun j ↦ a j.succ) (fun j ↦ ha j.succ)
      leaf body sBody (hBody.cast_rem (by omega))
  have hInv0 := ScopedBlock.withCliffAlloc_block (M := M)
    (rem := M - (ohCur + 34)) (remIn := M - (ohCur + 34))
    (by omega) le_rfl cCol0.inv hcInv0_supp hBlkStr
  have hStep0 := ScopedBlock.withLtStep0_block (M := M) (ohCur + 33) (by omega)
    (a 0) wTh
    (wire_ne_of_lt (lt_trans (ha 0) (by dsimp [wTh]; omega)))
    (lt_trans (ha 0) (by omega))
    (by dsimp [wTh]; omega) hInv0
  have hFull := ScopedBlock.withCliffAlloc_block (M := M)
    (rem := M - (ohCur + 33)) (remIn := M - (ohCur + 33))
    (by omega) le_rfl cCol0 hcCol0_supp hStep0
  refine ⟨fun β ↦ stStr (step0 β), hFull, fun β hβ hwTh0 hbasis ↦ ?_⟩
  let b0 : ZMod 2 := if (tbl u).testBit 0 then 1 else 0
  have hcCol0_eval : cCol0.eval β = Function.update β wTh b0 := by
    dsimp only [cCol0]
    rw [ohColLoop_eval_32 ohCur hoh32 wTh (by dsimp [wTh]; omega) tbl 0 u β hbasis,
        hwTh0, zero_add]
  have hstep0_eq : step0 β =
      Function.update β ⟨ohCur + 33, by omega⟩ ((β (a 0) + 1) * b0) := by
    dsimp only [step0, ltStep0Setup]
    rw [cliff_eval_update_outside cCol0.inv (CliffProg.inv_supportsBelow cCol0 hcCol0_supp33)
      (cCol0.eval β) ⟨ohCur + 33, by omega⟩ (by dsimp; omega),
      CliffProg.inv_eval]
    congr 1
    rw [hcCol0_eval]
    have ha0_ne : a 0 ≠ wTh := wire_ne_of_lt (lt_trans (ha 0) (by dsimp [wTh]; omega))
    rw [Function.update_self, Function.update_of_ne ha0_ne]
  let β₁ := step0 β
  have hβ₁_clean : cleanRem M (M - (ohCur + 33 + 1)) β₁ := fun w hw ↦ by
    rw [show β₁ = _ from hstep0_eq,
      Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
    exact hβ w (by omega)
  have hβ₁_wTh : β₁ wTh = 0 := by
    rw [show β₁ = _ from hstep0_eq,
      Function.update_of_ne (wire_ne_of_lt (by dsimp [wTh]; omega))]
    exact hwTh0
  have hβ₁_basis : ∀ m : Fin 32,
      β₁ ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0 := fun m ↦ by
    rw [show β₁ = _ from hstep0_eq,
      Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))]
    exact hbasis m
  obtain ⟨hclStr, hbelStr, hiffStr⟩ := hSpecStr β₁ hβ₁_clean hβ₁_wTh hβ₁_basis
  have hcur74_eq : (⟨ohCur + 33 + 41, by omega⟩ : Wire M) = ⟨ohCur + 74, by omega⟩ :=
    Fin.ext (by dsimp)
  have ha_succ_eq : ∀ j : Fin 41, β₁ (a j.succ) = β (a j.succ) := fun j ↦ by
    rw [show β₁ = _ from hstep0_eq,
      Function.update_of_ne (wire_ne_of_lt (by have := ha j.succ; dsimp; omega))]
  have hbit0 : β₁ ⟨ohCur + 33, by omega⟩ = 1 ↔ (β (a 0)).val < b0.val := by
    rw [show β₁ = _ from hstep0_eq, Function.update_self]
    exact ltStep0_bit_iff (β (a 0)) b0
  have splitVal {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
      bitsVal f = (f 0).val + 2 * bitsVal (fun j : Fin W ↦ f j.succ) := by
    rw [bitsVal, Fin.sum_univ_succ]
    simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Fin.val_succ, pow_succ]; ring
  let bVirt : Fin 42 → ZMod 2 := fun j ↦ if (tbl u).testBit j.val then 1 else 0
  have hb_succ : bitsVal (fun j : Fin 41 ↦ if (tbl u).testBit (1 + j.val) then (1 : ZMod 2)
      else 0) = bitsVal (fun j : Fin 41 ↦ bVirt j.succ) := by
    refine congrArg bitsVal (funext fun j ↦ ?_)
    have htb : (tbl u).testBit (1 + j.val) = (tbl u).testBit (j.succ).val :=
      congrArg (tbl u).testBit (by rw [Fin.val_succ]; omega)
    dsimp only [bVirt]; rw [htb]
  have ha_bv : bitsVal (fun j : Fin 41 ↦ β₁ (a j.succ)) = bitsVal (fun j : Fin 41 ↦ β (a j.succ)) :=
    congrArg bitsVal (funext ha_succ_eq)
  have hb0_val : (bVirt 0).val = b0.val := rfl
  have hiff74 : stStr β₁ ⟨ohCur + 74, by omega⟩ = 1 ↔
      bitsVal (fun j : Fin 42 ↦ β (a j)) < bitsVal bVirt := by
    rw [← hcur74_eq, hiffStr, ha_bv, hb_succ, hbit0,
      splitVal (fun j ↦ β (a j)), splitVal bVirt, hb0_val]
    have ha0 := ZMod.val_lt (β (a 0))
    have hb0_lt := ZMod.val_lt b0
    omega
  refine ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hclStr,
    (hbelStr wTh (by dsimp [wTh]; omega)).trans hβ₁_wTh,
    fun w hw ↦ by
      dsimp only
      rw [hbelStr w (by omega), show β₁ = _ from hstep0_eq,
        Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))],
    ?_⟩
  let wOut : Wire M := ⟨ohCur + 74, by omega⟩
  rcases zmod2_cases (stStr β₁ wOut) with hz | ho
  · have hnot : ¬ bitsVal (fun j : Fin 42 ↦ β (a j)) < bitsVal bVirt := by
      intro hlt
      have h1 := hiff74.mpr hlt
      change stStr β₁ wOut = 1 at h1
      rw [hz] at h1
      exact absurd h1 (by decide)
    rw [ite_neg_eq hnot]
    exact hz
  · have hyes : bitsVal (fun j : Fin 42 ↦ β (a j)) < bitsVal bVirt := hiff74.mp ho
    rw [ite_pos_eq hyes]
    exact ho
/-- Prefix `TempPhaseProg` (`21` `TempAnd`s: `5` tail decode + `6` muxA + `6` muxB + `4` mag5)
before the `wStateTree 4` one-hot router. -/
noncomputable def slot0TailPreOhProg21 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires128))
    (hOut : Mod3ReducedOut (coreWiresSym mPayload) (coreWiresSym mPayload + 32) a1 b1 a2 b2)
    (body : TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128)) :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let payW (k : ℕ) (_hk : k < 80) : Wire M :=
    ⟨3954 + k, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let bParW : Wire M := payW 36 (by omega)
  let elecAx (a : ℕ) (_ha : a < 3) : Fin 6 → Wire M :=
    fun b ↦ ⟨6 * a + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let selBW : Wire M := ⟨C + 32 + 3, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let selAW : Wire M := ⟨C + 32 + 4, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ax01 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 37 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ax012 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  withSlot0TailDecodeInPlace (C + 32) (by dsimp [M, slot0LocalWorkWires128]; omega)
    a1 b1 a2 b2 bParW hOut
    (by dsimp [bParW, payW]; omega)
    (not_inMod3Pool_of_out (by dsimp [bParW, payW]; omega))
    (withMuxReg 6 (C + 37) (by dsimp [M, slot0LocalWorkWires128]; omega)
      selAW (elecAx 0 (by decide)) (elecAx 1 (by decide))
      (fun i ↦ wire_ne_of_lt (by dsimp [elecAx]; omega))
      (fun i ↦ wire_ne_of_gt (by dsimp [selAW, elecAx]; omega))
      (fun i ↦ wire_ne_of_gt (by dsimp [selAW, elecAx]; omega))
      (by dsimp [selAW]; omega)
      (fun i ↦ by dsimp [elecAx]; omega)
      (fun i ↦ by dsimp [elecAx]; omega)
      (withMuxReg 6 (C + 43) (by dsimp [M, slot0LocalWorkWires128]; omega)
        selBW ax01 (elecAx 2 (by decide))
        (fun i ↦ wire_ne_of_gt (by dsimp [ax01, elecAx]; omega))
        (fun i ↦ wire_ne_of_lt (by dsimp [selBW, ax01]; omega))
        (fun i ↦ wire_ne_of_gt (by dsimp [selBW, elecAx]; omega))
        (by dsimp [selBW]; omega)
        (fun i ↦ by dsimp [ax01]; omega)
        (fun i ↦ by dsimp [elecAx]; omega)
        (withMag5InPlace (C + 49) (by dsimp [M, slot0LocalWorkWires128]; omega)
          ax012
          (fun i ↦ by dsimp [ax012]; omega)
          (wire_offset_inj (C + 43) (fun i ↦ by dsimp [M, slot0LocalWorkWires128]; omega))
          body)))
theorem isPurePhaseCtx_slot0TailPreOhProg21 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires128))
    (hOut : Mod3ReducedOut (coreWiresSym mPayload) (coreWiresSym mPayload + 32) a1 b1 a2 b2) :
    IsPurePhaseCtx (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut) := by
  unfold slot0TailPreOhProg21
  dsimp only
  exact isPurePhaseCtx_withSlot0TailDecodeInPlace _ _ _ _ _ _ _ _ _ _
    (isPurePhaseCtx_withMuxReg 6 _ _ _ _ _ _ _ _ _ _ _ (isPurePhaseCtx_withMuxReg 6 _ _ _ _ _
    _ _ _ _ _ _ (isPurePhaseCtx_withMag5InPlace _ _ _ _ _ .id)))
theorem slot0TailPreOhProg21_countTempAnd {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires128))
    (hOut : Mod3ReducedOut (coreWiresSym mPayload) (coreWiresSym mPayload + 32) a1 b1 a2 b2) :
    (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut .nil).countTempAnd = 21 := by
  unfold slot0TailPreOhProg21
  dsimp only
  rw [withSlot0TailDecodeInPlace_countTempAnd, withMuxReg_countTempAnd,
    withMuxReg_countTempAnd, withMag5InPlace_countTempAnd, TempPhaseProg.countTempAnd]
theorem slot0AxisInt_natAbs_lt_32 (u : Fin 64) :
    (MomSlots01Slot0ElectronKinetic.slot0AxisInt u).natAbs < 2 ^ 5 := by
  revert u; decide
theorem slot0TailPreOhProg21_block {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires128))
    (hOut : Mod3ReducedOut (coreWiresSym mPayload) (coreWiresSym mPayload + 32) a1 b1 a2 b2)
    (q : Wire (coreWiresSym mPayload + slot0LocalWorkWires128)) :
    let C := coreWiresSym mPayload
    let M := C + slot0LocalWorkWires128
    have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
    let allOnesW : Wire M := ⟨C + 34, by dsimp [M, slot0LocalWorkWires128]; omega⟩
    let ax012 : Fin 6 → Wire M :=
      fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
    let mag5 : Fin 5 → Wire M := mag5InPlaceWires ax012
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - (C + 32)) setup (.z q)
        (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q)) ∧
      ∀ β : BitAssignment M, cleanRem M (M - (C + 32)) β →
        (C + 53 ≤ q.val →
          (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q)).evalSign β = 0) ∧
        (q.val < C + 32 → ¬ InMod3Pool C q →
          (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q)).evalSign β = β q) ∧
        (q = allOnesW →
          (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q)).evalSign β =
            β a1 * β b1 * (β a2 * β b2)) ∧
        (∀ i : Fin 5, q = mag5 i →
          let bPar := (β ⟨3954 + 36, by dsimp [M, slot0LocalWorkWires128]; omega⟩).val
          let ax := ((β a1).val + (β b1).val + 2 * ((β a2).val + (β b2).val) + bPar) % 3
          let u6 : Fin 64 := ⟨bitsVal (fun b : Fin 6 ↦
            β ⟨6 * ax + b.val, lt_of_lt_of_le (six_mul_add_lt_core (Nat.mod_lt _ (by decide)) b)
              (Nat.le_add_right C slot0LocalWorkWires128)⟩), bitsVal_lt_two_pow _⟩
          (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q)).evalSign β =
            if ((MomSlots01Slot0ElectronKinetic.slot0AxisInt u6).natAbs).testBit i.val then 1 else
              0) := by
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let payW (k : ℕ) (_hk : k < 80) : Wire M :=
    ⟨3954 + k, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let bParW : Wire M := payW 36 (by omega)
  let elecAx (a : ℕ) (_ha : a < 3) : Fin 6 → Wire M :=
    fun b ↦ ⟨6 * a + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let allOnesW : Wire M := ⟨C + 34, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let selBW : Wire M := ⟨C + 32 + 3, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let selAW : Wire M := ⟨C + 32 + 4, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ax01 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 37 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ax012 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let mag5 : Fin 5 → Wire M := mag5InPlaceWires ax012
  have hZ : ScopedBlock M (M - (C + 49 + 4)) id (.z q) (.z q) :=
    ⟨by simp [ValidCleanRem], fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  obtain ⟨stMag, hMag, hMagSpec⟩ := ScopedBlock.withMag5InPlace_block (M := M) (C + 49)
    (by dsimp [M, slot0LocalWorkWires128]; omega) ax012
    (fun i ↦ by dsimp [ax012]; omega)
    (wire_offset_inj (C + 43) (fun i ↦ by dsimp [M, slot0LocalWorkWires128]; omega))
    hZ
  obtain ⟨stM2, hM2, hM2Spec⟩ := ScopedBlock.withMuxReg_block (M := M) 6 (C + 43)
    (by dsimp [M, slot0LocalWorkWires128]; omega) selBW ax01 (elecAx 2 (by decide))
    (fun i ↦ wire_ne_of_gt (by dsimp [ax01, elecAx]; omega))
    (fun i ↦ wire_ne_of_lt (by dsimp [selBW, ax01]; omega))
    (fun i ↦ wire_ne_of_gt (by dsimp [selBW, elecAx]; omega))
    (by dsimp [selBW]; omega) (fun i ↦ by dsimp [ax01]; omega) (fun i ↦ by dsimp [elecAx]; omega)
    _ _ _ (hMag.cast_rem (by omega))
  obtain ⟨stM1, hM1, hM1Spec⟩ := ScopedBlock.withMuxReg_block (M := M) 6 (C + 37)
    (by
      dsimp [M, slot0LocalWorkWires128]; omega) selAW (elecAx 0 (by decide)) (elecAx 1 (by decide))
    (fun i ↦ wire_ne_of_lt (by dsimp [elecAx]; omega))
    (fun i ↦ wire_ne_of_gt (by dsimp [selAW, elecAx]; omega))
    (fun i ↦ wire_ne_of_gt (by dsimp [selAW, elecAx]; omega))
    (by dsimp [selAW]; omega) (fun i ↦ by dsimp [elecAx]; omega) (fun i ↦ by dsimp [elecAx]; omega)
    _ _ _ (hM2.cast_rem (by omega))
  obtain ⟨stDec, hDec, hDecSpec⟩ := ScopedBlock.withSlot0TailDecodeInPlace_block (M := M) (C + 32)
    (by dsimp [M, slot0LocalWorkWires128]; omega) a1 b1 a2 b2 bParW hOut
    (by dsimp [bParW, payW]; omega) (not_inMod3Pool_of_out (by dsimp [bParW, payW]; omega))
    (hM1.cast_rem (by omega))
  refine ⟨_, hDec, fun β hβ ↦ ?_⟩
  obtain ⟨β₁, hβ₁⟩ := step_witness (stDec β)
  obtain ⟨hcl1, hbel1, hall1, hselB1, hselA1⟩ := hDecSpec β hβ
  rw [← hβ₁] at hcl1 hbel1 hall1 hselB1 hselA1
  obtain ⟨β₂, hβ₂⟩ := step_witness (stM1 β₁)
  obtain ⟨hcl2, hbel2, hv2⟩ := hM1Spec β₁ (by simpa [Nat.add_assoc] using hcl1)
  rw [← hβ₂] at hcl2 hbel2 hv2
  obtain ⟨β₃, hβ₃⟩ := step_witness (stM2 β₂)
  obtain ⟨hcl3, hbel3, hv3⟩ := hM2Spec β₂ (by simpa [Nat.add_assoc] using hcl2)
  rw [← hβ₃] at hcl3 hbel3 hv3
  obtain ⟨β₄, hβ₄⟩ := step_witness (stMag β₃)
  obtain ⟨hcl4, hbel4, hv4⟩ := hMagSpec β₃ (by simpa [Nat.add_assoc] using hcl3)
  rw [← hβ₄] at hcl4 hbel4 hv4
  have hSignEq : (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q)).evalSign β = β₄ q := by
    have hst : id (stMag (stM2 (stM1 (stDec β)))) = β₄ := by
      dsimp only [id]; rw [← hβ₁, ← hβ₂, ← hβ₃, ← hβ₄]
    unfold slot0TailPreOhProg21
    rw [hDec.sign β hβ, hst]
    rfl
  rw [hSignEq]
  have hbel4_43 : ∀ w : Wire M, w.val < C + 43 → β₄ w = β₃ w := fun w hw ↦
    hbel4 w (by omega) (fun i ↦ wire_ne_of_lt (by dsimp [ax012]; omega))
  have hkeep4 : ∀ w : Wire M, w.val < C + 32 → ¬ InMod3Pool C w → β₄ w = β w :=
    fun w hw hnp ↦ by
      rw [hbel4_43 w (by omega), hbel3 w (by omega), hbel2 w (by omega), hbel1 w hw hnp]
  have hall4 : β₄ allOnesW = β a1 * β b1 * (β a2 * β b2) := by
    rw [hbel4_43 allOnesW (by dsimp [allOnesW]; omega),
        hbel3 allOnesW (by dsimp [allOnesW]; omega),
        hbel2 allOnesW (by dsimp [allOnesW]; omega)]
    exact hall1
  let ax : ℕ := ((β a1).val + (β b1).val + 2 * ((β a2).val + (β b2).val) + (β bParW).val) % 3
  have hax_lt : ax < 3 := Nat.mod_lt _ (by decide)
  have hax012_bits : ∀ b : Fin 6, β₃ (ax012 b) =
      β ⟨6 * ax + b.val, lt_of_lt_of_le (six_mul_add_lt_core hax_lt b)
        (Nat.le_add_right C slot0LocalWorkWires128)⟩ := fun b ↦ by
    rw [hv3 b, hbel2 selBW (by dsimp [selBW]; omega), hselB1]
    have he2 : β₂ (elecAx 2 (by decide) b) = β (elecAx 2 (by decide) b) := by
      rw [hbel2 _ (by dsimp [elecAx]; omega),
        hbel1 _ (by dsimp [elecAx]; omega) (not_inMod3Pool_of_out (by dsimp [elecAx]; omega))]
    have he1 : β₁ (elecAx 1 (by decide) b) = β (elecAx 1 (by decide) b) :=
      hbel1 _ (by dsimp [elecAx]; omega) (not_inMod3Pool_of_out (by dsimp [elecAx]; omega))
    have he0 : β₁ (elecAx 0 (by decide) b) = β (elecAx 0 (by decide) b) :=
      hbel1 _ (by dsimp [elecAx]; omega) (not_inMod3Pool_of_out (by dsimp [elecAx]; omega))
    rcases nat_lt3_cases hax_lt with r0 | r1 | r2
    · have hne2 : ax ≠ 2 := fun h ↦ by cases r0.symm.trans h
      have hne1 : ax ≠ 1 := fun h ↦ by cases r0.symm.trans h
      rw [ite_neg_eq hne2, ite_neg_eq (by decide : (0 : ZMod 2) ≠ 1),
        hv2 b, hselA1 hne2, ite_neg_eq hne1, ite_neg_eq (by decide : (0 : ZMod 2) ≠ 1), he0]
      exact congrArg β (Fin.ext (six_mul_congr r0.symm b.val))
    · have hne2 : ax ≠ 2 := fun h ↦ by cases r1.symm.trans h
      rw [ite_neg_eq hne2, ite_neg_eq (by decide : (0 : ZMod 2) ≠ 1),
        hv2 b, hselA1 hne2, ite_pos_eq r1, ite_pos_eq rfl, he1]
      exact congrArg β (Fin.ext (six_mul_congr r1.symm b.val))
    · rw [ite_pos_eq r2, ite_pos_eq rfl, he2]
      exact congrArg β (Fin.ext (six_mul_congr r2.symm b.val))
  let u6 : Fin 64 := ⟨bitsVal (fun b : Fin 6 ↦
    β ⟨6 * ax + b.val, lt_of_lt_of_le (six_mul_add_lt_core hax_lt b)
      (Nat.le_add_right C slot0LocalWorkWires128)⟩), bitsVal_lt_two_pow _⟩
  have hu6_eq : (⟨bitsVal (fun b : Fin 6 ↦ β₃ (ax012 b)), bitsVal_lt_two_pow _⟩ : Fin 64) = u6 :=
    Fin.ext (congrArg bitsVal (funext hax012_bits))
  rw [hu6_eq] at hv4
  refine ⟨fun hq53 ↦ hcl4 q (by omega), fun hq32 hnp ↦ hkeep4 q hq32 hnp, fun hq ↦ hq ▸ hall4,
    fun i hqi ↦ ?_⟩
  subst hqi
  dsimp only
  rw [hv4]
  exact mag5_apply_eq_testBit mag5 β₄ i
def slot0PayW128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (k : ℕ) (hk : k < 80) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  ⟨3954 + k, lt_of_lt_of_le (slot0Pay_lt_core hmPay k hk) (Nat.le_add_right _ _)⟩
def slot0InitW1_128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  slot0PayW128 hmPay (2 * m.val + 1) (slot0Odd18_lt80 m)
def slot0InitW2_128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  slot0PayW128 hmPay (2 * m.val) (slot0Even18_lt80 m)
theorem slot0InitW1_128_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    (slot0InitW1_128 hmPay m).val < coreWiresSym mPayload :=
  slot0Pay_lt_core hmPay (2 * m.val + 1) (slot0Odd18_lt80 m)
theorem slot0InitW2_128_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    (slot0InitW2_128 hmPay m).val < coreWiresSym mPayload :=
  slot0Pay_lt_core hmPay (2 * m.val) (slot0Even18_lt80 m)
theorem slot0InitW1_128_inj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Injective (slot0InitW1_128 hmPay) := fun i j hij ↦ by
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW1_128, slot0PayW128] at hv
  exact Fin.ext (by omega)
theorem slot0InitW2_128_inj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Injective (slot0InitW2_128 hmPay) := fun i j hij ↦ by
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW2_128, slot0PayW128] at hv
  exact Fin.ext (by omega)
theorem slot0Init12_128_disj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (i j : Fin 18) :
    slot0InitW1_128 hmPay i ≠ slot0InitW2_128 hmPay j := by
  intro hij
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW1_128, slot0InitW2_128, slot0PayW128] at hv
  omega
theorem slot0InitW1_128_pool {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    InMod3Pool (coreWiresSym mPayload) (slot0InitW1_128 hmPay m) :=
  Or.inl ⟨by dsimp [slot0InitW1_128, slot0PayW128]; omega,
    by have := m.isLt; dsimp [slot0InitW1_128, slot0PayW128]; omega⟩
theorem slot0InitW2_128_pool {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    InMod3Pool (coreWiresSym mPayload) (slot0InitW2_128 hmPay m) :=
  Or.inl ⟨by dsimp [slot0InitW2_128, slot0PayW128]; omega,
    by have := m.isLt; dsimp [slot0InitW2_128, slot0PayW128]; omega⟩
theorem slot0Core_add32_le128 {mPayload : ℕ} : coreWiresSym mPayload + 2 * 16 ≤ coreWiresSym
    mPayload + slot0LocalWorkWires128 := Nat.add_le_add_left (by decide) _
theorem slot0Core_sub_eq128 (mPayload : ℕ) : (coreWiresSym mPayload + slot0LocalWorkWires128)
    - coreWiresSym mPayload = slot0LocalWorkWires128 := Nat.add_sub_cancel_left _ _
/-- Full `53`-`TempAnd` (`212-T`) prefix program before `wStateTree 4`. -/
noncomputable def slot0LocalPreOhProg53 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (body :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128)) : TempPhaseProg
    (coreWiresSym mPayload + slot0LocalWorkWires128) := withMod3AllOnesReduceInPlace
    (coreWiresSym mPayload) 16 (coreWiresSym mPayload) le_rfl slot0Core_add32_le128
    (slot0InitW1_128 hmPay) (slot0InitW2_128 hmPay) (slot0InitW1_128_lt hmPay)
    (slot0InitW2_128_lt hmPay) (slot0InitW1_128_inj hmPay) (slot0InitW2_128_inj hmPay)
    (slot0Init12_128_disj hmPay) (slot0InitW1_128_pool hmPay) (slot0InitW2_128_pool hmPay)
    (fun a1 b1 a2 b2 hOut ↦ slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut body)
theorem isPurePhaseCtx_slot0LocalPreOhProg53 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    IsPurePhaseCtx (slot0LocalPreOhProg53 hmPay) :=
    isPurePhaseCtx_withMod3AllOnesReduceInPlace (coreWiresSym mPayload) 16
    (coreWiresSym mPayload) le_rfl slot0Core_add32_le128 (slot0InitW1_128 hmPay)
    (slot0InitW2_128 hmPay) (slot0InitW1_128_lt hmPay) (slot0InitW2_128_lt hmPay)
    (slot0InitW1_128_inj hmPay) (slot0InitW2_128_inj hmPay) (slot0Init12_128_disj hmPay)
    (slot0InitW1_128_pool hmPay) (slot0InitW2_128_pool hmPay)
    (fun a1 b1 a2 b2 hOut ↦ slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut) (fun a1 b1 a2 b2 hOut
    ↦ isPurePhaseCtx_slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut)
theorem slot0LocalPreOhProg53_countTempAnd {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (slot0LocalPreOhProg53 hmPay .nil).countTempAnd = 53 :=
    withMod3AllOnesReduceInPlace_countTempAnd (coreWiresSym mPayload) 16
    (coreWiresSym mPayload) le_rfl slot0Core_add32_le128 (slot0InitW1_128 hmPay)
    (slot0InitW2_128 hmPay) (slot0InitW1_128_lt hmPay) (slot0InitW2_128_lt hmPay)
    (slot0InitW1_128_inj hmPay) (slot0InitW2_128_inj hmPay) (slot0Init12_128_disj hmPay)
    (slot0InitW1_128_pool hmPay) (slot0InitW2_128_pool hmPay) _ 21 (fun a1 b1 a2 b2 hOut ↦
    slot0TailPreOhProg21_countTempAnd hmPay a1 b1 a2 b2 hOut)
noncomputable def ctxSlot0PreOh53 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    DiagCtxW (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  Classical.choose (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0LocalPreOhProg53 hmPay))
theorem ctxSlot0PreOh53_spec_raw {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    let M := coreWiresSym mPayload + slot0LocalWorkWires128
    let K := ctxSlot0PreOh53 hmPay
    K.countT = 212 ∧
    (∀ q : Wire M, ∀ γ : BitAssignment M,
      K.fwdBits γ q = (slot0LocalPreOhProg53 hmPay (.z q)).evalSign γ) ∧
    (∀ (q : Wire M) (rem : ℕ) (γ : BitAssignment M),
      ValidCleanRem M rem (slot0LocalPreOhProg53 hmPay (.z q)) →
      cleanRem M rem γ → K.ValidAt γ) := by
  have h := Classical.choose_spec
    (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0LocalPreOhProg53 hmPay))
  exact ⟨h.1.trans (by rw [slot0LocalPreOhProg53_countTempAnd]), h.2.1, h.2.2⟩
/-- `42`-`TempAnd` (`168-T`) one-hot streaming comparator program after `wStateTree 4`. -/
noncomputable def slot0OhCmpProg42 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (body : TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128)) :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let payW (k : ℕ) (_hk : k < 80) : Wire M :=
    ⟨3954 + k, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let cmpPay42 : Fin 42 → Wire M := fun j ↦ payW (37 + j.val) (by omega)
  let threshTbl : Fin 32 → ℕ := fun m ↦
    MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff ⟨m.val, lt_trans m.isLt (by decide)⟩
  withOhStreamLtComp42 (C + 53) (by dsimp [M, slot0LocalWorkWires128]; omega)
    threshTbl cmpPay42 (fun j ↦ by dsimp [cmpPay42, payW]; omega) body
theorem isPurePhaseCtx_slot0OhCmpProg42 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    IsPurePhaseCtx (slot0OhCmpProg42 hmPay w_eff) := by
  unfold slot0OhCmpProg42
  exact isPurePhaseCtx_withOhStreamLtComp42 _ _ _ _ _ .id
theorem slot0OhCmpProg42_countTempAnd {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0OhCmpProg42 hmPay w_eff .nil).countTempAnd = 42 := by
  unfold slot0OhCmpProg42
  rw [withOhStreamLtComp42_countTempAnd, TempPhaseProg.countTempAnd, add_zero]
noncomputable def ctxSlot0OhCmp42 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    DiagCtxW (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  Classical.choose (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0OhCmpProg42 hmPay w_eff))
theorem ctxSlot0OhCmp42_spec_raw {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    let M := coreWiresSym mPayload + slot0LocalWorkWires128
    let K := ctxSlot0OhCmp42 hmPay w_eff
    K.countT = 168 ∧
    (∀ q : Wire M, ∀ γ : BitAssignment M,
      K.fwdBits γ q = (slot0OhCmpProg42 hmPay w_eff (.z q)).evalSign γ) ∧
    (∀ (q : Wire M) (rem : ℕ) (γ : BitAssignment M),
      ValidCleanRem M rem (slot0OhCmpProg42 hmPay w_eff (.z q)) →
      cleanRem M rem γ → K.ValidAt γ) := by
  have h := Classical.choose_spec
    (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0OhCmpProg42 hmPay w_eff))
  exact ⟨h.1.trans (by rw [slot0OhCmpProg42_countTempAnd]), h.2.1, h.2.2⟩
def slot0Mag5Wires128 (mPayload : ℕ) :
    Fin 5 → Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  let ax012 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  mag5InPlaceWires ax012
def slot0OutOH32Wires128 (mPayload : ℕ) :
    Fin (2 ^ 5) → Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  fun k ↦ ⟨C + 53 + k.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
def slot0WThWire128 (mPayload : ℕ) : Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  ⟨C + 85, by dsimp [M, slot0LocalWorkWires128]; omega⟩
theorem slot0DisjWUncond128 (mPayload : ℕ) : DisjWUncond (slot0Mag5Wires128 mPayload)
    (slot0OutOH32Wires128 mPayload) (slot0WThWire128 mPayload) := by
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  let ax012 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  have hmag := mag5InPlaceWires_lt_and_inj (C + 49) ax012
    (fun i ↦ by dsimp [ax012]; omega)
    (wire_offset_inj (C + 43) (fun i ↦ by dsimp [M, slot0LocalWorkWires128]; omega))
  refine ⟨fun d j ↦ wire_ne_of_lt (lt_of_lt_of_le (hmag.1 d) (by
    dsimp [slot0OutOH32Wires128]; omega)),
    fun i j h ↦ Fin.ext (by
      have := congrArg Fin.val h; dsimp [slot0OutOH32Wires128] at this; omega),
    fun d ↦ wire_ne_of_lt (lt_of_lt_of_le (hmag.1 d) (by dsimp [slot0WThWire128]; omega)),
    fun j ↦ wire_ne_of_lt (by have := j.isLt; dsimp [slot0OutOH32Wires128, slot0WThWire128]; omega)⟩
/-- **`440-T` (`212 + 60 + 168`) W-State `Slot 0` `DiagCtxW` Context (`ctxSlot0WState128`)**
replacing `26`-`TempAnd` (`104-T`) `withAnf5Loop` with `60-T` `wStateTree 4`. -/
noncomputable def ctxSlot0WState128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    DiagCtxW (coreWiresSym mPayload + slot0LocalWorkWires128) := DiagCtxW_append
    (ctxSlot0PreOh53 hmPay) (.wStateTree 4 (slot0Mag5Wires128 mPayload) (slot0OutOH32Wires128
    mPayload) (slot0WThWire128 mPayload) (slot0DisjWUncond128 mPayload) (ctxSlot0OhCmp42 hmPay
    w_eff))
@[simp] theorem ctxSlot0WState128_countT {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (ctxSlot0WState128 hmPay w_eff).countT = 440 := by
  unfold ctxSlot0WState128
  rw [DiagCtxW_append_countT, (ctxSlot0PreOh53_spec_raw hmPay).1]
  dsimp only [DiagCtxW.countT]
  rw [(ctxSlot0OhCmp42_spec_raw hmPay w_eff).1]
  decide
theorem ctxSlot0WState128_spec {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (hw_eff : LiteralKineticAndMidpoint128.elecQuadCenterOffset < w_eff) :
    let C := coreWiresSym mPayload
    let M := C + slot0LocalWorkWires128
    have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
    let wTh : Wire M := ⟨C + 85, by dsimp [M, slot0LocalWorkWires128]; omega⟩
    let c2 : Wire M := ⟨3950, by dsimp [M, slot0LocalWorkWires128]; omega⟩
    let allOnesW : Wire M := ⟨C + 34, by dsimp [M, slot0LocalWorkWires128]; omega⟩
    let bTieW : Wire M := ⟨3954 + 79, by dsimp [M, slot0LocalWorkWires128]; omega⟩
    let ltOut : Wire M := ⟨C + 127, by dsimp [M, slot0LocalWorkWires128]; omega⟩
    let K := ctxSlot0WState128 hmPay w_eff
    (∀ γ : BitAssignment M, cleanRem M slot0LocalWorkWires128 γ → K.ValidAt γ) ∧
    (∀ γ : BitAssignment M, cleanRem M slot0LocalWorkWires128 γ → K.fwdBits γ wTh = 0) ∧
    (∀ α : BitAssignment C,
      let γ := padZeroBits (mClean := slot0LocalWorkWires128) α
      (if K.fwdBits γ allOnesW = 1 then K.fwdBits γ bTieW else K.fwdBits γ ltOut) * K.fwdBits γ c2 =
        slot0LocalC2PhaseBit hmPay w_eff α) := by
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let wTh : Wire M := ⟨C + 85, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let c2 : Wire M := ⟨3950, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let allOnesW : Wire M := ⟨C + 34, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let bTieW : Wire M := ⟨3954 + 79, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ltOut : Wire M := ⟨C + 127, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let payW (k : ℕ) (_hk : k < 80) : Wire M :=
    ⟨3954 + k, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let cmpPay42 : Fin 42 → Wire M := fun j ↦ payW (37 + j.val) (by omega)
  let threshTbl : Fin 32 → ℕ := fun m ↦
    MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff ⟨m.val, lt_trans m.isLt (by decide)⟩
  let K_pre := ctxSlot0PreOh53 hmPay
  let K_cmp := ctxSlot0OhCmp42 hmPay w_eff
  let K := ctxSlot0WState128 hmPay w_eff
  obtain ⟨_, hFwdPre, hValPre⟩ := ctxSlot0PreOh53_spec_raw hmPay
  obtain ⟨_, hFwdCmp, hValCmp⟩ := ctxSlot0OhCmp42_spec_raw hmPay w_eff
  let w1 := slot0InitW1_128 hmPay
  let w2 := slot0InitW2_128 hmPay
  have hBlockPreAll : ∀ q : Wire M, ∃ (a1 b1 a2 b2 : Wire M)
      (hOut : Mod3ReducedOut C (C + 32) a1 b1 a2 b2)
      (stRed stTop : BitAssignment M → BitAssignment M), ScopedBlock M slot0LocalWorkWires128
      stTop (.z q) (slot0LocalPreOhProg53 hmPay (.z q)) ∧ (∀ γ : BitAssignment M, cleanRem M
      slot0LocalWorkWires128 γ → cleanRem M (M - (C + 32)) (stRed γ) ∧ (∀ w : Wire M, w.val <
      C → ¬ InMod3Pool C w → stRed γ w = γ w) ∧ (((stRed γ a1).val + (stRed γ b1).val + 2 *
      ((stRed γ a2).val + (stRed γ b2).val)) % 3 = ((∑ i : Fin 18, (γ (w1 i)).val) + 2 * (∑ i
      : Fin 18, (γ (w2 i)).val)) % 3) ∧ (stRed γ a1 * stRed γ b1 * (stRed γ a2 * stRed γ b2) =
      (∏ i : Fin 18, γ (w1 i)) * (∏ i : Fin 18, γ (w2 i))) ∧ K_pre.fwdBits γ q =
      (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q)).evalSign (stRed γ)) :=
    fun q ↦ by
      classical
      obtain ⟨a1, b1, a2, b2, hOut, stRed, hRed, hRedSpec⟩ :=
        ScopedBlock.withMod3AllOnesReduceInPlace_block (M := M) C 16 C le_rfl slot0Core_add32_le128
          w1 w2
          (slot0InitW1_128_lt hmPay) (slot0InitW2_128_lt hmPay)
          (slot0InitW1_128_inj hmPay) (slot0InitW2_128_inj hmPay)
          (slot0Init12_128_disj hmPay)
          (slot0InitW1_128_pool hmPay) (slot0InitW2_128_pool hmPay)
          (fun a1 b1 a2 b2 hOut ↦ slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut (.z q))
          (.z q)
          (fun a1 b1 a2 b2 ↦
            if h : Mod3ReducedOut C (C + 32) a1 b1 a2 b2 then
              Classical.choose (slot0TailPreOhProg21_block hmPay a1 b1 a2 b2 h q)
            else fun x ↦ x)
          (fun a1 b1 a2 b2 h ↦ by
            rw [dite_pos_eq h]
            exact (Classical.choose_spec (slot0TailPreOhProg21_block hmPay a1 b1 a2 b2 h q)).1)
      have hTop0 : ScopedBlock M (M - C) _ (.z q) (slot0LocalPreOhProg53 hmPay (.z q)) := hRed
      have hTop := hTop0.cast_rem (slot0Core_sub_eq128 mPayload)
      refine ⟨a1, b1, a2, b2, hOut, stRed, _, hTop, fun γ hγ ↦ ?_⟩
      have hγ' : cleanRem M (M - C) γ := (slot0Core_sub_eq128 mPayload).symm ▸ hγ
      obtain ⟨hcl1, hbel1, hmod1, hprod1⟩ := hRedSpec γ hγ'
      have hTailSpec := Classical.choose_spec (slot0TailPreOhProg21_block hmPay a1 b1 a2 b2 hOut q)
      have hs0 := hFwdPre q γ
      have hs1 := hTop.sign γ hγ
      dsimp only at hs1
      rw [dite_pos_eq hOut] at hs1
      exact ⟨hcl1, hbel1, hmod1, hprod1,
        hs0.trans (hs1.trans (hTailSpec.1.sign (stRed γ) hcl1).symm)⟩
  have hPreClean53 : ∀ γ : BitAssignment M, cleanRem M slot0LocalWorkWires128 γ →
      cleanRem M (M - (C + 53)) (K_pre.fwdBits γ) := fun γ hγ q hq ↦ by
    obtain ⟨a1, b1, a2, b2, hOut, stRed, _, _, hS⟩ := hBlockPreAll q
    obtain ⟨hcl1, _, _, _, hfwd⟩ := hS γ hγ
    have hTailSpec := Classical.choose_spec (slot0TailPreOhProg21_block hmPay a1 b1 a2 b2 hOut q)
    exact hfwd.trans ((hTailSpec.2 (stRed γ) hcl1).1 (by omega))
  have hStepAll : ∀ γ : BitAssignment M, cleanRem M slot0LocalWorkWires128 γ →
      let γ₁ := K_pre.fwdBits γ
      let u : Fin 32 := ⟨bitsVal (fun i : Fin 5 ↦
        γ₁ (slot0Mag5Wires128 mPayload i)), bitsVal_lt_two_pow _⟩
      ∃ γ₂ : BitAssignment M,
        K.ValidAt γ ∧
        K.fwdBits γ = K_cmp.fwdBits γ₂ ∧
        cleanRem M (M - (C + 86)) γ₂ ∧
        γ₂ wTh = 0 ∧
        (∀ m : Fin 32, γ₂ ⟨C + 53 + m.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩ =
          if m.val = u.val then 1 else 0) ∧
        (∀ w : Wire M, w.val < C + 53 → γ₂ w = γ₁ w) := fun γ hγ ↦ by
    intro γ₁ u
    have hcl53 : cleanRem M (M - (C + 53)) γ₁ := hPreClean53 γ hγ
    obtain ⟨_, _, _, _, _, _, _, hTopTh, _⟩ := hBlockPreAll wTh
    have hVal1 : K_pre.ValidAt γ := hValPre wTh slot0LocalWorkWires128 γ hTopTh.valid hγ
    have hOut0 : ∀ j : Fin (2 ^ (4 + 1)), γ₁ (slot0OutOH32Wires128 mPayload j) = 0 :=
      fun j ↦ hcl53 _ (by dsimp [slot0OutOH32Wires128]; omega)
    have hq0 : γ₁ (slot0WThWire128 mPayload) = 0 :=
      hcl53 _ (by dsimp [slot0WThWire128]; omega)
    obtain ⟨γ₂, hFwdW, hValW, hOH₂, hOut₂⟩ :=
      DiagCtxW.wStateTree_step 4 (slot0Mag5Wires128 mPayload) (slot0OutOH32Wires128 mPayload)
        (slot0WThWire128 mPayload) (slot0DisjWUncond128 mPayload) K_cmp γ₁ hOut0 hq0
    have hcl86 : cleanRem M (M - (C + 86)) γ₂ := fun w hw ↦ by
      rw [hOut₂ w (fun j ↦ wire_ne_of_gt (by have := j.isLt; dsimp [slot0OutOH32Wires128]; omega))]
      exact hcl53 w (by omega)
    have hwTh2 : γ₂ wTh = 0 := by
      rw [hOut₂ wTh (fun j ↦ wire_ne_of_gt (by
        have := j.isLt; dsimp [wTh, slot0OutOH32Wires128]; omega))]
      exact hq0
    have hbel2 : ∀ w : Wire M, w.val < C + 53 → γ₂ w = γ₁ w := fun w hw ↦
      hOut₂ w (fun j ↦ wire_ne_of_lt (by dsimp [slot0OutOH32Wires128]; omega))
    have hZ_wTh : ScopedBlock M (M - (C + 53 + 75)) id (.z wTh) (.z wTh) :=
      ⟨by simp [ValidCleanRem], fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    obtain ⟨_, hBlkCmpTh, _⟩ :=
      ScopedBlock.withOhStreamLtComp42_block (M := M) (C + 53)
        (by dsimp [M, slot0LocalWorkWires128]; omega) threshTbl cmpPay42
        (fun j ↦ by dsimp [cmpPay42, payW]; omega) u hZ_wTh
    have hVal2 : K_cmp.ValidAt γ₂ :=
      hValCmp wTh (M - (C + 53 + 33)) γ₂ hBlkCmpTh.valid (by simpa [Nat.add_assoc] using hcl86)
    refine ⟨γ₂, DiagCtxW_append_validAt K_pre _ hVal1 (hValW hVal2), (DiagCtxW_append_fwdBits
      K_pre _ γ).trans hFwdW, hcl86, hwTh2, hOH₂, hbel2⟩
  refine ⟨fun γ hγ ↦ (Classical.choose_spec (hStepAll γ hγ)).1, fun γ hγ ↦ ?_, fun α ↦ ?_⟩
  · obtain ⟨γ₂, _, hFwdEq, hcl86, hwTh2, hOH₂, _⟩ := hStepAll γ hγ
    let u : Fin 32 := ⟨bitsVal (fun i : Fin 5 ↦ (K_pre.fwdBits γ) (slot0Mag5Wires128 mPayload i)),
      bitsVal_lt_two_pow _⟩
    have hZ_wTh : ScopedBlock M (M - (C + 53 + 75)) id (.z wTh) (.z wTh) :=
      ⟨by simp [ValidCleanRem], fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    obtain ⟨stCmp, hBlkCmp, hSpecCmp⟩ :=
      ScopedBlock.withOhStreamLtComp42_block (M := M) (C + 53)
        (by dsimp [M, slot0LocalWorkWires128]; omega) threshTbl cmpPay42
        (fun j ↦ by dsimp [cmpPay42, payW]; omega) u hZ_wTh
    obtain ⟨_, hwTh_out, _, _⟩ :=
      hSpecCmp γ₂ (by simpa [Nat.add_assoc] using hcl86) hwTh2 hOH₂
    have hSignCmp := hBlkCmp.sign γ₂ (by simpa [Nat.add_assoc] using hcl86)
    have hwTh_eq : (⟨C + 53 + 32, by dsimp [M, slot0LocalWorkWires128]; omega⟩ : Wire M) = wTh :=
      Fin.ext (by dsimp [wTh])
    rw [hwTh_eq] at hwTh_out
    rw [hFwdEq, hFwdCmp wTh γ₂]
    exact hSignCmp.trans hwTh_out
  · let β₀ : BitAssignment M := padZeroBits (mClean := slot0LocalWorkWires128) α
    have hcl0 : cleanRem M slot0LocalWorkWires128 β₀ := cleanRem_padZeroBits α
    obtain ⟨γ₂, _, hFwdEq, hcl86, hwTh2, hOH₂, hbel2⟩ := hStepAll β₀ hcl0
    let γ₁ := K_pre.fwdBits β₀
    let u : Fin 32 := ⟨bitsVal (fun i : Fin 5 ↦ γ₁ (slot0Mag5Wires128 mPayload i)),
      bitsVal_lt_two_pow _⟩
    have hKeepCmp : ∀ q : Wire M, q.val < C + 53 → K.fwdBits β₀ q = γ₁ q := fun q hq ↦ by
      have hZ_q : ScopedBlock M (M - (C + 53 + 75)) id (.z q) (.z q) :=
        ⟨by simp [ValidCleanRem], fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
      obtain ⟨stCmp, hBlkCmp, hSpecCmp⟩ :=
        ScopedBlock.withOhStreamLtComp42_block (M := M) (C + 53)
          (by dsimp [M, slot0LocalWorkWires128]; omega) threshTbl cmpPay42
          (fun j ↦ by dsimp [cmpPay42, payW]; omega) u hZ_q
      obtain ⟨_, _, hbelCmp, _⟩ :=
        hSpecCmp γ₂ (by simpa [Nat.add_assoc] using hcl86) hwTh2 hOH₂
      have hSignCmp := hBlkCmp.sign γ₂ (by simpa [Nat.add_assoc] using hcl86)
      rw [hFwdEq, hFwdCmp q γ₂]
      exact hSignCmp.trans ((hbelCmp q (by omega)).trans (hbel2 q hq))
    have hsc := slot0SysCoin_lt_core mPayload
    have hc2_ltC : 3950 < C := slot0Coin_lt_core mPayload 2 (by decide)
    have h36_ltC : 3954 + 36 < C := slot0Pay_lt_core hmPay 36 (by decide)
    have h79_ltC : 3954 + 79 < C := slot0Pay_lt_core hmPay 79 (by decide)
    have h36_ltP : 36 < mPayload := lt_of_lt_of_le (by decide) hmPay
    have h79_ltP : 79 < mPayload := lt_of_lt_of_le (by decide) hmPay
    have hpadCore : ∀ (k : ℕ) (hk : k < C),
        β₀ ⟨k, lt_of_lt_of_le hk (Nat.le_add_right C slot0LocalWorkWires128)⟩ = α ⟨k, hk⟩ :=
          fun k hk ↦ by
      have heq : (⟨k, lt_of_lt_of_le hk (Nat.le_add_right C slot0LocalWorkWires128)⟩ : Wire M) =
          Fin.castAdd slot0LocalWorkWires128 ⟨k, hk⟩ := rfl
      rw [heq]; exact Fin.addCases_left _
    have hpayCore : ∀ (k : ℕ) (hk : k < 80),
        β₀ (slot0PayW128 hmPay k hk) = α (corePayloadSym mPayload ⟨k, lt_of_lt_of_le hk hmPay⟩) :=
      fun k hk ↦ by
        dsimp only [slot0PayW128]
        rw [hpadCore (3954 + k) (slot0Pay_lt_core hmPay k hk)]
        exact congrArg α (Fin.ext (by
          dsimp [corePayloadSym, MomSlot0LocalAndMomCombine288Alt.qreg_block_apply,
            MomSlot0LocalAndMomCombine288Alt.qreg_block_wires_apply,
            MomSlot0LocalAndMomCombine288Alt.qreg_whole_wires,
            MomSlot0LocalAndMomCombine288Alt.emb_trans_apply,
            MomSlot0LocalAndMomCombine288Alt.emb_refl_apply,
            MomSlot0LocalAndMomCombine288Alt.emb_mk_apply, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
              SpecsAux.SpecMirror.projectileBits]))
    have hPreKeepOut : ∀ (q : Wire M), q.val < C → ¬ InMod3Pool C q → γ₁ q = β₀ q := fun q hq hnp ↦
      by
      obtain ⟨a1, b1, a2, b2, hOut, stRed, _, _, hS⟩ := hBlockPreAll q
      obtain ⟨hcl1, hbel1, _, _, hfwd⟩ := hS β₀ hcl0
      have hTailSpec := Classical.choose_spec (slot0TailPreOhProg21_block hmPay a1 b1 a2 b2 hOut q)
      dsimp only [γ₁]
      rw [hfwd, (hTailSpec.2 (stRed β₀) hcl1).2.1 (by omega) hnp]
      exact hbel1 q hq hnp
    have hFwdC2 : K.fwdBits β₀ c2 = α ⟨SpecsAux.SpecMirror.systemQubits + 2, hsc.2.2⟩ := by
      rw [hKeepCmp c2 (by dsimp [c2]; omega),
          hPreKeepOut c2 hc2_ltC (not_inMod3Pool_of_out ⟨Or.inl (by dsimp [c2]; omega), hc2_ltC⟩)]
      exact hpadCore 3950 hc2_ltC
    let f36 : Fin 36 → ZMod 2 := fun i ↦
      α (corePayloadSym mPayload ⟨i.val, pay36_lt_payload hmPay i⟩)
    have hw1_f : ∀ m : Fin 18, β₀ (w1 m) = f36 ⟨2 * m.val + 1, slot0Odd18_lt36 m⟩ :=
      fun m ↦ hpayCore (2 * m.val + 1) (slot0Odd18_lt80 m)
    have hw2_f : ∀ m : Fin 18, β₀ (w2 m) = f36 ⟨2 * m.val, slot0Even18_lt36 m⟩ :=
      fun m ↦ hpayCore (2 * m.val) (slot0Even18_lt80 m)
    have hFwdAO : K.fwdBits β₀ allOnesW = 1 ↔ (∑ i : Fin 36, (α (corePayloadSym mPayload
        ⟨i.val, pay36_lt_payload hmPay i⟩)).val * 2 ^ i.val) = 2 ^ 36 - 1 := by
      rw [hKeepCmp allOnesW (by dsimp [allOnesW]; omega)]
      obtain ⟨a1, b1, a2, b2, hOut, stRed, _, _, hS⟩ := hBlockPreAll allOnesW
      obtain ⟨hcl1, _, _, hprod1, hfwd⟩ := hS β₀ hcl0
      have hTailSpec :=
        Classical.choose_spec (slot0TailPreOhProg21_block hmPay a1 b1 a2 b2 hOut allOnesW)
      dsimp only [γ₁]
      rw [hfwd, (hTailSpec.2 (stRed β₀) hcl1).2.2.1 rfl, hprod1]
      have hprod_eq : (∏ i : Fin 18, β₀ (w1 i)) * (∏ i : Fin 18, β₀ (w2 i)) =
          (∏ m : Fin 18, f36 ⟨2 * m.val + 1, slot0Odd18_lt36 m⟩) *
            (∏ m : Fin 18, f36 ⟨2 * m.val, slot0Even18_lt36 m⟩) :=
        congrArg₂ (· * ·) (Finset.prod_congr rfl fun m _ ↦ hw1_f m) (Finset.prod_congr rfl fun m _ ↦
          hw2_f m)
      rw [hprod_eq]
      exact even_odd_prod_eq_one_iff_u36_allOnes f36
    have hFwdBT : K.fwdBits β₀ bTieW = α (corePayloadSym mPayload ⟨79, h79_ltP⟩) := by
      rw [hKeepCmp bTieW (by dsimp [bTieW]; omega),
          hPreKeepOut bTieW h79_ltC (not_inMod3Pool_of_out ⟨Or.inr (by
            dsimp [bTieW]; omega), h79_ltC⟩)]
      exact hpayCore 79 (by decide)
    let ax_α : ℕ := (2 * ((∑ i : Fin 36,
      (α (corePayloadSym mPayload ⟨i.val, pay36_lt_payload hmPay i⟩)).val * 2 ^ i.val) % 327) +
      (α (corePayloadSym mPayload ⟨36, h36_ltP⟩)).val) % 3
    let u6_α : Fin 64 := ⟨bitsVal (fun b : Fin 6 ↦ α ⟨6 * ax_α + b.val, six_mul_add_lt_core
        (Nat.mod_lt _ (by decide)) b⟩), bitsVal_lt_two_pow _⟩
    have hMagBits : ∀ i : Fin 5,
        γ₁ (slot0Mag5Wires128 mPayload i) =
          if ((MomSlots01Slot0ElectronKinetic.slot0AxisInt u6_α).natAbs).testBit i.val then 1 else
            0 :=
      fun i ↦ by
        let q_i := slot0Mag5Wires128 mPayload i
        obtain ⟨a1, b1, a2, b2, hOut, stRed, _, _, hS⟩ := hBlockPreAll q_i
        obtain ⟨hcl1, hbel1, hmod1, _, hfwd⟩ := hS β₀ hcl0
        have hTailSpec :=
          Classical.choose_spec (slot0TailPreOhProg21_block hmPay a1 b1 a2 b2 hOut q_i)
        dsimp only [γ₁]
        rw [hfwd, (hTailSpec.2 (stRed β₀) hcl1).2.2.2 i rfl]
        let β₁ := stRed β₀
        have hbel_out : ∀ (k : ℕ) (hk : k < C), (k < 3954 ∨ 3990 ≤ k) →
            β₁ ⟨k, lt_of_lt_of_le hk (Nat.le_add_right C slot0LocalWorkWires128)⟩ = α ⟨k, hk⟩ :=
          fun k hk hout ↦
            (hbel1 _ hk (not_inMod3Pool_of_out ⟨hout, hk⟩)).trans (hpadCore k hk)
        have hbPar_eq : (β₁ ⟨3954 + 36, lt_of_lt_of_le h36_ltC (Nat.le_add_right C
            slot0LocalWorkWires128)⟩).val = (α (corePayloadSym mPayload ⟨36, h36_ltP⟩)).val :=
          congrArg ZMod.val
            ((hbel1 _ h36_ltC (not_inMod3Pool_of_out ⟨Or.inr (by dsimp; omega), h36_ltC⟩)).trans
              (hpayCore 36 (by decide)))
        have hsum1_eq : (∑ m : Fin 18, (β₀ (w1 m)).val) =
            ∑ m : Fin 18, (f36 ⟨2 * m.val + 1, slot0Odd18_lt36 m⟩).val :=
          Finset.sum_congr rfl fun m _ ↦ congrArg ZMod.val (hw1_f m)
        have hsum2_eq : (∑ m : Fin 18, (β₀ (w2 m)).val) =
            ∑ m : Fin 18, (f36 ⟨2 * m.val, slot0Even18_lt36 m⟩).val :=
          Finset.sum_congr rfl fun m _ ↦ congrArg ZMod.val (hw2_f m)
        have hax_eq : (((β₁ a1).val + (β₁ b1).val + 2 * ((β₁ a2).val + (β₁ b2).val) + (β₁
            ⟨3954 + 36, lt_of_lt_of_le h36_ltC (Nat.le_add_right C
            slot0LocalWorkWires128)⟩).val) % 3) = ax_α := by
          dsimp only [ax_α]
          rw [hbPar_eq, mod327_mul2_add_mod3, even_odd_bits_mul2_mod3 18 f36]
          have hm := hmod1
          rw [hsum1_eq, hsum2_eq] at hm
          rw [add_mod3_left, hm]
        have hu6_eq : (⟨bitsVal (fun b : Fin 6 ↦ β₁ ⟨6 * (((β₁ a1).val + (β₁ b1).val + 2 *
            ((β₁ a2).val + (β₁ b2).val) + (β₁ ⟨3954 + 36, lt_of_lt_of_le h36_ltC
            (Nat.le_add_right C slot0LocalWorkWires128)⟩).val) % 3) + b.val, lt_of_lt_of_le
            (six_mul_add_lt_core (Nat.mod_lt _ (by decide)) b) (Nat.le_add_right C
            slot0LocalWorkWires128)⟩), bitsVal_lt_two_pow _⟩ : Fin 64) = u6_α := by
          apply Fin.ext; dsimp only [u6_α]; apply congrArg bitsVal; funext b
          have hmod_lt3 :=
            Nat.mod_lt (((β₁ a1).val + (β₁ b1).val + 2 * ((β₁ a2).val + (β₁ b2).val) +
            (β₁ ⟨3954 + 36,
              lt_of_lt_of_le h36_ltC (Nat.le_add_right C slot0LocalWorkWires128)⟩).val))
            (by decide : 0 < 3)
          rw [hbel_out _ (six_mul_add_lt_core hmod_lt3 b)
            (Or.inl (by have := b.isLt; omega))]
          exact congrArg α (Fin.ext (six_mul_congr hax_eq b.val))
        rw [hu6_eq]
    have hu_val : u.val = (MomSlots01Slot0ElectronKinetic.slot0AxisInt u6_α).natAbs := by
      dsimp only [u]
      rw [show (fun i : Fin 5 ↦ γ₁ (slot0Mag5Wires128 mPayload i)) = _ from funext hMagBits]
      exact bitsVal_of_testBit _ (slot0AxisInt_natAbs_lt_32 u6_α)
    have hFwdLT : K.fwdBits β₀ ltOut =
        let uCmp42 := ∑ i : Fin 42,
          (α (corePayloadSym mPayload ⟨37 + i.val, pay37_lt_payload hmPay i⟩)).val * 2 ^ i.val
        if uCmp42 < MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u6_α then 1 else 0 := by
      have hZ_lt : ScopedBlock M (M - (C + 53 + 75)) id (.z ltOut) (.z ltOut) :=
        ⟨by simp [ValidCleanRem], fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
      obtain ⟨stCmp, hBlkCmp, hSpecCmp⟩ :=
        ScopedBlock.withOhStreamLtComp42_block (M := M) (C + 53)
          (by dsimp [M, slot0LocalWorkWires128]; omega) threshTbl cmpPay42
          (fun j ↦ by dsimp [cmpPay42, payW]; omega) u hZ_lt
      obtain ⟨_, _, _, hlt_out⟩ :=
        hSpecCmp γ₂ (by simpa [Nat.add_assoc] using hcl86) hwTh2 hOH₂
      have hSignCmp : (slot0OhCmpProg42 hmPay w_eff (.z ltOut)).evalSign γ₂ = stCmp γ₂ ltOut :=
        hBlkCmp.sign γ₂ (by simpa [Nat.add_assoc] using hcl86)
      have hltOut_eq : (⟨C + 53 + 74, by
        dsimp [M, slot0LocalWorkWires128]; omega⟩ : Wire M) = ltOut :=
        Fin.ext (by dsimp [ltOut])
      rw [hltOut_eq] at hlt_out
      rw [hFwdEq, hFwdCmp ltOut γ₂, hSignCmp, hlt_out]
      have hcmp_eq :
          bitsVal (fun j : Fin 42 ↦
            γ₂ ⟨3954 + (37 + j.val), by dsimp [M, slot0LocalWorkWires128]; omega⟩) =
            ∑ i : Fin 42, (α (corePayloadSym mPayload ⟨37 + i.val,
              pay37_lt_payload hmPay i⟩)).val * 2 ^ i.val := by
        unfold bitsVal
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        dsimp only
        have hlt_j := slot0Pay_lt_core hmPay (37 + j.val) (pay37_lt_80 j)
        have hj :
            γ₂ ⟨3954 + (37 + j.val),
              lt_of_lt_of_le hlt_j (Nat.le_add_right C slot0LocalWorkWires128)⟩ =
            α (corePayloadSym mPayload ⟨37 + j.val, pay37_lt_payload hmPay j⟩) :=
          (hbel2 _ (by dsimp; omega)).trans
            ((hPreKeepOut _ hlt_j (not_inMod3Pool_of_out
                ⟨Or.inr (by change 3990 ≤ 3954 + (37 + j.val); omega), hlt_j⟩)).trans
              (hpayCore (37 + j.val) (pay37_lt_80 j)))
        rw [hj]
      have hthr_eq : MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u6_α = threshTbl u :=
        slot0Thresh_eq_of_natAbs w_eff u6_α u hu_val.symm
      have hth_val : bitsVal (fun j : Fin 42 ↦ if (threshTbl u).testBit j.val then (1 : ZMod
          2) else 0) = MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u6_α := by
        rw [← hthr_eq]
        exact bitsVal_of_testBit _ (slot0Thresh_lt_two_pow_42 hw_eff u6_α)
      dsimp only
      rw [hcmp_eq, hth_val]
    change (if K.fwdBits β₀ allOnesW = 1 then K.fwdBits β₀ bTieW else K.fwdBits β₀ ltOut) *
      K.fwdBits β₀ c2 =
      slot0LocalC2PhaseBit hmPay w_eff α
    rw [hFwdC2]
    let ca2 := α ⟨SpecsAux.SpecMirror.systemQubits + 2, hsc.2.2⟩
    rcases zmod2_cases ca2 with h2z | h2o
    · change _ * ca2 = slot0LocalC2PhaseBit hmPay w_eff α
      rw [h2z, mul_zero]
      unfold slot0LocalC2PhaseBit
      have hnot1 : ¬(α ⟨SpecsAux.SpecMirror.systemQubits + 2, hsc.2.2⟩ = 1) := by
        change ¬(ca2 = 1); rw [h2z]; decide
      rw [ite_neg_eq hnot1]
    · change _ * ca2 = slot0LocalC2PhaseBit hmPay w_eff α
      rw [h2o, mul_one]
      unfold slot0LocalC2PhaseBit
      rw [ite_pos_eq h2o]
      dsimp only
      by_cases hAll : K.fwdBits β₀ allOnesW = 1
      · rw [ite_pos_eq hAll, ite_pos_eq (hFwdAO.mp hAll), hFwdBT]
      · rw [ite_neg_eq hAll, ite_neg_eq (mt hFwdAO.mpr hAll), hFwdLT]
set_option allowUnsafeReducibility true in
/-- **`128`-wire W-State `dSlot0LocalWState128` (`444 T`, `0 TOFF`, `-44 T` below `488 T`)**
realizing `uSlot0LocalC2 hmPay w_eff`. -/
noncomputable def dSlot0LocalWState128 {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0LocalWorkWires128 ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let rSub : QRegister slot0LocalWorkWires128 n := rWork.slice 0 slot0LocalWorkWires128 hw_len
  let rComb : QRegister M n := rCore.concat rSub (hdisj.compose_right _)
  let wTh : Wire M := ⟨C + 85, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let c2 : Wire M := ⟨3950, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let allOnesW : Wire M := ⟨C + 34, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let bTieW : Wire M := ⟨3954 + 79, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ltOut : Wire M := ⟨C + 127, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let inner : DynamicCircuit Var n :=
    dMuxCz5 v (rComb allOnesW) (rComb ltOut) (rComb bTieW) (rComb wTh) (rComb c2)
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [ltOut, bTieW]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [allOnesW, bTieW]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_lt (by dsimp [allOnesW, wTh]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_lt (by dsimp [bTieW, wTh]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [ltOut, wTh]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [wTh, c2]; omega)))
  toDynW v rComb inner (ctxSlot0WState128 hmPay w_eff)
@[simp] theorem dSlot0LocalWState128_count_toff {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0LocalWorkWires128 ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot0LocalWState128 hmPay hw_len w_eff v rCore rWork hdisj).count TOFF = 0 :=
    (toDynW_count_toff v _ _ _).trans (dMuxCz5_count_toff ..)
@[simp] theorem dSlot0LocalWState128_count_t {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0LocalWorkWires128 ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot0LocalWState128 hmPay hw_len w_eff v rCore rWork hdisj).count PrimitiveGate.T =
    slot0LocalTCost444 := by
  dsimp only [dSlot0LocalWState128, slot0LocalTCost444]
  rw [toDynW_count_t, ctxSlot0WState128_countT, dMuxCz5_count_t]
theorem dSlot0LocalWState128_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWork : ℕ} [NeZero (2 ^ n)] (hmPay : 80 ≤ mPayload)
    (hw_len : slot0LocalWorkWires128 ≤ mWork) (w_eff : ℝ)
    (hw_eff : LiteralKineticAndMidpoint128.elecQuadCenterOffset < w_eff) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork
    (uSlot0LocalC2 hmPay w_eff) (dSlot0LocalWState128 hmPay hw_len w_eff v rCore rWork hdisj)
    := by
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let rSub : QRegister slot0LocalWorkWires128 n := rWork.slice 0 slot0LocalWorkWires128 hw_len
  let rComb : QRegister M n := rCore.concat rSub (hdisj.compose_right _)
  let wTh : Wire M := ⟨C + 85, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let c2 : Wire M := ⟨3950, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let allOnesW : Wire M := ⟨C + 34, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let bTieW : Wire M := ⟨3954 + 79, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ltOut : Wire M := ⟨C + 127, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  have h1 : ltOut ≠ bTieW := wire_ne_of_gt (by dsimp [ltOut, bTieW]; omega)
  have h2 : allOnesW ≠ bTieW := wire_ne_of_gt (by dsimp [allOnesW, bTieW]; omega)
  have h3 : allOnesW ≠ wTh := wire_ne_of_lt (by dsimp [allOnesW, wTh]; omega)
  have h4 : bTieW ≠ wTh := wire_ne_of_lt (by dsimp [bTieW, wTh]; omega)
  have h5 : ltOut ≠ wTh := wire_ne_of_gt (by dsimp [ltOut, wTh]; omega)
  have h6 : wTh ≠ c2 := wire_ne_of_gt (by dsimp [wTh, c2]; omega)
  have h7 : bTieW ≠ c2 := wire_ne_of_gt (by dsimp [bTieW, c2]; omega)
  obtain ⟨hValidK, hwTh0, hPhase⟩ := ctxSlot0WState128_spec hmPay w_eff hw_eff
  let Φ : BitAssignment M → BitAssignment 0 → ℂ :=
    fun γ _ ↦ (-1 : ℂ) ^ ((if γ allOnesW = 1 then γ bTieW else γ ltOut) * γ c2).val
  obtain ⟨U_dyn, hRealDyn, hKetDyn⟩ := realizes_toDynW_pred_diagComplex v rComb
      (p2dEmptyReg n) (p2dEmptyReg_disj rComb) (fun γ ↦ γ wTh = 0) (dMuxCz5 v (rComb allOnesW)
      (rComb ltOut) (rComb bTieW) (rComb wTh) (rComb c2) (rComb.wires.injective.ne h1)
      (rComb.wires.injective.ne h2) (rComb.wires.injective.ne h3) (rComb.wires.injective.ne
      h4) (rComb.wires.injective.ne h5) (rComb.wires.injective.ne h6)) (uMuxCz5 (rComb
      allOnesW) (rComb ltOut) (rComb bTieW) (rComb wTh) (rComb c2) (rComb.wires.injective.ne
      h1) (rComb.wires.injective.ne h2) (rComb.wires.injective.ne h3)
      (rComb.wires.injective.ne h4) (rComb.wires.injective.ne h5) (rComb.wires.injective.ne
      h6)) (dMuxCz5_realizes v rComb allOnesW ltOut bTieW wTh c2 h1 h2 h3 h4 h5 h6 h7) Φ (fun
      β _ hInv ↦ uMuxCz5_mulVec_ket (rComb allOnesW) (rComb ltOut) (rComb bTieW) (rComb wTh)
      (rComb c2) (rComb.wires.injective.ne h1) (rComb.wires.injective.ne h2)
      (rComb.wires.injective.ne h3) (rComb.wires.injective.ne h4) (rComb.wires.injective.ne
      h5) (rComb.wires.injective.ne h6) (rComb.wires.injective.ne h7) β hInv)
      (ctxSlot0WState128 hmPay w_eff) slot0LocalWorkWires128 (fun _ ↦ True)
      (fun γ hcl _ ↦ hValidK γ hcl) (fun γ hcl _ ↦ hwTh0 γ hcl)
  let P_pre := p2d_ketPredProj fun β : BitAssignment n ↦
    cleanRem M slot0LocalWorkWires128 (fun idx ↦ β (rComb idx)) ∧ True
  let P_work := rWork.basisOutcomeProjector 0
  have hPwork_eq : P_work = p2d_ketPredProj (fun β ↦ ∀ i : Fin mWork, β (rWork i) = 0) :=
    p2d_basisOutcomeProjector_zero_eq_ketPredProj rWork
  have hClOfWork : ∀ β : BitAssignment n, (∀ i : Fin mWork, β (rWork i) = 0) →
      cleanRem M slot0LocalWorkWires128 (fun idx ↦ β (rComb idx)) := fun β hw w hw_lo ↦ by
    have hidx : w = Fin.natAdd C ⟨w.val - C, by dsimp [M] at *; omega⟩ :=
      Fin.ext (by dsimp [M] at *; omega)
    dsimp only [rComb]
    rw [hidx, QRegister.concat_apply_right, QRegister.slice_apply]
    exact hw ⟨0 + (w.val - C), by omega⟩
  have hSub : P_pre * P_work = P_work := by
    rw [hPwork_eq]
    exact p2d_ketPredProj_mul_imp (fun β hw ↦ ⟨hClOfWork β hw, trivial⟩)
  have hMono := p2d_RealizesConstCleanUnitary_mono_proj (p2d_ketPredProj_conjTranspose _)
      (QRegister.basisOutcomeProjector_conjTranspose rWork 0) hSub hRealDyn
  have hUeq : U_dyn.1 * P_work = (rCore.embedUnitary (uSlot0LocalC2 hmPay w_eff)).1 * P_work := by
    apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPwork_eq, p2d_ketPredProj_mul_ket]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · rw [ite_eq_left hw, hKetDyn β ⟨hClOfWork β hw, trivial⟩]
      let α : BitAssignment C := fun i ↦ β (rCore i)
      have hpad : (fun idx ↦ β (rComb idx)) = padZeroBits (mClean := slot0LocalWorkWires128) α := by
        funext idx
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
        · dsimp only [rComb, padZeroBits, α]
          rw [QRegister.concat_apply_left, Fin.addCases_left]
        · dsimp only [rComb, padZeroBits]
          rw [QRegister.concat_apply_right, Fin.addCases_right, QRegister.slice_apply]
          exact hw ⟨0 + j.val, by omega⟩
      have hwAct : writeRegProg β rCore α = β := by
        funext w
        by_cases hm : w ∈ Set.range rCore.wires
        · obtain ⟨i, rfl⟩ := hm; exact writeRegProg_apply_reg _ _ _ _
        · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
      dsimp only [Φ]
      rw [hpad, hPhase α]
      dsimp only [uSlot0LocalC2]
      rw [QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
      have hEvalAct : ∀ l : Fin (2 ^ C),
          (phaseDiagUnitary (slot0LocalC2PhaseBit hmPay w_eff)).1 l (localIdxProg rCore β) =
            if l = localIdxProg rCore β then
              ((-1 : ℂ) ^ (slot0LocalC2PhaseBit hmPay w_eff α).val) else 0 := by
        intro l
        by_cases hl : l = localIdxProg rCore β
        · subst hl
          have hb : basisBits C (localIdxProg rCore β) = α :=
            (basisBitsEquiv C).apply_symm_apply α
          simp [phaseDiagUnitary]
          rfl
        · simp [phaseDiagUnitary, hl]
      simp_rw [hEvalAct, ite_smul, zero_smul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hbb : basisBits C (localIdxProg rCore β) = α :=
        (basisBitsEquiv C).apply_symm_apply α
      rw [hbb, hwAct]
    · rw [ite_eq_right hw, Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact p2d_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace rCore rWork _ _
    (p2d_RealizesConstCleanUnitary_congr_unitary
      (QRegister.basisOutcomeProjector_conjTranspose rWork 0) hMono hUeq)
set_option allowUnsafeReducibility true in
/-- **`444 T`, `0` `TOFF`, `128`-wire (`≤ mRest`) `DynamicCircuit`
  (`dSlot0LocalXorBit5C2_128_444`)**
realizing `uSlot0LocalXorBit5C2 hm w_eff` on `rCore : QRegister (fullSysCoreWires mPayload) n`. -/
noncomputable def dSlot0LocalXorBit5C2_128_444 {Var : Type} {n mPayload mRest : ℕ}
    (hm : 80 ≤ mPayload) (hRest : slot0LocalWorkWires128 ≤ mRest) (w_eff : ℝ) (v : Var) (rCore
    : QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n)
    (rRest : QRegister mRest n) (hCR : rCore.DisjointWires rRest) : DynamicCircuit Var n :=
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  let rSym := OraAndPrepBundle.coreRegToSym rCore
  let hdisjSym := (OraAndPrepBundle.castNatReg_disjoint hCoreEq.symm rCore rRest).mpr hCR
  let dFlip : DynamicCircuit Var n :=
    .circuit ((Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).onRegister rCore)
  .seq dFlip (.seq (dSlot0LocalWState128 hm hRest w_eff v rSym rRest hdisjSym) dFlip)
@[simp] theorem count_dSlot0LocalXorBit5C2_128_444_toff {Var : Type} {n mPayload mRest : ℕ}
    (hm : 80 ≤ mPayload) (hRest : slot0LocalWorkWires128 ≤ mRest) (w_eff : ℝ) (v : Var) (rCore
    : QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n)
    (rRest : QRegister mRest n) (hCR : rCore.DisjointWires rRest) :
    (dSlot0LocalXorBit5C2_128_444 hm hRest w_eff v rCore rRest hCR).count TOFF = 0 := by
  unfold dSlot0LocalXorBit5C2_128_444
  simp [Circuit.count_onRegister, dSlot0LocalWState128_count_toff]
@[simp] theorem count_dSlot0LocalXorBit5C2_128_444_t {Var : Type} {n mPayload mRest : ℕ}
    (hm : 80 ≤ mPayload) (hRest : slot0LocalWorkWires128 ≤ mRest) (w_eff : ℝ) (v : Var) (rCore
    : QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n)
    (rRest : QRegister mRest n) (hCR : rCore.DisjointWires rRest) :
    (dSlot0LocalXorBit5C2_128_444 hm hRest w_eff v rCore rRest hCR).count .T = 444 := by
  unfold dSlot0LocalXorBit5C2_128_444
  simp [Circuit.count_onRegister, dSlot0LocalWState128_count_t, slot0LocalTCost444]
theorem dSlot0LocalXorBit5C2_128_444_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mRest : ℕ} [NeZero (2 ^ n)] (hm : 80 ≤ mPayload)
    (hRest : slot0LocalWorkWires128 ≤ mRest) (w_eff : ℝ)
    (hw_eff : LiteralKineticAndMidpoint128.elecQuadCenterOffset < w_eff) (v : Var) (rCore :
    QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n)
    (rRest : QRegister mRest n) (hCR : rCore.DisjointWires rRest) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rRest
    (uSlot0LocalXorBit5C2 hm w_eff)
    (dSlot0LocalXorBit5C2_128_444 hm hRest w_eff v rCore rRest hCR) := by
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  have hFlip : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var)
      rCore rRest (Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).eval
      (.circuit ((Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).onRegister rCore)) :=
        by
    apply DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
    exact Circuit.eval_onRegister rCore (Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit
      mPayload)
  have hMid : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var)
      rCore rRest
      (OraAndPrepBundle.coreUnitaryToFullSys (uSlot0LocalC2 hm w_eff))
      (dSlot0LocalWState128 hm hRest w_eff v
        (OraAndPrepBundle.coreRegToSym rCore)
        rRest ((OraAndPrepBundle.castNatReg_disjoint
          hCoreEq.symm rCore rRest).mpr hCR)) :=
    OraAndPrepBundle.castNatReg_realizes hCoreEq.symm rCore rRest _ _
      (dSlot0LocalWState128_realizes hm hRest w_eff hw_eff v _ rRest _)
  have h3 := hFlip.seq hCR (hMid.seq hCR hFlip)
  have hUnitEq : ((Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).eval *
      OraAndPrepBundle.coreUnitaryToFullSys (uSlot0LocalC2 hm w_eff)) *
      (Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).eval =
      uSlot0LocalXorBit5C2 hm w_eff := by
    apply Subtype.ext
    apply matrix_ext_ket
    intro γ
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    dsimp only [OraAndPrepBundle.coreUnitaryToFullSys, uSlot0LocalC2]
    rw[Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit_eval_ket,
        Barrel3PassCommuteHelpers.castNatUnitary_phaseDiag_mulVec_ket hCoreEq,
        Matrix.mulVec_smul, Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit_eval_ket,
        Barrel3PassCommuteHelpers.flipElec0Bit5Fn_involutive mPayload γ]
    exact (Barrel3PassCommuteHelpers.phaseDiagUnitary_mulVec_ket_local
      (slot0LocalC2XorBit5PhaseBit hm w_eff) γ).symm
  rwa [hUnitEq] at h3
end Slot0LocalWState128
attribute [irreducible] ctxSlot0WState128 dSlot0LocalWState128 dSlot0LocalXorBit5C2_128_444
end Pass1InnerAndIdx128Aux
namespace Leaf1Pass1And3OptAux
open Leaf1Pass1And3Opt
section Part2_FusedSlot4AndSlot0_130_584
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open QuantumComputation HermitianMat
open scoped ComplexOrder MatrixOrder Circuit.Notation
open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding basisBits_symm_apply fullSysCoreWires_eq_add zmod2_eq_zero_or_one
open FusedVepCore288
open JunctionApexCSA288 hiding HProjFlag HProjFlag_congr_S wfBitVal_of_HProjFlag HCoin0Flag
  dXor32_spec HSlot4Flag HSlot4Flag_congr_S dSlot4Axis count_dSlot4Axis_toff count_dSlot4Axis_t
  dSlot4Axis_spec dSlot4Axis_biSpec HPos01AndCoin0 dSlot4Conj count_dSlot4Conj_toff
  count_dSlot4Conj_t dSlot4Conj_spec
open Leaf1Pass1And3Width204 (mWork13 compose_rCoreBlock4_eq uPass1InnerT4)
open Pass1Leaf273 (hm22_80 hm80_80)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open MomSlots01Slot0ElectronKinetic (elecQuadCenterOffset_lt_lambdaSlot0TeHi)
open Pass1InnerAndIdx128 (slot0LocalC2XorBit5PhaseBit slot0LocalXorBit5PhaseBit uSlot0LocalXorBit5C2
  uSlot0LocalXorBit5_eq_phaseDiagUnitary)
open Pass1InnerAndIdx128Aux (dSlot0LocalXorBit5C2_128_444 count_dSlot0LocalXorBit5C2_128_444_toff
  count_dSlot0LocalXorBit5C2_128_444_t dSlot0LocalXorBit5C2_128_444_realizes)
/-- **`130`-Wire Fused Coin-Sharing W-State `Slot 4 + Slot 0` Circuit
(`dSlot4AndSlot0FusedT4_130_584`, `4 + 4 + 444 + 132 = 584 T`, `0 TOFF`, `-44 T` below `628 T`)**
on `4` catalyst wires (`rT4 : QRegister 4 n`), realizing `uPass1InnerT4`. -/
noncomputable def dSlot4AndSlot0FusedT4_130_584 {Var : Type} {n mW : ℕ} (hW130 : 130 ≤ mW)
    (v : Var) (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n)
    (rW : QRegister mW n) (hCT4 : rC.DisjointWires rT4) (hCW : rC.DisjointWires rW)
    (hTW : rT4.DisjointWires rW) : DynamicCircuit Var n :=
  let rW13 : QRegister mWork13 n := rW.slice 0 13 (by dsimp [mWork13]; omega)
  let rW128 : QRegister 128 n := rW.slice 2 128 (by omega)
  let hCW13 : rC.DisjointWires rW13 := hCW.compose_right _
  let hTW13 : rT4.DisjointWires rW13 := hTW.compose_right _
  have hCA2 : ∀ i : Wire (fullSysCoreWires 80), rC i ≠ rW13 ⟨1, by decide⟩ :=
    fun i ↦ hCW13.ne i ⟨1, by decide⟩
  let rCSwapC2 := rCoreSubstC2Flag rC (rW13 ⟨1, by decide⟩) hCA2
  have hCSwapC2_W128 : rCSwapC2.DisjointWires rW128 := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    change (if i.val = 3950 then rW ⟨1, by omega⟩ else rC i) = rW ⟨2 + j.val, by omega⟩ at hij
    split_ifs at hij with hi
    · have hv := congrArg Fin.val (rW.wires.injective hij)
      dsimp at hv; omega
    · exact hCW.ne i ⟨2 + j.val, by omega⟩ hij
  have hs0_ne_s2 : wSlot0 rC ≠ wSlot2 rC := by
    unfold wSlot0 wSlot2; exact core_wire_ne rC (by decide)
  have hs1_ne_s2 : wSlot1 rC ≠ wSlot2 rC := by
    unfold wSlot1 wSlot2; exact core_wire_ne rC (by decide)
  have hCore_ne_W13 : ∀ {u : Wire n}, u ∈ (rHigh rC).image → ∀ (i : Fin mWork13), u ≠ rW13 i
      := fun hu i h ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW13) (rHigh_sub_rCore rC hu)
      ((QRegister.mem_image rW13 _).mpr ⟨i, h.symm⟩)
  have hs1_ne_w0 : wSlot1 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot1_mem_rHigh rC) ⟨0, by decide⟩
  have hs2_ne_w0 : wSlot2 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot2_mem_rHigh rC) ⟨0, by decide⟩
  have hs0_ne_w0 : wSlot0 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot0_mem_rHigh rC) ⟨0, by decide⟩
  have hw0_ne_w1 : rW13 ⟨0, by decide⟩ ≠ rW13 ⟨1, by decide⟩ := fun h ↦ by
    cases rW13.wires.injective h
  have hs2_ne_w1 : wSlot2 rC ≠ rW13 ⟨1, by decide⟩ :=
    hCore_ne_W13 (wSlot2_mem_rHigh rC) ⟨1, by decide⟩
  let dInner128 : DynamicCircuit Var n := .seq (dSlot0LocalXorBit5C2_128_444 hm80_80 le_rfl
      lambdaSlot0TeHi v rCSwapC2 rW128 hCSwapC2_W128)
      (dSlot4ConjT4_13_44 false hm22_80 v rC rT4 rW13 hCT4 hCW13 hTW13)
  dXorAndWrap v
    (wSlot1 rC) (wSlot0 rC) (wSlot2 rC)
    (rW13 ⟨0, by decide⟩)
    hs0_ne_s2 hs1_ne_s2 hs1_ne_w0 hs2_ne_w0
    (dPureConj (Circuit.CNOT (wSlot2 rC) (rW13 ⟨0, by decide⟩) hs2_ne_w0)
      (dPureConj (Circuit.CNOT (wSlot0 rC) (rW13 ⟨0, by decide⟩) hs0_ne_w0)
        (dGenBoolWrap false false false v
          (rW13 ⟨0, by decide⟩) (wSlot2 rC) (rW13 ⟨1, by decide⟩)
          hs2_ne_w0.symm hw0_ne_w1 hs2_ne_w1
          dInner128)))
@[simp] theorem count_dSlot4AndSlot0FusedT4_130_584_toff {Var : Type} {n mW : ℕ}
    (hW130 : 130 ≤ mW) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n) (rW : QRegister mW n)
    (hCT4 : rC.DisjointWires rT4) (hCW : rC.DisjointWires rW) (hTW : rT4.DisjointWires rW) :
    (dSlot4AndSlot0FusedT4_130_584 hW130 v rC rT4 rW hCT4 hCW hTW).count TOFF = 0 := by
  unfold dSlot4AndSlot0FusedT4_130_584
  dsimp only
  rw [count_dXorAndWrap_toff,
      count_dPureConj_toff _ (by simp [Circuit.CNOT]),
      count_dPureConj_toff _ (by simp [Circuit.CNOT]),
      count_dGenBoolWrap_toff]
  simp only [DynamicCircuit.count, count_dSlot0LocalXorBit5C2_128_444_toff,
    count_dSlot4ConjT4_13_44_toff]
@[simp] theorem count_dSlot4AndSlot0FusedT4_130_584_t {Var : Type} {n mW : ℕ}
    (hW130 : 130 ≤ mW) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n) (rW : QRegister mW n)
    (hCT4 : rC.DisjointWires rT4) (hCW : rC.DisjointWires rW) (hTW : rT4.DisjointWires rW) :
    (dSlot4AndSlot0FusedT4_130_584 hW130 v rC rT4 rW hCT4 hCW hTW).count .T = 584 := by
  unfold dSlot4AndSlot0FusedT4_130_584
  dsimp only
  rw [count_dXorAndWrap_t,
      count_dPureConj_t _ (by simp [Circuit.CNOT]),
      count_dPureConj_t _ (by simp [Circuit.CNOT]),
      count_dGenBoolWrap_t]
  simp only [DynamicCircuit.count, count_dSlot0LocalXorBit5C2_128_444_t, count_dSlot4ConjT4_13_44_t]
theorem dSlot4AndSlot0FusedT4_130_584_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mW : ℕ} [NeZero (2 ^ n)] (hW130 : 130 ≤ mW) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n) (rW : QRegister mW n)
    (hCT4 : rC.DisjointWires rT4) (hCW : rC.DisjointWires rW) (hTW : rT4.DisjointWires rW) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rC.concat rT4 hCT4) rW
    uPass1InnerT4 (dSlot4AndSlot0FusedT4_130_584 hW130 v rC rT4 rW hCT4 hCW hTW) := by
  let rCT4 := rC.concat rT4 hCT4
  let rW13 : QRegister mWork13 n := rW.slice 0 13 (by dsimp [mWork13]; omega)
  let rW11 := rW13.slice 2 11 (by dsimp [mWork13]; omega)
  let rW128 : QRegister 128 n := rW.slice 2 128 (by omega)
  let rW129 : QRegister 129 n := rW.slice 1 129 (by omega)
  let rW130 : QRegister 130 n := rW.slice 0 130 (by omega)
  let rS2 := rW13.slice 0 2 (by dsimp [mWork13]; omega)
  let S_pres := (rHigh rC).image ∪ rS2.image
  let hCW13 : rC.DisjointWires rW13 := hCW.compose_right _
  let hTW13 : rT4.DisjointWires rW13 := hTW.compose_right _
  have hCA2 : ∀ i : Wire (fullSysCoreWires 80), rC i ≠ rW13 ⟨1, by decide⟩ :=
    fun i ↦ hCW13.ne i ⟨1, by decide⟩
  let rCSwapC2 := rCoreSubstC2Flag rC (rW13 ⟨1, by decide⟩) hCA2
  have hCSwapC2_W128 : rCSwapC2.DisjointWires rW128 := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    change (if i.val = 3950 then rW ⟨1, by omega⟩ else rC i) = rW ⟨2 + j.val, by omega⟩ at hij
    split_ifs at hij with hi
    · have hv := congrArg Fin.val (rW.wires.injective hij)
      dsimp at hv; omega
    · exact hCW.ne i ⟨2 + j.val, by omega⟩ hij
  have hW11_sub_128 : rW11.image ⊆ rW128.image := by
    intro u hu
    rcases (QRegister.mem_image rW11 u).mp hu with ⟨j, rfl⟩
    refine (QRegister.mem_image rW128 _).mpr ⟨⟨j.val, by have := j.isLt; omega⟩, ?_⟩
    exact congrArg rW (Fin.ext (by dsimp [rW11, rW13, rW128, QRegister.slice]; omega))
  have hs4_128 := (CondStageSpecPres.of_condStageSpec
    (dSlot4ConjT4_13_44_shared_spec (Var :=
      Var) v rC rT4 rW13 hCT4 hCW13 hTW13)).widen_workspace hW11_sub_128
  rcases hs4_128.exists_u with ⟨u₂, hw₂, hDiag₂, hKet₂⟩
  let u₁ := rCSwapC2.embedUnitary (uSlot0LocalXorBit5C2 hm80_80 lambdaSlot0TeHi)
  have hw₁ : CleanUnitaryWp rW128 u₁ (dSlot0LocalXorBit5C2_128_444 hm80_80 le_rfl
      lambdaSlot0TeHi v rCSwapC2 rW128 hCSwapC2_W128) := CleanUnitaryWp.of_realizesClean
      (dSlot0LocalXorBit5C2_128_444_realizes hm80_80 le_rfl lambdaSlot0TeHi
      elecQuadCenterOffset_lt_lambdaSlot0TeHi v rCSwapC2 rW128 hCSwapC2_W128)
  have hDiag₁_univ : DiagOn Finset.univ u₁.1 :=
    diagOn_univ_embed_phaseDiagUnitary rCSwapC2 (slot0LocalC2XorBit5PhaseBit hm80_80
      lambdaSlot0TeHi)
  let dInner128 : DynamicCircuit Var n := .seq (dSlot0LocalXorBit5C2_128_444 hm80_80 le_rfl
      lambdaSlot0TeHi v rCSwapC2 rW128 hCSwapC2_W128)
      (dSlot4ConjT4_13_44 false hm22_80 v rC rT4 rW13 hCT4 hCW13 hTW13)
  have hw12 : CleanUnitaryWp rW128 (u₂ * u₁) dInner128 :=
    hw₁.seq_of_diag hw₂ (DiagOn.anti (Finset.subset_univ _) hDiag₁_univ)
  have hDiag12 : DiagOn S_pres (u₂ * u₁).1 :=
    DiagOn.mul hDiag₂ (DiagOn.anti (Finset.subset_univ _) hDiag₁_univ)
  have hsInner128 : CondStageSpecPres rCT4 rW128 S_pres (HSharedCoin04T4 rC rW13)
      uPass1InnerT4 dInner128 := by
    refine ⟨⟨u₂ * u₁, hw12, hDiag12, fun ξ hz128 hH ↦ ?_⟩⟩
    change (u₂.1 * u₁.1).mulVec (basisKet ξ) = _
    rw [← Matrix.mulVec_mulVec]
    have hu1_ket : u₁.1.mulVec (basisKet ξ) =
        ((-1 : ℂ) ^ (slot0LocalXorBit5PhaseBit hm80_80 lambdaSlot0TeHi (fun q ↦
          ξ (rC q))).val) • basisKet ξ := by
      dsimp only [u₁, uSlot0LocalXorBit5C2]
      rw [embed_phaseDiagUnitary_mulVec_basisKet]
      have hBitEq := slot0LocalC2XorBit5PhaseBit_rCoreSubstC2_eq lambdaSlot0TeHi rC
        (rW13 ⟨1, by decide⟩) hCA2 ξ hH.2
      exact congrArg (fun b : ZMod 2 ↦ ((-1 : ℂ) ^ b.val) • basisKet ξ) hBitEq
    rw [hu1_ket, Matrix.mulVec_smul, hKet₂ ξ hz128 hH]
    unfold uPass1InnerT4
    dsimp only [rCT4]
    obtain ⟨c, ξ', hk4, hCoreEq⟩ := embed_uSlot4ApexCatT4_preserves_rCore rC rT4 hCT4 ξ
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ← QRegister.embedUnitary_compose,
      compose_rCoreBlock4_eq rC rT4 hCT4,
      hk4, Matrix.mulVec_smul,
      uSlot0LocalXorBit5_eq_phaseDiagUnitary,
      embed_phaseDiagUnitary_mulVec_basisKet,
      show (fun i ↦ ξ' (rC i)) = (fun i ↦ ξ (rC i)) from funext hCoreEq,
      smul_smul, smul_smul, mul_comm]
  have h128_sub_129 : rW128.image ⊆ rW129.image :=
    slice_sub_slice_b2 rW 2 128 1 129 (by omega) (by omega) (by omega) (by omega)
  have h129_sub_130 : rW129.image ⊆ rW130.image :=
    slice_sub_slice_b2 rW 1 129 0 130 (by omega) (by omega) (by omega) (by omega)
  have hs0_not_W : wSlot0 rC ∉ rW.image := by
    intro hm
    rcases (QRegister.mem_image rW _).mp hm with ⟨j, hj⟩
    exact hCW.ne ⟨3948, by decide⟩ j hj.symm
  have hs1_not_W : wSlot1 rC ∉ rW.image := by
    intro hm
    rcases (QRegister.mem_image rW _).mp hm with ⟨j, hj⟩
    exact hCW.ne ⟨3949, by decide⟩ j hj.symm
  have hs2_not_W : wSlot2 rC ∉ rW.image := by
    intro hm
    rcases (QRegister.mem_image rW _).mp hm with ⟨j, hj⟩
    exact hCW.ne ⟨3950, by decide⟩ j hj.symm
  have hw0_not_CT4 : rW13 ⟨0, by decide⟩ ∉ rCT4.image := by
    rw [qreg_image_concat]; intro hm
    have hw13 : rW13 ⟨0, by decide⟩ ∈ rW13.image := (QRegister.mem_image rW13 _).mpr ⟨0, rfl⟩
    rcases Finset.mem_union.mp hm with hC | hT
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW13) hC hw13
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTW13) hT hw13
  have hw1_not_CT4 : rW13 ⟨1, by decide⟩ ∉ rCT4.image := by
    rw [qreg_image_concat]; intro hm
    have hw13 : rW13 ⟨1, by decide⟩ ∈ rW13.image := (QRegister.mem_image rW13 _).mpr ⟨1, rfl⟩
    rcases Finset.mem_union.mp hm with hC | hT
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW13) hC hw13
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTW13) hT hw13
  have hw0_S : rW13 ⟨0, by decide⟩ ∈ S_pres :=
    Finset.mem_union_right _ ((QRegister.mem_image rS2 _).mpr ⟨0, rfl⟩)
  have hw1_S : rW13 ⟨1, by decide⟩ ∈ S_pres :=
    Finset.mem_union_right _ ((QRegister.mem_image rS2 _).mpr ⟨1, rfl⟩)
  have hs0_S : wSlot0 rC ∈ S_pres := Finset.mem_union_left _ (wSlot0_mem_rHigh rC)
  have hs1_S : wSlot1 rC ∈ S_pres := Finset.mem_union_left _ (wSlot1_mem_rHigh rC)
  have hs2_S : wSlot2 rC ∈ S_pres := Finset.mem_union_left _ (wSlot2_mem_rHigh rC)
  have hs0_ne_s2 : wSlot0 rC ≠ wSlot2 rC := by
    unfold wSlot0 wSlot2; exact core_wire_ne rC (by decide)
  have hs1_ne_s2 : wSlot1 rC ≠ wSlot2 rC := by
    unfold wSlot1 wSlot2; exact core_wire_ne rC (by decide)
  have hs1_ne_s0 : wSlot1 rC ≠ wSlot0 rC := by
    unfold wSlot1 wSlot0; exact core_wire_ne rC (by decide)
  have hCore_ne_W13 : ∀ {u : Wire n}, u ∈ (rHigh rC).image → ∀ (i : Fin mWork13), u ≠ rW13 i
      := fun hu i h ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW13) (rHigh_sub_rCore rC hu)
      ((QRegister.mem_image rW13 _).mpr ⟨i, h.symm⟩)
  have hs1_ne_w0 : wSlot1 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot1_mem_rHigh rC) ⟨0, by decide⟩
  have hs2_ne_w0 : wSlot2 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot2_mem_rHigh rC) ⟨0, by decide⟩
  have hs0_ne_w0 : wSlot0 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot0_mem_rHigh rC) ⟨0, by decide⟩
  have hw0_ne_w1 : rW13 ⟨0, by decide⟩ ≠ rW13 ⟨1, by decide⟩ := fun h ↦ by
    cases rW13.wires.injective h
  have hs2_ne_w1 : wSlot2 rC ≠ rW13 ⟨1, by decide⟩ :=
    hCore_ne_W13 (wSlot2_mem_rHigh rC) ⟨1, by decide⟩
  let H_w0_full : BitAssignment n → Prop := fun η ↦
    η (rW13 ⟨0, by decide⟩) =
      η (wSlot1 rC) * (η (wSlot2 rC) + η (wSlot0 rC)) +
        η (wSlot2 rC) + η (wSlot0 rC)
  have hImp_w1 : ∀ η : BitAssignment n,
      H_w0_full η ∧
        η (rW13 ⟨1, by decide⟩) =
          genBoolBit false false false (η (rW13 ⟨0, by decide⟩)) (η (wSlot2 rC)) →
      HSharedCoin04T4 rC rW13 η := by
    rintro η ⟨hw0, hw1⟩
    exact ⟨hw0, zmod2_shared_coin_slot0 hw0 hw1⟩
  have hH_w0_anc : ∀ ξ₁ ξ₂ : BitAssignment n,
      (∀ w, w ≠ rW13 ⟨1, by decide⟩ → ξ₁ w = ξ₂ w) → H_w0_full ξ₁ → H_w0_full ξ₂ := by
    intro ξ₁ ξ₂ hEq h1
    dsimp only [H_w0_full] at h1 ⊢
    rw [← hEq (rW13 ⟨0, by decide⟩) hw0_ne_w1,
        ← hEq (wSlot1 rC) (hCore_ne_W13 (wSlot1_mem_rHigh rC) ⟨1, by decide⟩),
        ← hEq (wSlot2 rC) hs2_ne_w1,
        ← hEq (wSlot0 rC) (hCore_ne_W13 (wSlot0_mem_rHigh rC) ⟨1, by decide⟩)]
    exact h1
  have hsGen1 := CondStageSpecPres.dGenBoolWrap false false false v
    (rW13 ⟨0, by decide⟩) (wSlot2 rC) (rW13 ⟨1, by decide⟩)
    hs2_ne_w0.symm hw0_ne_w1 hs2_ne_w1
    rW128 rW129 h128_sub_129
    (reg_mem_slice_b2 rW 1 129 (by omega) ⟨1, by omega⟩ (by dsimp; omega) (by dsimp; omega))
    (reg_not_mem_slice_b2 rW 1 129 (by omega) ⟨0, by omega⟩ (by dsimp; omega))
    (fun hm ↦ hs2_not_W (QRegister.image_compose_subset rW _ hm))
    (reg_not_mem_slice_b2 rW 2 128 (by omega) ⟨1, by omega⟩ (by dsimp; omega))
    hw1_not_CT4 hw0_S hs2_S hw1_S hH_w0_anc
    (hsInner128.weaken_H hImp_w1)
  let H_w0_mid : BitAssignment n → Prop := fun η ↦
    η (rW13 ⟨0, by decide⟩) =
      η (wSlot1 rC) * (η (wSlot2 rC) + η (wSlot0 rC)) +
        η (wSlot2 rC)
  have hsCnot0 := CondStageSpecPres.dPureConjCNOT (H_outer := H_w0_mid)
    (wSlot0 rC) (rW13 ⟨0, by decide⟩) hs0_ne_w0
    (fun hm ↦ hs0_not_W (QRegister.image_compose_subset rW _ hm))
    (reg_not_mem_slice_b2 rW 1 129 (by omega) ⟨0, by omega⟩ (by dsimp; omega))
    hw0_not_CT4 hs0_S hw0_S
    (fun ξ hMid ↦ by
      change Function.update ξ (rW13 ⟨0, by decide⟩) (ξ (rW13 ⟨0,
        by decide⟩) + ξ (wSlot0 rC)) (rW13 ⟨0, by decide⟩) = _
      rw[Function.update_self, Function.update_of_ne hs1_ne_w0,
          Function.update_of_ne hs2_ne_w0, Function.update_of_ne hs0_ne_w0]
      exact congrArg (· + ξ (wSlot0 rC)) hMid)
    hsGen1
  let H_w0_base : BitAssignment n → Prop := fun η ↦
    True ∧ η (rW13 ⟨0, by decide⟩) =
      η (wSlot1 rC) * (η (wSlot2 rC) + η (wSlot0 rC))
  have hsCnot2 := CondStageSpecPres.dPureConjCNOT (H_outer := H_w0_base)
    (wSlot2 rC) (rW13 ⟨0, by decide⟩) hs2_ne_w0
    (fun hm ↦ hs2_not_W (QRegister.image_compose_subset rW _ hm))
    (reg_not_mem_slice_b2 rW 1 129 (by omega) ⟨0, by omega⟩ (by dsimp; omega))
    hw0_not_CT4 hs2_S hw0_S
    (fun ξ ⟨_, hBase⟩ ↦ by
      change Function.update ξ (rW13 ⟨0, by decide⟩) (ξ (rW13 ⟨0,
        by decide⟩) + ξ (wSlot2 rC)) (rW13 ⟨0, by decide⟩) = _
      rw[Function.update_self, Function.update_of_ne hs1_ne_w0,
          Function.update_of_ne hs2_ne_w0, Function.update_of_ne hs0_ne_w0]
      exact congrArg (· + ξ (wSlot2 rC)) hBase)
    hsCnot0
  have hsXor0 := CondStageSpecPres.dXorAndWrap v
    (wSlot1 rC) (wSlot0 rC) (wSlot2 rC)
    (rW13 ⟨0, by decide⟩)
    hs0_ne_s2 hs1_ne_s2 hs1_ne_s0 hs1_ne_w0 hs2_ne_w0 hs0_ne_w0
    rW129 rW130 h129_sub_130
    (reg_mem_slice_b2 rW 0 130 (by omega) ⟨0, by omega⟩ (by dsimp; omega) (by dsimp; omega))
    (reg_not_mem_slice_b2 rW 1 129 (by omega) ⟨0, by omega⟩ (by dsimp; omega))
    (fun hm ↦ hs1_not_W (QRegister.image_compose_subset rW _ hm))
    (fun hm ↦ hs0_not_W (QRegister.image_compose_subset rW _ hm))
    (fun hm ↦ hs2_not_W (QRegister.image_compose_subset rW _ hm))
    hw0_not_CT4 hs1_S hs0_S hs2_S hw0_S
    (fun _ _ _ _ ↦ trivial)
    hsCnot2
  exact hsXor0.to_realizesClean.widenWorkspace
end Part2_FusedSlot4AndSlot0_130_584
attribute [irreducible] dSlot4AndSlot0FusedT4_130_584
end Leaf1Pass1And3OptAux
namespace SingleBarrel7StepSelectAux
section ConfigFusedSlot4
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
open SpecsAux SpecsAux.SpecMirror
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires FullSysQft654Bundle
  FullSysSelectOracleBundle)
open CoinDispatchedBarrel288 (uBarrelFast)
open Pass1Leaf273 (uPass1Cat uPass3Cat)
open Barrel3PassSelectStitch (rCTSeg rCoreSeg uTrailCliffordXor80)
set_option exponentiation.threshold 8192 in
/-- Combined `Pass 1 + QFT + Pass 2 + QFT⁻¹ + Pass 3` unitary on `fullSysBEWires 80 + 48`:
realized by the single-barrel 7-step momentum-basis circuit `dFoldedPass123`. -/
noncomputable def uFoldedPass123Seg (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (uPosPhase0 : Unitary (2 ^ (fullSysCoreWires 80))) : Unitary
    (2 ^ (fullSysBEWires 80 + 48)) := rCTSeg.embedUnitary uPass3Cat * (rCoreSeg.embedUnitary
    uTrailCliffordXor80⁻¹ * ((Barrel3PassSelectStitch.rQSeg selOra).embedUnitary qft.uQftCat⁻¹
    * (rCoreSeg.embedUnitary (unitaryConj (uBarrelFast (le_refl 80)) uPosPhase0) *
    ((Barrel3PassSelectStitch.rQSeg selOra).embedUnitary qft.uQftCat * (rCoreSeg.embedUnitary
    uTrailCliffordXor80 * rCTSeg.embedUnitary uPass1Cat)))))
end ConfigFusedSlot4
end SingleBarrel7StepSelectAux
namespace SingleBarrelPass123Fold
noncomputable section
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires fullSysRawAncWires FullSysQft654Bundle
  fullSysQftCoreUnitary)
open CoinDispatchedBarrel288 (uBarrelFast)
open Barrel3PassCommuteHelpers (uXor32Core_comm_uBarrelFast)
open Barrel3PassSelectStitch (uTrailCliffordXor80)
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermUnitary_apply)
open SpecsAux.BridgeFermionicComm (permutationUnitary_apply)
open InterWalkRSum42Hoist (qreg_ext)
open Leaf1Pass1And3Width204 (rCoreBlock4 t4CarryExp t4WinPerm t4WinPerm_apply uApexShift4
  uSlot4ApexCatT4 uSlot4AxisCatT4)
open Leaf4Ext48TopStitch (CommutesWithReg commutesWithReg_fwdPermUnitary)
open SelectExtStitch (h22_80 h6_80)
open SelectPass13Gen (commutesWithReg_diagonal_of_agreeOutside t4WinPerm_symm_eq)
section Part1Spectator217Comm
set_option maxRecDepth 4096
theorem h3924_core80 : 18 + 3906 ≤ fullSysCoreWires 80 := by decide
/-- The `3,906`-wire register `[18 .. 3924)` holding all `217` non-anchor electrons `e ∈ {1..217}`
inside `fullSysCoreWires 80 = 4,034`. -/
def rSpectatorElec3906 : QRegister 3906 (fullSysCoreWires 80) :=
  QRegister.block 18 3906 h3924_core80
theorem h3924_core80Cat4 : 18 + 3906 ≤ fullSysCoreWires 80 + 4 := by decide
/-- The `3,906`-wire register `[18 .. 3924)` holding all `217` non-anchor electrons `e ∈ {1..217}`
inside `fullSysCoreWires 80 + 4 = 4,038`. -/
def rSpectatorElec3906Cat4 : QRegister 3906 (fullSysCoreWires 80 + 4) :=
  QRegister.block 18 3906 h3924_core80Cat4
theorem not_mem_rSpectatorElec3906_of_val {w : Wire (fullSysCoreWires 80)}
    (hw : w.val < 18 ∨ 3924 ≤ w.val) : w ∉ Set.range rSpectatorElec3906.wires := by
  rintro ⟨t, ht⟩
  have h0 := congrArg Fin.val ht
  simp [rSpectatorElec3906, QRegister.block, Fin.castLEEmb, Fin.natAddEmb] at h0
  have := t.isLt
  omega
theorem rCoreBlock4_compose_rSpectatorElec3906 :
    (rCoreBlock4 80).compose rSpectatorElec3906 = rSpectatorElec3906Cat4 := by
  apply qreg_ext; intro t
  ext; simp [rCoreBlock4, rSpectatorElec3906, rSpectatorElec3906Cat4, QRegister.block]
theorem slot0LocalPhaseBit_congr_outside_spectator3906 (w_eff : ℝ)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ w ∉ Set.range rSpectatorElec3906.wires, γ₁ w = γ₂ w) :
    MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit (le_refl 80)
    w_eff γ₁ = MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit
    (le_refl 80) w_eff γ₂ := by
  have hAt : ∀ w : Wire (fullSysCoreWires 80), (w.val < 18 ∨ 3924 ≤ w.val) → γ₁ w = γ₂ w :=
    fun w hw ↦ ho w (not_mem_rSpectatorElec3906_of_val hw)
  have hc0 : γ₁ ⟨SpecsAux.SpecMirror.systemQubits, by dsimp [fullSysCoreWires, fullSysBEWires,
      fullSysRawAncWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega⟩ =
      γ₂ ⟨SpecsAux.SpecMirror.systemQubits, _⟩ :=
        hAt _ (Or.inr (by dsimp [SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]; omega))
  have hc1 : γ₁ ⟨SpecsAux.SpecMirror.systemQubits + 1, by dsimp [fullSysCoreWires, fullSysBEWires,
      fullSysRawAncWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega⟩ =
      γ₂ ⟨SpecsAux.SpecMirror.systemQubits + 1, _⟩ :=
        hAt _ (Or.inr (by dsimp [SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]; omega))
  have hc2 : γ₁ ⟨SpecsAux.SpecMirror.systemQubits + 2, by dsimp [fullSysCoreWires, fullSysBEWires,
      fullSysRawAncWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega⟩ =
      γ₂ ⟨SpecsAux.SpecMirror.systemQubits + 2, _⟩ :=
        hAt _ (Or.inr (by dsimp [SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]; omega))
  have hPay : ∀ k : Fin 80,
      γ₁ (MomSlots01Slot1ProjKinetic.corePayloadSym 80 k) =
      γ₂ (MomSlots01Slot1ProjKinetic.corePayloadSym 80 k) :=
    fun k ↦ hAt _ (Or.inr (by
      change 3924 ≤ 3954 + k.val
      omega))
  have hBits : ∀ (x : ℕ) (h : ∀ b : Fin 6, 6 * (x % 3) + b.val < fullSysCoreWires 80),
      (fun b : Fin 6 ↦ γ₁ ⟨6 * (x % 3) + b.val, h b⟩) =
      (fun b : Fin 6 ↦ γ₂ ⟨6 * (x % 3) + b.val, h b⟩) :=
    fun x h ↦ funext fun b ↦ hAt _ (Or.inl (by
      change 6 * (x % 3) + b.val < 18
      have := Nat.mod_lt x (by decide : 0 < 3)
      have := b.isLt
      omega))
  dsimp only [MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit]
  simp only [hc0, hc1, hc2, hPay, hBits]
theorem slot4Sgn_congr_outside_spectator3906 (isInv : Bool) (w : Fin 3)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ q ∉ Set.range rSpectatorElec3906.wires, γ₁ q = γ₂ q) :
    JunctionApexCSA288.slot4Sgn isInv h22_80 w γ₁ =
      JunctionApexCSA288.slot4Sgn isInv h22_80 w γ₂ := by
  have hb1_val : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rCosetB1 h22_80
        (QRegExt.idReg (fullSysCoreWires 80)) u).val < 18 ∨
      3924 ≤ (NuclearTwistAndXor654Concrete.rCosetB1 h22_80
        (QRegExt.idReg (fullSysCoreWires 80)) u).val := by
    decide
  have hb0_val : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rCosetB0 h22_80
        (QRegExt.idReg (fullSysCoreWires 80)) u).val < 18 ∨
      3924 ≤ (NuclearTwistAndXor654Concrete.rCosetB0 h22_80
        (QRegExt.idReg (fullSysCoreWires 80)) u).val := by
    decide
  have hs2 : γ₁ (NuclearTwistAndXor654Concrete.wSlot2
      (QRegExt.idReg (fullSysCoreWires 80))) =
      γ₂ (NuclearTwistAndXor654Concrete.wSlot2
      (QRegExt.idReg (fullSysCoreWires 80))) :=
    ho _ (not_mem_rSpectatorElec3906_of_val (by decide))
  have hs1 : γ₁ (NuclearTwistAndXor654Concrete.wSlot1
      (QRegExt.idReg (fullSysCoreWires 80))) =
      γ₂ (NuclearTwistAndXor654Concrete.wSlot1
      (QRegExt.idReg (fullSysCoreWires 80))) :=
    ho _ (not_mem_rSpectatorElec3906_of_val (by decide))
  have hs0 : γ₁ (NuclearTwistAndXor654Concrete.wSlot0
      (QRegExt.idReg (fullSysCoreWires 80))) =
      γ₂ (NuclearTwistAndXor654Concrete.wSlot0
      (QRegExt.idReg (fullSysCoreWires 80))) :=
    ho _ (not_mem_rSpectatorElec3906_of_val (by decide))
  have hb1 : γ₁ (NuclearTwistAndXor654Concrete.rCosetB1 h22_80
      (QRegExt.idReg (fullSysCoreWires 80)) w) =
      γ₂ (NuclearTwistAndXor654Concrete.rCosetB1 h22_80
      (QRegExt.idReg (fullSysCoreWires 80)) w) :=
    ho _ (not_mem_rSpectatorElec3906_of_val (hb1_val w))
  have hb0 : γ₁ (NuclearTwistAndXor654Concrete.rCosetB0 h22_80
      (QRegExt.idReg (fullSysCoreWires 80)) w) =
      γ₂ (NuclearTwistAndXor654Concrete.rCosetB0 h22_80
      (QRegExt.idReg (fullSysCoreWires 80)) w) :=
    ho _ (not_mem_rSpectatorElec3906_of_val (hb0_val w))
  dsimp only [JunctionApexCSA288.slot4Sgn]
  simp only [hs2, hs1, hs0, hb1, hb0]
theorem slot4LowShift_congr_outside_spectator3906 (isInv : Bool) (w : Fin 3)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ q ∉ Set.range rSpectatorElec3906.wires, γ₁ q = γ₂ q) :
    JunctionApexCSA288.slot4LowShift isInv h22_80 w γ₁ =
      JunctionApexCSA288.slot4LowShift isInv h22_80 w γ₂ := by
  have hEl_val : ∀ (u : Fin 3) (j : Fin 4),
      (((NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 u).slice 0 4 (by omega)) j).val < 18 ∨
      3924 ≤ (((NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 u).slice 0 4 (by omega)) j).val := by
    decide
  have hSgn := slot4Sgn_congr_outside_spectator3906 isInv w ho
  have hEl : ∀ j : Fin 4,
      γ₁ (((NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 w).slice 0 4 (by omega)) j) =
      γ₂ (((NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 w).slice 0 4 (by omega)) j) :=
    fun j ↦ ho _ (not_mem_rSpectatorElec3906_of_val (hEl_val w j))
  have hReg : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      ((NuclearTwistAndXor654Concrete.rElecSlotAxis
      (QRegExt.idReg (fullSysCoreWires 80))
      0 w).slice 0 4 (by omega)) γ₁ = _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      ((NuclearTwistAndXor654Concrete.rElecSlotAxis
      (QRegExt.idReg (fullSysCoreWires 80))
      0 w).slice 0 4 (by omega)) γ₂ := by
    unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    congr 1; funext j; exact hEl j
  dsimp only [JunctionApexCSA288.slot4LowShift]
  rw [hSgn, hReg]
theorem slot4TopExp_congr_outside_spectator3906 (isInv : Bool) (w : Fin 3)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ q ∉ Set.range rSpectatorElec3906.wires, γ₁ q = γ₂ q) :
    JunctionApexCSA288.slot4TopExp isInv h22_80 w γ₁ =
      JunctionApexCSA288.slot4TopExp isInv h22_80 w γ₂ := by
  have he4_val : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 u 4).val < 18 ∨
      3924 ≤ (NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 u 4).val := by
    decide
  have he5_val : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 u 5).val < 18 ∨
      3924 ≤ (NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (fullSysCoreWires 80))
        0 u 5).val := by
    decide
  have hSgn := slot4Sgn_congr_outside_spectator3906 isInv w ho
  have he4 : γ₁ (NuclearTwistAndXor654Concrete.rElecSlotAxis
      (QRegExt.idReg (fullSysCoreWires 80))
      0 w 4) = γ₂ (NuclearTwistAndXor654Concrete.rElecSlotAxis
      (QRegExt.idReg (fullSysCoreWires 80))
      0 w 4) := ho _ (not_mem_rSpectatorElec3906_of_val (he4_val w))
  have he5 : γ₁ (NuclearTwistAndXor654Concrete.rElecSlotAxis
      (QRegExt.idReg (fullSysCoreWires 80))
      0 w 5) = γ₂ (NuclearTwistAndXor654Concrete.rElecSlotAxis
      (QRegExt.idReg (fullSysCoreWires 80))
      0 w 5) := ho _ (not_mem_rSpectatorElec3906_of_val (he5_val w))
  dsimp only [JunctionApexCSA288.slot4TopExp]
  rw [hSgn, he4, he5]
theorem commutesWithReg_rSpectatorElec3906Cat4_uApexShift4
    (δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (hδ : ∀ {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)},
      (∀ q ∉ Set.range rSpectatorElec3906.wires, γ₁ q = γ₂ q) → δ γ₁ = δ γ₂) :
    CommutesWithReg rSpectatorElec3906Cat4 (uApexShift4 (fullSysCoreWires 80) δ).1 := by
  have hCastNotMem : ∀ {q : Wire (fullSysCoreWires 80)}, q ∉ Set.range rSpectatorElec3906.wires →
      Fin.castAdd 4 q ∉ Set.range rSpectatorElec3906Cat4.wires := by
    intro q hq ⟨t, ht⟩
    apply hq
    refine ⟨t, Fin.ext ?_⟩
    have hv := congrArg Fin.val ht
    simpa [rSpectatorElec3906, rSpectatorElec3906Cat4, QRegister.block] using hv
  have hNatNotMem : ∀ k : Fin 4,
      Fin.natAdd (fullSysCoreWires 80) k ∉ Set.range rSpectatorElec3906Cat4.wires := by
    intro k ⟨t, ht⟩
    have hv := congrArg Fin.val ht
    have hk := k.isLt; have ht' := t.isLt
    dsimp [rSpectatorElec3906Cat4, QRegister.block, Fin.castLEEmb, Fin.natAddEmb,
      fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
      SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hv
    omega
  have hPermAux : ∀ (δ' : BitAssignment (fullSysCoreWires 80) → ℤ), (∀ {γ₁ γ₂ : BitAssignment
      (fullSysCoreWires 80)}, (∀ q ∉ Set.range rSpectatorElec3906.wires, γ₁ q = γ₂ q) → δ' γ₁
      = δ' γ₂) → (∀ x : Fin (2 ^ (fullSysCoreWires 80 + 4)),
      rSpectatorElec3906Cat4.extractIndex (t4WinPerm (fullSysCoreWires 80) δ' x) =
      rSpectatorElec3906Cat4.extractIndex x) ∧ (∀ x y : Fin (2 ^ (fullSysCoreWires 80 + 4)),
      rSpectatorElec3906Cat4.AgreeOutside x y → rSpectatorElec3906Cat4.AgreeOutside (t4WinPerm
      (fullSysCoreWires 80) δ' x) (t4WinPerm (fullSysCoreWires 80) δ' y)) := by
    intro δ' hδ'
    have hSysBits : ∀ z : Fin (2 ^ (fullSysCoreWires 80 + 4)),
        (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 z).1 =
          fun i ↦ basisBits (fullSysCoreWires 80 + 4) z (Fin.castAdd 4 i) := by
      intro z
      let p := DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 z
      have hz : z = (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4).symm (p.1, p.2) := by
        dsimp only [p]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
      funext i
      conv_rhs => rw [hz,
        JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
    have hCatBits : ∀ z : Fin (2 ^ (fullSysCoreWires 80 + 4)),
        basisBits 4 (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 z).2 =
          fun k ↦ basisBits (fullSysCoreWires 80 + 4) z (Fin.natAdd (fullSysCoreWires 80) k) := by
      intro z
      let p := DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 z
      have hz : z = (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4).symm (p.1, p.2) := by
        dsimp only [p]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
      funext k
      conv_rhs => rw [hz,
        JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_natAdd]
    refine ⟨fun x ↦ ?_, fun x y ho q ↦ ?_⟩
    · apply (basisBitsEquiv 3906).injective; funext t
      change basisBits 3906 _ t = basisBits 3906 _ t
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      have hrc : rSpectatorElec3906Cat4 t = Fin.castAdd 4 (rSpectatorElec3906 t) := by
        ext; simp [rSpectatorElec3906Cat4, rSpectatorElec3906, QRegister.block]
      rw [hrc, t4WinPerm_apply,
        JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
      exact congrFun (hSysBits x) (rSpectatorElec3906 t)
    · refine Fin.addCases (fun i hqi ↦ ?_) (fun k _ ↦ ?_) q
      · rw [t4WinPerm_apply, t4WinPerm_apply,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd,
          hSysBits x, hSysBits y]
        exact ho (Fin.castAdd 4 i) hqi
      · have hCatEq : (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 x).2 =
            (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 y).2 := by
          apply (basisBitsEquiv 4).injective
          change basisBits 4 _ = basisBits 4 _
          rw [hCatBits x, hCatBits y]
          funext l; exact ho _ (hNatNotMem l)
        have hDelEq : δ' (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 x).1 =
            δ' (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 y).1 := by
          rw [hSysBits x, hSysBits y]
          exact hδ' fun c hc ↦ ho (Fin.castAdd 4 c) (hCastNotMem hc)
        rw [t4WinPerm_apply, t4WinPerm_apply,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_natAdd,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_natAdd,
          hCatEq, hDelEq]
  unfold uApexShift4
  rw [Submonoid.coe_mul]
  have hFwdEq : (Operator.permutationUnitary (t4WinPerm (fullSysCoreWires 80) δ)).1 =
      (fwdPermUnitary (t4WinPerm (fullSysCoreWires 80) δ)).1 := by
    ext a b; rw [permutationUnitary_apply, fwdPermUnitary_apply]; simp only [eq_comm]
  refine CommutesWithReg.mul ?_ ?_
  · rw [hFwdEq]
    refine commutesWithReg_fwdPermUnitary rSpectatorElec3906Cat4 _
      (hPermAux δ hδ).1 (hPermAux δ hδ).2 ?_
    rw [t4WinPerm_symm_eq]
    exact (hPermAux (fun γ ↦ -δ γ) fun ho ↦ congrArg Neg.neg (hδ ho)).2
  · exact commutesWithReg_diagonal_of_agreeOutside rSpectatorElec3906Cat4 _ fun i j ho ↦ by
      congr 1
      unfold t4CarryExp
      have h1 : (fun k : Fin 4 ↦ basisBits (fullSysCoreWires 80 + 4) i (Fin.natAdd
          (fullSysCoreWires 80) k)) = (fun k : Fin 4 ↦ basisBits (fullSysCoreWires 80 + 4) j
          (Fin.natAdd (fullSysCoreWires 80) k)) := funext fun k ↦ ho _ (hNatNotMem k)
      have h2 : δ (fun c ↦ basisBits (fullSysCoreWires 80 + 4) i (Fin.castAdd 4 c)) =
          δ (fun c ↦ basisBits (fullSysCoreWires 80 + 4) j (Fin.castAdd 4 c)) :=
        hδ fun c hc ↦ ho (Fin.castAdd 4 c) (hCastNotMem hc)
      rw [h1, h2]
/-- **Spectator 217-Electron Commutation Theorem for `uSlot4ApexCatT4` (`0 sorry`)**:
`uSlot4ApexCatT4` (`Pass 1` / `Pass 3` `Slot 4` inner unitary on `fullSysCoreWires 80 + 4`)
commutes with ANY operator embedded on the `217` spectator electrons `rSpectatorElec3906Cat4`
(`[18 .. 3924)`). -/
theorem commutesWithReg_rSpectatorElec3906Cat4_uSlot4ApexCatT4 :
    CommutesWithReg rSpectatorElec3906Cat4 (uSlot4ApexCatT4 h22_80).1 := by
  have hAx : ∀ w : Fin 3,
      CommutesWithReg rSpectatorElec3906Cat4 (uSlot4AxisCatT4 false h22_80 w).1 :=
    fun w ↦ by
      unfold uSlot4AxisCatT4
      rw [Submonoid.coe_mul]
      refine (commutesWithReg_rSpectatorElec3906Cat4_uApexShift4 _
        (slot4LowShift_congr_outside_spectator3906 false w)).mul ?_
      rw [QRegister.embedUnitary_val, ← rCoreBlock4_compose_rSpectatorElec3906]
      refine CommutesWithReg.embedMatrix (rCoreBlock4 80) ?_
      exact commutesWithReg_diagonal_of_agreeOutside rSpectatorElec3906 _ fun i j ho ↦ by
        rw [slot4TopExp_congr_outside_spectator3906 false w ho]
  unfold uSlot4ApexCatT4
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  exact (hAx 2).mul ((hAx 1).mul (hAx 0))
end Part1Spectator217Comm
section Part2SingleBarrelPass123Fold
set_option maxRecDepth 65536
/-- `uTrailCliffordXor80` commutes with `uBarrelFast (le_refl 80)`. -/
theorem uTrailCliffordXor80_comm_uBarrelFast : uTrailCliffordXor80 * uBarrelFast (le_refl 80)
    = uBarrelFast (le_refl 80) * uTrailCliffordXor80 := by
  apply Subtype.ext
  exact DyadicQft64WalkCircuit.comm_mul_op
    (uXor32Core_comm_uBarrelFast (le_refl 80))
    (Barrel3PassCommuteHelpers.uPreDiagCliffordCore_comm_uBarrelFast (le_refl 80))
/-- For any `qft : FullSysQft654Bundle` commuting with `uBarrelFast`, the combined QFT + trail
Clifford unitary `fullSysQftCoreUnitary h6_80 qft * uTrailCliffordXor80` commutes with `uBarrelFast
(le_refl 80)`. -/
theorem qft_mul_uTrailCliffordXor80_comm_uBarrelFast (qft : FullSysQft654Bundle) (hQft :
    qft.uQft654 =
    CoreQftHadamardPrunedCore.coreQftHadamardPrunedBundle128.uQft654)
    : (fullSysQftCoreUnitary h6_80 qft * uTrailCliffordXor80) * uBarrelFast (le_refl 80) =
    uBarrelFast (le_refl 80) * (fullSysQftCoreUnitary h6_80 qft * uTrailCliffordXor80) := by
  have hQ : fullSysQftCoreUnitary h6_80 qft * uBarrelFast (le_refl 80) =
      uBarrelFast (le_refl 80) * fullSysQftCoreUnitary h6_80 qft :=
    SchedBranchStitchGen.fullSysQftCoreIdeal80_comm_uBarrelFast
      h6_80 qft hQft
  have hC := uTrailCliffordXor80_comm_uBarrelFast
  apply Subtype.ext
  have hQ0 := congrArg Subtype.val hQ
  have hC0 := congrArg Subtype.val hC
  simp only [Submonoid.coe_mul] at hQ0 hC0 ⊢
  rw [Matrix.mul_assoc, hC0, ← Matrix.mul_assoc, hQ0, Matrix.mul_assoc]
end Part2SingleBarrelPass123Fold
end
end SingleBarrelPass123Fold
namespace SingleBarrelPass123FoldOnStep
section ConfigK9
set_option maxRecDepth 65536
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open Pass1Leaf273 (hm22_80)
open Leaf1Pass1And3Width204 (uSlot4ApexCatT4)
open Leaf1Pass1And3Opt (dSlot4StandaloneT4_13 count_dSlot4StandaloneT4_13_toff
  count_dSlot4StandaloneT4_13_t dSlot4StandaloneT4_13_realizes)
/-- Unbarreled `Pass 3` inner circuit (`140 T`, `0 TOFF`, `13 ≤ mRest`) acting on `rC.concat rT4`,
omitting `Pass 3`'s `8,696 T` barrel swap network. -/
noncomputable def dFoldedPass3InnerT4 {Var : Type} {n mRest : ℕ} (hRest13 : 13 ≤ mRest)
    (v : Var) (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n)
    (rRest : QRegister mRest n) (hCT4 : rC.DisjointWires rT4) (hCR : rC.DisjointWires rRest)
    (hTR : rT4.DisjointWires rRest) : DynamicCircuit Var n := dSlot4StandaloneT4_13 true
    hm22_80 hRest13 v rC rT4 rRest hCT4 hCR hTR
@[simp] theorem count_dFoldedPass3InnerT4_toff {Var : Type} {n mRest : ℕ}
    (hRest13 : 13 ≤ mRest) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n) (rRest : QRegister mRest n)
    (hCT4 : rC.DisjointWires rT4) (hCR : rC.DisjointWires rRest) (hTR : rT4.DisjointWires rRest) :
    (dFoldedPass3InnerT4 hRest13 v rC rT4 rRest hCT4 hCR hTR).count TOFF = 0 :=
  count_dSlot4StandaloneT4_13_toff ..
@[simp] theorem count_dFoldedPass3InnerT4_t {Var : Type} {n mRest : ℕ}
    (hRest13 : 13 ≤ mRest) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n) (rRest : QRegister mRest n)
    (hCT4 : rC.DisjointWires rT4) (hCR : rC.DisjointWires rRest) (hTR : rT4.DisjointWires rRest) :
    (dFoldedPass3InnerT4 hRest13 v rC rT4 rRest hCT4 hCR hTR).count .T = 140 :=
  count_dSlot4StandaloneT4_13_t ..
theorem dFoldedPass3InnerT4_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mRest : ℕ} [NeZero (2 ^ n)] (hRest13 : 13 ≤ mRest) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n)
    (rRest : QRegister mRest n) (hCT4 : rC.DisjointWires rT4) (hCR : rC.DisjointWires rRest)
    (hTR : rT4.DisjointWires rRest) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rC.concat rT4 hCT4) rRest (uSlot4ApexCatT4 hm22_80)⁻¹
    (dFoldedPass3InnerT4 hRest13 v rC rT4 rRest hCT4 hCR hTR) :=
    dSlot4StandaloneT4_13_realizes true hm22_80 hRest13 v rC rT4 rRest hCT4 hCR hTR
end ConfigK9
end SingleBarrelPass123FoldOnStep
namespace FullConcrete7StepAndTrueSwapSelect
section Config06c
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
/-- `0-T`, `0-TOFF` circuit applying `Circuit.H` to the first `m` wires of `Fin k`. -/
def cHadamardPrefix {k : ℕ} : (m : ℕ) → (hm : m ≤ k) → Circuit k
  | 0, _ => .identity
  | m + 1, hm =>
      cHadamardPrefix m (Nat.le_of_succ_le hm) ;;ᶜ Circuit.H ⟨m, hm⟩
@[simp] theorem count_cHadamardPrefix_toff {k : ℕ} :
    ∀ (m : ℕ) (hm : m ≤ k), (cHadamardPrefix m hm).count TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cHadamardPrefix]
      rw [Circuit.count_seq, count_cHadamardPrefix_toff m (Nat.le_of_succ_le hm)]
      rfl
@[simp] theorem count_cHadamardPrefix_t {k : ℕ} :
    ∀ (m : ℕ) (hm : m ≤ k), (cHadamardPrefix m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cHadamardPrefix]
      rw [Circuit.count_seq, count_cHadamardPrefix_t m (Nat.le_of_succ_le hm)]
      rfl
/-- `0-T`, `0-TOFF` Hadamard unitary across all `k` wires of `Fin k`. -/
noncomputable def uHadamardAll (k : ℕ) : Unitary (2 ^ k) := (cHadamardPrefix k le_rfl).eval
/-- `0-T`, `0-TOFF` Hadamard sweep across all `k` wires of `r : QRegister k n`. -/
def cHadamardAll {k n : ℕ} (r : QRegister k n) : Circuit n :=
  (cHadamardPrefix k le_rfl).onRegister r
@[simp] theorem count_cHadamardAll_toff {k n : ℕ} (r : QRegister k n) :
    (cHadamardAll r).count TOFF = 0 := by
  dsimp only [cHadamardAll]
  rw [Circuit.count_onRegister, count_cHadamardPrefix_toff]
@[simp] theorem count_cHadamardAll_t {k n : ℕ} (r : QRegister k n) :
    (cHadamardAll r).count .T = 0 := by
  dsimp only [cHadamardAll]
  rw [Circuit.count_onRegister, count_cHadamardPrefix_t]
theorem eval_cHadamardAll {k n : ℕ} (r : QRegister k n) : (cHadamardAll r).eval =
    r.embedUnitary (uHadamardAll k) := Circuit.eval_onRegister r (cHadamardPrefix k le_rfl)
end Config06c
end FullConcrete7StepAndTrueSwapSelect
namespace HeldStreamFoldedPass123Bridge
section Impl07f
set_option maxRecDepth 65536
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistRealizes (uXor32Core)
open Barrel3PassCommuteHelpers (uSlot0LocalXorBit5)
open InterWalkRSum42Hoist (rAct0 rSegFull rCTOrig E_rawStream42 rCTFull_eq_compose PreservesFeature
  FixesLow3924 PreservesRawStream42 low3924Bits preservesFeature_permutationUnitary
  fixesLow3924_embedMatrix_prefix isLow3924Prefix_block0 isLow3924Prefix_rCTOrig h3924_core
  h3924_cat embedAct0_comm_E_rawStream42)
open Barrel3PassSelectStitch (rCTSeg rSegFull_compose_rCTSeg)
open Leaf1Pass1And3Width204 (selCT4InCT t4WinPerm t4WinPerm_symm_apply stepT4Fin uApexShift4
  uSlot4ApexCatT4 uSlot4AxisCatT4)
open Leaf4Ext48TopStitch
open SelectExtStitch (h22_80)
theorem rCTSeg_comm_E_rawStream42_of_preservesRaw
    {U : Unitary (2 ^ (fullSysCoreWires 80 + 48))} (hU : PreservesRawStream42 h3924_cat U.1) :
    (rSegFull.embedUnitary (rCTSeg.embedUnitary U)).1 * E_rawStream42 =
      E_rawStream42 * (rSegFull.embedUnitary (rCTSeg.embedUnitary U)).1 := by
  have hEq : rSegFull.compose rCTSeg = rAct0.compose rCTOrig :=
    rSegFull_compose_rCTSeg.trans rCTFull_eq_compose
  rw [← QRegister.embedUnitary_compose, hEq, QRegister.embedUnitary_compose]
  refine embedAct0_comm_E_rawStream42 ?_
  rw [QRegister.embedUnitary_val]
  exact preservesRawStream42_embedMatrix_prefix isLow3924Prefix_rCTOrig hU
theorem h3924_ct4 : 3924 ≤ fullSysCoreWires 80 + 4 := h3924_core.trans (Nat.le_add_right _ 4)
theorem perm_conj_diagonal_eq {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : Fin N → ℂ) :
    ((Operator.permutationUnitary σ)⁻¹).1 * Matrix.diagonal d * (Operator.permutationUnitary σ).1 =
      Matrix.diagonal (fun j ↦ d (σ j)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · rw [SpecsAux.BridgeFermionicComm.permutationUnitary_apply,
      ite_eq_left rfl, mul_one,
      Matrix.mul_diagonal]
    have hInv : ((Operator.permutationUnitary σ)⁻¹).1 i (σ j) =
        ((Operator.permutationUnitary σ).1ᴴ) i (σ j) := by
      rw [← Matrix.star_eq_conjTranspose]; rfl
    rw [hInv, Matrix.conjTranspose_apply,
      SpecsAux.BridgeFermionicComm.permutationUnitary_apply]
    by_cases hij : i = j
    · subst hij; rw [ite_eq_left rfl, star_one, one_mul, Matrix.diagonal_apply_eq]
    · rw [ite_eq_right (fun h ↦ hij (σ.injective h.symm)), star_zero, zero_mul,
        Matrix.diagonal_apply_ne _ hij]
  · intro z _ hzj
    rw [SpecsAux.BridgeFermionicComm.permutationUnitary_apply,
      ite_eq_right hzj, mul_zero]
  · intro h; exact (h (Finset.mem_univ _)).elim
theorem fixesLow3924_uSlot0LocalXorBit5 : FixesLow3924 h3924_core (uSlot0LocalXorBit5 (le_refl
    80) LiteralKineticAndMidpoint128.lambdaSlot0TeHi).1 := by
  unfold uSlot0LocalXorBit5 unitaryConj uXor32Core
  have hDiag : (OraAndPrepBundle.coreUnitaryToFullSys
      (MomSlot0LocalAndMomCombine288.uSlot0Local (le_refl 80)
        LiteralKineticAndMidpoint128.lambdaSlot0TeHi)).1 =
      Matrix.diagonal (fun g ↦ (-1 : ℂ) ^
        (MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit (le_refl 80)
          LiteralKineticAndMidpoint128.lambdaSlot0TeHi
          (basisBits (fullSysCoreWires 80) g)).val) := rfl
  rw [Submonoid.coe_mul, Submonoid.coe_mul, hDiag, perm_conj_diagonal_eq]
  exact PreservesFeature.diagonal _ _
theorem fixesLow3924_uApexShift4 (δ : BitAssignment (fullSysCoreWires 80) → ℤ) :
    FixesLow3924 h3924_ct4 (uApexShift4 (fullSysCoreWires 80) δ).1 := by
  unfold uApexShift4
  refine (preservesFeature_permutationUnitary _ (t4WinPerm (fullSysCoreWires 80) δ) fun x ↦ ?_).mul
    (PreservesFeature.diagonal _ _)
  let p := DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 x
  have hx : x = (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4).symm (p.1, p.2) := by
    dsimp only [p]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
  have hp : t4WinPerm (fullSysCoreWires 80) δ x =
      (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4).symm (p.1, stepT4Fin (δ p.1) p.2) := by
    conv_lhs => rw [hx]; exact t4WinPerm_symm_apply (fullSysCoreWires 80) δ p.1 p.2
  funext q
  dsimp only [low3924Bits]
  have hlt : q.val < fullSysCoreWires 80 := lt_of_lt_of_le q.isLt h3924_core
  have hCast : ∀ y i (hi : i < fullSysCoreWires 80),
      basisBits (fullSysCoreWires 80 + 4) y ⟨i, Nat.lt_add_right 4 hi⟩ =
        basisBits (fullSysCoreWires 80 + 4) y (Fin.castAdd 4 ⟨i, hi⟩) := fun _ _ _ ↦ rfl
  rw[hCast (t4WinPerm (fullSysCoreWires 80) δ x) q.val hlt, hCast x q.val hlt, hp]
  conv_rhs => rw [hx]
  rw [JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd,
      JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
theorem fixesLow3924_uSlot4ApexCatT4 : FixesLow3924 h3924_ct4 (uSlot4ApexCatT4 h22_80).1 := by
  have hAx : ∀ w : Fin 3, FixesLow3924 h3924_ct4 (uSlot4AxisCatT4 false h22_80 w).1 := fun w ↦ by
    unfold uSlot4AxisCatT4
    refine (fixesLow3924_uApexShift4 _).mul ?_
    rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_prefix (isLow3924Prefix_block0 h3924_core h3924_ct4 _)
      (PreservesFeature.diagonal _ _)
  exact (hAx 2).mul ((hAx 1).mul (hAx 0))
theorem isLow3924Prefix_selCT4InCT :
    InterWalkRSum42Hoist.IsLow3924Prefix h3924_ct4 h3924_cat (selCT4InCT 80) :=
  fun q ↦ by
    have hc : (⟨q.val, lt_of_lt_of_le q.isLt h3924_ct4⟩ : Fin (fullSysCoreWires 80 + 4)) =
        Fin.castAdd 4 ⟨q.val, lt_of_lt_of_le q.isLt h3924_core⟩ := rfl
    rw [hc]; unfold selCT4InCT; rw [QRegister.concat_apply_left]
    ext; simp [ProjZ512QftAndTwist288.rCoreBlock48, QRegister.block]
end Impl07f
end HeldStreamFoldedPass123Bridge
end SharedScope
end
end SlimStageBOuterDepsA

noncomputable section SlimFermApproxSec1And2A

section
set_option maxRecDepth 262144
set_option exponentiation.threshold 8192
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroK2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
namespace StageAConjHAndStreamBridge
noncomputable section ImplAlt
open HermitianMat LocalClassicalPerm
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror OctahedralOrbit
open Dyadic128CoulombMath
open CanonRank7Circuit
open SpecsAux.DyadicSubgridToeplitz128 (anchorSubTarget1D)
open KaratsubaQft64Matrix (omega128 omega128_zero omega128_add star_mul_omega128_self bit6 bitRev6)
open DyadicQft64WalkCircuit (u18GridEquiv)
open StreamingBchComparator PosSlots24BranchConcrete
open GridGuard654ReflAux (symStepFwdList symStepFwdList_append ValidSymStepList
  validSymStepList_append polBit litAndSymStep litAndSymStep_stepFwd)
open PosSlots24CompactHead123 PosHeadRev18CacheAux PosHeadMod4_15476
open InterWalkRSum42Hoist (qreg_block_apply)
open HeadMod4Wide178 (omega128_eq_of_emod_eq)
open StageAPosHeadConjugatedCircuit (rSpectatorSlot elecProd217)
open OriginZeroHeadMod4Reduction (zeroSlot0Bits)
open Origin0Head34RealizesAndLeaf2Spec (headEnBoolSpec_zeroSlot0Bits)
open StageAPointPhase128OnStep (bit7 pointSumCliffordExp128 pointElecCliffordExp128)
section HeadAndPhi
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
section Part1_RepairedOrigin0Head35Realizes
/-- Boolean flag `β (wSlot0Core (QRegister.ofFin posCoreWires)) == 1` on `posCoreWires`. -/
def headS0Bool (β : BitAssignment posCoreWires) : Bool :=
  β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1
/-- Target 3D subgrid coordinate `yTarget : SubGridCoord64` tested by `headHitSetSpec` on
  `posCoreWires`:
equals `⟨(dHead w).val / 2, _⟩` when `s0 = false`, and
`(anchorSubTarget1D (y0 w) (if b0 w then 1 else 0) (dHead w)).1` when `s0 = true`. -/
def headTargetCoord64 (β : BitAssignment posCoreWires) : SubGridCoord64 :=
  let rCore := QRegExt.ofFin posCoreWires
  let s0 := headS0Bool β
  let dHead := fineCoordOfReg21 (rHeadFine21 rCore) β
  let y0 := slotSubGridCoord64 (rElecSlot rCore 0) β
  let b0 := parity3OfReg (rCosetB0 rCore) β
  fun w ↦
    if Bool.not s0 then ⟨(dHead w).val / 2, by have := (dHead w).isLt; omega⟩
    else (anchorSubTarget1D (y0 w) (if b0 w then 1 else 0) (dHead w)).1
/-- Bit-reversed 18-bit target point `Fin (2 ^ 18)` corresponding to `headTargetCoord64 β`. -/
def headTargetPoint18 (β : BitAssignment posCoreWires) : Fin (2 ^ 18) :=
  u18GridEquiv.symm (fun w ↦ bitRev6 (headTargetCoord64 β w))
theorem u18GridEquiv_headTargetPoint18 (β : BitAssignment posCoreWires) (w : Fin 3) :
    u18GridEquiv (headTargetPoint18 β) w = bitRev6 (headTargetCoord64 β w) := by
  unfold headTargetPoint18
  rw [Equiv.apply_symm_apply]
/-- Repaired origin-`0` hit set on `posCoreWires`: tests spectator slots `1 .. 217` against the
origin `0 : SubGridCoord64` (`fun _ ↦ 0`), while preserving the exact slot-`0` (`e = 0`) test
`Bool.not s0 && decide (slotSubGridCoord64 (rElecSlot rCore 0) β = headTargetCoord64 β)`. -/
def headHitSetOrigin0RepairedSpec (β : BitAssignment posCoreWires) : Finset (Fin 218) :=
  let rCore := QRegExt.ofFin posCoreWires
  Finset.univ.filter fun e : Fin 218 ↦
    if e.val = 0 then
      Bool.not (headS0Bool β) &&
        decide (slotSubGridCoord64 (rElecSlot rCore 0) β = headTargetCoord64 β)
    else
      decide (slotSubGridCoord64 (rElecSlot rCore e) β = fun _ ↦ 0)
/-- `ZMod 8` phase exponent of the repaired origin-`0` Mod-4 Head Phase Oracle on `posCoreWires`. -/
def headPhaseMod4Origin0RepairedZ8Spec (β : BitAssignment posCoreWires) : ZMod 8 :=
  let rCore := QRegExt.ofFin posCoreWires
  if Bool.not (headEnBoolSpec β) then 0
  else
    let s0Z8 : ZMod 8 := if headS0Bool β then 4 else 0
    let tZ8 : ZMod 8 := if β (wHeadThresh rCore) == 1 then 4 else 0
    s0Z8 + ((headHitSetOrigin0RepairedSpec β).card : ZMod 8) * (2 + tZ8)
/-- Repaired origin-`0` Mod-4 Head Phase Unitary on `posCoreWires`. -/
noncomputable def uHeadPhaseMod4Origin0Repaired : Unitary (2 ^ posCoreWires) :=
  monomialZ8UnitaryN (wHeadThresh (QRegExt.ofFin posCoreWires))
    headEnBoolSpec headPhaseMod4Origin0RepairedZ8Spec
/-- Parallel `m`-wire CNOT copy-XOR circuit (`0 T`, `count TOFF = 0`) from `src` into `dst`. -/
def cXorWires {n : ℕ} :
    (m : ℕ) → (src dst : Fin m → Wire n) → (∀ i : Fin m, src i ≠ dst i) → Circuit n
  | 0, _, _, _ => .identity
  | m + 1, src, dst, hne =>
      Circuit.CNOT (src 0) (dst 0) (hne 0) ;;ᶜ
        cXorWires m (fun i ↦ src i.succ) (fun i ↦ dst i.succ) (fun i ↦ hne i.succ)
@[simp] theorem count_cXorWires_toff {n : ℕ} :
    ∀ (m : ℕ) (src dst : Fin m → Wire n) (hne : ∀ i : Fin m, src i ≠ dst i),
      (cXorWires m src dst hne).count TOFF = 0
  | 0, _, _, _ => rfl
  | m + 1, src, dst, hne => by
      simp only [cXorWires, Circuit.count_seq, count_cXorWires_toff m]
      simp [Circuit.CNOT]
@[simp] theorem count_cXorWires_t {n : ℕ} :
    ∀ (m : ℕ) (src dst : Fin m → Wire n) (hne : ∀ i : Fin m, src i ≠ dst i),
      (cXorWires m src dst hne).count T = 0
  | 0, _, _, _ => rfl
  | m + 1, src, dst, hne => by
      simp only [cXorWires, Circuit.count_seq, count_cXorWires_t m]
      simp [Circuit.CNOT]
/-- Classical bit-assignment update performed by `cXorWires m src dst` when `dst` is injective and
disjoint from `src`. -/
def xorWiresBits {n : ℕ} :
    (m : ℕ) → (src dst : Fin m → Wire n) → BitAssignment n → BitAssignment n
  | 0, _, _, β => β
  | m + 1, src, dst, β =>
      xorWiresBits m (fun i ↦ src i.succ) (fun i ↦ dst i.succ)
        (Function.update β (dst 0) (β (dst 0) + β (src 0)))
theorem ket_cXorWires {n : ℕ} :
    ∀ (m : ℕ) (src dst : Fin m → Wire n) (hne : ∀ i : Fin m, src i ≠ dst i)
      (β : BitAssignment n),
      (cXorWires m src dst hne).eval.1.mulVec (ket β) = ket (xorWiresBits m src dst β)
  | 0, _, _, _, _ => by simp [cXorWires, xorWiresBits]
  | m + 1, src, dst, hne, β => by
      dsimp only [cXorWires, xorWiresBits]
      rw [OctahedralOrbit.eval_seq_mulVec, OctahedralOrbit.ket_CNOT, ket_cXorWires m]
theorem xorWiresBits_outside {n : ℕ} :
    ∀ (m : ℕ) (src dst : Fin m → Wire n) (β : BitAssignment n) (w : Wire n),
      (∀ i : Fin m, w ≠ dst i) → xorWiresBits m src dst β w = β w
  | 0, _, _, _, _, _ => rfl
  | m + 1, src, dst, β, w, hw => by
      dsimp only [xorWiresBits]
      rw [xorWiresBits_outside m _ _ _ w (fun i ↦ hw i.succ), Function.update_of_ne (hw 0)]
theorem xorWiresBits_dst {n : ℕ} :
    ∀ (m : ℕ) (src dst : Fin m → Wire n)
      (_hdst_inj : Function.Injective dst)
      (_hdisj : ∀ i j : Fin m, src i ≠ dst j)
      (β : BitAssignment n) (i : Fin m),
      xorWiresBits m src dst β (dst i) = β (dst i) + β (src i)
  | 0, _, _, _, _, _, i => Fin.elim0 i
  | m + 1, src, dst, hdst_inj, hdisj, β, i => by
      dsimp only [xorWiresBits]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [xorWiresBits_outside m _ _ _ (dst 0)
            (fun k hk ↦ Fin.succ_ne_zero k (hdst_inj hk.symm)),
          Function.update_self]
      · have hdst_succ : Function.Injective (fun k : Fin m ↦ dst k.succ) :=
          fun a b h ↦ Fin.succ_inj.mp (hdst_inj h)
        rw [xorWiresBits_dst m _ _ hdst_succ (fun a b ↦ hdisj a.succ b.succ),
          Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (hdst_inj h)),
          Function.update_of_ne (hdisj j.succ 0)]
theorem xorWiresBits_involutive {n : ℕ} (m : ℕ) (src dst : Fin m → Wire n)
    (hdst_inj : Function.Injective dst) (hdisj : ∀ i j : Fin m, src i ≠ dst j)
    (β : BitAssignment n) : xorWiresBits m src dst (xorWiresBits m src dst β) = β := by
  funext w
  by_cases hw : ∃ i : Fin m, w = dst i
  · obtain ⟨i, rfl⟩ := hw
    rw[xorWiresBits_dst m src dst hdst_inj hdisj, xorWiresBits_dst m src dst hdst_inj hdisj,
        xorWiresBits_outside m src dst β (src i) (fun j ↦ hdisj i j), add_assoc,
        CharTwo.add_self_eq_zero, add_zero]
  · have hw' : ∀ i : Fin m, w ≠ dst i := fun i h ↦ hw ⟨i, h⟩
    rw [xorWiresBits_outside m src dst _ w hw', xorWiresBits_outside m src dst β w hw']
theorem phcHead_rQRev18_ne_rElec0 (k q : Fin 18) : phcHead_rQRev18
    (QRegExt.ofFin posCoreWires) k ≠ rElecSlot (QRegExt.ofFin posCoreWires) 0 q := by
  revert k q; decide
/-- Fixed-width `0-T`, `0-TOFF` 18-CNOT shift XORing `phcHead_rQRev18` (`dHead / 2` bit-reversed)
  into
Electron `0` (`rElecSlot 0`) on `posCoreWires`. -/
def cPreShift0Core : Circuit posCoreWires := cXorWires 18
    (phcHead_rQRev18 (QRegExt.ofFin posCoreWires))
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) (fun i ↦ phcHead_rQRev18_ne_rElec0 i i)
@[simp] theorem count_cPreShift0Core_toff : cPreShift0Core.count TOFF = 0 :=
  count_cXorWires_toff 18 _ _ _
@[simp] theorem count_cPreShift0Core_t : cPreShift0Core.count T = 0 :=
  count_cXorWires_t 18 _ _ _
/-- Bit-level involution on `BitAssignment posCoreWires` induced by `cPreShift0Core`. -/
def preShift0Bits : BitAssignment posCoreWires → BitAssignment posCoreWires :=
  xorWiresBits 18 (phcHead_rQRev18 (QRegExt.ofFin posCoreWires))
    (rElecSlot (QRegExt.ofFin posCoreWires) 0)
theorem ket_cPreShift0Core (β : BitAssignment posCoreWires) : cPreShift0Core.eval.1.mulVec
    (ket β) = ket (preShift0Bits β) := ket_cXorWires 18 _ _ _ β
theorem preShift0Bits_involutive (β : BitAssignment posCoreWires) : preShift0Bits
    (preShift0Bits β) = β := xorWiresBits_involutive 18 _ _
    (rElecSlot (QRegExt.ofFin posCoreWires) 0).wires.injective phcHead_rQRev18_ne_rElec0 β
theorem preShift0Bits_high (β : BitAssignment posCoreWires) {w : Wire posCoreWires}
    (hw : 18 ≤ w.val) : preShift0Bits β w = β w := by
  have hv : ∀ i : Fin 18, (rElecSlot (QRegExt.ofFin posCoreWires) 0 i).val = i.val := by decide
  refine xorWiresBits_outside 18 _ _ β w fun q h ↦ ?_
  have hq := q.isLt
  have hwq : w.val = q.val := (congrArg Fin.val h).trans (hv q)
  omega
theorem preShift0Bits_elec0 (β : BitAssignment posCoreWires) (q : Fin 18) : preShift0Bits β
    (rElecSlot (QRegExt.ofFin posCoreWires) 0 q) = β
    (rElecSlot (QRegExt.ofFin posCoreWires) 0 q) + β
    (phcHead_rQRev18 (QRegExt.ofFin posCoreWires) q) := xorWiresBits_dst 18 _ _
    (rElecSlot (QRegExt.ofFin posCoreWires) 0).wires.injective phcHead_rQRev18_ne_rElec0 β q
/-- Unshifted `218`-slot origin-`0` hit set (`e = 0` tested at `0` when `s0 = false`, `e ≥ 1` at
  `0`). -/
def headHitSetOrigin0AllZeroSpec (β : BitAssignment posCoreWires) : Finset (Fin 218) :=
  let rCore := QRegExt.ofFin posCoreWires
  Finset.univ.filter fun e : Fin 218 ↦
    if e.val = 0 then
      Bool.not (headS0Bool β) &&
        decide (slotSubGridCoord64 (rElecSlot rCore 0) β = fun _ ↦ 0)
    else
      decide (slotSubGridCoord64 (rElecSlot rCore e) β = fun _ ↦ 0)
/-- `ZMod 8` phase exponent of `dHeadOrigin0Core35Dyn` on `posCoreWires`. -/
def headPhaseMod4Origin0AllZeroZ8Spec (β : BitAssignment posCoreWires) : ZMod 8 :=
  let rCore := QRegExt.ofFin posCoreWires
  if Bool.not (headEnBoolSpec β) then 0
  else
    let s0Z8 : ZMod 8 := if headS0Bool β then 4 else 0
    let tZ8 : ZMod 8 := if β (wHeadThresh rCore) == 1 then 4 else 0
    s0Z8 + ((headHitSetOrigin0AllZeroSpec β).card : ZMod 8) * (2 + tZ8)
/-- Unshifted `218`-slot origin-`0` unitary realized by `dHeadOrigin0Core35Dyn`. -/
noncomputable def uHeadOrigin0Core35 : Unitary (2 ^ posCoreWires) :=
  monomialZ8UnitaryN (wHeadThresh (QRegExt.ofFin posCoreWires))
    headEnBoolSpec headPhaseMod4Origin0AllZeroZ8Spec
theorem slotSubGridCoord64_eq_zero_iff {n : ℕ} (rSlot : QRegister 18 n) (β : BitAssignment n) :
    slotSubGridCoord64 rSlot β = (fun _ ↦ 0) ↔ ∀ q : Fin 18, β (rSlot q) = 0 := by
  have hz : slotSubGridCoord64 rSlot (fun _ : Wire n ↦ (0 : ZMod 2)) = fun _ ↦ 0 := by
    funext w; ext; simp [slotSubGridCoord64, regVal, bitsVal]
  rw [← hz, slotSubGridCoord64_eq_iff]
theorem zeroSlot0Bits_preShift0Bits (β : BitAssignment posCoreWires) :
    zeroSlot0Bits (preShift0Bits β) = zeroSlot0Bits β := by
  funext w
  dsimp only [zeroSlot0Bits]
  split_ifs with hw
  · rfl
  · exact preShift0Bits_high β (Nat.le_of_not_lt hw)
theorem headEnBoolSpec_preShift0Bits (β : BitAssignment posCoreWires) :
    headEnBoolSpec (preShift0Bits β) = headEnBoolSpec β := by
  rw [← headEnBoolSpec_zeroSlot0Bits (preShift0Bits β),
      zeroSlot0Bits_preShift0Bits, headEnBoolSpec_zeroSlot0Bits]
theorem slotSubGridCoord64_phcHead_rQRev18 (β : BitAssignment posCoreWires) (w : Fin 3) :
    slotSubGridCoord64 (phcHead_rQRev18 (QRegExt.ofFin posCoreWires)) β w =
      ⟨(fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β w).val / 2,
       by
         have := (fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β w).isLt; omega⟩ :=
         by
  have hWire : ∀ (u : Fin 3) (j : Fin 6),
      axisBitRev6 (phcHead_rQRev18 (QRegExt.ofFin posCoreWires)) u j =
        (((rHeadFine21 (QRegExt.ofFin posCoreWires)).slice (7 * u.val) 7
          (by have := u.isLt; omega)).slice 1 6 (by decide)) j := fun u j ↦
    Fin.ext (by revert u j; decide)
  ext
  change bitsVal (fun j : Fin 6 ↦
    β (axisBitRev6 (phcHead_rQRev18 (QRegExt.ofFin posCoreWires)) w j)) = _
  have hsl : bitsVal (fun j : Fin 6 ↦
    β (axisBitRev6 (phcHead_rQRev18 (QRegExt.ofFin posCoreWires)) w j)) =
      regVal (((rHeadFine21 (QRegExt.ofFin posCoreWires)).slice (7 * w.val) 7
        (by have := w.isLt; omega)).slice 1 6 (by decide)) β := by
    unfold regVal bitsVal
    exact Finset.sum_congr rfl fun j _ ↦ by dsimp only; rw [hWire w j]
  rw [hsl, regVal_slice1_eq_div2]; rfl
theorem headHitSetOrigin0AllZeroSpec_preShift0Bits (β : BitAssignment posCoreWires) :
    headHitSetOrigin0AllZeroSpec (preShift0Bits β) = headHitSetOrigin0RepairedSpec β := by
  have hS0Ge : 18 ≤ (wSlot0Core (QRegExt.ofFin posCoreWires)).val := by decide
  ext e
  unfold headHitSetOrigin0AllZeroSpec headHitSetOrigin0RepairedSpec headS0Bool
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [preShift0Bits_high β hS0Ge]
  split_ifs with he0
  · by_cases hs0 : Bool.not (β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) = true
    · rw [hs0]
      simp only [Bool.true_and]
      have hTgt : headTargetCoord64 β =
          slotSubGridCoord64 (phcHead_rQRev18 (QRegExt.ofFin posCoreWires)) β := by
        funext w
        unfold headTargetCoord64 headS0Bool
        rw [ite_eq_left hs0, slotSubGridCoord64_phcHead_rQRev18 β w]
      have hz2 : ∀ x y : ZMod 2, (x + y = 0) ↔ x = y := by decide
      have hIff :
          (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) (preShift0Bits β) = fun _ ↦
            0) ↔
            (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β =
              slotSubGridCoord64 (phcHead_rQRev18 (QRegExt.ofFin posCoreWires)) β) := by
        rw [slotSubGridCoord64_eq_zero_iff, slotSubGridCoord64_eq_iff]
        exact ⟨fun h q ↦ (hz2 _ _).mp ((preShift0Bits_elec0 β q).symm.trans (h q)),
          fun h q ↦ (preShift0Bits_elec0 β q).trans (by rw [h q]; exact (hz2 _ _).mpr rfl)⟩
      rw [hTgt, decide_eq_decide.mpr hIff]
    · have hs0f : Bool.not (β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) = false :=
        Bool.eq_false_iff.mpr hs0
      rw [hs0f]; simp
  · have hEq : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) (preShift0Bits β) =
        slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β := by
      have he_pos : 0 < e.val := Nat.pos_of_ne_zero he0
      funext w; apply Fin.ext
      change bitsVal (fun j : Fin 6 ↦
        (preShift0Bits β) (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j)) =
        bitsVal (fun j : Fin 6 ↦ β (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j))
      refine congrArg bitsVal (funext fun j ↦ ?_)
      have hge : 18 ≤ (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j).val := by
        change 18 ≤ 18 * e.val + (6 * w.val + (5 - j.val))
        have := e.isLt; have := w.isLt; have := j.isLt; omega
      exact preShift0Bits_high β hge
    rw [hEq]
theorem preShift0Bits_update_wHeadThresh (γ : BitAssignment posCoreWires) (v : ZMod 2) :
    preShift0Bits (Function.update γ (wHeadThresh (QRegExt.ofFin posCoreWires)) v) =
      Function.update (preShift0Bits γ) (wHeadThresh (QRegExt.ofFin posCoreWires)) v := by
  let rCore := QRegExt.ofFin posCoreWires
  let wTh := wHeadThresh rCore
  have hThGe : 18 ≤ wTh.val := by decide
  have hQNeTh : ∀ q : Fin 18, phcHead_rQRev18 rCore q ≠ wTh := by
    have hd : ∀ q : Fin 18,
        (phcHead_rQRev18 (QRegExt.ofFin posCoreWires) q).val ≠
          (wHeadThresh (QRegExt.ofFin posCoreWires)).val := by decide
    exact fun q h ↦ hd q (congrArg Fin.val h)
  have hEl0 : ∀ (w : Wire posCoreWires) (hlt : w.val < 18),
      rElecSlot rCore 0 ⟨w.val, hlt⟩ = w := fun w _ ↦
    Fin.ext (by change 18 * 0 + w.val = w.val; omega)
  funext w
  by_cases hw : w = wTh
  · subst hw
    rw [preShift0Bits_high _ hThGe, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hw]
    by_cases hge : 18 ≤ w.val
    · rw [preShift0Bits_high _ hge, preShift0Bits_high _ hge, Function.update_of_ne hw]
    · have hlt : w.val < 18 := Nat.lt_of_not_ge hge
      rw [← hEl0 w hlt, preShift0Bits_elec0, preShift0Bits_elec0,
          hEl0 w hlt, Function.update_of_ne hw, Function.update_of_ne (hQNeTh ⟨w.val, hlt⟩)]
theorem cPreShift0Core_conj_uHeadOrigin0Core35_eq : cPreShift0Core.eval * uHeadOrigin0Core35 *
    cPreShift0Core.eval = uHeadPhaseMod4Origin0Repaired := by
  let rCore := QRegExt.ofFin posCoreWires
  let wTh := wHeadThresh rCore
  have hS0Ge : 18 ≤ (wSlot0Core rCore).val := by decide
  have hThGe : 18 ≤ wTh.val := by decide
  apply Subtype.ext
  apply matrix_ext_of_ket
  intro β
  change (cPreShift0Core.eval.1 * uHeadOrigin0Core35.1 * cPreShift0Core.eval.1).mulVec (ket β) = _
  rw[Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_cPreShift0Core]
  dsimp only [uHeadOrigin0Core35, uHeadPhaseMod4Origin0Repaired]
  rw [ket_monomialZ8UnitaryN, Matrix.mulVec_smul, ket_cPreShift0Core, ket_monomialZ8UnitaryN]
  have hPhase : headPhaseMod4Origin0AllZeroZ8Spec (preShift0Bits β) =
      headPhaseMod4Origin0RepairedZ8Spec β := by
    unfold headPhaseMod4Origin0AllZeroZ8Spec headPhaseMod4Origin0RepairedZ8Spec headS0Bool
    dsimp only
    rw [headEnBoolSpec_preShift0Bits, headHitSetOrigin0AllZeroSpec_preShift0Bits,
        preShift0Bits_high β hS0Ge, preShift0Bits_high β hThGe]
  have hKet : preShift0Bits (flipThClean wTh headEnBoolSpec (preShift0Bits β)) =
      flipThClean wTh headEnBoolSpec β := by
    unfold flipThClean flipTh
    rw [← preShift0Bits_update_wHeadThresh, headEnBoolSpec_preShift0Bits]
    split_ifs
    · rw [preShift0Bits_high β hThGe,
          preShift0Bits_update_wHeadThresh, preShift0Bits_involutive]
    · exact preShift0Bits_involutive β
  rw [hPhase, hKet]
end Part1_RepairedOrigin0Head35Realizes
section Part2_Target18AndPointPhiSave0
open DyadicQft64WalkCircuit (block6_extractIndex_u18)
theorem bitRev6_involutive_assoc : ∀ a : Fin 64, bitRev6 (bitRev6 a) = a := by decide
theorem bitRev6_val_eq_bitsVal_rev_assoc :
    ∀ a : Fin 64, (bitRev6 a).val = bitsVal (fun j : Fin 6 ↦ basisBits 6 a ⟨5 - j.val, by omega⟩) :=
      by
  decide
theorem slotSubGridCoord64_eq_bitRev6_u18GridEquiv {n : ℕ} (r18 : QRegister 18 n)
    (x : Fin (2 ^ n)) (w : Fin 3) : slotSubGridCoord64 r18 (basisBits n x) w = bitRev6
    (u18GridEquiv (r18.extractIndex x) w) := by
  apply Fin.ext
  have hw : 6 * w.val + 6 ≤ 18 := by have := w.isLt; omega
  let r6 : QRegister 6 18 := QRegister.block (6 * w.val) 6 hw
  have hu : u18GridEquiv (r18.extractIndex x) w = r6.extractIndex (r18.extractIndex x) :=
    (block6_extractIndex_u18 w hw (r18.extractIndex x)).symm
  rw [hu, bitRev6_val_eq_bitsVal_rev_assoc]
  change bitsVal (fun j : Fin 6 ↦ basisBits n x (axisBitRev6 r18 w j)) =
    bitsVal (fun j : Fin 6 ↦
      basisBits 6 (r6.extractIndex (r18.extractIndex x)) ⟨5 - j.val, by omega⟩)
  unfold bitsVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  rw [QRegister.basisBits_extractIndex r6, QRegister.basisBits_extractIndex r18]
  have hidx : r6 ⟨5 - j.val, by omega⟩ = ⟨6 * w.val + (5 - j.val), by have := w.isLt; omega⟩ := by
    ext; simp [r6]
  rw [hidx]; rfl
theorem slotSubGridCoord64_eq_iff_extractIndex {n : ℕ} (r18 : QRegister 18 n)
    (x : Fin (2 ^ n)) (c : SubGridCoord64) : slotSubGridCoord64 r18 (basisBits n x) = c ↔
    r18.extractIndex x = u18GridEquiv.symm (fun w ↦ bitRev6 (c w)) := by
  constructor
  · intro h
    apply u18GridEquiv.injective
    rw [Equiv.apply_symm_apply]
    funext w
    rw [← h, slotSubGridCoord64_eq_bitRev6_u18GridEquiv, bitRev6_involutive_assoc]
  · intro h
    funext w
    rw [slotSubGridCoord64_eq_bitRev6_u18GridEquiv, h, Equiv.apply_symm_apply,
      bitRev6_involutive_assoc]
/-- Per-axis 6-step symmetric `TempAnd` carry chain into `rW[6*w .. 6*w+5]` (`24 T`, `count TOFF
  = 0`). -/
def zTargetAxisCarrySteps {n mW : ℕ} (hm36 : 36 ≤ mW)
    (rCore : QRegister posCoreWires n) (rW : QRegister mW n)
    (hCW : rCore.DisjointWires rW) (w : Fin 3) : List (SymTempAndStep n) :=
  let hw := w.isLt
  let c : Fin 6 → Wire n := fun j ↦ rW ⟨6 * w.val + j.val, by have := j.isLt; omega⟩
  let y : Fin 6 → Wire n := fun j ↦ axisBitRev6 (rElecSlot rCore 0) w j
  let q : Fin 6 → Wire n := fun j ↦ rHeadFine21 rCore ⟨7 * w.val + j.val + 1, by
    have := j.isLt; omega⟩
  have hCoreW : ∀ {z : Wire n}, z ∈ rCore.image → ∀ idx : Fin mW, z ≠ rW idx :=
    fun hz idx heq ↦ by
      obtain ⟨i, hi⟩ := (QRegister.mem_image rCore _).mp hz; exact hCW.ne i idx (hi.trans heq)
  have hc_ne : ∀ a b : Fin 6, a ≠ b → c a ≠ c b := fun a b hab h ↦
    hab (Fin.ext (by have hv := congrArg Fin.val (rW.wires.injective h); dsimp only at hv; omega));
  [ litAndSymStep true false true (rCosetB0 rCore w) (rHeadFine21 rCore ⟨7 * w.val, by omega⟩) (c 0)
      (phcHead_b0_ne_d0 rCore w)
      (hCoreW (phcHead_b0_mem_core rCore w) _)
      (hCoreW (phcHead_dBit_mem_core rCore _) _),
    carryOnlySymStep (y 0) (q 0) (c 0) (c 1) (phcHead_y0_ne_q rCore w 0)
      (hCoreW (phcHead_y0_mem_core rCore w 0) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hCoreW (phcHead_y0_mem_core rCore w 0) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hc_ne 0 1 (by decide)),
    carryOnlySymStep (y 1) (q 1) (c 1) (c 2) (phcHead_y0_ne_q rCore w 1)
      (hCoreW (phcHead_y0_mem_core rCore w 1) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hCoreW (phcHead_y0_mem_core rCore w 1) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hc_ne 1 2 (by decide)),
    carryOnlySymStep (y 2) (q 2) (c 2) (c 3) (phcHead_y0_ne_q rCore w 2)
      (hCoreW (phcHead_y0_mem_core rCore w 2) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hCoreW (phcHead_y0_mem_core rCore w 2) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hc_ne 2 3 (by decide)),
    carryOnlySymStep (y 3) (q 3) (c 3) (c 4) (phcHead_y0_ne_q rCore w 3)
      (hCoreW (phcHead_y0_mem_core rCore w 3) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hCoreW (phcHead_y0_mem_core rCore w 3) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hc_ne 3 4 (by decide)),
    carryOnlySymStep (y 4) (q 4) (c 4) (c 5) (phcHead_y0_ne_q rCore w 4)
      (hCoreW (phcHead_y0_mem_core rCore w 4) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hCoreW (phcHead_y0_mem_core rCore w 4) _) (hCoreW (phcHead_dBit_mem_core rCore _) _)
      (hc_ne 4 5 (by decide)) ]
theorem wSlot0Core_mem_core {n : ℕ} (rCore : QRegister posCoreWires n) : wSlot0Core rCore ∈
    rCore.image := (QRegister.mem_image rCore _).mpr ⟨_, rfl⟩
/-- Per-axis 6-step `s0`-gated mux difference into `rW[18 + 6*w .. 18 + 6*w + 5]` (`24 T`, `count
  TOFF = 0`). -/
def zTargetAxisMuxSteps {n mW : ℕ} (hm36 : 36 ≤ mW)
    (rCore : QRegister posCoreWires n) (rW : QRegister mW n)
    (hCW : rCore.DisjointWires rW) (w : Fin 3) : List (SymTempAndStep n) :=
  let hw := w.isLt
  have hCoreW : ∀ {z : Wire n}, z ∈ rCore.image → ∀ idx : Fin mW, z ≠ rW idx :=
    fun hz idx heq ↦ by
      obtain ⟨i, hi⟩ := (QRegister.mem_image rCore _).mp hz; exact hCW.ne i idx (hi.trans heq)
  List.ofFn fun u : Fin 6 ↦
    let hu := u.isLt
    let j : Fin 6 := ⟨5 - u.val, by omega⟩
    let c_j : Wire n := rW ⟨6 * w.val + j.val, by have := j.isLt; omega⟩
    let m_u : Wire n := rW ⟨18 + 6 * w.val + u.val, by omega⟩
    let y_j : Wire n := axisBitRev6 (rElecSlot rCore 0) w j
    muxDiffSymStep (wSlot0Core rCore) y_j c_j m_u
      (phcHead_s0_ne_y0 rCore w j) (hCoreW (wSlot0Core_mem_core rCore) _) (hCoreW
        (wSlot0Core_mem_core rCore) _)
      (hCoreW (phcHead_y0_mem_core rCore w j) _) (hCoreW (phcHead_y0_mem_core rCore w j) _)
      (fun h ↦ by have hv := congrArg Fin.val (rW.wires.injective h); dsimp only at hv; omega)
/-- Full 36-step symmetric `TempAnd` list (`144 T`, `count TOFF = 0`) into `rW[0..35]`. -/
def zTargetSteps36 {n mW : ℕ} (hm36 : 36 ≤ mW) (rCore : QRegister posCoreWires n)
    (rW : QRegister mW n) (hCW : rCore.DisjointWires rW) : List (SymTempAndStep n) :=
    zTargetAxisCarrySteps hm36 rCore rW hCW 0 ++ zTargetAxisCarrySteps hm36 rCore rW hCW 1 ++
    zTargetAxisCarrySteps hm36 rCore rW hCW 2 ++ zTargetAxisMuxSteps hm36 rCore rW hCW 0 ++
    zTargetAxisMuxSteps hm36 rCore rW hCW 1 ++ zTargetAxisMuxSteps hm36 rCore rW hCW 2
@[simp] theorem length_zTargetSteps36 {n mW : ℕ} (hm36 : 36 ≤ mW)
    (rCore : QRegister posCoreWires n) (rW : QRegister mW n) (hCW : rCore.DisjointWires rW) :
    (zTargetSteps36 hm36 rCore rW hCW).length = 36 := by
  simp [zTargetSteps36, zTargetAxisCarrySteps, zTargetAxisMuxSteps]
theorem zTargetAxisCarrySteps_valid_and_eval {n mW : ℕ} (hm36 : 36 ≤ mW)
    (rCore : QRegister posCoreWires n) (rW : QRegister mW n)
    (hCW : rCore.DisjointWires rW) (w : Fin 3)
    (M : Finset (Wire n)) (hCM : Disjoint rCore.image M) (hWM : Disjoint rW.image M) :
    ValidSymStepList M rW (6 * w.val) (zTargetAxisCarrySteps hm36 rCore rW hCW w) ∧
    (∀ (β : BitAssignment n),
      (∀ j : Fin 6, β (rW ⟨6 * w.val + j.val, by have := w.isLt; have := j.isLt; omega⟩) = 0) →
      (∀ j : Fin 6,
        (symStepFwdList (zTargetAxisCarrySteps hm36 rCore rW hCW w) β)
          (rW ⟨6 * w.val + j.val, by have := w.isLt; have := j.isLt; omega⟩) =
          carrySeq6 (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) w i))
            (fun i ↦ β (rHeadFine21 rCore ⟨7 * w.val + i.val + 1, by
              have := w.isLt; have := i.isLt; omega⟩))
            (1 + (β (rCosetB0 rCore w) + 1) * β (rHeadFine21 rCore ⟨7 * w.val, by
              have := w.isLt; omega⟩)) j.val) ∧
      (∀ z, (∀ j : Fin 6, z ≠ rW ⟨6 * w.val + j.val, by have := w.isLt; have := j.isLt; omega⟩) →
        (symStepFwdList (zTargetAxisCarrySteps hm36 rCore rW hCW w) β) z = β z)) := by
  let hw := w.isLt
  let y : Fin 6 → Wire n := fun j ↦ axisBitRev6 (rElecSlot rCore 0) w j
  let q : Fin 6 → Wire n := fun j ↦ rHeadFine21 rCore ⟨7 * w.val + j.val + 1, by
    have := j.isLt; omega⟩
  let c : Fin 6 → Wire n := fun j ↦ rW ⟨6 * w.val + j.val, by have := j.isLt; omega⟩
  have hc_ne : ∀ a b : Fin 6, a ≠ b → c a ≠ c b := fun a b hab h ↦
    hab (Fin.ext (by
      have hv := congrArg Fin.val (rW.wires.injective h); dsimp only [c] at hv; omega))
  have latCore : ∀ {z : Wire n}, z ∈ rCore.image → ∀ idx : Fin mW, rW idx ≠ z := fun hz idx heq ↦ by
    obtain ⟨i, hi⟩ := (QRegister.mem_image rCore _).mp hz
    exact hCW.ne i idx (hi.trans heq.symm)
  have notMCore : ∀ {z : Wire n}, z ∈ rCore.image → z ∉ M :=
    fun hz hm ↦ Finset.disjoint_left.mp hCM hz hm
  have notMW : ∀ idx : Fin mW, rW idx ∉ M :=
    fun idx hm ↦ Finset.disjoint_left.mp hWM ((QRegister.mem_image rW _).mpr ⟨idx, rfl⟩) hm
  constructor
  · dsimp only [zTargetAxisCarrySteps, ValidSymStepList, litAndSymStep, carryOnlySymStep]
    refine ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_,
      ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_, trivial⟩⟩⟩⟩⟩⟩
    · rw [Finset.disjoint_left]; intro z hz;
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact notMCore (phcHead_b0_mem_core rCore w)
      · exact notMCore (phcHead_dBit_mem_core rCore _)
      · exact notMW _
    · intro idx hlt; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨latCore (phcHead_b0_mem_core rCore w) idx, latCore (phcHead_dBit_mem_core rCore _) idx,
        fun h ↦ by have hv := congrArg Fin.val (rW.wires.injective h); dsimp only [c] at hv; omega⟩
    all_goals
      try (rw [Finset.disjoint_left]; intro z hz;
           simp only [Finset.mem_insert, Finset.mem_singleton] at hz;
           rcases hz with rfl | rfl | rfl | rfl;
           · exact notMCore (phcHead_y0_mem_core rCore w _)
           · exact notMCore (phcHead_dBit_mem_core rCore _)
           · exact notMW _
           · exact notMW _)
      try (intro idx hlt; simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
           exact ⟨latCore (phcHead_y0_mem_core rCore w _) idx,
             latCore (phcHead_dBit_mem_core rCore _) idx,
             fun h ↦ by
               have hv := congrArg Fin.val (rW.wires.injective h); dsimp only [c] at hv; omega,
             fun h ↦ by
               have hv := congrArg Fin.val (rW.wires.injective h); dsimp only [c] at hv; omega⟩)
  · intro β hClean
    have hc_clean : ∀ j : Fin 6, β (c j) = 0 := hClean
    dsimp only [zTargetAxisCarrySteps, symStepFwdList]
    rw [litAndSymStep_stepFwd true false true
      (rCosetB0 rCore w) (rHeadFine21 rCore ⟨7 * w.val, by omega⟩) (c 0) _ _ _ β (hc_clean 0)]
    let s0 := Function.update β (c 0)
      (polBit true (polBit true (β (rCosetB0 rCore w)) *
        polBit false (β (rHeadFine21 rCore ⟨7 * w.val, by omega⟩))))
    have hs0_1 : s0 (c 1) = 0 := by simp [s0, Function.update_of_ne (hc_ne 1 0 (by
      decide)), hc_clean 1]
    rw [carryOnlySymStep_stepFwd (y 0) (q 0) (c 0) (c 1) _ _ _ _ _ _ s0 hs0_1]
    let s1 :=
      Function.update s0 (c 1) (s0 (c 0) + (s0 (y 0) + s0 (c 0)) * (s0 (q 0) + 1 + s0 (c 0)))
    have hs1_2 : s1 (c 2) = 0 := by
      simp [s1, s0, Function.update_of_ne (hc_ne 2 1 (by
        decide)), Function.update_of_ne (hc_ne 2 0 (by decide)), hc_clean 2]
    rw [carryOnlySymStep_stepFwd (y 1) (q 1) (c 1) (c 2) _ _ _ _ _ _ s1 hs1_2]
    let s2 :=
      Function.update s1 (c 2) (s1 (c 1) + (s1 (y 1) + s1 (c 1)) * (s1 (q 1) + 1 + s1 (c 1)))
    have hs2_3 : s2 (c 3) = 0 := by
      simp [s2, s1, s0, Function.update_of_ne (hc_ne 3 2 (by decide)),
        Function.update_of_ne (hc_ne 3 1 (by
          decide)), Function.update_of_ne (hc_ne 3 0 (by decide)), hc_clean 3]
    rw [carryOnlySymStep_stepFwd (y 2) (q 2) (c 2) (c 3) _ _ _ _ _ _ s2 hs2_3]
    let s3 :=
      Function.update s2 (c 3) (s2 (c 2) + (s2 (y 2) + s2 (c 2)) * (s2 (q 2) + 1 + s2 (c 2)))
    have hs3_4 : s3 (c 4) = 0 := by
      simp [s3, s2, s1, s0, Function.update_of_ne (hc_ne 4 3 (by decide)),
        Function.update_of_ne (hc_ne 4 2 (by
          decide)), Function.update_of_ne (hc_ne 4 1 (by decide)),
        Function.update_of_ne (hc_ne 4 0 (by decide)), hc_clean 4]
    rw [carryOnlySymStep_stepFwd (y 3) (q 3) (c 3) (c 4) _ _ _ _ _ _ s3 hs3_4]
    let s4 :=
      Function.update s3 (c 4) (s3 (c 3) + (s3 (y 3) + s3 (c 3)) * (s3 (q 3) + 1 + s3 (c 3)))
    have hs4_5 : s4 (c 5) = 0 := by
      simp [s4, s3, s2, s1, s0, Function.update_of_ne (hc_ne 5 4 (by decide)),
        Function.update_of_ne (hc_ne 5 3 (by
          decide)), Function.update_of_ne (hc_ne 5 2 (by decide)),
        Function.update_of_ne (hc_ne 5 1 (by
          decide)), Function.update_of_ne (hc_ne 5 0 (by decide)), hc_clean 5]
    rw [carryOnlySymStep_stepFwd (y 4) (q 4) (c 4) (c 5) _ _ _ _ _ _ s4 hs4_5]
    have hy_ne : ∀ a b : Fin 6, y a ≠ c b := fun a b h ↦
      latCore (phcHead_y0_mem_core rCore w a) _ h.symm
    have hq_ne : ∀ a b : Fin 6, q a ≠ c b := fun a b h ↦
      latCore (phcHead_dBit_mem_core rCore _) _ h.symm
    have hc_upd : ∀ (f : BitAssignment n) (a b : Fin 6) (val : ZMod 2),
        Function.update f (c a) val (c b) = if a == b then val else f (c b) := fun f a b val ↦ by
      rcases eq_or_ne a b with rfl | h
      · simp
      · simp [h, Function.update_of_ne (hc_ne b a h.symm)]
    constructor
    · intro j
      have hj_eq : (rW ⟨6 * w.val + j.val, by
        have := w.isLt; have := j.isLt; omega⟩ : Wire n) = c j := rfl
      rw [hj_eq]
      fin_cases j
      all_goals
        simp only [s4, s3, s2, s1, s0, Function.update_of_ne (hy_ne _ _),
          Function.update_of_ne (hq_ne _ _), hc_upd, BEq.beq]
        dsimp [polBit, carrySeq6, y, q]
        rw [add_comm ((β (rCosetB0 rCore w) + 1) * β (rHeadFine21 rCore ⟨7 * w.val, by omega⟩)) 1]
    · intro z hne
      have hne' : ∀ j : Fin 6, z ≠ c j := hne
      simp only [s4, s3, s2, s1, s0, Function.update_of_ne (hne' _)]
theorem zTargetAxisMuxSteps_valid_and_eval {n mW : ℕ} (hm36 : 36 ≤ mW)
    (rCore : QRegister posCoreWires n) (rW : QRegister mW n)
    (hCW : rCore.DisjointWires rW) (w : Fin 3)
    (M : Finset (Wire n)) (hCM : Disjoint rCore.image M) (hWM : Disjoint rW.image M) :
    ValidSymStepList M rW (18 + 6 * w.val) (zTargetAxisMuxSteps hm36 rCore rW hCW w) ∧
    (∀ (β : BitAssignment n),
      (∀ u : Fin 6, β (rW ⟨18 + 6 * w.val + u.val, by have := w.isLt; have := u.isLt; omega⟩) = 0) →
      (∀ j : Fin 6,
        (symStepFwdList (zTargetAxisMuxSteps hm36 rCore rW hCW w) β)
          (rW ⟨18 + 6 * w.val + (5 - j.val), by have := w.isLt; have := j.isLt; omega⟩) =
          β (wSlot0Core rCore) *
            (β (axisBitRev6 (rElecSlot rCore 0) w j) +
              β (rW ⟨6 * w.val + j.val, by have := w.isLt; have := j.isLt; omega⟩) + 1)) ∧
      (∀ z, (∀ u : Fin 6, z ≠ rW ⟨18 + 6 * w.val + u.val, by
        have := w.isLt; have := u.isLt; omega⟩) →
        (symStepFwdList (zTargetAxisMuxSteps hm36 rCore rW hCW w) β) z = β z)) := by
  let hw := w.isLt
  let y : Fin 6 → Wire n := fun j ↦ axisBitRev6 (rElecSlot rCore 0) w j
  let c : Fin 6 → Wire n := fun j ↦ rW ⟨6 * w.val + j.val, by have := j.isLt; omega⟩
  let m : Fin 6 → Wire n := fun u ↦ rW ⟨18 + 6 * w.val + u.val, by have := u.isLt; omega⟩
  have hm_ne : ∀ a b : Fin 6, a ≠ b → m a ≠ m b := fun a b hab h ↦
    hab (Fin.ext (by
      have hv := congrArg Fin.val (rW.wires.injective h); dsimp only [m] at hv; omega))
  have hc_ne_m : ∀ a b : Fin 6, c a ≠ m b := fun a b h ↦ by
    have hv := congrArg Fin.val (rW.wires.injective h); have := a.isLt; have := b.isLt;
      dsimp only [c, m] at hv; omega
  have latCore : ∀ {z : Wire n}, z ∈ rCore.image → ∀ idx : Fin mW, rW idx ≠ z := fun hz idx heq ↦ by
    obtain ⟨i, hi⟩ := (QRegister.mem_image rCore _).mp hz
    exact hCW.ne i idx (hi.trans heq.symm)
  have hCoreW : ∀ {z : Wire n}, z ∈ rCore.image → ∀ idx : Fin mW, z ≠ rW idx :=
    fun hz idx heq ↦ (latCore hz idx heq.symm)
  have notMCore : ∀ {z : Wire n}, z ∈ rCore.image → z ∉ M :=
    fun hz hm' ↦ Finset.disjoint_left.mp hCM hz hm'
  have notMW : ∀ idx : Fin mW, rW idx ∉ M :=
    fun idx hm' ↦ Finset.disjoint_left.mp hWM ((QRegister.mem_image rW _).mpr ⟨idx, rfl⟩) hm'
  have hlist : zTargetAxisMuxSteps hm36 rCore rW hCW w =
      [ muxDiffSymStep (wSlot0Core rCore) (y 5) (c 5) (m 0) (phcHead_s0_ne_y0 rCore w 5) (hCoreW
        (wSlot0Core_mem_core rCore) _)
          (hCoreW (wSlot0Core_mem_core rCore) _) (hCoreW (phcHead_y0_mem_core rCore w 5) _) (hCoreW
            (phcHead_y0_mem_core rCore w 5) _) (hc_ne_m 5 0),
        muxDiffSymStep (wSlot0Core rCore) (y 4) (c 4) (m 1) (phcHead_s0_ne_y0 rCore w 4) (hCoreW
          (wSlot0Core_mem_core rCore) _)
          (hCoreW (wSlot0Core_mem_core rCore) _) (hCoreW (phcHead_y0_mem_core rCore w 4) _) (hCoreW
            (phcHead_y0_mem_core rCore w 4) _) (hc_ne_m 4 1),
        muxDiffSymStep (wSlot0Core rCore) (y 3) (c 3) (m 2) (phcHead_s0_ne_y0 rCore w 3) (hCoreW
          (wSlot0Core_mem_core rCore) _)
          (hCoreW (wSlot0Core_mem_core rCore) _) (hCoreW (phcHead_y0_mem_core rCore w 3) _) (hCoreW
            (phcHead_y0_mem_core rCore w 3) _) (hc_ne_m 3 2),
        muxDiffSymStep (wSlot0Core rCore) (y 2) (c 2) (m 3) (phcHead_s0_ne_y0 rCore w 2) (hCoreW
          (wSlot0Core_mem_core rCore) _)
          (hCoreW (wSlot0Core_mem_core rCore) _) (hCoreW (phcHead_y0_mem_core rCore w 2) _) (hCoreW
            (phcHead_y0_mem_core rCore w 2) _) (hc_ne_m 2 3),
        muxDiffSymStep (wSlot0Core rCore) (y 1) (c 1) (m 4) (phcHead_s0_ne_y0 rCore w 1) (hCoreW
          (wSlot0Core_mem_core rCore) _)
          (hCoreW (wSlot0Core_mem_core rCore) _) (hCoreW (phcHead_y0_mem_core rCore w 1) _) (hCoreW
            (phcHead_y0_mem_core rCore w 1) _) (hc_ne_m 1 4),
        muxDiffSymStep (wSlot0Core rCore) (y 0) (c 0) (m 5) (phcHead_s0_ne_y0 rCore w 0) (hCoreW
          (wSlot0Core_mem_core rCore) _)
          (hCoreW (wSlot0Core_mem_core rCore) _) (hCoreW (phcHead_y0_mem_core rCore w 0) _) (hCoreW
            (phcHead_y0_mem_core rCore w 0) _) (hc_ne_m 0 5) ] := rfl
  rw [hlist]
  have hs0_mem : wSlot0Core rCore ∈ rCore.image := wSlot0Core_mem_core rCore
  constructor
  · dsimp only [ValidSymStepList, muxDiffSymStep]
    refine ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_,
      ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_, ⟨by omega, rfl, ?_, ?_, trivial⟩⟩⟩⟩⟩⟩
    all_goals
      try (rw [Finset.disjoint_left]; intro z hz;
           simp only [Finset.mem_insert, Finset.mem_singleton] at hz;
           rcases hz with rfl | rfl | rfl | rfl;
           · exact notMCore hs0_mem
           · exact notMCore (phcHead_y0_mem_core rCore w _)
           · exact notMW _
           · exact notMW _)
      try (intro idx hlt; simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
           exact ⟨latCore hs0_mem idx, latCore (phcHead_y0_mem_core rCore w _) idx,
             fun h ↦ by
               have hv := congrArg Fin.val (rW.wires.injective h); dsimp only [c] at hv; omega,
             fun h ↦ by
               have hv := congrArg Fin.val (rW.wires.injective h); dsimp only [m] at hv; omega⟩)
  · intro β hClean
    have hm_clean : ∀ u : Fin 6, β (m u) = 0 := hClean
    dsimp only [symStepFwdList]
    rw [muxDiffSymStep_stepFwd (wSlot0Core rCore) (y 5) (c 5) (m 0) _ _ _ _ _ _ β (hm_clean 0)]
    let s0 := Function.update β (m 0) (β (wSlot0Core rCore) * (β (y 5) + β (c 5) + 1))
    have hs0_1 : s0 (m 1) = 0 := by simp [s0, Function.update_of_ne (hm_ne 1 0 (by
      decide)), hm_clean 1]
    rw [muxDiffSymStep_stepFwd (wSlot0Core rCore) (y 4) (c 4) (m 1) _ _ _ _ _ _ s0 hs0_1]
    let s1 := Function.update s0 (m 1) (s0 (wSlot0Core rCore) * (s0 (y 4) + s0 (c 4) + 1))
    have hs1_2 : s1 (m 2) = 0 := by
      simp [s1, s0, Function.update_of_ne (hm_ne 2 1 (by
        decide)), Function.update_of_ne (hm_ne 2 0 (by decide)), hm_clean 2]
    rw [muxDiffSymStep_stepFwd (wSlot0Core rCore) (y 3) (c 3) (m 2) _ _ _ _ _ _ s1 hs1_2]
    let s2 := Function.update s1 (m 2) (s1 (wSlot0Core rCore) * (s1 (y 3) + s1 (c 3) + 1))
    have hs2_3 : s2 (m 3) = 0 := by
      simp [s2, s1, s0, Function.update_of_ne (hm_ne 3 2 (by decide)),
        Function.update_of_ne (hm_ne 3 1 (by
          decide)), Function.update_of_ne (hm_ne 3 0 (by decide)), hm_clean 3]
    rw [muxDiffSymStep_stepFwd (wSlot0Core rCore) (y 2) (c 2) (m 3) _ _ _ _ _ _ s2 hs2_3]
    let s3 := Function.update s2 (m 3) (s2 (wSlot0Core rCore) * (s2 (y 2) + s2 (c 2) + 1))
    have hs3_4 : s3 (m 4) = 0 := by
      simp [s3, s2, s1, s0, Function.update_of_ne (hm_ne 4 3 (by decide)),
        Function.update_of_ne (hm_ne 4 2 (by
          decide)), Function.update_of_ne (hm_ne 4 1 (by decide)),
        Function.update_of_ne (hm_ne 4 0 (by decide)), hm_clean 4]
    rw [muxDiffSymStep_stepFwd (wSlot0Core rCore) (y 1) (c 1) (m 4) _ _ _ _ _ _ s3 hs3_4]
    let s4 := Function.update s3 (m 4) (s3 (wSlot0Core rCore) * (s3 (y 1) + s3 (c 1) + 1))
    have hs4_5 : s4 (m 5) = 0 := by
      simp [s4, s3, s2, s1, s0, Function.update_of_ne (hm_ne 5 4 (by decide)),
        Function.update_of_ne (hm_ne 5 3 (by
          decide)), Function.update_of_ne (hm_ne 5 2 (by decide)),
        Function.update_of_ne (hm_ne 5 1 (by
          decide)), Function.update_of_ne (hm_ne 5 0 (by decide)), hm_clean 5]
    rw [muxDiffSymStep_stepFwd (wSlot0Core rCore) (y 0) (c 0) (m 5) _ _ _ _ _ _ s4 hs4_5]
    have hs0_ne : ∀ b : Fin 6, wSlot0Core rCore ≠ m b := fun _ ↦ hCoreW hs0_mem _
    have hy_ne : ∀ a b : Fin 6, y a ≠ m b := fun a _ ↦ hCoreW (phcHead_y0_mem_core rCore w a) _
    have hm_upd : ∀ (f : BitAssignment n) (a b : Fin 6) (val : ZMod 2),
        Function.update f (m a) val (m b) = if a == b then val else f (m b) := fun f a b val ↦ by
      rcases eq_or_ne a b with rfl | h
      · simp
      · simp [h, Function.update_of_ne (hm_ne b a h.symm)]
    constructor
    · intro j
      have hj_eq : (rW ⟨18 + 6 * w.val + (5 - j.val), by
        have := w.isLt; have := j.isLt; omega⟩ : Wire n) =
          m ⟨5 - j.val, by have := j.isLt; omega⟩ := rfl
      rw [hj_eq]
      fin_cases j
      all_goals
        simp only [s4, s3, s2, s1, s0, Function.update_of_ne (hs0_ne _),
          Function.update_of_ne (hy_ne _ _), Function.update_of_ne (hc_ne_m _ _),
          hm_upd, BEq.beq]
        rfl
    · intro z hne
      have hne' : ∀ u : Fin 6, z ≠ m u := hne
      simp only [s4, s3, s2, s1, s0, Function.update_of_ne (hne' _)]
/-- Unitary matrix on `2 ^ m` qubits induced by an involutive bit-assignment permutation `f`. -/
def involutivePermUnitary {m : ℕ} (f : BitAssignment m → BitAssignment m)
    (hf : Function.Involutive f) : Unitary (2 ^ m) :=
  let e : Fin (2 ^ m) → Fin (2 ^ m) := fun x ↦ (basisBitsEquiv m).symm (f (basisBits m x))
  have he : Function.Involutive e := fun x ↦ by
    dsimp only [e]
    rw [basisBits_basisBitsEquiv_symm, hf, basisBitsEquiv_symm_basisBits]
  let M : Operator (2 ^ m) := Matrix.of fun i j ↦ if i = e j then (1 : ℂ) else 0
  have hHerm : Mᴴ = M := by
    ext i j
    have hiff : j = e i ↔ i = e j := ⟨fun h ↦ by rw [h, he], fun h ↦ by rw [h, he]⟩
    simp [M, Matrix.conjTranspose_apply, hiff]
  have hSq : M * M = 1 := by
    ext i j
    have hiff2 : ∀ k, (i = e k) ↔ (e i = k) := fun k ↦
      ⟨fun h ↦ by rw [h, he], fun h ↦ by rw [← h, he]⟩
    have hiff3 : e i = e j ↔ i = j :=
      ⟨fun h ↦ by rw [← he i, h, he j], fun h ↦ by rw [h]⟩
    simp only [M, Matrix.mul_apply, Matrix.of_apply, hiff2, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hiff3, Matrix.one_apply]
  ⟨M, by
    rw [Matrix.mem_unitaryGroup_iff]
    change M * Mᴴ = 1
    rw [hHerm, hSq]⟩
theorem ket_involutivePermUnitary {m : ℕ} (f : BitAssignment m → BitAssignment m)
    (hf : Function.Involutive f) (β : BitAssignment m) :
    (involutivePermUnitary f hf).1.mulVec (ket β) = ket (f β) := by
  ext i
  simp only [involutivePermUnitary, OctahedralOrbit.ket, basisState, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Pi.single_apply, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    basisBits_basisBitsEquiv_symm]
theorem involutivePermUnitary_mul_self {m : ℕ} (f : BitAssignment m → BitAssignment m)
    (hf : Function.Involutive f) :
    involutivePermUnitary f hf * involutivePermUnitary f hf = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  change ((involutivePermUnitary f hf).1 * (involutivePermUnitary f hf).1).mulVec (ket β) = _
  rw [← Matrix.mulVec_mulVec, ket_involutivePermUnitary, ket_involutivePermUnitary, hf]
  simp
theorem ket_embedUnitary_involutivePermUnitary {m n : ℕ} (r : QRegister m n)
    (f : BitAssignment m → BitAssignment m) (hf : Function.Involutive f) (β : BitAssignment n) :
    (r.embedUnitary (involutivePermUnitary f hf)).1.mulVec (ket β) =
      ket (writeReg β r (f (fun i ↦ β (r i)))) := by
  rw [QRegister.embedUnitary_val, embedMatrix_mulVec_ket]
  let yLoc : Fin (2 ^ m) := (basisBitsEquiv m).symm (f (fun i ↦ β (r i)))
  have hLoc : basisBits m (localIdx r β) = fun i ↦ β (r i) := basisBits_basisBitsEquiv_symm _
  have hEntry : ∀ z : Fin (2 ^ m),
      (involutivePermUnitary f hf).1 z (localIdx r β) = if z = yLoc then 1 else 0 := fun z ↦ by
    dsimp only [involutivePermUnitary, Matrix.of_apply, yLoc]
    congr 1; exact propext ⟨fun h ↦ by rwa [hLoc] at h, fun h ↦ by rwa [hLoc]⟩
  rw [Finset.sum_eq_single yLoc]
  · rw [hEntry yLoc, ite_eq_left rfl, one_smul]
    dsimp only [yLoc]; rw [basisBits_basisBitsEquiv_symm]
  · intro l _ hl
    rw [hEntry l, ite_eq_right hl, zero_smul]
  · simp
/-- Local bit-assignment permutation on `posCoreWires + 18` XORing `headTargetPoint18` onto the
  18 target wires. -/
def xorTargetLocalBits (γ : BitAssignment (posCoreWires + 18)) :
    BitAssignment (posCoreWires + 18) :=
  let γCore : BitAssignment posCoreWires := fun i ↦ γ ⟨i.val, by have := i.isLt; omega⟩
  let tgt : Fin (2 ^ 18) := headTargetPoint18 γCore
  fun idx ↦
    if h : idx.val < posCoreWires then γ idx
    else γ idx + basisBits 18 tgt ⟨idx.val - posCoreWires, by have := idx.isLt; omega⟩
theorem xorTargetLocalBits_involutive : Function.Involutive xorTargetLocalBits := by
  intro γ
  funext idx
  have hCoreEq : (fun i : Fin posCoreWires ↦ xorTargetLocalBits γ ⟨i.val, by
    have := i.isLt; omega⟩) =
      fun i : Fin posCoreWires ↦ γ ⟨i.val, by have := i.isLt; omega⟩ := by
    funext i; simp [xorTargetLocalBits, i.isLt]
  conv_lhs => rw [xorTargetLocalBits]
  rw [hCoreEq]
  by_cases h : idx.val < posCoreWires
  · simp [h, xorTargetLocalBits]
  · simp [h, xorTargetLocalBits, add_assoc, CharTwo.add_self_eq_zero]
/-- Self-inverse unitary `Unitary (2 ^ (posCoreWires + 18))` XORing `headTargetPoint18` onto
  `rSave0`. -/
def uXorTarget18 : Unitary (2 ^ (posCoreWires + 18)) :=
  involutivePermUnitary xorTargetLocalBits xorTargetLocalBits_involutive
theorem uXorTarget18_mul_self : uXorTarget18 * uXorTarget18 = 1 :=
  involutivePermUnitary_mul_self xorTargetLocalBits xorTargetLocalBits_involutive
theorem bitsVal_inj : ∀ {m : ℕ} {a b : Fin m → ZMod 2}, bitsVal a = bitsVal b → a = b
  | 0, a, b, _ => funext fun i ↦ Fin.elim0 i
  | m + 1, a, b, h => by
      have hSum : ∀ f : Fin (m + 1) → ZMod 2,
          bitsVal f = (f 0).val + 2 * bitsVal (fun i : Fin m ↦ f i.succ) := fun f ↦ by
        unfold bitsVal
        rw [Fin.sum_univ_succ, Finset.mul_sum]
        simp only [Fin.val_zero, _root_.pow_zero, mul_one, Fin.val_succ, pow_succ']
        refine congrArg ((f 0).val + ·) (Finset.sum_congr rfl fun i _ ↦ by ring)
      rw [hSum a, hSum b] at h
      have ha0 : (a 0).val < 2 := (a 0).val_lt
      have hb0 : (b 0).val < 2 := (b 0).val_lt
      have h0 : a 0 = b 0 := ZMod.val_injective 2 (by omega)
      have hTail : (fun i : Fin m ↦ a i.succ) = (fun i : Fin m ↦ b i.succ) := bitsVal_inj (by omega)
      funext i
      exact Fin.cases h0 (fun j ↦ congrFun hTail j) i
theorem zTargetSteps36_valid_and_eval {n mW : ℕ} (hm36 : 36 ≤ mW)
    (rCore : QRegister posCoreWires n) (rW : QRegister mW n)
    (hCW : rCore.DisjointWires rW)
    (M : Finset (Wire n)) (hCM : Disjoint rCore.image M) (hWM : Disjoint rW.image M) :
    ValidSymStepList M rW 0 (zTargetSteps36 hm36 rCore rW hCW) ∧
    (∀ (β : BitAssignment n),
      (∀ idx : Fin 36, β (rW ⟨idx.val, by have := idx.isLt; omega⟩) = 0) →
      (∀ (w : Fin 3) (j : Fin 6),
        (symStepFwdList (zTargetSteps36 hm36 rCore rW hCW) β)
          (rW ⟨18 + 6 * w.val + (5 - j.val), by have := w.isLt; have := j.isLt; omega⟩) =
        β (wSlot0Core rCore) *
          (β (axisBitRev6 (rElecSlot rCore 0) w j) +
            carrySeq6
              (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) w i))
              (fun i ↦ β (rHeadFine21 rCore ⟨7 * w.val + i.val + 1, by
                have := w.isLt; have := i.isLt; omega⟩))
              (1 + (β (rCosetB0 rCore w) + 1) * β (rHeadFine21 rCore ⟨7 * w.val, by
                have := w.isLt; omega⟩))
              j.val + 1)) ∧
      (∀ z, (∀ idx : Fin 36, z ≠ rW ⟨idx.val, by have := idx.isLt; omega⟩) →
        (symStepFwdList (zTargetSteps36 hm36 rCore rW hCW) β) z = β z)) := by
  obtain ⟨hvC0, heC0⟩ := zTargetAxisCarrySteps_valid_and_eval hm36 rCore rW hCW 0 M hCM hWM
  obtain ⟨hvC1, heC1⟩ := zTargetAxisCarrySteps_valid_and_eval hm36 rCore rW hCW 1 M hCM hWM
  obtain ⟨hvC2, heC2⟩ := zTargetAxisCarrySteps_valid_and_eval hm36 rCore rW hCW 2 M hCM hWM
  obtain ⟨hvM0, heM0⟩ := zTargetAxisMuxSteps_valid_and_eval hm36 rCore rW hCW 0 M hCM hWM
  obtain ⟨hvM1, heM1⟩ := zTargetAxisMuxSteps_valid_and_eval hm36 rCore rW hCW 1 M hCM hWM
  obtain ⟨hvM2, heM2⟩ := zTargetAxisMuxSteps_valid_and_eval hm36 rCore rW hCW 2 M hCM hWM
  have hlenC : ∀ w : Fin 3, (zTargetAxisCarrySteps hm36 rCore rW hCW w).length = 6 :=
    fun _ ↦ by simp [zTargetAxisCarrySteps]
  have hlenM : ∀ w : Fin 3, (zTargetAxisMuxSteps hm36 rCore rW hCW w).length = 6 :=
    fun _ ↦ by simp [zTargetAxisMuxSteps]
  constructor
  · dsimp only [zTargetSteps36]
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    rw [validSymStepList_append]; refine ⟨hvC0, ?_⟩; rw [hlenC 0]
    rw [validSymStepList_append]; refine ⟨hvC1, ?_⟩; rw [hlenC 1]
    rw [validSymStepList_append]; refine ⟨hvC2, ?_⟩; rw [hlenC 2]
    rw [validSymStepList_append]; refine ⟨hvM0, ?_⟩; rw [hlenM 0]
    rw [validSymStepList_append]; exact ⟨hvM1, hvM2⟩
  · intro β hClean
    let b1 := symStepFwdList (zTargetAxisCarrySteps hm36 rCore rW hCW 0) β
    let b2 := symStepFwdList (zTargetAxisCarrySteps hm36 rCore rW hCW 1) b1
    let b3 := symStepFwdList (zTargetAxisCarrySteps hm36 rCore rW hCW 2) b2
    let b4 := symStepFwdList (zTargetAxisMuxSteps hm36 rCore rW hCW 0) b3
    let b5 := symStepFwdList (zTargetAxisMuxSteps hm36 rCore rW hCW 1) b4
    let b6 := symStepFwdList (zTargetAxisMuxSteps hm36 rCore rW hCW 2) b5
    have hSeq : symStepFwdList (zTargetSteps36 hm36 rCore rW hCW) β = b6 := by
      dsimp only [zTargetSteps36, b6, b5, b4, b3, b2, b1]
      simp only [symStepFwdList_append]
    rw [hSeq]
    have hw_ne : ∀ (a b : ℕ) (ha : a < mW) (hb : b < mW), a ≠ b → rW ⟨a, ha⟩ ≠ rW ⟨b, hb⟩ :=
      fun a b _ _ hab h ↦ hab (congrArg Fin.val (rW.wires.injective h))
    have latCore : ∀ {z : Wire n}, z ∈ rCore.image → ∀ idx : Fin mW, z ≠ rW idx := fun hz idx heq ↦
      by
      obtain ⟨i, hi⟩ := (QRegister.mem_image rCore _).mp hz
      exact hCW.ne i idx (hi.trans heq)
    obtain ⟨hc0, ho0⟩ := heC0 β (fun j ↦ hClean ⟨6 * (0 : Fin 3).val + j.val, by
      have := j.isLt; omega⟩)
    obtain ⟨hc1, ho1⟩ := heC1 b1 (fun j ↦ by
      dsimp only [b1]
      rw [ho0 _ (fun i ↦ hw_ne _ _ _ _ (by have := j.isLt; have := i.isLt; omega))]
      exact hClean ⟨6 + j.val, by have := j.isLt; omega⟩)
    obtain ⟨hc2, ho2⟩ := heC2 b2 (fun j ↦ by
      dsimp only [b2]; rw [ho1 _ (fun i ↦ hw_ne _ _ _ _ (by have := j.isLt; have := i.isLt; omega))]
      dsimp only [b1]; rw [ho0 _ (fun i ↦ hw_ne _ _ _ _ (by have := j.isLt; have := i.isLt; omega))]
      exact hClean ⟨12 + j.val, by have := j.isLt; omega⟩)
    have hCore_b3 : ∀ {z : Wire n}, z ∈ rCore.image → b3 z = β z := fun hz ↦ by
      dsimp only [b3]; rw [ho2 _ (fun i ↦ latCore hz _)]
      dsimp only [b2]; rw [ho1 _ (fun i ↦ latCore hz _)]
      dsimp only [b1]; rw [ho0 _ (fun i ↦ latCore hz _)]
    obtain ⟨hm0, hoM0⟩ := heM0 b3 (fun u ↦ by
      dsimp only [b3]; rw [ho2 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      dsimp only [b2]; rw [ho1 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      dsimp only [b1]; rw [ho0 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      exact hClean ⟨18 + u.val, by have := u.isLt; omega⟩)
    obtain ⟨hm1, hoM1⟩ := heM1 b4 (fun u ↦ by
      dsimp only [b4]; rw [hoM0 _ (fun i ↦ hw_ne _ _ _ _ (by
        have := u.isLt; have := i.isLt; omega))]
      dsimp only [b3]; rw [ho2 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      dsimp only [b2]; rw [ho1 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      dsimp only [b1]; rw [ho0 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      exact hClean ⟨24 + u.val, by have := u.isLt; omega⟩)
    obtain ⟨hm2, hoM2⟩ := heM2 b5 (fun u ↦ by
      dsimp only [b5]; rw [hoM1 _ (fun i ↦ hw_ne _ _ _ _ (by
        have := u.isLt; have := i.isLt; omega))]
      dsimp only [b4]; rw [hoM0 _ (fun i ↦ hw_ne _ _ _ _ (by
        have := u.isLt; have := i.isLt; omega))]
      dsimp only [b3]; rw [ho2 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      dsimp only [b2]; rw [ho1 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      dsimp only [b1]; rw [ho0 _ (fun i ↦ hw_ne _ _ _ _ (by have := u.isLt; have := i.isLt; omega))]
      exact hClean ⟨30 + u.val, by have := u.isLt; omega⟩)
    have hs0_mem : wSlot0Core rCore ∈ rCore.image := wSlot0Core_mem_core rCore
    constructor
    · intro w j
      fin_cases w
      · change b6 (rW ⟨18 + 6 * (0 : Fin 3).val + (5 - j.val), by have := j.isLt; omega⟩) =
          β (wSlot0Core rCore) *
            (β (axisBitRev6 (rElecSlot rCore 0) 0 j) +
              carrySeq6 (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) 0 i))
                (fun i ↦ β (rHeadFine21 rCore ⟨7 * (0 : Fin 3).val + i.val + 1, by
                  have := i.isLt; omega⟩))
                (1 + (β (rCosetB0 rCore 0) + 1) * β (rHeadFine21 rCore ⟨7 * (0 : Fin 3).val,
                  by omega⟩)) j.val + 1)
        dsimp only [b6]; rw [hoM2 _ (fun u ↦ hw_ne _ _ _ _ (by
          have := j.isLt; have := u.isLt; omega))]
        dsimp only [b5]; rw [hoM1 _ (fun u ↦ hw_ne _ _ _ _ (by
          have := j.isLt; have := u.isLt; omega))]
        dsimp only [b4]; rw [hm0 j, hCore_b3 hs0_mem, hCore_b3 (phcHead_y0_mem_core rCore 0 j)]
        have hc_b3 : b3 (rW ⟨6 * (0 : Fin 3).val + j.val, by have := j.isLt; omega⟩) =
            b1 (rW ⟨6 * (0 : Fin 3).val + j.val, by have := j.isLt; omega⟩) := by
          dsimp only [b3]; rw [ho2 _ (fun i ↦ hw_ne _ _ _ _ (by
            have := j.isLt; have := i.isLt; omega))]
          dsimp only [b2]; rw [ho1 _ (fun i ↦ hw_ne _ _ _ _ (by
            have := j.isLt; have := i.isLt; omega))]
        rw [hc_b3]; dsimp only [b1]; rw [hc0 j]
      · change b6 (rW ⟨18 + 6 * (1 : Fin 3).val + (5 - j.val), by have := j.isLt; omega⟩) =
          β (wSlot0Core rCore) *
            (β (axisBitRev6 (rElecSlot rCore 0) 1 j) +
              carrySeq6 (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) 1 i))
                (fun i ↦ β (rHeadFine21 rCore ⟨7 * (1 : Fin 3).val + i.val + 1, by
                  have := i.isLt; omega⟩))
                (1 + (β (rCosetB0 rCore 1) + 1) * β (rHeadFine21 rCore ⟨7 * (1 : Fin 3).val,
                  by omega⟩)) j.val + 1)
        dsimp only [b6]; rw [hoM2 _ (fun u ↦ hw_ne _ _ _ _ (by
          have := j.isLt; have := u.isLt; omega))]
        dsimp only [b5]; rw [hm1 j]
        have hCore_b4 : ∀ {z : Wire n}, z ∈ rCore.image → b4 z = β z := fun hz ↦ by
          dsimp only [b4]; exact (hoM0 _ (fun u ↦ latCore hz _)).trans (hCore_b3 hz)
        rw [hCore_b4 hs0_mem, hCore_b4 (phcHead_y0_mem_core rCore 1 j)]
        have hc_b4 : b4 (rW ⟨6 * (1 : Fin 3).val + j.val, by have := j.isLt; omega⟩) =
            b2 (rW ⟨6 * (1 : Fin 3).val + j.val, by have := j.isLt; omega⟩) := by
          dsimp only [b4]; rw [hoM0 _ (fun u ↦ hw_ne _ _ _ _ (by
            have := j.isLt; have := u.isLt; omega))]
          dsimp only [b3]; rw [ho2 _ (fun i ↦ hw_ne _ _ _ _ (by
            have := j.isLt; have := i.isLt; omega))]
        rw [hc_b4]; dsimp only [b2]; rw [hc1 j]
        have hy1 : (fun i : Fin 6 ↦ b1 (axisBitRev6 (rElecSlot rCore 0) 1 i)) =
            fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) 1 i) :=
          funext fun i ↦ by
            dsimp only [b1]; exact ho0 _ (fun u ↦ latCore (phcHead_y0_mem_core rCore 1 i) _)
        have hq1 : (fun i : Fin 6 ↦ b1 (rHeadFine21 rCore ⟨7 * (1 : Fin 3).val + i.val + 1, by
          have := i.isLt; omega⟩)) =
            fun i ↦ β (rHeadFine21 rCore ⟨7 * (1 : Fin 3).val + i.val + 1, by
              have := i.isLt; omega⟩) :=
          funext fun i ↦ by
            dsimp only [b1]; exact ho0 _ (fun u ↦ latCore (phcHead_dBit_mem_core rCore _) _)
        have hb0_1 : b1 (rCosetB0 rCore 1) = β (rCosetB0 rCore 1) := by
          dsimp only [b1]; exact ho0 _ (fun u ↦ latCore (phcHead_b0_mem_core rCore 1) _)
        have hd0_1 : b1 (rHeadFine21 rCore ⟨7 * (1 : Fin 3).val,
          by omega⟩) = β (rHeadFine21 rCore ⟨7 * (1 : Fin 3).val, by omega⟩) := by
          dsimp only [b1]; exact ho0 _ (fun u ↦ latCore (phcHead_dBit_mem_core rCore _) _)
        rw [hy1, hq1, hb0_1, hd0_1]
      · change b6 (rW ⟨18 + 6 * (2 : Fin 3).val + (5 - j.val), by have := j.isLt; omega⟩) =
          β (wSlot0Core rCore) *
            (β (axisBitRev6 (rElecSlot rCore 0) 2 j) +
              carrySeq6 (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) 2 i))
                (fun i ↦ β (rHeadFine21 rCore ⟨7 * (2 : Fin 3).val + i.val + 1, by
                  have := i.isLt; omega⟩))
                (1 + (β (rCosetB0 rCore 2) + 1) * β (rHeadFine21 rCore ⟨7 * (2 : Fin 3).val,
                  by omega⟩)) j.val + 1)
        dsimp only [b6]; rw [hm2 j]
        have hCore_b5 : ∀ {z : Wire n}, z ∈ rCore.image → b5 z = β z := fun hz ↦ by
          dsimp only [b5]; rw [hoM1 _ (fun u ↦ latCore hz _)]
          dsimp only [b4]; rw [hoM0 _ (fun u ↦ latCore hz _)]
          exact hCore_b3 hz
        rw [hCore_b5 hs0_mem, hCore_b5 (phcHead_y0_mem_core rCore 2 j)]
        have hc_b5 : b5 (rW ⟨6 * (2 : Fin 3).val + j.val, by have := j.isLt; omega⟩) =
            b3 (rW ⟨6 * (2 : Fin 3).val + j.val, by have := j.isLt; omega⟩) := by
          dsimp only [b5]; rw [hoM1 _ (fun u ↦ hw_ne _ _ _ _ (by
            have := j.isLt; have := u.isLt; omega))]
          dsimp only [b4]; rw [hoM0 _ (fun u ↦ hw_ne _ _ _ _ (by
            have := j.isLt; have := u.isLt; omega))]
        rw [hc_b5]; dsimp only [b3]; rw [hc2 j]
        have hCore_b2 : ∀ {z : Wire n}, z ∈ rCore.image → b2 z = β z := fun hz ↦ by
          dsimp only [b2]; rw [ho1 _ (fun u ↦ latCore hz _)]
          dsimp only [b1]; exact ho0 _ (fun u ↦ latCore hz _)
        have hy2 : (fun i : Fin 6 ↦ b2 (axisBitRev6 (rElecSlot rCore 0) 2 i)) =
            fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) 2 i) :=
          funext fun i ↦ hCore_b2 (phcHead_y0_mem_core rCore 2 i)
        have hq2 : (fun i : Fin 6 ↦ b2 (rHeadFine21 rCore ⟨7 * (2 : Fin 3).val + i.val + 1, by
          have := i.isLt; omega⟩)) =
            fun i ↦ β (rHeadFine21 rCore ⟨7 * (2 : Fin 3).val + i.val + 1, by
              have := i.isLt; omega⟩) :=
          funext fun i ↦ hCore_b2 (phcHead_dBit_mem_core rCore _)
        have hb0_2 : b2 (rCosetB0 rCore 2) = β (rCosetB0 rCore 2) :=
          hCore_b2 (phcHead_b0_mem_core rCore 2)
        have hd0_2 : b2 (rHeadFine21 rCore ⟨7 * (2 : Fin 3).val,
          by omega⟩) = β (rHeadFine21 rCore ⟨7 * (2 : Fin 3).val, by omega⟩) :=
          hCore_b2 (phcHead_dBit_mem_core rCore _)
        rw [hy2, hq2, hb0_2, hd0_2]
    · intro z hne
      dsimp only [b6]; rw [hoM2 _ (fun u ↦ hne ⟨30 + u.val, by have := u.isLt; omega⟩)]
      dsimp only [b5]; rw [hoM1 _ (fun u ↦ hne ⟨24 + u.val, by have := u.isLt; omega⟩)]
      dsimp only [b4]; rw [hoM0 _ (fun u ↦ hne ⟨18 + u.val, by have := u.isLt; omega⟩)]
      dsimp only [b3]; rw [ho2 _ (fun u ↦ hne ⟨12 + u.val, by have := u.isLt; omega⟩)]
      dsimp only [b2]; rw [ho1 _ (fun u ↦ hne ⟨6 + u.val, by have := u.isLt; omega⟩)]
      dsimp only [b1]; rw [ho0 _ (fun u ↦ hne ⟨0 + u.val, by have := u.isLt; omega⟩)]
theorem headTargetPoint18_bit_eq_mux_xor_q {n : ℕ}
    (rCore : QRegister posCoreWires n) (β : BitAssignment n)
    (w : Fin 3) (j : Fin 6) :
    basisBits 18 (headTargetPoint18 (fun i ↦ β (rCore i)))
      ⟨6 * w.val + (5 - j.val), by have := w.isLt; have := j.isLt; omega⟩ =
    β (wSlot0Core rCore) *
      (β (axisBitRev6 (rElecSlot rCore 0) w j) +
        carrySeq6
          (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) w i))
          (fun i ↦ β (rHeadFine21 rCore ⟨7 * w.val + i.val + 1, by
            have := w.isLt; have := i.isLt; omega⟩))
          (1 + (β (rCosetB0 rCore w) + 1) * β (rHeadFine21 rCore ⟨7 * w.val, by
            have := w.isLt; omega⟩))
          j.val + 1) +
    β (rHeadFine21 rCore ⟨7 * w.val + j.val + 1, by have := w.isLt; have := j.isLt; omega⟩) := by
  let βCore : BitAssignment posCoreWires := fun i ↦ β (rCore i)
  let lhs6 : Fin 6 → ZMod 2 := fun u ↦
    basisBits 18 (headTargetPoint18 βCore)
      ⟨6 * w.val + (5 - u.val), by have := w.isLt; have := u.isLt; omega⟩
  let rhs6 : Fin 6 → ZMod 2 := fun u ↦
    β (wSlot0Core rCore) *
      (β (axisBitRev6 (rElecSlot rCore 0) w u) +
        carrySeq6
          (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) w i))
          (fun i ↦ β (rHeadFine21 rCore ⟨7 * w.val + i.val + 1, by
            have := w.isLt; have := i.isLt; omega⟩))
          (1 + (β (rCosetB0 rCore w) + 1) * β (rHeadFine21 rCore ⟨7 * w.val, by
            have := w.isLt; omega⟩))
          u.val + 1) +
    β (rHeadFine21 rCore ⟨7 * w.val + u.val + 1, by have := w.isLt; have := u.isLt; omega⟩)
  suffices h6 : lhs6 = rhs6 from congrFun h6 j
  apply bitsVal_inj
  have hLhs : bitsVal lhs6 = (headTargetCoord64 βCore w).val := by
    have hSlot := (slotSubGridCoord64_eq_iff_extractIndex (QRegExt.ofFin 18)
      (headTargetPoint18 βCore) (headTargetCoord64 βCore)).mpr (by
        have hex : (QRegExt.ofFin 18).extractIndex (headTargetPoint18 βCore) =
            headTargetPoint18 βCore := by
          apply (basisBitsEquiv 18).injective
          change basisBits 18 ((QRegExt.ofFin 18).extractIndex (headTargetPoint18 βCore)) =
            basisBits 18 (headTargetPoint18 βCore)
          funext idx
          rw [(QRegExt.ofFin 18).basisBits_extractIndex]; rfl
        rw [hex]; rfl)
    exact congrArg Fin.val (congrFun hSlot w)
  rw [hLhs]
  symm
  dsimp only [rhs6]
  rw [mux_target_bitsVal_eq]
  let rCore0 := QRegExt.ofFin posCoreWires
  have hwS0 : β (wSlot0Core rCore) = βCore (wSlot0Core rCore0) := rfl
  have hyEq : (fun i : Fin 6 ↦ β (axisBitRev6 (rElecSlot rCore 0) w i)) =
      fun i ↦ βCore (axisBitRev6 (rElecSlot rCore0 0) w i) := rfl
  have hqEq : (fun i : Fin 6 ↦ β (rHeadFine21 rCore ⟨7 * w.val + i.val + 1, by
    have := w.isLt; have := i.isLt; omega⟩)) =
      fun i ↦ βCore (rHeadFine21 rCore0 ⟨7 * w.val + i.val + 1, by
        have := w.isLt; have := i.isLt; omega⟩) := rfl
  have hb0Eq : β (rCosetB0 rCore w) = βCore (rCosetB0 rCore0 w) := rfl
  have hd0Eq : β (rHeadFine21 rCore ⟨7 * w.val, by have := w.isLt; omega⟩) =
      βCore (rHeadFine21 rCore0 ⟨7 * w.val, by have := w.isLt; omega⟩) := rfl
  rw [hwS0, hyEq, hqEq, hb0Eq, hd0Eq]
  let rAx7 : QRegister 7 posCoreWires := (rHeadFine21 rCore0).slice (7 * w.val) 7 (by
    have := w.isLt; omega)
  have hq_val : bitsVal (fun i : Fin 6 ↦ βCore (rHeadFine21 rCore0 ⟨7 * w.val + i.val + 1, by
    have := w.isLt; have := i.isLt; omega⟩)) =
      (fineCoordOfReg21 (rHeadFine21 rCore0) βCore w).val / 2 := by
    have hsl : bitsVal (fun i : Fin 6 ↦ βCore (rHeadFine21 rCore0 ⟨7 * w.val + i.val + 1, by
      have := w.isLt; have := i.isLt; omega⟩)) =
        regVal (rAx7.slice 1 6 (by omega)) βCore := by
      unfold bitsVal regVal
      refine Finset.sum_congr rfl fun i _ ↦ congrArg (fun q ↦ (βCore q).val * 2 ^ i.val) ?_
      dsimp only [rAx7]
      simp only [QRegister.slice_apply]
      exact congrArg (rHeadFine21 rCore0).wires (Fin.ext (by dsimp only; omega))
    rw [hsl, regVal_slice1_eq_div2]; rfl
  have hd_expand : (βCore (rHeadFine21 rCore0 ⟨7 * w.val, by have := w.isLt; omega⟩)).val +
      2 * bitsVal (fun i : Fin 6 ↦ βCore (rHeadFine21 rCore0 ⟨7 * w.val + i.val + 1, by
        have := w.isLt; have := i.isLt; omega⟩)) =
      (fineCoordOfReg21 (rHeadFine21 rCore0) βCore w).val := by
    symm
    change ∑ x : Fin 7, (βCore (rAx7 x)).val * 2 ^ x.val = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, _root_.pow_zero, mul_one]
    have h0_eq : rAx7 0 = rHeadFine21 rCore0 ⟨7 * w.val, by have := w.isLt; omega⟩ := by
      dsimp only [rAx7]
      simp only [QRegister.slice_apply]
      exact congrArg (rHeadFine21 rCore0).wires (Fin.ext (by dsimp only [Fin.val_zero]; omega))
    have htail : (∑ i : Fin 6, (βCore (rAx7 i.succ)).val * 2 ^ i.succ.val) =
        2 * bitsVal (fun i : Fin 6 ↦ βCore (rHeadFine21 rCore0 ⟨7 * w.val + i.val + 1, by
          have := w.isLt; have := i.isLt; omega⟩)) := by
      unfold bitsVal
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have his : rAx7 i.succ = rHeadFine21 rCore0 ⟨7 * w.val + i.val + 1, by
        have := w.isLt; have := i.isLt; omega⟩ := by
        dsimp only [rAx7]
        simp only [QRegister.slice_apply]
        exact congrArg (rHeadFine21 rCore0).wires (Fin.ext (by dsimp only [Fin.val_succ]; omega))
      rw [his, Fin.val_succ, pow_succ']; ring
    rw [h0_eq, htail]
  have hb0_if : (if βCore (rCosetB0 rCore0 w) = 1 then (1 : ℕ) else 0) =
      if parity3OfReg (rCosetB0 rCore0) βCore w then 1 else 0 := by
    dsimp [parity3OfReg]
    by_cases hb : βCore (rCosetB0 rCore0 w) = 1 <;> simp [hb]
  rw [hd_expand, hq_val, hb0_if]
  unfold headTargetCoord64 headS0Bool
  dsimp only [rCore0]
  by_cases hs0 : Bool.not (βCore (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) = true
  · simp only [hs0, ↓reduceIte]
  · simp only [Bool.eq_false_iff.mpr hs0, Bool.false_eq_true, ↓reduceIte]
    exact (PosSlots24BranchConcrete.anchorSubTarget1D_fst_val_eq
      (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) βCore w)
      (parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) βCore w)
      (fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) βCore w)).symm
theorem ket_embedUnitary_uXorTarget18 {n : ℕ} (rCore : QRegister posCoreWires n)
    (rSave0 : QRegister 18 n) (hCT : rCore.DisjointWires rSave0) (β : BitAssignment n) :
    ((rCore.concat rSave0 hCT).embedUnitary uXorTarget18).1.mulVec (ket β) = ket (writeReg β
    rSave0 fun k ↦ β (rSave0 k) + basisBits 18 (headTargetPoint18 (fun i ↦ β (rCore i))) k)
    := by
  let rCZ := rCore.concat rSave0 hCT
  rw [uXorTarget18, ket_embedUnitary_involutivePermUnitary]
  refine congrArg ket (funext fun z ↦ ?_)
  have hCoreLoc : (fun i : Fin posCoreWires ↦ β (rCZ ⟨i.val, by have := i.isLt; omega⟩)) =
      fun i : Fin posCoreWires ↦ β (rCore i) := by
    funext i
    have hwire : rCZ (Fin.castAdd 18 i) = rCore i := QRegister.concat_apply_left rCore rSave0 hCT i
    exact congrArg β hwire
  by_cases hT : ∃ k : Fin 18, rSave0 k = z
  · obtain ⟨k, rfl⟩ := hT
    have hkCZ : rCZ ⟨posCoreWires + k.val, by have := k.isLt; omega⟩ = rSave0 k :=
      QRegister.concat_apply_right rCore rSave0 hCT k
    rw [← hkCZ, writeReg_apply_reg, hkCZ, writeReg_apply_reg]
    dsimp only [xorTargetLocalBits]
    have hnot : ¬ (posCoreWires + k.val < posCoreWires) := by omega
    rw [dite_eq_right hnot, hkCZ, hCoreLoc]
    have hsub : (⟨posCoreWires + k.val - posCoreWires, by have := k.isLt; omega⟩ : Fin 18) = k :=
      Fin.ext (by dsimp only; omega)
    rw [hsub]
  · have hT' : z ∉ Set.range rSave0.wires := hT
    rw [writeReg_apply_of_not_mem _ _ _ _ hT']
    by_cases hC : ∃ i : Fin posCoreWires, rCore i = z
    · obtain ⟨i, rfl⟩ := hC
      have hiCZ : rCZ ⟨i.val, by have := i.isLt; omega⟩ = rCore i :=
        QRegister.concat_apply_left rCore rSave0 hCT i
      rw [← hiCZ, writeReg_apply_reg]
      dsimp only [xorTargetLocalBits]
      rw [dite_eq_left i.isLt]
    · have hCZ' : z ∉ Set.range rCZ.wires := by
        rintro ⟨idx, hidx⟩
        dsimp only [rCZ] at hidx
        refine Fin.addCases
          (motive := fun idx ↦ (rCore.concat rSave0 hCT) idx = z → False)
          (fun i hEq ↦ hC ⟨i, by rwa [QRegister.concat_apply_left] at hEq⟩)
          (fun k hEq ↦ hT ⟨k, by rwa [QRegister.concat_apply_right] at hEq⟩)
          idx hidx
      exact writeReg_apply_of_not_mem _ _ _ _ hCZ'
theorem list_unitary_val_prod_assoc {D : ℕ} :
    ∀ (L : List (Unitary D)), (L.prod).1 = (L.map Subtype.val).prod
  | [] => rfl
  | u :: us => by simp [List.prod_cons, Submonoid.coe_mul, list_unitary_val_prod_assoc us]
theorem diagonal_mul_diagonal_op_assoc {D : ℕ} (d₁ d₂ : Fin D → ℂ) :
    (Matrix.diagonal d₁ : Operator D) * Matrix.diagonal d₂ = Matrix.diagonal
    (fun i ↦ d₁ i * d₂ i) := Matrix.diagonal_mul_diagonal d₁ d₂
theorem diagonal_comm_op_assoc {D : ℕ} (d₁ d₂ : Fin D → ℂ) : (Matrix.diagonal d₁ : Operator D)
    * Matrix.diagonal d₂ = Matrix.diagonal d₂ * Matrix.diagonal d₁ := by
  rw [diagonal_mul_diagonal_op_assoc, diagonal_mul_diagonal_op_assoc]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
theorem diagonal_one_op_assoc {D : ℕ} : (Matrix.diagonal (1 : Fin D → ℂ) : Operator D) = 1 :=
    Matrix.diagonal_one
theorem list_ofFn_diagonal_prod_assoc {D : ℕ} :
    ∀ {m : ℕ} (g : Fin m → Fin D → ℂ),
      (List.ofFn fun i : Fin m ↦ Matrix.diagonal (g i)).prod =
        Matrix.diagonal (fun x : Fin D ↦ ∏ i : Fin m, g i x)
  | 0, _ => by simp [Matrix.diagonal_one]
  | m + 1, g => by
      rw [List.ofFn_succ, List.prod_cons,
          list_ofFn_diagonal_prod_assoc (fun i : Fin m ↦ g i.succ),
          Matrix.diagonal_mul_diagonal]
      congr 1; funext x; rw [Fin.prod_univ_succ]
theorem omega128_finset_sum_assoc {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    omega128 (∑ i ∈ s, f i) = ∏ i ∈ s, omega128 (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [omega128_zero]
  | cons a s _ ih => rw [Finset.sum_cons, Finset.prod_cons, omega128_add, ih]
theorem bitsVal_basisBits6 : ∀ u : Fin 64, bitsVal (basisBits 6 u) = u.val := by decide
theorem bitsVal_basisBits7 : ∀ s : Fin 128, bitsVal (basisBits 7 s) = s.val := by decide
theorem basisBits6_bitsVal (γ : BitAssignment 6) : basisBits 6
    ⟨bitsVal γ, bitsVal_lt_two_pow γ⟩ = γ := bitsVal_inj (bitsVal_basisBits6 _)
theorem basisBits7_bitsVal (γ : BitAssignment 7) : basisBits 7
    ⟨bitsVal γ, bitsVal_lt_two_pow γ⟩ = γ := bitsVal_inj (bitsVal_basisBits7 _)
/-- `0-T`, `count TOFF = 0` 1-axis Point-QFT Clifford circuit on 13 wires (`z_0..z_5` ++
  `s_0..s_6`):
applies `S` on `s_1`, `S†` on `s_2..s_5`, `Z` on `s_6`, and 6 `cliffordCZ` gates on `(z_r, s_r)`. -/
def cPointSumClifford13 : Circuit 13 :=
  let z : Fin 6 → Wire 13 := fun r ↦ ⟨r.val, by have := r.isLt; omega⟩
  let s : Fin 7 → Wire 13 := fun k ↦ ⟨6 + k.val, by have := k.isLt; omega⟩
  Circuit.S (s 1) ;;ᶜ
  (Circuit.S (s 2)).inverse ;;ᶜ
  (Circuit.S (s 3)).inverse ;;ᶜ
  (Circuit.S (s 4)).inverse ;;ᶜ
  (Circuit.S (s 5)).inverse ;;ᶜ
  Circuit.Z (s 6) ;;ᶜ
  DyadicQft64.cliffordCZ (z 5) (s 5) (by decide) ;;ᶜ
  DyadicQft64.cliffordCZ (z 4) (s 4) (by decide) ;;ᶜ
  DyadicQft64.cliffordCZ (z 3) (s 3) (by decide) ;;ᶜ
  DyadicQft64.cliffordCZ (z 2) (s 2) (by decide) ;;ᶜ
  DyadicQft64.cliffordCZ (z 1) (s 1) (by decide) ;;ᶜ
  DyadicQft64.cliffordCZ (z 0) (s 0) (by decide)
@[simp] theorem count_cPointSumClifford13_toff : cPointSumClifford13.count TOFF = 0 := by decide
@[simp] theorem count_cPointSumClifford13_t : cPointSumClifford13.count T = 0 := by decide
@[simp] theorem count_cPointSumClifford13Inv_toff : cPointSumClifford13.inverse.count TOFF = 0 := by
  decide
@[simp] theorem count_cPointSumClifford13Inv_t : cPointSumClifford13.inverse.count T = 0 := by
  decide
/-- `0-T`, `count TOFF = 0` 1-axis single-electron Point-QFT Clifford circuit on 6 wires (`S†` on
  `u_1`, `S` on `u_2..u_5`). -/
def cPointElecClifford6 : Circuit 6 :=
  (Circuit.S 1).inverse ;;ᶜ
  Circuit.S 2 ;;ᶜ
  Circuit.S 3 ;;ᶜ
  Circuit.S 4 ;;ᶜ
  Circuit.S 5
@[simp] theorem count_cPointElecClifford6_toff : cPointElecClifford6.count TOFF = 0 := by decide
@[simp] theorem count_cPointElecClifford6_t : cPointElecClifford6.count T = 0 := by decide
@[simp] theorem count_cPointElecClifford6Inv_toff : cPointElecClifford6.inverse.count TOFF = 0 := by
  decide
@[simp] theorem count_cPointElecClifford6Inv_t : cPointElecClifford6.inverse.count T = 0 := by
  decide
theorem basisBits6_val_eq_bit6 :
    ∀ (z : Fin 64) (r : Fin 6), (basisBits 6 z r).val = bit6 z r := by decide
theorem basisBits7_val_eq_bit7 :
    ∀ (s : Fin 128) (k : Fin 7),
      (basisBits 7 s k).val = StageAPointPhase128OnStep.bit7 s k := by decide
theorem cPointElecClifford6_eval_ket_u (u : Fin 64) : cPointElecClifford6.eval.1.mulVec
    (ket (basisBits 6 u)) = omega128 (pointElecCliffordExp128 u) • ket (basisBits 6 u) := by
  have hp := (DyadicQft64.PhasePerm.gateSDag (1 : Wire 6)).seq ((DyadicQft64.PhasePerm.gateS
      2).seq ((DyadicQft64.PhasePerm.gateS 3).seq ((DyadicQft64.PhasePerm.gateS 4).seq
      (DyadicQft64.PhasePerm.gateS 5))))
  have hev := hp.evolve (basisBits 6 u)
  change cPointElecClifford6.eval.1.mulVec (basisKet (basisBits 6 u)) = _ at hev
  rw [ket_eq_basisKet, hev]
  clear hp hev
  dsimp only [Function.comp_apply, id_eq]
  congr 1
  simp only [DyadicQft64.dyadicTurn_eq_omega128, ← omega128_add]
  apply omega128_eq_of_emod_eq
  revert u; decide
theorem cPointElecClifford6_eval_ket (β : BitAssignment 6) :
    cPointElecClifford6.eval.1.mulVec (ket β) =
      omega128 (pointElecCliffordExp128 ⟨bitsVal β, bitsVal_lt_two_pow β⟩) • ket β := by
  conv_lhs => rw [← basisBits6_bitsVal β]
  rw [cPointElecClifford6_eval_ket_u, basisBits6_bitsVal]
theorem cPointSumClifford13_eval_ket (β : BitAssignment 13) :
    let z : Fin 64 := ⟨bitsVal (fun r : Fin 6 ↦ β ⟨r.val, by have := r.isLt; omega⟩),
      bitsVal_lt_two_pow _⟩
    let s : Fin 128 := ⟨bitsVal (fun k : Fin 7 ↦ β ⟨6 + k.val, by have := k.isLt; omega⟩),
      bitsVal_lt_two_pow _⟩
    cPointSumClifford13.eval.1.mulVec (ket β) =
      omega128 (pointSumCliffordExp128 z s) • ket β := by
  intro z s
  let zw : Fin 6 → Wire 13 := fun r ↦ ⟨r.val, by have := r.isLt; omega⟩
  let sw : Fin 7 → Wire 13 := fun k ↦ ⟨6 + k.val, by have := k.isLt; omega⟩
  have hp := (DyadicQft64.PhasePerm.gateS (sw 1)).seq ((DyadicQft64.PhasePerm.gateSDag (sw
      2)).seq ((DyadicQft64.PhasePerm.gateSDag (sw 3)).seq ((DyadicQft64.PhasePerm.gateSDag
      (sw 4)).seq ((DyadicQft64.PhasePerm.gateSDag (sw 5)).seq ((DyadicQft64.PhasePerm.gateZ
      (sw 6)).seq ((DyadicQft64.phasePerm_cliffordCZ (zw 5) (sw 5) (by decide)).seq
      ((DyadicQft64.phasePerm_cliffordCZ (zw 4) (sw 4) (by decide)).seq
      ((DyadicQft64.phasePerm_cliffordCZ (zw 3) (sw 3) (by decide)).seq
      ((DyadicQft64.phasePerm_cliffordCZ (zw 2) (sw 2) (by decide)).seq
      ((DyadicQft64.phasePerm_cliffordCZ (zw 1) (sw 1) (by decide)).seq
      (DyadicQft64.phasePerm_cliffordCZ (zw 0) (sw 0) (by decide))))))))))))
  have hev := hp.evolve β
  change cPointSumClifford13.eval.1.mulVec (basisKet β) = _ at hev
  rw [ket_eq_basisKet, hev]
  dsimp only [Function.comp_apply, id_eq]
  congr 1
  simp only [DyadicQft64.dyadicTurn_eq_omega128, ← omega128_add]
  apply omega128_eq_of_emod_eq
  have hz_b : ∀ r : Fin 6, (β (zw r)).val = bit6 z r := fun r ↦ by
    have hb : (fun i : Fin 6 ↦ β (zw i)) = basisBits 6 z := (basisBits6_bitsVal _).symm
    have hr := congrFun hb r
    rw [hr]; exact basisBits6_val_eq_bit6 z r
  have hs_b : ∀ k : Fin 7, (β (sw k)).val = bit7 s k := fun k ↦ by
    have hb : (fun i : Fin 7 ↦ β (sw i)) = basisBits 7 s := (basisBits7_bitsVal _).symm
    have hk := congrFun hb k
    rw [hk]; exact basisBits7_val_eq_bit7 s k
  simp only [hz_b, hs_b, pointSumCliffordExp128]
  have hDiff :
      (32 : ℤ) * ↑(bit7 s 1) +
        (-32 * ↑(bit7 s 2) +
          (-32 * ↑(bit7 s 3) +
            (-32 * ↑(bit7 s 4) +
              (-32 * ↑(bit7 s 5) +
                (64 * ↑(bit7 s 6) +
                  (64 * (↑(bit6 z 5) * ↑(bit7 s 5)) +
                    (64 * (↑(bit6 z 4) * ↑(bit7 s 4)) +
                      (64 * (↑(bit6 z 3) * ↑(bit7 s 3)) +
                        (64 * (↑(bit6 z 2) * ↑(bit7 s 2)) +
                          (64 * (↑(bit6 z 1) * ↑(bit7 s 1)) +
                            64 * (↑(bit6 z 0) * ↑(bit7 s 0)))))))))))) =
      (32 * ↑(bit7 s 1) +
        96 * (↑(bit7 s 2) + ↑(bit7 s 3) + ↑(bit7 s 4) + ↑(bit7 s 5)) +
        64 * ↑(bit7 s 6) +
        64 * (↑(bit6 z 5) * ↑(bit7 s 5) + ↑(bit6 z 4) * ↑(bit7 s 4) +
          ↑(bit6 z 3) * ↑(bit7 s 3) + ↑(bit6 z 2) * ↑(bit7 s 2) +
          ↑(bit6 z 1) * ↑(bit7 s 1) + ↑(bit6 z 0) * ↑(bit7 s 0))) +
      (-(↑(bit7 s 2) + ↑(bit7 s 3) + ↑(bit7 s 4) + ↑(bit7 s 5))) * 128 := by ring
  rw [hDiff, Int.add_mul_emod_self_right]
/-- Selector `Fin 13 → Fin (18 + 42)` picking axis `w`'s 6 target wires `rSave0[6w .. 6w+5]`
followed by axis `w`'s lower 7 sum wires `rSum42[14w .. 14w+6]`. -/
def selAxisZ6Sum7 (w : Fin 3) : QRegister 13 (18 + 42) where
  wires := ⟨fun idx ↦
    if h : idx.val < 6 then ⟨6 * w.val + idx.val, by have := w.isLt; omega⟩
    else ⟨18 + 14 * w.val + (idx.val - 6), by have := w.isLt; have := idx.isLt; omega⟩,
    fun a b hab ↦ by
      have hv := congrArg Fin.val hab
      dsimp only at hv
      have ha := a.isLt; have hb := b.isLt; have hw := w.isLt
      by_cases ha6 : a.val < 6 <;> by_cases hb6 : b.val < 6
      · rw [dite_eq_left ha6, dite_eq_left hb6] at hv; dsimp only at hv; exact Fin.ext (by omega)
      · rw [dite_eq_left ha6, dite_eq_right hb6] at hv; dsimp only at hv; omega
      · rw [dite_eq_right ha6, dite_eq_left hb6] at hv; dsimp only at hv; omega
      · rw [dite_eq_right ha6, dite_eq_right hb6] at hv; dsimp only at hv; exact Fin.ext (by omega)⟩
/-- `0-T`, `count TOFF = 0` 3-axis Point-QFT sum+CZ Clifford circuit on `18 + 42 = 60` wires
  (`rSave0 ++ rSum42`). -/
def cPointSumClifford60 : Circuit (18 + 42) :=
  cPointSumClifford13.onRegister (selAxisZ6Sum7 0) ;;ᶜ
  cPointSumClifford13.onRegister (selAxisZ6Sum7 1) ;;ᶜ
  cPointSumClifford13.onRegister (selAxisZ6Sum7 2)
@[simp] theorem count_cPointSumClifford60_toff : cPointSumClifford60.count TOFF = 0 := by
  simp [cPointSumClifford60]
@[simp] theorem count_cPointSumClifford60_t : cPointSumClifford60.count T = 0 := by
  simp [cPointSumClifford60]
@[simp] theorem count_cPointSumClifford60Inv_toff : cPointSumClifford60.inverse.count TOFF = 0 := by
  simp [cPointSumClifford60, Circuit.inverse]
@[simp] theorem count_cPointSumClifford60Inv_t : cPointSumClifford60.inverse.count T = 0 := by
  simp [cPointSumClifford60, Circuit.inverse]
/-- Diagonal unitary on `2 ^ (18 + 42)` realized by `cPointSumClifford60`. -/
def uPointSumClifford60 : Unitary (2 ^ (18 + 42)) :=
  ⟨Matrix.diagonal fun x : Fin (2 ^ (18 + 42)) ↦
    let β := basisBits (18 + 42) x
    ∏ w : Fin 3,
      let z_w : Fin 64 := ⟨bitsVal (fun r : Fin 6 ↦ β ⟨6 * w.val + r.val, by
        have := w.isLt; have := r.isLt; omega⟩),
        bitsVal_lt_two_pow _⟩
      let s_w : Fin 128 := ⟨bitsVal (fun k : Fin 7 ↦ β ⟨18 + 14 * w.val + k.val, by
        have := w.isLt; have := k.isLt; omega⟩),
        bitsVal_lt_two_pow _⟩
      omega128 (pointSumCliffordExp128 z_w s_w), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext x
    simp only [Pi.star_apply, ← omega128_finset_sum_assoc]
    exact star_mul_omega128_self _⟩
theorem cPointSumClifford60_eval : cPointSumClifford60.eval = uPointSumClifford60 := by
  have h13 : ∀ (w : Fin 3) (β : BitAssignment (18 + 42)),
      (cPointSumClifford13.onRegister (selAxisZ6Sum7 w)).eval.1.mulVec (ket β) =
        omega128 (pointSumCliffordExp128
          ⟨bitsVal (fun r : Fin 6 ↦ β ⟨6 * w.val + r.val, by
            have := w.isLt; have := r.isLt; omega⟩), bitsVal_lt_two_pow _⟩
          ⟨bitsVal (fun k : Fin 7 ↦ β ⟨18 + 14 * w.val + k.val, by
            have := w.isLt; have := k.isLt; omega⟩), bitsVal_lt_two_pow _⟩) •
        ket β := fun w β ↦ by
    rw [Circuit.eval_onRegister]
    let x : Fin (2 ^ (18 + 42)) := (basisBitsEquiv (18 + 42)).symm β
    have hx : basisBits (18 + 42) x = β := basisBits_basisBitsEquiv_symm β
    have hDiag13 : cPointSumClifford13.eval.1 =
        Matrix.diagonal fun y : Fin (2 ^ 13) ↦
          let γ := basisBits 13 y
          omega128 (pointSumCliffordExp128
            ⟨bitsVal (fun r : Fin 6 ↦ γ ⟨r.val, by have := r.isLt; omega⟩), bitsVal_lt_two_pow _⟩
            ⟨bitsVal (fun k : Fin 7 ↦ γ ⟨6 + k.val, by
              have := k.isLt; omega⟩), bitsVal_lt_two_pow _⟩) := by
      apply matrix_ext_ket; intro γ
      rw [cPointSumClifford13_eval_ket γ]
      have hγ : basisBits 13 ((basisBitsEquiv 13).symm γ) = γ := basisBits_basisBitsEquiv_symm γ
      ext i
      by_cases hi : i = (basisBitsEquiv 13).symm γ
      · subst hi
        simp [OctahedralOrbit.ket, basisState, Matrix.mulVec_diagonal, hγ]
      · simp [hi, OctahedralOrbit.ket, basisState, Matrix.mulVec_diagonal]
    rw [QRegister.embedUnitary_val, hDiag13, QRegister.embedMatrix_diagonal]
    have hMul : ∀ (d : Fin (2 ^ (18 + 42)) → ℂ),
        (Matrix.diagonal d).mulVec (ket β) = d x • ket β := fun d ↦ by
      ext i
      by_cases hi : i = x <;>
        simp [hi, OctahedralOrbit.ket, basisState, x, Matrix.mulVec_diagonal]
    rw [hMul]
    congr 1
    have hEx : ∀ idx : Fin 13,
        basisBits 13 ((selAxisZ6Sum7 w).extractIndex x) idx = β (selAxisZ6Sum7 w idx) := fun idx ↦
          by
      rw [(selAxisZ6Sum7 w).basisBits_extractIndex x idx, hx]
    have hz : (fun r : Fin 6 ↦ basisBits 13 ((selAxisZ6Sum7 w).extractIndex x) ⟨r.val, by
      have := r.isLt; omega⟩) =
        fun r : Fin 6 ↦ β ⟨6 * w.val + r.val, by have := w.isLt; have := r.isLt; omega⟩ := by
      funext r; rw [hEx]
      exact congrArg β (Fin.ext (by dsimp [selAxisZ6Sum7]; rw [dite_eq_left r.isLt]))
    have hs : (fun k : Fin 7 ↦ basisBits 13 ((selAxisZ6Sum7 w).extractIndex x) ⟨6 + k.val, by
      have := k.isLt; omega⟩) =
        fun k : Fin 7 ↦ β ⟨18 + 14 * w.val + k.val, by have := w.isLt; have := k.isLt; omega⟩ := by
      funext k; rw [hEx]
      have hnot : ¬ (6 + k.val < 6) := by omega
      exact congrArg β (Fin.ext (by
        dsimp [selAxisZ6Sum7]; rw [dite_eq_right hnot]; dsimp only; omega))
    dsimp only
    rw [hz, hs]
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  dsimp only [cPointSumClifford60]
  rw [OctahedralOrbit.eval_seq_mulVec, OctahedralOrbit.eval_seq_mulVec,
      h13 0 β, Matrix.mulVec_smul, Matrix.mulVec_smul, h13 1 β, Matrix.mulVec_smul, h13 2 β,
        smul_smul, smul_smul]
  let x : Fin (2 ^ (18 + 42)) := (basisBitsEquiv (18 + 42)).symm β
  have hx : basisBits (18 + 42) x = β := basisBits_basisBitsEquiv_symm β
  have hRhs : uPointSumClifford60.1.mulVec (ket β) =
      (∏ w : Fin 3, omega128 (pointSumCliffordExp128
        ⟨bitsVal (fun r : Fin 6 ↦ β ⟨6 * w.val + r.val, by
          have := w.isLt; have := r.isLt; omega⟩), bitsVal_lt_two_pow _⟩
        ⟨bitsVal (fun k : Fin 7 ↦ β ⟨18 + 14 * w.val + k.val, by
          have := w.isLt; have := k.isLt; omega⟩), bitsVal_lt_two_pow _⟩)) •
      ket β := by
    dsimp only [uPointSumClifford60]
    ext i
    by_cases hi : i = x
    · subst hi
      simp [OctahedralOrbit.ket, basisState, hx, Matrix.mulVec_diagonal, Pi.single_apply]
    · simp [hi, OctahedralOrbit.ket, basisState, x, Matrix.mulVec_diagonal]
  rw [hRhs, Fin.prod_univ_three]
/-- `0-T`, `count TOFF = 0` 3-axis single-electron Point-QFT Clifford circuit on 18 wires. -/
def cPointElec18 : Circuit 18 :=
  cPointElecClifford6.onRegister (QRegister.block 0 6 (by decide)) ;;ᶜ
  cPointElecClifford6.onRegister (QRegister.block 6 6 (by decide)) ;;ᶜ
  cPointElecClifford6.onRegister (QRegister.block 12 6 (by decide))
@[simp] theorem count_cPointElec18_toff : cPointElec18.count TOFF = 0 := by simp [cPointElec18]
@[simp] theorem count_cPointElec18_t : cPointElec18.count T = 0 := by simp [cPointElec18]
@[simp] theorem count_cPointElec18Inv_toff : cPointElec18.inverse.count TOFF = 0 := by
  simp [cPointElec18, Circuit.inverse]
@[simp] theorem count_cPointElec18Inv_t : cPointElec18.inverse.count T = 0 := by
  simp [cPointElec18, Circuit.inverse]
/-- Diagonal 18-qubit unitary applying `∏ w : Fin 3, omega128 (pointElecCliffordExp128
  (u18GridEquiv z w))`. -/
def uPointElec18 : Unitary (2 ^ 18) :=
  ⟨Matrix.diagonal fun z : Fin (2 ^ 18) ↦
    ∏ w : Fin 3, omega128 (pointElecCliffordExp128 (u18GridEquiv z w)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext z
    simp only [Pi.star_apply, ← omega128_finset_sum_assoc]
    exact star_mul_omega128_self _⟩
theorem cPointElec18_eval : cPointElec18.eval = uPointElec18 := by
  have hDiag6 : cPointElecClifford6.eval.1 =
      Matrix.diagonal fun u : Fin 64 ↦ omega128 (pointElecCliffordExp128 u) := by
    apply matrix_ext_ket; intro γ
    rw [cPointElecClifford6_eval_ket γ]
    have hfin : (⟨bitsVal γ, bitsVal_lt_two_pow γ⟩ : Fin 64) = (basisBitsEquiv 6).symm γ :=
      ((basisBitsEquiv 6).symm_apply_eq.mpr (basisBits6_bitsVal γ).symm).symm
    rw [hfin]
    ext i
    by_cases hi : i = (basisBitsEquiv 6).symm γ <;>
      simp [hi, OctahedralOrbit.ket, basisState, Matrix.mulVec_diagonal]
  have hAx : ∀ (w : Fin 3),
      (cPointElecClifford6.onRegister (QRegister.block (6 * w.val) 6 (by
        have := w.isLt; omega))).eval.1 =
        Matrix.diagonal fun z : Fin (2 ^ 18) ↦
          omega128 (pointElecCliffordExp128 (u18GridEquiv z w)) := fun w ↦ by
    rw [Circuit.eval_onRegister, QRegister.embedUnitary_val, hDiag6, QRegister.embedMatrix_diagonal]
    congr 1; funext z
    rw [block6_extractIndex_u18 w _ z]
  have h2 : (cPointElecClifford6.onRegister (QRegister.block 12 6 (by decide))).eval.1 =
      Matrix.diagonal fun z : Fin (2 ^ 18) ↦
        omega128 (pointElecCliffordExp128 (u18GridEquiv z 2)) := hAx 2
  have h1 : (cPointElecClifford6.onRegister (QRegister.block 6 6 (by decide))).eval.1 =
      Matrix.diagonal fun z : Fin (2 ^ 18) ↦
        omega128 (pointElecCliffordExp128 (u18GridEquiv z 1)) := hAx 1
  have h0 : (cPointElecClifford6.onRegister (QRegister.block 0 6 (by decide))).eval.1 =
      Matrix.diagonal fun z : Fin (2 ^ 18) ↦
        omega128 (pointElecCliffordExp128 (u18GridEquiv z 0)) := hAx 0
  apply Subtype.ext
  unfold cPointElec18 uPointElec18
  simp only [Circuit.eval_seq, Submonoid.coe_mul]
  rw [h2, h1, h0]
  simp only [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext z
  rw [Fin.prod_univ_three]; ring
/-- Prefix `0-T`, `count TOFF = 0` circuit applying `cPointElec18` on the first `m ≤ 217`
  spectator slots of `posCoreWires`. -/
def cPointElec217Prefix : (m : ℕ) → (hm : m ≤ 217) → Circuit posCoreWires
  | 0, _ => .identity
  | m + 1, hm =>
      cPointElec217Prefix m (Nat.le_of_succ_le hm) ;;ᶜ
        cPointElec18.onRegister (rSpectatorSlot ⟨m, hm⟩)
/-- `0-T`, `count TOFF = 0` circuit applying `cPointElec18` across all 217 spectator slots of
  `posCoreWires`. -/
def cPointElec217Core : Circuit posCoreWires := cPointElec217Prefix 217 le_rfl
@[simp] theorem count_cPointElec217Prefix_toff :
    ∀ (m : ℕ) (hm : m ≤ 217), (cPointElec217Prefix m hm).count TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [cPointElec217Prefix, count_cPointElec217Prefix_toff m]
@[simp] theorem count_cPointElec217Prefix_t :
    ∀ (m : ℕ) (hm : m ≤ 217), (cPointElec217Prefix m hm).count T = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [cPointElec217Prefix, count_cPointElec217Prefix_t m]
@[simp] theorem count_cPointElec217PrefixInv_toff :
    ∀ (m : ℕ) (hm : m ≤ 217), (cPointElec217Prefix m hm).inverse.count TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp [cPointElec217Prefix, Circuit.inverse_onRegister,
        count_cPointElec217PrefixInv_toff m]
@[simp] theorem count_cPointElec217PrefixInv_t :
    ∀ (m : ℕ) (hm : m ≤ 217), (cPointElec217Prefix m hm).inverse.count T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp[cPointElec217Prefix, Circuit.inverse_onRegister, count_cPointElec217PrefixInv_t m]
@[simp] theorem count_cPointElec217Core_toff : cPointElec217Core.count TOFF = 0 :=
  count_cPointElec217Prefix_toff 217 le_rfl
@[simp] theorem count_cPointElec217Core_t : cPointElec217Core.count T = 0 :=
  count_cPointElec217Prefix_t 217 le_rfl
@[simp] theorem count_cPointElec217CoreInv_toff : cPointElec217Core.inverse.count TOFF = 0 :=
  count_cPointElec217PrefixInv_toff 217 le_rfl
@[simp] theorem count_cPointElec217CoreInv_t : cPointElec217Core.inverse.count T = 0 :=
  count_cPointElec217PrefixInv_t 217 le_rfl
/-- Diagonal unitary on `2 ^ posCoreWires` applying `uPointElec18` across all 217 spectator
  slots. -/
def uPointElec217Core : Unitary (2 ^ posCoreWires) := elecProd217 fun _ ↦ uPointElec18
theorem uPointElec217Core_eq_diagonal : uPointElec217Core.1 = Matrix.diagonal fun x : Fin
    (2 ^ posCoreWires) ↦ ∏ w : Fin 3, omega128 (∑ e : Fin 217, pointElecCliffordExp128
    (u18GridEquiv ((rSpectatorSlot e).extractIndex x) w)) := by
  dsimp only [uPointElec217Core, elecProd217]
  rw [list_unitary_val_prod_assoc, List.map_ofFn, Function.comp_def]
  have hFn : (fun e : Fin 217 ↦ Subtype.val ((rSpectatorSlot e).embedUnitary uPointElec18)) =
      fun e : Fin 217 ↦ Matrix.diagonal (fun x : Fin (2 ^ posCoreWires) ↦
        ∏ w : Fin 3, omega128 (pointElecCliffordExp128
          (u18GridEquiv ((rSpectatorSlot e).extractIndex x) w))) := by
    funext e
    rw [QRegister.embedUnitary_val, uPointElec18]
    exact QRegister.embedMatrix_diagonal (rSpectatorSlot e) _
  rw [hFn, list_ofFn_diagonal_prod_assoc]
  congr 1; funext x
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun w _ ↦ (omega128_finset_sum_assoc Finset.univ _).symm
theorem cPointElec217Core_eval : cPointElec217Core.eval = uPointElec217Core := by
  have hPref : ∀ (m : ℕ) (hm : m ≤ 217), (cPointElec217Prefix m hm).eval.1 = Matrix.diagonal
      fun x : Fin (2 ^ posCoreWires) ↦ ∏ i : Fin m, ∏ w : Fin 3, omega128
      (pointElecCliffordExp128 (u18GridEquiv ((rSpectatorSlot ⟨i.val, Nat.lt_of_lt_of_le
      i.isLt hm⟩).extractIndex x) w)) := by
    intro m hm
    induction m with
    | zero => simp [cPointElec217Prefix]
    | succ m ih =>
        dsimp only [cPointElec217Prefix]
        rw [Circuit.eval_seq, Submonoid.coe_mul, ih (Nat.le_of_succ_le hm),
            Circuit.eval_onRegister, cPointElec18_eval, QRegister.embedUnitary_val,
            uPointElec18, QRegister.embedMatrix_diagonal, diagonal_mul_diagonal_op_assoc]
        congr 1; funext x
        rw [Fin.prod_univ_castSucc (n := m), mul_comm]
        rfl
  apply Subtype.ext
  rw [cPointElec217Core, hPref 217 le_rfl, uPointElec217Core_eq_diagonal]
  congr 1; funext x
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun w _ ↦ (omega128_finset_sum_assoc Finset.univ _).symm
end Part2_Target18AndPointPhiSave0
end HeadAndPhi
end ImplAlt
end StageAConjHAndStreamBridge
end SharedScope
end
end SlimFermApproxSec1And2A

end QuantumComputation.Specs.StoppingPowerSolution
end
