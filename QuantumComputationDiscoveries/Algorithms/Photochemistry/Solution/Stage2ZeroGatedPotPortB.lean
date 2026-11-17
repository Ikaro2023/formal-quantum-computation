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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage1SplitCoinTurnkey
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.OuterCoin70MuxLift

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 8192

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
noncomputable section

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
open QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
namespace QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
open PhotochemistrySolution.KetSupport PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.GenWeightsSelect
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
/--
Sector-ordering invariant on a 41-bit `ZeroNEremSector` coin decoder (`e1 < e2` on `.ee` and
`n1 < n2` on `.nn`), satisfied by every `ValidGenZeroNEremCoin` (including `ValidZeroNEremCoin`,
and multi-coin `PopBernstein` families).
-/
def SortedZeroNEremCoin (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) : Prop :=
    (∀ (c : Fin (2 ^ 41)) (n1 : Fin 47) (e1 e2 : Fin 187), decodeCoin c = .ee n1 e1 e2 → e1 < e2) ∧
    (∀ (c : Fin (2 ^ 41)) (n1 n2 : Fin 47) (e1 : Fin 187), decodeCoin c = .nn n1 n2 e1 → n1 < n2)
theorem SortedZeroNEremCoin.of_validGen {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ}
    {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decodeCoin) :
    SortedZeroNEremCoin decodeCoin :=
    ⟨fun _ _ _ _ hc ↦ hCoin.ee_lt hc, fun _ _ _ _ hc ↦ hCoin.nn_lt hc⟩
theorem idxValD_congr_gen {D n₁ n₂ : ℕ} {w₁ : Fin D → Wire n₁} {w₂ : Fin D → Wire n₂}
    {β₁ : BitAssignment n₁} {β₂ : BitAssignment n₂} (h : ∀ d : Fin D, β₁ (w₁ d) = β₂ (w₂ d)) :
    idxValD w₁ β₁ = idxValD w₂ β₂ :=
  Nat.eq_of_testBit_eq fun d ↦ by by_cases hd : d < D <;> simp [testBit_idxValD, hd, h]
theorem bits_zero_of_idxValD_eq_zero {D n : ℕ} (wBit : Fin D → Wire n) (δ : BitAssignment n)
    (h0 : idxValD wBit δ = 0) (d : Fin D) : δ (wBit d) = 0 := by
  have htb := congrArg (Nat.testBit · d.val) h0
  rw [testBit_idxValD, dite_eq_left d.isLt, Nat.zero_testBit] at htb
  rcases zmod2_cases (δ (wBit d)) with hz | ho <;> simp_all
theorem zeroNEremOutMask_router_sorted {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (hSort : SortedZeroNEremCoin decodeCoin) (c : Fin (2 ^ 41)) (δ : BitAssignment dLayout)
    (hOut : ∀ j : Fin 40, δ (rOut40Layout j) = outMaskBits40 (decodeCoin c) j) :
    (δ (rHas1 rNucLayout) = 0 → ∀ d : Fin 6, δ (rIdx1 rNucLayout d) = 0) ∧
    (δ (rRawHas2 rNucLayout) = 0 → ∀ d : Fin 6, δ (rIdx2 rNucLayout d) = 0) ∧
    (δ (rRawHas2 rNucLayout) = 1 → idxValD (rIdx1 rNucLayout) δ < idxValD (rIdx2 rNucLayout) δ) ∧
    (δ (rHas1 rElecLayout) = 0 → ∀ d : Fin 8, δ (rIdx1 rElecLayout d) = 0) ∧
    (δ (rRawHas2 rElecLayout) = 0 → ∀ d : Fin 8, δ (rIdx2 rElecLayout d) = 0) ∧
    (δ (rRawHas2 rElecLayout) = 1 → idxValD (rIdx1 rElecLayout) δ < idxValD (rIdx2 rElecLayout) δ)
    :=
    by
  have zB {D : ℕ} {q} {w : Fin D → Wire dLayout} (b : Bool) {v}
      (hq : δ q = if b then 1 else 0) (hv : idxValD w δ = v) (hz : b = false → v = 0)
          (_ : δ q = 0) :
      ∀ d, δ (w d) = 0 := bits_zero_of_idxValD_eq_zero w δ (by cases b <;> simp_all)
  have ltB {q} (b : Bool) {u v x y : ℕ} (hq : δ q = if b then 1 else 0)
      (hx : x = u) (hy : y = v) (hl : b = true → u < v) (_ : δ q = 1) : x < y := by
        cases b <;> simp_all
  have chk (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ) (isS isP isK isNN : Bool)
      (sp1 aux2 : ℕ)
      (lN1 : n1 < 64 := by
        omega) (lN2 : n2 < 64 := by omega) (lE1 : e1 < 256 := by omega) (lE2 : e2 < 256 := by omega)
      (zN1 : hN1 = false → n1 = 0 := by simp) (zN2 : hN2 = false → n2 = 0 := by simp)
      (ltN : hN2 = true → n1 < n2 := by simp) (zE1 : hE1 = false → e1 = 0 := by simp)
      (zE2 : hE2 = false → e2 = 0 := by simp) (ltE : hE2 = true → e1 < e2 := by simp)
      (heq : zeroNEremOutMask (decodeCoin c) =
        packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isS isP isK isNN sp1 aux2) :=
    let F := packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isS isP isK isNN
      sp1 aux2 lN1 lN2 lE1 lE2 δ fun j ↦ (hOut j).trans (by simp [outMaskBits40, heq])
    And.intro (zB hN1 F.1 F.2.2.1 zN1) (And.intro (zB hN2 F.2.1 F.2.2.2.1 zN2)
      (And.intro (ltB hN2 F.2.1 F.2.2.1 F.2.2.2.1 ltN)
          (And.intro (zB hE1 F.2.2.2.2.1 F.2.2.2.2.2.2.1 zE1)
        (And.intro (zB hE2 F.2.2.2.2.2.1 F.2.2.2.2.2.2.2.1 zE2)
          (ltB hE2 F.2.2.2.2.2.1 F.2.2.2.2.2.2.1 F.2.2.2.2.2.2.2.1 ltE)))))
  cases hc : decodeCoin c with
  | idle => exact chk false false 0 0 false false 0 0 false false false false 0 0 (heq := hc ▸ rfl)
  | ee n1 e1 e2 => exact chk true false n1.val 0 true true e1.val e2.val true true false false
                      (nucSpecies n1).val 0 (ltE := fun _ ↦ hSort.1 c n1 e1 e2 hc) (heq := hc ▸ rfl)
  | nn n1 n2 e1 => exact chk true true n1.val n2.val true false e1.val 0 true true false true
                      (nucSpecies n1).val (nucSpecies n2).val (ltN := fun _ ↦ hSort.2 c n1 n2 e1 hc)
                          (heq := hc ▸ rfl)
  | en n1 e1 => exact chk true false n1.val 0 true false e1.val 0 false true false false
                      (nucSpecies n1).val 0 (heq := hc ▸ rfl)
  | kin i ax =>
      have _ := i.isLt
      by_cases hi : i.val < 47
      · exact chk true false i.val 0 false false 0 0 false false true false 0 ax.val
          (heq := by simp [hc, zeroNEremOutMask, hi])
      · exact chk false false 0 0 true false (i.val - 47) 0 false false true false 0 ax.val
          (heq := by simp [hc, zeroNEremOutMask, hi])
theorem validZeroGatedSorted_compose_writeReg {M D n : ℕ} (rTot : QRegister dLayout n)
    (r : RouterReg M D dLayout) (η : BitAssignment n) (δ : BitAssignment dLayout)
    (hVal : ValidZeroGatedSortedRouterInput r δ) : ValidZeroGatedSortedRouterInput (rTot.compose r)
    (DynCircExt.writeReg η rTot δ) := by
  have hw (i) : DynCircExt.writeReg η rTot δ ((rTot.compose r) i) = δ (r i) :=
    DynCircExt.writeReg_apply_reg η rTot δ (r i)
  exact ⟨validRouter_compose_writeReg rTot r η δ hVal.1,
    fun hz d ↦ (hw _).trans (hVal.2.1 ((hw _).symm.trans hz) d),
    fun hz d ↦ (hw _).trans (hVal.2.2.1 ((hw _).symm.trans hz) d), fun ho ↦ by
      rw [idxValD_congr_gen fun _ ↦ hw _, idxValD_congr_gen fun _ ↦ hw _]
      exact hVal.2.2.2 ((hw _).symm.trans ho)⟩
end QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec

section
open PrimitiveGate QuantumComputation.Specs.PhotochemistrySolution.ProviderZeroFloor
  QuantumComputation.Specs.PhotochemistrySolution.Kinetic664
  QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState
attribute [local irreducible] phaseFlipUnitary bSpeciesSwap50 Stage4KinFull.bAxisMux27
theorem muxMat_mulVec_ket_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n)
    (U : BitAssignment m → Unitary (2 ^ n)) (β : BitAssignment n) :
    (muxMat_c70 rC U).mulVec (ket β) = (U (fun j ↦ β (rC j))).1.mulVec (ket β) := by
  rw [muxMat_c70, Matrix.sum_mulVec, Finset.sum_eq_single (fun j ↦ β (rC j))]
  · rw [← Matrix.mulVec_mulVec, projBits_mulVec_ket_c70, ite_eq_left (fun _ ↦ rfl)]
  · intro γ _ hne
    rw [← Matrix.mulVec_mulVec, projBits_mulVec_ket_c70,
      ite_eq_right fun hγ ↦ hne (funext fun j ↦ (hγ j).symm), Matrix.mulVec_zero]
  · exact fun hm ↦ absurd (Finset.mem_univ _) hm
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
open scoped Circuit.Notation
open PhotochemistrySolution.KetSupport PhotochemistrySolution.PotOraclePortB
  PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg)
/-! ## Block 1C: Ghost 24-Bit Fredkin Unitary `uSwapHi24` & Disjoint Dynamic Commutation -/

def swap1Bits {n : ℕ} (c a b : Wire n) (β : BitAssignment n) : BitAssignment n :=
  if β c = 1 then Function.update (Function.update β a (β b)) b (β a) else β
/--
Specification-only 3-gate Fredkin circuit swapping `a` and `b` when `c = 1`
(never placed in any physical `DynamicCircuit`).
-/
def cFredkin {n : ℕ} (c a b : Wire n) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) : Circuit n :=
  Circuit.CNOT a b hab ;;ᶜ Circuit.TOFF c b a hcb hca hab.symm ;;ᶜ Circuit.CNOT a b hab
end QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
end
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
namespace QuantumComputation.Specs.PhotochemistrySolution.Sub5885
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.GenWeightsSelect PhotochemistrySolution.BlockApprox
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.SelectCompactAnc
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr reflULGen
def decDisjSysAnc_top {n : ℕ} (rS : QRegister systemQubits_frozen n)
    (rA : QRegister (ancWOfScr scrWLayout) n) : Decidable (rS.DisjointWires rA) :=
    decidable_of_iff (∀ i j, rS i ≠ rA j) QRegister.disjoint_iff.symm
end QuantumComputation.Specs.PhotochemistrySolution.Sub5885

namespace QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk
set_option maxRecDepth 4096
open DynamicCircuit PhotochemistrySolution.OvBidir PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectCompactRot34
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.UnembedIdleAncillas PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.FusedUnembedLGen PhotochemistrySolution.Sub5885
attribute [local semireducible] mkShared34DataLGenOff
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen hamiltonian_frozen
theorem hOff65_le_scrL_31 {offRefl m scrL : ℕ} (hOff65 : 65 ≤ offRefl)
    (hm : offRefl + (m + 1) ≤ scrL) : 65 ≤ scrL := by omega
end QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
open QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.UnembedO3Bridge
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage2Xor84
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2PotUnld
open PhotochemistrySolution.Stage2ElecFirst PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn)
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
/-- Generalized outer-Elec ket and operator chain on ANY `ValidMuxD1Stage2Regs rNuc rElec`. -/
theorem routerChain_sorted_of_validMuxD1Stage2Regs {n wIn : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout} (hRegs : ValidMuxD1Stage2Regs rNuc rElec)
    (hSort : SortedZeroNEremCoin decodeCoin) (rTot : QRegister dLayout n)
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {X : Operator (2 ^ n)}
    (hX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X = X) :
    SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rElec))
    ((rTot.embedUnitary o1.uLocal).1 * X) ∧
    SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rNuc))
    ((uRouterSwapConj (rTot.compose rElec)).1 * ((rTot.embedUnitary o1.uLocal).1 * X)) ∧
    (uRouterSwapConj (rTot.compose rNuc)).1 * ((uRouterSwapConj (rTot.compose rElec)).1 *
    ((rTot.embedUnitary o1.uLocal).1 * X)) = (rTot.embedUnitary (wNoHad o1.uLocal)).1 * X ∧
    (rTot.compose rScrCompact1493).basisOutcomeProjector 0 * ((rTot.embedUnitary o1.uLocal).1 * X) =
    (rTot.embedUnitary o1.uLocal).1 * X ∧ (rTot.compose rClean690Layout).basisOutcomeProjector 0 *
    ((rTot.embedUnitary (wNoHad o1.uLocal)).1 * X) = (rTot.embedUnitary (wNoHad o1.uLocal)).1 *
    X := by
  obtain ⟨_, _, _, c1493, c690⟩ := routerChain_elecFirst rTot o1 hX
  have hCleanIn (ξ : BitAssignment n) : inKetPred (fun η ↦ CleanScr (fun i ↦ η (rTot i)))
      (X.mulVec (ket ξ)) :=
    fun η hnz ↦ by
      by_contra hnot
      have heq := congrFun (congrArg (·.mulVec (ket ξ)) hX) ((basisBitsEquiv n).symm η)
      rw [← Matrix.mulVec_mulVec, proj_zero_vec_entry (rTot.compose rScrLayout) _ η,
        ite_eq_right (id hnot : ¬ ∀ i : Fin scrLLayout, η ((rTot.compose rScrLayout) i) = 0)] at heq
      exact hnz heq.symm
  have hScr0 {α : BitAssignment dLayout} (hScr : CleanScr α) (c) (z) (m : Fin scrLLayout)
      (hmOut : m.val < 65 ∨ 105 ≤ m.val) : routedStage1 decodeCoin α c z (rScrLayout m) = 0 := by
    have _ : m.val < 1565 := m.isLt
    rw [routedStage1, routedStage0,
        DynCircExt.writeReg_apply_of_not_mem _ rOut40Layout _ _ fun ⟨k, hk⟩ ↦
        (fun _ _ ↦
            by omega) k.isLt ((val_rOut40Layout k).symm.trans ((congrArg Fin.val hk).trans
                 (val_rScrLayout m))),
      DynCircExt.writeReg_apply_of_not_mem _ rLcu82Layout _ _ fun ⟨l, hl⟩ ↦
        (fun _ ↦ by omega)
            ((val_rLcu82Layout l).symm.trans ((congrArg Fin.val hl).trans (val_rScrLayout m)))]
    exact hScr m
  have mkValZG {M D : ℕ} {r r₀ : RouterReg M D dLayout} {β δ : BitAssignment dLayout}
      (hR : MuxD1RolesEq r r₀)
      (hs : ∀ i, β (r i) = δ (r i)) (hV : ValidRouterInput r₀ δ)
      (hg1 : δ (rHas1 r₀) = 0 → ∀ d : Fin D, δ (rIdx1 r₀ d) = 0)
      (hg2 : δ (rRawHas2 r₀) = 0 → ∀ d : Fin D, δ (rIdx2 r₀ d) = 0)
      (hord : δ (rRawHas2 r₀) = 1 → idxValD (rIdx1 r₀) δ < idxValD (rIdx2 r₀) δ)
      (hPriv : ∀ i : Fin (routerWidth M D), basePub M D ≤ i.val → δ (r i) = 0) :
      ValidZeroGatedSortedRouterInput r β := by
    obtain ⟨h1, h2, hi1, hi2, hBL, hBH, hA, hB, _⟩ := hR
    have e1 := (hs _).trans (congrArg δ h1)
    have e2 := (hs _).trans (congrArg δ h2)
    have ei1 (d) := (hs _).trans (congrArg δ (congrFun hi1 d))
    have ei2 (d) := (hs _).trans (congrArg δ (congrFun hi2 d))
    have id1 := idxValD_congr_gen ei1
    have id2 := idxValD_congr_gen ei2
    exact ⟨⟨fun h ↦ e1.trans (hV.1 (e2.symm.trans h)), fun h ↦
        lt_of_eq_of_lt id1 (hV.2.1 (e1.symm.trans h)),
        fun h ↦ lt_of_eq_of_lt id2 (hV.2.2.1 (e2.symm.trans h)),
        fun b ↦ ⟨(hs _).trans ((congrArg δ (congrFun hBL b)).trans (hV.2.2.2.1 b).1),
          (hs _).trans ((congrArg δ (congrFun hBH b)).trans (hV.2.2.2.1 b).2.1),
          (hs _).trans ((congrArg δ (congrFun hA b)).trans (hV.2.2.2.1 b).2.2.1),
          (hs _).trans ((congrArg δ (congrFun hB b)).trans (hV.2.2.2.1 b).2.2.2)⟩,
        fun _ hw ↦ by
          rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
          exact (hs i).trans (hPriv i (Finset.mem_filter.mp hi).2)⟩,
      fun hz d ↦ (ei1 d).trans (hg1 (e1.symm.trans hz) d), fun hz d ↦
          (ei2 d).trans (hg2 (e2.symm.trans hz) d),
      fun ho ↦ lt_of_eq_of_lt id1 (lt_of_lt_of_eq (hord (e2.symm.trans ho)) id2.symm)⟩
  have hVE1 {α : BitAssignment dLayout} (hScr : CleanScr α) (c) (z) :
      ValidRouterInput rElecLayout (routedStage1 decodeCoin α c z) := by
    obtain ⟨_, hE, h2, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
    exact ⟨by simpa only [← hE] using h2.1,
        by simpa only [← hE, idxValD_congr_gen fun _ ↦ (hE _).symm] using h2.2.1,
      by simpa only [← hE, idxValD_congr_gen fun _ ↦ (hE _).symm] using h2.2.2.1,
      fun b ↦ by simpa only [← hE] using h2.2.2.2.1 b, fun _ hw ↦ by
        rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
        exact (hE j).symm ▸ h2.2.2.2.2 _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
  have hValEC {α : BitAssignment dLayout} (hScr : CleanScr α) (c) (z) :
      ValidZeroGatedSortedRouterInput rElec (routedStage1 decodeCoin α c z) := by
    have hSH := zeroNEremOutMask_router_sorted hSort c (routedStage1 decodeCoin α c z)
      fun j ↦ DynCircExt.writeReg_apply_reg _ rOut40Layout _ j
    refine mkValZG hRegs.rolesElec (fun _ ↦ rfl)
        (hVE1 hScr c z) hSH.2.2.2.1 hSH.2.2.2.2.1 hSH.2.2.2.2.2 fun i hi ↦ ?_
    let j : Fin 454 :=
        ⟨i.val - 4602, (fun _ : 4602 ≤ i.val ↦ fun _ : i.val < 5056 ↦
        by omega) hi (hEW5056 ▸ i.isLt)⟩
    obtain ⟨m, hm, hmOut⟩ := hRegs.privElec j
    exact (congrArg _ ((congrArg rElec
      (Fin.ext (Nat.add_sub_of_le hi).symm : i = ⟨4602 + j.val, privIdx_lt j⟩)).trans hm)).trans
      (hScr0 hScr c z m hmOut)
  have hValNC {α : BitAssignment dLayout} (hScr : CleanScr α) (c) (z) :
      ValidZeroGatedSortedRouterInput rNuc (routerSwapBits rElecLayout (routedStage1 decodeCoin
          α c z)) := by
    let δ₁ := routedStage1 decodeCoin α c z
    have hSH := zeroNEremOutMask_router_sorted hSort c δ₁ fun j ↦
        DynCircExt.writeReg_apply_reg _ rOut40Layout _ j
    have sameN (i : Fin (routerWidth 47 6)) : routerSwapBits rElecLayout δ₁ (rNuc i) = δ₁ (rNuc i)
        := by
      have _ := hRegs.val_rNuc_bounds i
      have _ := hEW5056
      have neE (k : ℕ) (hk : k < routerWidth 187 8) (e : rNuc i = rElecLayout ⟨k, hk⟩)
          (_ : 18 ≤ k ∧ k < 66 ∨ 114 ≤ k ∧ k < 4602 := by omega) : False := by
        have hb := (congrArg Fin.val e).trans (val_elecRouterWireFn ⟨k, hk⟩)
        dsimp at hb
        split_ifs at hb <;> omega
      exact routerSwapBits_outside_mod rElecLayout (hVE1 hScr c z) (fun b e ↦ neE (18 + b.val)
          (by omega) e)
        (fun b e ↦ neE (42 + b.val) (by omega) e) (fun p b e ↦ neE (114 + 24 * p.val + b.val)
            (by omega) e)
    refine mkValZG hRegs.rolesNuc sameN (validRouter_stage1 (decodeCoin :=
        decodeCoin) hScr c z).1
      hSH.1 hSH.2.1 hSH.2.2.1 fun i hi ↦ ?_
    let k : Fin 156 :=
        ⟨i.val - 1238, (fun _ : 1238 ≤ i.val ↦ fun _ : i.val < 1394 ↦
        by omega) hi (hNW1394 ▸ i.isLt)⟩
    obtain ⟨m, hm, hmOut⟩ := hRegs.privNuc k
    exact (congrArg _ ((congrArg rNuc
      (Fin.ext (Nat.add_sub_of_le hi).symm : i = ⟨1238 + k.val, nucPrivIdx_lt k⟩)).trans hm)).trans
      (hScr0 hScr c z m (hmOut.imp_right fun _ ↦ by omega))
  have stepBoth (η : BitAssignment n) (hScr : CleanScr (fun i ↦ η (rTot i))) :
      let α := fun i ↦ η (rTot i)
      let c := outerCoinOf82 (fun i ↦ α (rLcu82Layout i))
      let z := innerBitsOf82 (fun i ↦ α (rLcu82Layout i))
      (uRouterSwapConj (rTot.compose rElec)).1.mulVec ((rTot.embedUnitary o1.uLocal).1.mulVec
          (ket η)) =
        ket (DynCircExt.writeReg η rTot (routerSwapBits rElecLayout (routedStage1 decodeCoin
            α c z))) ∧
      (uRouterSwapConj (rTot.compose rNuc)).1.mulVec
        ((uRouterSwapConj (rTot.compose rElec)).1.mulVec ((rTot.embedUnitary o1.uLocal).1.mulVec
            (ket η))) =
        (rTot.embedUnitary (wNoHad o1.uLocal)).1.mulVec (ket η) := by
    let α := fun i ↦ η (rTot i)
    let c := outerCoinOf82 (fun i ↦ α (rLcu82Layout i))
    let z := innerBitsOf82 (fun i ↦ α (rLcu82Layout i))
    have hStepE :
        (uRouterSwapConj (rTot.compose rElec)).1.mulVec ((rTot.embedUnitary o1.uLocal).1.mulVec
        (ket η)) =
        ket (DynCircExt.writeReg η rTot (routerSwapBits rElecLayout (routedStage1 decodeCoin
            α c z))) := by
      rw [w1Ket rTot o1 η hScr, uRouterSwapConj_ket_eq (rTot.compose rElec)
          (validRouter_compose_writeReg rTot rElec η _ (hValEC hScr c z).1),
        routerSwapBits_compose_writeReg rTot rElec η _,
            routerSwapBits_congr_roles rElec rElecLayout hRegs.rolesElec _]
    refine ⟨hStepE, ?_⟩
    rw [hStepE, uRouterSwapConj_ket_eq (rTot.compose rNuc)
        (validRouter_compose_writeReg rTot rNuc η _ (hValNC hScr c z).1),
      routerSwapBits_compose_writeReg rTot rNuc η _,
          routerSwapBits_congr_roles rNuc rNucLayout hRegs.rolesNuc _,
      routerSwap_nuc_elec_comm (validRouter_stage1 (decodeCoin :=
          decodeCoin) hScr c z).1 (hVE1 hScr c z),
      QRegister.embedUnitary_val,
          embedMatrix_ket_eq_writeReg rTot _ η ((congrArg (wNoHad o1.uLocal).1.mulVec
        (congrArg ket (routedStage0_self α).symm)).trans (wNoHad_mulVec_ket o1 hScr c z))]
    rfl
  exact ⟨supportedOn_of_inKetPred fun ξ ↦ by
      rw [← Matrix.mulVec_mulVec]
      exact inKetPred_mulVec _ (fun η hScr ↦ w1Ket rTot o1 η hScr ▸
        inKetPred_ket (validZeroGatedSorted_compose_writeReg rTot rElec η _ (hValEC hScr _ _)))
            (hCleanIn ξ),
    supportedOn_of_inKetPred fun ξ ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      exact inKetPred_mulVec _ (fun η hScr ↦
          (Matrix.mulVec_mulVec _ _ _).symm.trans (stepBoth η hScr).1 ▸
        inKetPred_ket (validZeroGatedSorted_compose_writeReg rTot rNuc η _ (hValNC hScr _ _)))
            (hCleanIn ξ),
    matrix_ext_ket fun ξ ↦ by
      simp only [← Matrix.mulVec_mulVec]
      have hv := vec_eq_sum_ket (X.mulVec (ket ξ))
      conv_lhs => rw [hv]
      conv_rhs => rw [hv]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
      exact Finset.sum_congr rfl fun η _ ↦
        if hc : (X.mulVec (ket ξ)) ((basisBitsEquiv n).symm η) = 0 then by simp [hc]
        else congrArg (_ • ·) (stepBoth η (hCleanIn ξ η hc)).2,
    c1493, c690⟩
end QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
open PhotochemistrySolution.CoulombFast PhotochemistrySolution.XMeasLinearCleanStep
  PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.CoinWrap
open PhotochemistrySolution.Stage1SingleWrap PhotochemistrySolution.FineLegendre
  PhotochemistrySolution.SplitBellVecCleanStep
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.XMeasChunkQromUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (xorWireUnitary
    xorWireUnitary_mulVec_ket)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local semireducible] remeasureIf projBit chunkXorOp
theorem pos32 : 0 < 32 := Nat.zero_lt_succ 31
theorem pos5 : 0 < 5 := Nat.zero_lt_succ 4
theorem mod32_lt (s : ℕ) : s % 32 < 32 := Nat.mod_lt s pos32
theorem wirePairsOfReg_mem {W n : ℕ} (r : QRegister W n) :
    ∀ (ps : List (ℕ × ℕ)) (wp : WirePair n), wp ∈ wirePairsOfReg r ps →
      (∃ u : Fin W, r u = wp.1) ∧ (∃ u : Fin W, r u = wp.2.1)
  | [], _, hmem => absurd hmem List.not_mem_nil
  | p :: ps, wp, hmem => by
      dsimp only [wirePairsOfReg] at hmem
      split at hmem
      · rename_i h1 h2
        exact (List.mem_cons.mp hmem).elim (fun e ↦ e ▸ ⟨⟨⟨p.1, lt_trans_ble h1 h2⟩, rfl⟩,
          ⟨⟨p.2, lt_of_ble_succ h2⟩, rfl⟩⟩) (wirePairsOfReg_mem r ps wp)
      · exact wirePairsOfReg_mem r ps wp hmem
theorem mkKetOpW_id_eq_proj {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n) :
    mkKetOpW rWork (fun δ ↦ δ) (fun _ ↦ 0) = rWork.basisOutcomeProjector 0 :=
  matrix_ext_ket fun η ↦ by
    rw [mkKetOpW_mulVec_ket, SelectRefl.ket_basisOutcomeProjector_zero]; split_ifs <;>
        simp [QubitizationWalkSem.bitSign]
theorem subspaceStep_triangularTierX {Var : Type} [Fintype Var] [DecidableEq Var] {B Wk Wp n : ℕ}
    [NeZero (2 ^ n)] (hB : 0 < B) (v : Var) (rWork : QRegister Wk n) (rPred : QRegister Wp n)
    (rOut : QRegister B n) (bnd : Fin B → ℕ) (px : Fin B → Bool) (rawPairs : Fin B → List (ℕ × ℕ))
    (stPost : BitAssignment n → BitAssignment n) (gBit : BitAssignment n → Fin B → Bool)
    (hBndLe : ∀ s : Fin B, bnd s ≤ Wp) (hPairsOk : ∀ s : Fin B, checkPairsBound (bnd s)
    (rawPairs s) = true) (hDisjLt : ∀ (s : Fin B) (u : Fin Wp), u.val < bnd s → rPred u ≠ rOut s)
    (hOut0 : ∀ (s : Fin B) (δ : BitAssignment n), (∀ k : Fin Wk, δ (rWork k) = 0) →
    stPost δ (rOut s) = 0) (hEval : ∀ (s : Fin B) (δ : BitAssignment n),
    (∀ k : Fin Wk, δ (rWork k) = 0) → ∃ bitOf : ℕ → Bool, (∀ u : Fin Wp, u.val < bnd s →
    updPrefix hB rOut (stPost δ)
    (fun q ↦ if gBit δ ⟨q % B, Nat.mod_lt q hB⟩ then 1 else 0) s.val (rPred u) =
    if bitOf u.val then 1 else 0) ∧ xor (px s) (pairsParityBool bitOf (rawPairs s)) = gBit δ s) :
    SubspaceStep (mkKetOpW rWork (fun δ ↦ writeReg (stPost δ) rOut (fun s ↦
    if gBit δ s then 1 else 0)) (fun _ ↦ 0)) (mkKetOpW rWork stPost (fun _ ↦ 0))
    (xUnloadChunkCzPairsXSeqDyn v (outWireOfReg hB rOut) 0 (fun i ↦ px ⟨i % B, Nat.mod_lt i hB⟩)
    (fun i ↦ wirePairsOfReg rPred (rawPairs ⟨i % B, Nat.mod_lt i hB⟩)) (.circuit .identity) B) := by
  let rO := outWireOfReg hB rOut
  let pxN (i : ℕ) := px ⟨i % B, Nat.mod_lt i hB⟩
  let pfN (i : ℕ) := wirePairsOfReg rPred (rawPairs ⟨i % B, Nat.mod_lt i hB⟩)
  let bf (i : ℕ) (β : BitAssignment n) :=
      (if pxN i then (1 : ZMod 2) else 0) + czPairsParity (pfN i) β
  have hdj (i) (p) (hp : p ∈ pfN i) : p.1 ≠ rO (0 + i) ∧ p.2.1 ≠ rO (0 + i) := by
    let s : Fin B := ⟨i % B, Nat.mod_lt i hB⟩
    rw [show rO (0 + i) = rOut s from congrArg rOut.wires (Fin.ext (congrArg (· % B)
        (Nat.zero_add i)))]
    obtain ⟨⟨u1, hu1, e1⟩, ⟨u2, hu2, e2⟩⟩ :=
        wirePairsOfReg_mem_lt rPred (rawPairs s) (hPairsOk s) p hp
    exact ⟨e1 ▸ hDisjLt s u1 hu1, e2 ▸ hDisjLt s u2 hu2⟩
  have hf (i) (β) (a) : bf i (Function.update β (rO (0 + i)) a) = bf i β :=
    congrArg ((if pxN i then (1 : ZMod 2) else 0) + ·) (czPairsParity_indep (rO (0 + i)) (pfN i)
        (hdj i) β a)
  let R := mkKetOpW rWork stPost (fun _ ↦ 0)
  let gZ (δ : BitAssignment n) (q : ℕ) : ZMod 2 := if gBit δ ⟨q % B, Nat.mod_lt q hB⟩ then 1 else 0
  have hChunk (k) (hk : k ≤ B) :
      chunkXorOp rO 0 bf hf k * R = mkKetOpW rWork (fun δ ↦ updPrefix hB rOut (stPost δ) (gZ δ) k)
          (fun _ ↦ 0) := by
    induction k with
    | zero => exact Matrix.one_mul R
    | succ m ih =>
        let s : Fin B := ⟨m, Nat.lt_of_succ_le hk⟩
        change ((xorWireUnitary (rO (0 + m)) (bf m) (hf m)).1 * chunkXorOp rO 0 bf hf m) * R = _
        rw [Matrix.mul_assoc, ih (Nat.le_of_lt s.isLt)]
        refine matrix_ext_ket fun δ ↦ ?_
        rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
        split_ifs with hz
        · rw [Matrix.mulVec_smul, xorWireUnitary_mulVec_ket (rO (0 + m)) (bf m)
              (hf m), Nat.zero_add]
          dsimp only [updPrefix]
          congr 3
          have hU (t) (ht : t ≤ m) : updPrefix hB rOut (stPost δ) (gZ δ) t (rO m) = stPost δ (rO m)
              := by
            induction t with
            | zero => rfl
            | succ q ihq =>
                refine (Function.update_of_ne (fun e ↦ ?_) _ _).trans (ihq (by omega))
                have hv : m % B = q % B := congrArg Fin.val (rOut.wires.injective e)
                rw [Nat.mod_eq_of_lt (Nat.lt_of_succ_le hk), Nat.mod_eq_of_lt (by omega)] at hv;
                    omega
          have hsEq : (⟨m % B, Nat.mod_lt m hB⟩ : Fin B) = s := Fin.ext (Nat.mod_eq_of_lt s.isLt)
          obtain ⟨bitOf, hBit, hPar⟩ := hEval s δ hz
          rw [(hU m le_rfl).trans ((congrArg (stPost δ ∘ rOut) hsEq).trans (hOut0 s δ hz)),
              zero_add]
          simp only [bf, pxN, pfN, gZ, hsEq]
          rw [czPairsParity_wirePairsOfReg rPred (hBndLe s) bitOf _ hBit (rawPairs s)
              (hPairsOk s), z2_add_ite_xor, hPar]
        · rw [Matrix.mulVec_zero]
  refine subspaceStep_congr_in ((hChunk B le_rfl).trans (mkKetOpW_congr rWork (fun δ _ ↦ ?_)
      (fun _ _ ↦ rfl))).symm
    (subspaceStep_xUnloadChunkCzPairsXSeqDyn v rO 0 pxN pfN bf hf (fun _ _ ↦
        rfl) hdj (.circuit .identity) R R
      (by simpa only [Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mul] using subspaceStep_of_circuit (Var := Var) R .identity) B
      (fun a ha b hb hab e ↦ hab (by
        have hv : (0 + a) % B = (0 + b) % B := congrArg Fin.val (rOut.wires.injective e)
        rwa [Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv))
      (fun i _ ↦ projBit_zero_mkKetOpW rWork (rO (0 + i)) stPost (fun _ ↦ 0) fun δ hz ↦
          hOut0 _ δ hz))
  rw [updPrefix_eq_writeReg]
  exact congrArg (writeReg (stPost δ) rOut) (funext fun s ↦ by
    simp only [gZ, show (⟨s.val % B, Nat.mod_lt s.val hB⟩ : Fin B) =
        s from Fin.ext (Nat.mod_eq_of_lt s.isLt)])
theorem updPrefix_tail5_readback {n : ℕ} (rTot : QRegister dLayout n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) :
    ∀ (k : ℕ), k ≤ 5 → ∀ (q : Fin 5), q.val < k →
      updPrefix pos5 (rTot.compose rOutTail5) β g k ((rTot.compose rOutTail5) q) = g q.val
  | 0, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | m + 1, _, q, _ => by
      dsimp only [updPrefix]
      if hqm : q.val = m then
        rw [show (rTot.compose rOutTail5) q = outWireOfReg pos5 (rTot.compose rOutTail5) m from
          congrArg (rTot.compose rOutTail5).wires (Fin.ext (hqm.trans (Nat.mod_eq_of_lt
              (by omega)).symm)),
          Function.update_self, hqm]
      else
        rw [Function.update_of_ne fun e ↦ hqm (by
          have hv : q.val = m % 5 :=
              congrArg Fin.val (rOutTail5.wires.injective (rTot.wires.injective e))
          rwa [Nat.mod_eq_of_lt (by omega)] at hv)]
        exact updPrefix_tail5_readback rTot β g m (by omega) q (by omega)
end QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge Operator QProg Matrix Circuit
  Qubit PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
  (subspaceStep_congr_out specFanoutCopyCirc specFanoutCopyCirc_mulVec_ket specFanoutCopyVecCirc
   specPortUnextract1Unitary specPortUnextractVecUnitary bellZHalfVecDyn bellXHalfVecDyn)
open QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_bellXHalfVec fanoutXorBits fanoutXorBits_of_ne_tgt czFanoutPhase
    czFanoutPhase_indep czFanoutPhase_of_all_zero czFanoutPhase_of_unique_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn
    CircSupportedIn DynSupportedIn circSupportedIn_id circSupportedIn_seq circSupportedIn_H
    circSupportedIn_CNOT circSupportedIn_single)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
section
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
open QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
  QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
open QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB
open PhotochemistrySolution.KetSupport PhotochemistrySolution.ProviderZeroFloor
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
    Stage4KinFull.bAxisMux27
theorem portB_reg_links {n Wp : ℕ} (hMax : max Wp 24 ≤ 714) (rTot : QRegister dLayout n) :
    let rW := rTot.compose rClean690Layout;
    let rB := rTot.compose (rPotZeroNEremPortB (max Wp 24) hMax)
    (rB ⟨4, by omega⟩ = rTot (wPotIsNN rPot0Layout)) ∧ (∀ b : Fin 24, rB ⟨57 + b.val, by omega⟩ =
        rTot (rBufHi rElecLayout b)) ∧
    (∀ b : Fin 24, rB ⟨122 + b.val, by omega⟩ = rTot (rBufHi rNucLayout b)) ∧
        (∀ u : Fin (max Wp 24), 24 ≤ u.val → rB ⟨122 + u.val,
      by omega⟩ = rW ⟨u.val - 24, by omega⟩) := by
  refine ⟨congrArg rTot.wires (potZeroNEremPortBWireFn_eq_old hMax ⟨4, by omega⟩),
    fun _ ↦ congrArg rTot.wires ?_, fun _ ↦ congrArg rTot.wires ?_, fun _ _ ↦
        congrArg rTot.wires ?_⟩ <;>
    change potZeroNEremPortBWireFn (max Wp 24) hMax _ = _ <;>
        dsimp only [potZeroNEremPortBWireFn] <;>
    split_ifs <;> first | omega | exact congrArg _ (Fin.ext (by dsimp; omega))
attribute [local irreducible] rPotZeroNEremPortB
theorem clampOneHot_apply {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    (∀ b : Fin 24, clampOneHot rTot β (rTot (rBufHi rNucLayout b)) =
    if β (rTot (wPotIsNN rPot0Layout)) == 1 then β (rTot (rBufHi rNucLayout b)) else 0) ∧
    (∀ b : Fin 24, clampOneHot rTot β (rTot (rBufHi rElecLayout b)) =
    if β (rTot (wPotIsNN rPot0Layout)) == 1 then 0 else β (rTot (rBufHi rElecLayout b))) ∧
    (∀ w : Wire n, (∀ b : Fin 24, w ≠ rTot (rBufHi rNucLayout b)) → (∀ b : Fin 24, w ≠
    rTot (rBufHi rElecLayout b)) → clampOneHot rTot β w = β w) := by
  obtain ⟨_, h57, h122, _⟩ := portB_reg_links (Wp := 0) (by decide) rTot
  dsimp only [clampOneHot]
  refine ⟨fun b ↦ writeReg_apply_reg _ (rTot.compose ⟨_, rBufHi_inj rNucLayout⟩) _ b,
    fun b ↦ (writeReg_apply_of_not_mem _ (rTot.compose ⟨_, rBufHi_inj rNucLayout⟩) _ _ fun ⟨j, hj⟩ ↦
      absurd (congrArg Fin.val ((rTot.compose _).wires.injective ((h122 j).trans
          (hj.trans (h57 b).symm))))
        (by dsimp; omega)).trans (writeReg_apply_reg _ (rTot.compose ⟨_,
            rBufHi_inj rElecLayout⟩) _ b),
    fun _ hN hE ↦ (writeReg_apply_of_not_mem _ _ _ _ fun ⟨b, hb⟩ ↦ hN b hb.symm).trans
      (writeReg_apply_of_not_mem _ _ _ _ fun ⟨b, hb⟩ ↦ hE b hb.symm)⟩
attribute [local irreducible] clampOneHot DynCircExt.writeReg routedKet outerCoinOf82
  innerBitsOf82 dLayout
end QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB

namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.SortedRouterSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB (clampOneHot
    clampOneHot_apply)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
    clampOneHot
theorem router_disj_rCoinExt_c70 {kExt : ℕ} (hk : kExt ≤ 72) : (∀ i j, rElecLayout i ≠
    rCoinExt kExt hk j) ∧ (∀ i j, rNucLayout i ≠ rCoinExt kExt hk j) ∧ (∀ i j, rElecBorrow96 i ≠
    rCoinExt kExt hk j) ∧ (∀ i j, rNucXor0 i ≠ rCoinExt kExt hk j) ∧ (∀ i j, rClean690Layout i ≠
    rCoinExt kExt hk j) := by
  refine ⟨fun i _ e ↦ ?_, fun i _ e ↦ ?_, fun i _ e ↦ ?_, fun i _ e ↦ ?_, fun _ _ e ↦ ?_⟩ <;>
    have hv := congrArg Fin.val e <;> rw [val_rCoinExt] at hv
  · have : i.val < 5056 := hEW5056 ▸ i.isLt
    rw [show (rElecLayout i).val = _ from val_elecRouterWireFn i] at hv; split_ifs at hv <;>
        omega
  · have := val_rNuc_bounds i
    omega
  · have : i.val < 5056 := hEW5056 ▸ i.isLt
    have : privRank454 (i.val - 4602) < 454 := privRank454_lt (by omega)
    rw [show (rElecBorrow96 i).val = _ from val_elecBorrow96WireFn i] at hv; split_ifs at hv <;>
        omega
  · have : i.val < 1394 := hNW1394 ▸ i.isLt
    rw [show (rNucXor0 i).val = _ from val_nucXor0WireFn i] at hv; split_ifs at hv <;> omega
  · rw [val_rClean690Layout] at hv; split_ifs at hv <;> omega
theorem wNoHadClean_comm_rCoinExt_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) {kExt n : ℕ}
    (hk : kExt ≤ 72) (rTot : QRegister dLayout n) (V : Unitary (2 ^ kExt)) :
    (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))).1 *
    ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 =
    ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 *
    (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))).1
    := by obtain ⟨dE, dN, _, _, _⟩ :=
            router_disj_rCoinExt_c70 hk; rw [QRegister.embedUnitary_compose,
            QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← rTot.embedMatrix_mul,
            ← rTot.embedMatrix_mul]; refine congrArg rTot.embedMatrix ?_; unfold wNoHad;
            rw [Submonoid.coe_mul, Submonoid.coe_mul,
            QRegister.embedUnitary_val]; exact Commute.mul_left (comm_uRouterSwapConj_embedMat_pot
            rElecLayout (rCoinExt kExt hk) dE V.1)
            (Commute.mul_left (comm_uRouterSwapConj_embedMat_pot rNucLayout (rCoinExt kExt hk) dN
            V.1) (uStage1Clean_comm_rCoinExt_c70 decodeCoin hk V.1))
theorem supportedOn_sum_c70 {ι : Type} [Fintype ι] {n : ℕ} {P : BitAssignment n → Prop}
    {M : ι → Operator (2 ^ n)} (hM : ∀ i, SupportedOn P (M i)) :
    SupportedOn P (∑ i, M i) := fun A B hAB ↦ by
  simpa only [Matrix.mul_sum] using Finset.sum_congr rfl fun i _ ↦ hM i A B hAB
theorem supportedOn_uTogGen_mul_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m)
    {P : BitAssignment n → Prop} {Y : Operator (2 ^ n)}
    (hP : ∀ β, P β → P (togBits_c70 rC γ β)) (hY : SupportedOn P Y) :
    SupportedOn P ((uTogGen_c70 rC γ).1 * Y) := fun A B hAB ↦ by
  simpa only [Matrix.mul_assoc] using hY (A * (uTogGen_c70 rC γ).1)
      (B * (uTogGen_c70 rC γ).1) fun β hβ ↦ by
    simpa only [← Matrix.mulVec_mulVec, uTogGen_mulVec_ket_c70] using hAB _ (hP β hβ)
theorem validRouterInput_congr_c70 {M D n : ℕ} (r : RouterReg M D n) {β₁ β₂ : BitAssignment n}
    (hEq : ∀ i : Fin (routerWidth M D), β₁ (r i) = β₂ (r i)) (h1 : ValidRouterInput r β₁) :
    ValidRouterInput r β₂ := by
  refine ⟨fun h ↦ (hEq _).symm.trans (h1.1 ((hEq _).trans h)),
    fun h ↦ (idxValD_congr_gen fun _ ↦ (hEq _).symm) ▸ h1.2.1 ((hEq _).trans h),
    fun h ↦ (idxValD_congr_gen fun _ ↦ (hEq _).symm) ▸ h1.2.2.1 ((hEq _).trans h),
    fun b ↦ ⟨(hEq _).symm.trans (h1.2.2.2.1 b).1, (hEq _).symm.trans (h1.2.2.2.1 b).2.1,
      (hEq _).symm.trans (h1.2.2.2.1 b).2.2.1, (hEq _).symm.trans (h1.2.2.2.1 b).2.2.2⟩,
    fun x hw ↦ by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact (hEq i).symm.trans (h1.2.2.2.2 (r i) hw)⟩
theorem validZeroGatedSorted_congr_c70 {M D n : ℕ} (r : RouterReg M D n) {β₁ β₂ : BitAssignment n}
    (hEq : ∀ i : Fin (routerWidth M D), β₁ (r i) = β₂ (r i))
    (h1 : ValidZeroGatedSortedRouterInput r β₁) : ValidZeroGatedSortedRouterInput r β₂ :=
  ⟨validRouterInput_congr_c70 r hEq h1.1, fun hz d ↦
      (hEq _).symm.trans (h1.2.1 ((hEq _).trans hz) d),
    fun hz d ↦ (hEq _).symm.trans (h1.2.2.1 ((hEq _).trans hz) d),
   fun ho ↦
       by simpa only [idxValD_congr_gen fun _ ↦ (hEq _).symm] using h1.2.2.2 ((hEq _).trans ho)⟩
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.Stage2QromMux
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Sub5885
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
/-! ## Block 2A: Scratch Control Bank `cHiNSub` (`47` Wires `[6021..6067]`, `353 ≤ wWork`) -/

theorem cHiNSub_scrIdx_lt (p : Fin 47) : 371 + p.val < scrLLayout := by
  have _ := p.isLt; dsimp [scrLLayout]; omega
/--
47-wire clean scratch bank `[6021..6067]` (`rScrLayout[371..417]`) holding `Hi_N` unary controls
during the nested `234`-target shared `PortB` Stage-5 unload (`353 ≤ wWork`).
-/
def cHiNSub (p : Fin 47) : Wire dLayout := rScrLayout ⟨371 + p.val, cHiNSub_scrIdx_lt p⟩
theorem val_cHiNSub (p : Fin 47) : (cHiNSub p).val = 6021 + p.val := by
  dsimp only [cHiNSub]; rw [val_rScrLayout]; dsimp; omega
theorem cHiNSub_disj_rCoinExt {kExt : ℕ} (hk : kExt ≤ 72) (p : Fin 47) (j : Fin kExt) :
    cHiNSub p ≠ rCoinExt kExt hk j := fun e ↦ by
  have _ := p.isLt; have _ := j.isLt;
  have hv := congrArg Fin.val e; rw [val_cHiNSub, val_rCoinExt] at hv; omega
theorem val_rNucLayout_eq (i : Fin (routerWidth 47 6)) :
    (rNucLayout i).val = (nucRouterWireFn i).val := rfl
theorem val_rElecLayout_eq (j : Fin (routerWidth 187 8)) :
    (rElecLayout j).val = (elecRouterWireFn j).val := rfl
theorem pubNuc_ne_pubElec {n : ℕ} {rNuc : RouterReg 47 6 dLayout} {rElec : RouterReg 187 8 dLayout}
    (hRegs : ValidMuxD1Stage2Regs rNuc rElec) (rTot : QRegister dLayout n)
    {i : Fin (routerWidth 47 6)} (hi : i.val < 1238)
    {j : Fin (routerWidth 187 8)} (hj : j.val < 4602) :
    (rTot.compose rNuc) i ≠ (rTot.compose rElec) j := fun e ↦ by
  have hv :=
      congrArg Fin.val (rTot.wires.injective e); change (rNuc i).val =
      (rElec j).val at hv; rw [hRegs.pubNuc i hi,
      hRegs.pubElec j hj] at hv; have hN : (rNucLayout i).val = _ :=
                                   val_nucRouterWireFn i; have hE : (rElecLayout j).val = _ :=
                                                            val_elecRouterWireFn j; rw [hN,
                                                            hE] at hv
  split_ifs at hv <;> omega
theorem allPlaneMod_pubIdx_nuc {n : ℕ} {rN : RouterReg 47 6 n} {w : Wire n} (h : AllPlaneMod rN w) :
    ∃ i : Fin (routerWidth 47 6), 14 ≤ i.val ∧ i.val < 1238 ∧ w = rN i := by
  rcases h with ⟨b, rfl | rfl | rfl | rfl | ⟨p, rfl⟩⟩ <;> simp only [planeOfRouter_bufLo,
      planeOfRouter_bufHi, planeOfRouter_hA,
    planeOfRouter_hB, planeOfRouter_sys] <;> exact ⟨_, by dsimp; omega, by dsimp; omega, rfl⟩
theorem allPlaneMod_pubIdx_elec {n : ℕ} {rE : RouterReg 187 8 n} {w : Wire n}
    (h : AllPlaneMod rE w) : ∃ j : Fin (routerWidth 187 8), 18 ≤ j.val ∧ j.val < 4602 ∧ w =
    rE j := by
  rcases h with ⟨b, rfl | rfl | rfl | rfl | ⟨q, rfl⟩⟩ <;> simp only [planeOfRouter_bufLo,
      planeOfRouter_bufHi, planeOfRouter_hA,
    planeOfRouter_hB, planeOfRouter_sys] <;> exact ⟨_, by dsimp; omega, by dsimp; omega, rfl⟩
/-! ## Block 2B: `SharedPortBInput` Invariant & `routerChain_sharedPortB_ext` -/

theorem zeroNEremOutMask_isNN_and_oneHot {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (c : Fin (2 ^ 41)) (δ : BitAssignment dLayout) (hOut : ∀ j : Fin 40, δ (rOut40Layout j) =
    outMaskBits40 (decodeCoin c) j) : δ (wPotIsNN rPot0Layout) = δ (rRawHas2 rNucLayout) ∧
    (δ (rRawHas2 rNucLayout) = 1 → δ (rRawHas2 rElecLayout) = 0) := by
  have cp (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ) (s p k : Bool) (sp1 a2 : ℕ)
      (heq : zeroNEremOutMask (decodeCoin c) =
          packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 s p k hN2 sp1 a2)
      (hb : n1 < 47 ∧ n2 < 47 ∧ e1 < 187 ∧ e2 < 187 := by
        omega) (hx : hN2 = true → hE2 = false := by decide) :
      δ (wPotIsNN rPot0Layout) = δ (rRawHas2 rNucLayout) ∧ (δ (rRawHas2 rNucLayout) = 1 →
          δ (rRawHas2 rElecLayout) = 0) := by
    have F := packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 s p k hN2 sp1 a2
      (by omega) (by omega) (by omega) (by omega) δ fun j ↦
          (hOut j).trans (by simp [outMaskBits40, heq])
    rw [F.2.2.2.2.2.2.2.2.2.2.2.1, F.2.1, F.2.2.2.2.2.1]
    exact ⟨rfl, fun h1 ↦ by cases hN2 <;> first | exact absurd h1 zero_ne_one | simp [hx rfl]⟩
  cases hc : decodeCoin c with
  | idle => exact cp false false 0 0 false false 0 0 false false false 0 0 (congrArg _ hc)
  | ee n1 e1 e2 =>
      exact cp true false n1.val 0 true true e1.val e2.val true true false (nucSpecies n1).val 0
        (congrArg _ hc)
  | nn n1 n2 e1 =>
      exact cp true true n1.val n2.val true false e1.val 0 true true false
        (nucSpecies n1).val (nucSpecies n2).val (congrArg _ hc)
  | en n1 e1 =>
      exact cp true false n1.val 0 true false e1.val 0 false true false (nucSpecies n1).val 0
        (congrArg _ hc)
  | kin i ax =>
      if hi : i.val < 47 then
        exact cp true false i.val 0 false false 0 0 false false true 0 ax.val ((congrArg _ hc).trans
            (ite_eq_left hi))
      else exact cp false false 0 0 true false (i.val -
          47) 0 false false true 0 ax.val ((congrArg _ hc).trans (ite_eq_right hi))
/--
Combined Stage-5 input subspace predicate for shared-`PortB` unloading:
both `(rE, rN)` satisfy `ValidZeroGatedSortedRouterInput`, `cHiNSub` (`[6021..6067]`) is `|0⟩^47`,
`wPotIsNN = rRawHas2 rN`, and at most one of `(rRawHas2 rN, rRawHas2 rE)` is `1`.
-/
def SharedPortBInput {n : ℕ} (rTot : QRegister dLayout n) (rN : RouterReg 47 6 n)
    (rE : RouterReg 187 8 n) (β : BitAssignment n) : Prop :=
    ValidZeroGatedSortedRouterInput rE β ∧ ValidZeroGatedSortedRouterInput rN β ∧
    (∀ p : Fin 47, β (rTot (cHiNSub p)) = 0) ∧ β (rTot (wPotIsNN rPot0Layout)) = β (rRawHas2 rN) ∧
    (β (rRawHas2 rN) = 1 → β (rRawHas2 rE) = 0)
theorem sharedPortBInput_congr {n : ℕ} (rTot : QRegister dLayout n) (rN : RouterReg 47 6 n)
    (rE : RouterReg 187 8 n) {β₁ β₂ : BitAssignment n} (hE : ∀ j, β₁ (rE j) = β₂ (rE j))
    (hN : ∀ i, β₁ (rN i) = β₂ (rN i)) (hC : ∀ p, β₁ (rTot (cHiNSub p)) = β₂ (rTot (cHiNSub p)))
    (hNN : β₁ (rTot (wPotIsNN rPot0Layout)) = β₂ (rTot (wPotIsNN rPot0Layout)))
    (h : SharedPortBInput rTot rN rE β₁) : SharedPortBInput rTot rN rE β₂ := by
  have hRawN : β₁ (rRawHas2 rN) = β₂ (rRawHas2 rN) := hN _;
  have hRawE : β₁ (rRawHas2 rE) = β₂ (rRawHas2 rE) := hE _
  exact ⟨validZeroGatedSorted_congr_c70 rE hE h.1, validZeroGatedSorted_congr_c70 rN hN h.2.1,
      fun p ↦ (hC p).symm.trans (h.2.2.1 p), hNN.symm.trans (h.2.2.2.1.trans hRawN), fun ho ↦
      hRawE.symm.trans (h.2.2.2.2 (hRawN.trans ho))⟩
end QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
open scoped Circuit.Notation
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.PotOraclePortB
open PhotochemistrySolution.ProviderZeroFloor PhotochemistrySolution.Kinetic664
  PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Sub5885
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
/-! ## Block 1A: Exact Wire Indices of `wPotIsNN` and `rBufHi` (`rElecLayout`, `rNucLayout`) -/

theorem hMax0_24_le_714 : max 0 24 ≤ 714 := by decide
theorem portB0_links_dLayout : (rPotZeroNEremPortB (max 0 24) hMax0_24_le_714 ⟨4, by decide⟩ =
    wPotIsNN rPot0Layout) ∧
    (∀ b : Fin 24, rPotZeroNEremPortB (max 0 24) hMax0_24_le_714 ⟨57 + b.val, by omega⟩ =
        rBufHi rElecLayout b) ∧
    (∀ b : Fin 24, rPotZeroNEremPortB (max 0 24) hMax0_24_le_714 ⟨122 + b.val, by omega⟩ =
        rBufHi rNucLayout b) :=
  let h := portB_reg_links (Wp := 0) hMax0_24_le_714 (QRegister.whole dLayout)
  ⟨h.1, h.2.1, h.2.2.1⟩
theorem val_wPotIsNN_rPot0Layout : (wPotIsNN rPot0Layout).val = 5750 := by decide
theorem val_rBufHi_rElecLayout (b : Fin 24) : (rBufHi rElecLayout b).val = 5875 + b.val := by
  have hb :=
      b.isLt; rw [← portB0_links_dLayout.2.1 b]; change (potZeroNEremPortBWireFn (max 0 24)
      hMax0_24_le_714 ⟨57 + b.val, _⟩).val = 5875 +
      b.val; rw [val_potZeroNEremPortBWireFn hMax0_24_le_714]
  dsimp only; split_ifs <;> omega
theorem val_rBufHi_rNucLayout (b : Fin 24) : (rBufHi rNucLayout b).val = 5779 + b.val := by
  have hb :=
      b.isLt; rw [← portB0_links_dLayout.2.2 b]; change (potZeroNEremPortBWireFn (max 0 24)
      hMax0_24_le_714 ⟨122 + b.val, _⟩).val = 5779 +
      b.val; rw [val_potZeroNEremPortBWireFn hMax0_24_le_714]
  dsimp only; split_ifs <;> omega
theorem swapHi24_wires_ne {n : ℕ} (rTot : QRegister dLayout n) :
    (∀ b : Fin 24, rTot (wPotIsNN rPot0Layout) ≠ rTot (rBufHi rElecLayout b)) ∧
    (∀ b : Fin 24, rTot (wPotIsNN rPot0Layout) ≠ rTot (rBufHi rNucLayout b)) ∧ (∀ a b : Fin 24,
    rTot (rBufHi rElecLayout a) ≠ rTot (rBufHi rNucLayout b)) ∧ (∀ a b : Fin 24,
    rTot (rBufHi rElecLayout a) = rTot (rBufHi rElecLayout b) → a = b) ∧ (∀ a b : Fin 24,
    rTot (rBufHi rNucLayout a) = rTot (rBufHi rNucLayout b) → a = b) := by
  refine ⟨fun b e ↦ ?_, fun b e ↦ ?_, fun a b e ↦ ?_, fun a b e ↦ Fin.ext ?_, fun a b e ↦
      Fin.ext ?_⟩ <;>
    have hv := congrArg Fin.val (rTot.wires.injective e) <;>
    simp only [val_wPotIsNN_rPot0Layout, val_rBufHi_rElecLayout, val_rBufHi_rNucLayout] at hv <;>
        omega
theorem cFredkin_mulVec_ket {n : ℕ} (c a b : Wire n) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (β : BitAssignment n) : (cFredkin c a b hab hca hcb).eval.1.mulVec (ket β) =
    ket (swap1Bits c a b β) := by
  change (Circuit.seq (.CNOT a b hab) (.seq (.TOFF c b a hcb hca hab.symm)
      (.CNOT a b hab))).eval.1.mulVec
      (DynCircExt.ket β) = DynCircExt.ket (swap1Bits c a b β)
  rw [DynCircExt.eval_seq_mulVec, DynCircExt.eval_seq_mulVec,
    DynCircExt.ket_CNOT, DynCircExt.ket_TOFF, DynCircExt.ket_CNOT]
  refine congrArg DynCircExt.ket (funext fun w ↦ ?_)
  if hw : w = b ∨ w = a then
    have hab' := hab.symm; have hca' := hca.symm; have hcb' := hcb.symm
    rcases hw with h | h <;> rw [h] <;> rcases DynCircExt.bit_cases (β c) with hc | hc <;>
      rcases DynCircExt.bit_cases (β a) with ha | ha <;>
      rcases DynCircExt.bit_cases (β b) with hb | hb <;> (
        dsimp only [swap1Bits]
        simp only [hc, ha, hb, zero_ne_one, ↓reduceIte, Function.update_apply]
        split_ifs <;> first | contradiction | decide)
  else
    dsimp only [swap1Bits]
    split_ifs <;> simp [(not_or.mp hw).1, (not_or.mp hw).2]
def swapHi24Prefix {n : ℕ} (rTot : QRegister dLayout n) : ℕ → BitAssignment n → BitAssignment n
  | 0, β => β
  | j + 1, β =>
      if hj : j < 24 then
        swap1Bits (rTot (wPotIsNN rPot0Layout))
          (rTot (rBufHi rElecLayout ⟨j, hj⟩))
          (rTot (rBufHi rNucLayout ⟨j, hj⟩))
          (swapHi24Prefix rTot j β)
      else swapHi24Prefix rTot j β
def cSwapHi24Aux {n : ℕ} (rTot : QRegister dLayout n) : ∀ k : ℕ, k ≤ 24 → Circuit n
  | 0, _ => .identity
  | j + 1, hj =>
      let hne := swapHi24_wires_ne rTot
      cSwapHi24Aux rTot j (Nat.le_of_succ_le hj) ;;ᶜ
        cFredkin (rTot (wPotIsNN rPot0Layout))
          (rTot (rBufHi rElecLayout ⟨j, hj⟩))
          (rTot (rBufHi rNucLayout ⟨j, hj⟩))
          (hne.2.2.1 ⟨j, hj⟩ ⟨j, hj⟩)
          (hne.1 ⟨j, hj⟩)
          (hne.2.1 ⟨j, hj⟩)
theorem cSwapHi24Aux_mulVec_ket {n : ℕ} (rTot : QRegister dLayout n) :
    ∀ (k : ℕ) (hk : k ≤ 24) (β : BitAssignment n),
      (cSwapHi24Aux rTot k hk).eval.1.mulVec (ket β) = ket (swapHi24Prefix rTot k β)
  | 0, _, β =>
        by simp only [cSwapHi24Aux, swapHi24Prefix, Circuit.eval_identity, Submonoid.coe_one,
             Matrix.one_mulVec]
  | j + 1, hj, β => by
      have hlt : j < 24 :=
          hj; dsimp only [cSwapHi24Aux, swapHi24Prefix]; rw [DynCircExt.eval_seq_mulVec,
          cSwapHi24Aux_mulVec_ket rTot j (Nat.le_of_succ_le hj) β,
          dite_eq_left hlt]; exact cFredkin_mulVec_ket _ _ _ _ _ _ _
theorem swapHi24Prefix_props {n : ℕ} (rTot : QRegister dLayout n) :
    ∀ (k : ℕ) (_hk : k ≤ 24) (β : BitAssignment n),
      (∀ b : Fin 24, b.val < k →
        swapHi24Prefix rTot k β (rTot (rBufHi rElecLayout b)) =
          if β (rTot (wPotIsNN rPot0Layout)) = 1 then β (rTot (rBufHi rNucLayout b))
          else β (rTot (rBufHi rElecLayout b))) ∧
      (∀ b : Fin 24, b.val < k →
        swapHi24Prefix rTot k β (rTot (rBufHi rNucLayout b)) =
          if β (rTot (wPotIsNN rPot0Layout)) = 1 then β (rTot (rBufHi rElecLayout b))
          else β (rTot (rBufHi rNucLayout b))) ∧
      (∀ w : Wire n,
        (∀ b : Fin 24, b.val < k →
          w ≠ rTot (rBufHi rElecLayout b) ∧ w ≠ rTot (rBufHi rNucLayout b)) →
        swapHi24Prefix rTot k β w = β w)
  | 0, _, _ =>
        ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ ↦
        rfl⟩
  | j + 1, hj, β => by
      obtain ⟨hE, hN, hO⟩ := swapHi24Prefix_props rTot j (Nat.le_of_succ_le hj) β
      obtain ⟨hneNE, hneNN, hneEN, hinjE, hinjN⟩ := swapHi24_wires_ne rTot
      let bj : Fin 24 := ⟨j, hj⟩
      dsimp only [swapHi24Prefix]
      rw [dite_eq_left (show j < 24 from hj)]
      set γ := swapHi24Prefix rTot j β
      have hγNN := hO (rTot (wPotIsNN rPot0Layout)) fun b _ ↦ ⟨hneNE b, hneNN b⟩
      have hγEj := hO (rTot (rBufHi rElecLayout bj)) fun b hb ↦
        ⟨fun e ↦ Nat.ne_of_gt hb (congrArg Fin.val (hinjE bj b e)), hneEN bj b⟩
      have hγNj := hO (rTot (rBufHi rNucLayout bj)) fun b hb ↦
        ⟨(hneEN b bj).symm, fun e ↦ Nat.ne_of_gt hb (congrArg Fin.val (hinjN bj b e))⟩
      have hKeep {w : Wire n} (h1 : w ≠ rTot (rBufHi rElecLayout bj))
          (h2 : w ≠ rTot (rBufHi rNucLayout bj)) :
          swap1Bits (rTot (wPotIsNN rPot0Layout)) (rTot (rBufHi rElecLayout bj))
            (rTot (rBufHi rNucLayout bj)) γ w = γ w := by
        dsimp only [swap1Bits]
        split_ifs <;> simp [h1, h2]
      refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_, fun w hw ↦
        (hKeep (hw bj (Nat.lt_succ_self j)).1 (hw bj (Nat.lt_succ_self j)).2).trans
          (hO w fun b hb ↦ hw b (Nat.lt_succ_of_lt hb))⟩
      · rcases eq_or_ne b bj with rfl | hbj
        · dsimp only [swap1Bits]
          rw [hγNN]
          split_ifs <;> first | exact hγEj | rw [Function.update_of_ne (hneEN bj bj),
              Function.update_self, hγNj]
        · exact (hKeep (fun e ↦ hbj (hinjE b bj e)) (hneEN b bj)).trans
            (hE b (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hb) (Fin.val_ne_of_ne hbj)))
      · rcases eq_or_ne b bj with rfl | hbj
        · dsimp only [swap1Bits]
          rw [hγNN]
          split_ifs <;> first | exact hγNj | rw [Function.update_self, hγEj]
        · exact (hKeep (hneEN bj b).symm (fun e ↦ hbj (hinjN b bj e))).trans
            (hN b (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hb) (Fin.val_ne_of_ne hbj)))
def swapHi24Bits {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) : BitAssignment n :=
  swapHi24Prefix rTot 24 β
/--
Pure-ghost 24-bit controlled-SWAP unitary swapping `rBufHi rElecLayout` and `rBufHi rNucLayout`
when `wPotIsNN rPot0Layout = 1`.
-/
def uSwapHi24 {n : ℕ} (rTot : QRegister dLayout n) : Unitary (2 ^ n) :=
    (cSwapHi24Aux rTot 24 le_rfl).eval
theorem uSwapHi24_mulVec_ket {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    (uSwapHi24 rTot).1.mulVec (ket β) = ket (swapHi24Bits rTot β) :=
    cSwapHi24Aux_mulVec_ket rTot 24 le_rfl β
theorem swapHi24Bits_apply {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    (∀ b : Fin 24, swapHi24Bits rTot β (rTot (rBufHi rElecLayout b)) =
    if β (rTot (wPotIsNN rPot0Layout)) =
    1 then β (rTot (rBufHi rNucLayout b)) else β (rTot (rBufHi rElecLayout b))) ∧
    (∀ b : Fin 24, swapHi24Bits rTot β (rTot (rBufHi rNucLayout b)) =
    if β (rTot (wPotIsNN rPot0Layout)) =
    1 then β (rTot (rBufHi rElecLayout b)) else β (rTot (rBufHi rNucLayout b))) ∧
    (∀ w : Wire n, (∀ b : Fin 24, w ≠ rTot (rBufHi rElecLayout b)) → (∀ b : Fin 24, w ≠
    rTot (rBufHi rNucLayout b)) → swapHi24Bits rTot β w = β w) := by
  obtain ⟨hE, hN, hO⟩ := swapHi24Prefix_props rTot 24 le_rfl β
  exact ⟨fun b ↦ hE b b.isLt, fun b ↦ hN b b.isLt, fun w hwE hwN ↦ hO w fun b _ ↦ ⟨hwE b, hwN b⟩⟩
/-! ## Block 1D: Universal `DynWires` -> `DynSupportedIn` & `uBellOverlayConj` Commutation -/

theorem circSupportedIn_of_circWires {n : ℕ} {S : Wire n → Prop} : ∀ {c : Circuit n},
    CircWires S c → c.count .TOFF = 0
    → CircSupportedIn S c
  | .identity, _, _ => circSupportedIn_id
  | .seq _ _, ⟨h₁, h₂⟩, ht => by
      rw [Circuit.count_seq] at ht
      exact circSupportedIn_seq (circSupportedIn_of_circWires h₁ (by omega))
          (circSupportedIn_of_circWires h₂ (by omega))
  | .gate g reg, hg, ht => by
      cases g with
      | x | y | z | h | s | t =>
          exact (show reg = QRegister.singleton (reg 0) from
            qreg_ext fun i ↦ by fin_cases i; rfl) ▸ circSupportedIn_single _ (hg 0)
      | cnot =>
          have h01 : reg 0 ≠ reg 1 := reg.wires.injective.ne (by decide)
          exact (congrArg _ (qreg_ext fun i ↦
              by fin_cases i <;> rfl) : (.gate .cnot reg : Circuit n) = Circuit.CNOT (reg 0)
                   (reg 1) h01) ▸
            circSupportedIn_CNOT h01 (hg 0) (hg 1)
      | swap =>
          have h01 : reg 0 ≠ reg 1 := reg.wires.injective.ne (by decide)
          intro U hU
          rw [eval_gate_swap_eq_polySwapWire2Circ reg]
          exact circSupportedIn_seq (circSupportedIn_CNOT h01 (hg 0) (hg 1))
            (circSupportedIn_seq (circSupportedIn_CNOT h01.symm (hg 1) (hg 0))
                (circSupportedIn_CNOT h01 (hg 0) (hg 1))) U hU
      | toffoli => simp [Circuit.count] at ht
theorem dynSupportedIn_of_dynWires {Var : Type} {n : ℕ} {S : Wire n → Prop} :
    ∀ {p : DynamicCircuit Var n}, DynWires S p → p.count .TOFF = 0 → DynSupportedIn S p := by
  intro p hp ht
  induction p with
  | circuit _ => exact circSupportedIn_of_circWires hp ht
  | measure _ reg => exact ⟨reg 0, hp 0, qreg_ext fun i ↦ by fin_cases i; rfl⟩
  | qIf _ _ _ ih₁ ih₂ | seq _ _ ih₁ ih₂ =>
      simp only [DynamicCircuit.count] at ht
      exact ⟨ih₁ hp.1 (by omega), ih₂ hp.2 (by omega)⟩
end QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
end

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PhotochemistrySolution.KetSupport PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.Sub5885MuxD1
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
  (validZeroGatedSorted_congr_c70)
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    SplitBellVecCleanStep.cnotFanoutCirc SplitBellVecCleanStep.czFanoutCirc
    SplitBellVecCleanStep.specFanoutCopyCirc SplitBellVecCleanStep.bellZHalf1Dyn
    SplitBellVecCleanStep.bellXHalf1Dyn SplitBellVecCleanStep.bellZHalfVecDyn
    SplitBellVecCleanStep.bellXHalfVecDyn
/-! ## Block 3A: `appendFin` & Combined One-Hot Control Properties -/

def appendFin {M₁ M₂ : ℕ} {α : Type*} (f₁ : Fin M₁ → α) (f₂ : Fin M₂ → α) (i : Fin (M₁ + M₂)) : α :=
  if h : i.val < M₁ then f₁ ⟨i.val, h⟩
  else f₂ ⟨i.val - M₁, by omega⟩
theorem appendFin_castAdd {M₁ M₂ : ℕ} {α : Type*} (f₁ : Fin M₁ → α) (f₂ : Fin M₂ → α)
    (p : Fin M₁) : appendFin f₁ f₂ (Fin.castAdd M₂ p) =
    f₁ p := by dsimp only [appendFin, Fin.val_castAdd]; rw [dite_eq_left p.isLt]
theorem appendFin_natAdd {M₁ M₂ : ℕ} {α : Type*} (f₁ : Fin M₁ → α) (f₂ : Fin M₂ → α)
    (q : Fin M₂) : appendFin f₁ f₂ (Fin.natAdd M₁ q) = f₂ q := by
  simp only [appendFin, Fin.val_natAdd, show ¬ M₁ + q.val < M₁ by omega, ↓reduceDIte]
  exact congrArg f₂ (Fin.ext (Nat.add_sub_cancel_left M₁ q.val))
theorem appendFin_cases {M₁ M₂ : ℕ} {P : Fin (M₁ + M₂) → Prop}
    (h₁ : ∀ p : Fin M₁, P (Fin.castAdd M₂ p)) (h₂ : ∀ q : Fin M₂,
  P (Fin.natAdd M₁ q)) (i : Fin (M₁ + M₂)) : P i :=
  if hi : i.val < M₁ then Eq.ndrec (motive := P) (h₁ ⟨i.val, hi⟩) (Fin.ext rfl)
  else Eq.ndrec (motive := P) (h₂ ⟨i.val - M₁, by omega⟩)
      (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hi)))
theorem appendFin_eq {M₁ M₂ : ℕ} (i : Fin (M₁ + M₂)) : (∃ p : Fin M₁, i = Fin.castAdd M₂ p) ∨
    (∃ q : Fin M₂, i = Fin.natAdd M₁ q) :=
  if hi : i.val < M₁ then Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  else Or.inr ⟨⟨i.val - M₁, by omega⟩, Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hi)).symm⟩
theorem appendFin_inj {M₁ M₂ : ℕ} {α : Type*} {f₁ : Fin M₁ → α} {f₂ : Fin M₂ → α}
    (h₁ : Function.Injective f₁)
    (h₂ : Function.Injective f₂) (hDisj : ∀ p q, f₁ p ≠ f₂ q) : Function.Injective (appendFin f₁ f₂)
        := fun i j ↦
  appendFin_cases (P := fun i ↦ appendFin f₁ f₂ i = appendFin f₁ f₂ j → i = j)
    (fun p₁ ↦ appendFin_cases (P := fun j ↦ appendFin f₁ f₂ (Fin.castAdd M₂ p₁) =
        appendFin f₁ f₂ j → Fin.castAdd M₂ p₁ = j)
      (fun p₂ e ↦ congrArg (Fin.castAdd M₂) (h₁ (by simpa only [appendFin_castAdd] using e)))
      (fun q₂ e ↦ absurd (by simpa only [appendFin_castAdd, appendFin_natAdd] using e)
          (hDisj p₁ q₂)) j)
    (fun q₁ ↦ appendFin_cases (P := fun j ↦ appendFin f₁ f₂ (Fin.natAdd M₁ q₁) = appendFin f₁ f₂ j →
        Fin.natAdd M₁ q₁ = j)
      (fun p₂ e ↦ absurd (by simpa only [appendFin_natAdd, appendFin_castAdd] using e.symm)
          (hDisj p₂ q₁))
      (fun q₂ e ↦ congrArg (Fin.natAdd M₁) (h₂ (by simpa only [appendFin_natAdd] using e))) j) i
theorem atMostOneCtrl_appendFin {M₁ M₂ n : ℕ} (w₁ : Fin M₁ → Wire n) (w₂ : Fin M₂ → Wire n)
    (γ : BitAssignment n) (h₁ : AtMostOneCtrl w₁ γ) (h₂ : AtMostOneCtrl w₂ γ)
    (hExcl : (∃ p, γ (w₁ p) = 1) → ∀ q, γ (w₂ q) = 0) : AtMostOneCtrl (appendFin w₁ w₂) γ := by
  have hc (p : Fin M₁) := congrArg γ (appendFin_castAdd w₁ w₂ p)
  have hn (q : Fin M₂) := congrArg γ (appendFin_natAdd w₁ w₂ q)
  rcases h₁ with hz₁ | ⟨p₀, hp1, hp0⟩
  · exact h₂.imp (fun hz₂ ↦ appendFin_cases (fun p ↦ (hc p).trans (hz₁ p))
        (fun q ↦ (hn q).trans (hz₂ q)))
      fun ⟨q₀, hq1, hq0⟩ ↦
          ⟨Fin.natAdd M₁ q₀, (hn q₀).trans hq1, appendFin_cases (fun p _ ↦ (hc p).trans (hz₁ p))
        fun q hne ↦ (hn q).trans (hq0 q fun e ↦ hne (congrArg (Fin.natAdd M₁) e))⟩
  · exact .inr ⟨Fin.castAdd M₂ p₀, (hc p₀).trans hp1, appendFin_cases
      (fun p hne ↦ (hc p).trans (hp0 p fun e ↦ hne (congrArg (Fin.castAdd M₂) e))) fun q _ ↦
          (hn q).trans (hExcl ⟨p₀, hp1⟩ q)⟩
/-! ## Block 3B: `RouterReg`-Free `subspaceStep_bellXHalfVec_general` -/

def GenPlaneMod {M n : ℕ} (qB : Wire n) (wT : Fin M → Wire n) (u : Wire n) : Prop :=
    u = qB ∨ ∃ p : Fin M, u = wT p
theorem genUnextract1_portSwap1_ket {M n : ℕ} (qB : Wire n) (wC wT : Fin M → Wire n)
    (hwT_inj : Function.Injective wT) (hbc : ∀ p, qB ≠ wC p) (hbt : ∀ p, qB ≠ wT p)
    (hc_disj : ∀ p q, wC p ≠ wT q) {δ : BitAssignment n} (hOne : AtMostOneCtrl wC δ)
    (hqB0 : δ qB = 0) : (specPortUnextract1Unitary M qB wC wT hbc hbt (fun p ↦
    hc_disj p p)).1.mulVec ((portSwap1Circ M qB wC wT hbc hbt (fun p ↦
    hc_disj p p)).eval.1.mulVec (ket δ)) = ket δ := by
  dsimp only [specPortUnextract1Unitary, Submonoid.coe_mul]
  rw [← Matrix.mulVec_mulVec, portSwap1Circ_mulVec_ket, ket_sr_eq, specFanoutCopyCirc_mulVec_ket]
  rcases hOne with hz | ⟨p₀, hp1, hp0⟩
  · rw [portSwap1Bits_of_all_zero M qB wC wT hc_disj hbc δ hz, itePos hqB0, ← ket_sr_eq,
        bitToggleUnitary_mulVec_ket, ket_sr_eq, hqB0,
      czFanoutPhase_of_all_zero M wC wT δ hz, add_zero, show Function.update δ qB 0 =
          δ from hqB0 ▸ Function.update_eq_self qB δ]
  · rw [portSwap1Bits_of_unique_one M qB wC wT hbc hbt hc_disj (fun a b hne e ↦
        hne (hwT_inj e)) δ p₀ hp1 hp0, hqB0]
    set δs := Function.update (Function.update δ qB (δ (wT p₀))) (wT p₀) 0
    have hδs_c (p : Fin M) : δs (wC p) = δ (wC p) := by
      simp only [δs, Function.update_of_ne (hc_disj p p₀), Function.update_of_ne (hbc p).symm]
    rw [show δs qB = δ (wT p₀) by simp [δs, hbt p₀]]
    have hu0 : Function.update δ qB 0 = δ := hqB0 ▸ Function.update_eq_self qB δ
    rcases DynCircExt.bit_cases (δ (wT p₀)) with hs0 | hs1
    · rw [itePos hs0, show δs = δ by
        dsimp only [δs]
        rw [hs0, hu0, show Function.update δ (wT p₀) 0 =
            δ from hs0 ▸ Function.update_eq_self (wT p₀) δ],
        ← ket_sr_eq, bitToggleUnitary_mulVec_ket, ket_sr_eq, hqB0,
        czFanoutPhase_of_unique_one M wC wT δ p₀ hp1 hp0, hs0, add_zero, hu0]
    · rw [iteNeg (hs1 ▸ one_ne_zero),
        SplitBellVecCleanStep.fanoutXorBits_of_unique_one M wC wT hc_disj δs p₀
          ((hδs_c p₀).trans hp1) (fun p hp ↦ (hδs_c p).trans (hp0 p hp)),
        show Function.update δs (wT p₀)
            (δs (wT p₀) + 1) = Function.update δ qB 1 from funext fun u ↦ by
          by_cases huS : u = wT p₀ <;> by_cases huB : u = qB <;> simp [δs, huS, huB, hbt p₀,
              (hbt p₀).symm, hs1],
        ← ket_sr_eq, bitToggleUnitary_mulVec_ket, ket_dc_eq, Function.update_self,
        czFanoutPhase_indep M wC wT (fun p ↦ (hbc p).symm) (fun p ↦ (hbt p).symm) δ 1,
        czFanoutPhase_of_unique_one M wC wT δ p₀ hp1 hp0, hs1, show (1 : ZMod 2) + 1 = 0 from rfl,
        Function.update_idem, hu0]
theorem genSwap1_localKetOp {M n : ℕ} (qB : Wire n) (wC wT : Fin M → Wire n) (hbc : ∀ p, qB ≠ wC p)
    (hbt : ∀ p, qB ≠ wT p) (hct : ∀ p, wC p ≠ wT p) (O : Wire n → Prop)
    (hO_disj : ∀ u, GenPlaneMod qB wT u → ¬ O u) (hO_C : ∀ p, ¬ O (wC p)) :
    LocalKetOp (GenPlaneMod qB wT) O (portSwap1Circ M qB wC wT hbc hbt hct).eval.1 (portSwap1Bits M
    qB wC wT) := by
  refine ⟨portSwap1Circ_mulVec_ket M qB wC wT hbc hbt hct, fun β w hw ↦ ?_, fun β₁ β₂ hEq w hwW ↦
      ?_⟩
  · refine (Nat.recOn (motive := fun k ↦ ∀ hk : k ≤ M,
        portSwap1Bits k qB (fun p ↦ wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩)
          (fun p ↦ wT ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) β w = β w) M (fun _ ↦
              rfl) fun q ih hq ↦ ?_) le_rfl
    simp only [portSwap1Bits, Fin.val_castSucc, Fin.val_last, ih (Nat.le_of_succ_le hq),
      Function.update_of_ne (show w ≠ wT ⟨q, hq⟩ from fun e ↦ hw (Or.inr ⟨_, e⟩)),
      Function.update_of_ne (show w ≠ qB from fun e ↦ hw (Or.inl e))]
  · refine (Nat.recOn (motive := fun k ↦ ∀ (hk : k ≤ M) (u : Wire n), ¬ O u →
        portSwap1Bits k qB (fun p ↦ wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩)
          (fun p ↦ wT ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) β₁ u =
        portSwap1Bits k qB (fun p ↦ wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩)
          (fun p ↦ wT ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) β₂ u) M
      (fun _ u hu ↦ hEq u hu) fun q ih hq u hu ↦ ?_) le_rfl w (hO_disj w hwW)
    dsimp only [portSwap1Bits, Fin.val_castSucc, Fin.val_last]
    by_cases huS : u = wT ⟨q, hq⟩ <;> by_cases huB : u = qB <;>
      simp [huS, huB, hbt ⟨q, hq⟩, ih (Nat.le_of_succ_le hq) (wC ⟨q, hq⟩) (hO_C ⟨q, hq⟩),
        ih (Nat.le_of_succ_le hq) (wT ⟨q, hq⟩) (hO_disj _ (Or.inr ⟨⟨q, hq⟩, rfl⟩)),
        ih (Nat.le_of_succ_le hq) qB (hO_disj _ (Or.inl rfl)), ih (Nat.le_of_succ_le hq) u hu]
theorem genFanout1_localKetOp {M n : ℕ} (qS : Wire n) (wC wT : Fin M → Wire n)
    (hsc : ∀ p, qS ≠ wC p) (hst : ∀ p, qS ≠ wT p) (hct : ∀ p, wC p ≠ wT p) (O : Wire n → Prop)
    (hO_disj : ∀ u, GenPlaneMod qS wT u → ¬ O u) (hO_C : ∀ p, ¬ O (wC p)) :
    LocalKetOp (GenPlaneMod qS wT) O (specFanoutCopyCirc M qS wC wT hsc hst hct).eval.1 (fun β ↦
    if β qS = 0 then β else fanoutXorBits M wC wT β) := by
  refine ⟨fun β ↦ by simp only [ket_sr_eq, specFanoutCopyCirc_mulVec_ket], fun β w hw ↦ ?_,
      fun β₁ β₂ hEq w hwW ↦ ?_⟩
  · dsimp only
    split_ifs <;>
      first | rfl | exact fanoutXorBits_of_ne_tgt M wC wT β w fun p e ↦ hw (Or.inr ⟨p, e⟩)
  · have hrec2 (k : ℕ) : ∀ (hk : k ≤ M) (u : Wire n), ¬ O u →
        fanoutXorBits k (fun p ↦ wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩)
          (fun p ↦ wT ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) β₁ u =
        fanoutXorBits k (fun p ↦ wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩)
          (fun p ↦ wT ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) β₂ u :=
      Nat.recOn k (fun _ u hu ↦ hEq u hu) fun q ih hq u hu ↦ by
        dsimp only [fanoutXorBits, Fin.val_castSucc, Fin.val_last]
        rcases eq_or_ne u (wT ⟨q, hq⟩) with rfl | huS
        · simp only [Function.update_self, ih (Nat.le_of_succ_le hq) (wC ⟨q, hq⟩) (hO_C ⟨q, hq⟩),
            ih (Nat.le_of_succ_le hq) (wT ⟨q, hq⟩) (hO_disj _ (Or.inr ⟨⟨q, hq⟩, rfl⟩))]
        · simp only [Function.update_of_ne huS, ih (Nat.le_of_succ_le hq) u hu]
    dsimp only
    rw [hEq qS (hO_disj qS (Or.inl rfl))]
    split_ifs <;> first | exact hEq w (hO_disj w hwW) | exact hrec2 M le_rfl w (hO_disj w hwW)
theorem genUnextract1_localKetOp {M n : ℕ} (qB : Wire n)
    (wC wT : Fin M → Wire n) (hbc : ∀ p, qB ≠ wC p) (hbt : ∀ p, qB ≠ wT p)
    (hct : ∀ p, wC p ≠ wT p) (O : Wire n → Prop)
    (hO_disj : ∀ u, GenPlaneMod qB wT u → ¬ O u) (hO_C : ∀ p, ¬ O (wC p)) :
    LocalKetOp (GenPlaneMod qB wT) O
      (specPortUnextract1Unitary M qB wC wT hbc hbt hct).1
      (fun β ↦
        let η := if β qB = 0 then β else fanoutXorBits M wC wT β
        Function.update η qB (η qB + czFanoutPhase M wC wT η)) := by
  have opC := genFanout1_localKetOp qB wC wT hbc hbt hct O hO_disj hO_C
  refine ⟨fun β ↦ ?_, fun β w hw ↦ by
    simp only [Function.update_of_ne (show w ≠ qB from fun h ↦ hw (Or.inl h)), opC.2.1 β w hw],
    fun β₁ β₂ hEq w hwW ↦ ?_⟩
  · dsimp only [specPortUnextract1Unitary, Submonoid.coe_mul]
    rw [← Matrix.mulVec_mulVec, ket_sr_eq, ← ket_sr_eq (α := β), opC.1 β, ket_sr_eq,
      ← ket_dc_eq, bitToggleUnitary_mulVec_ket, ket_dc_eq, ket_sr_eq]
  · let fβ (β : BitAssignment n) := if β qB = 0 then β else fanoutXorBits M wC wT β
    have hEqη (u : Wire n) (hu : ¬ O u) : fβ β₁ u = fβ β₂ u := by
      by_cases huW : GenPlaneMod qB wT u
      · exact opC.2.2 β₁ β₂ hEq u huW
      · exact (opC.2.1 β₁ u huW).trans ((hEq u hu).trans (opC.2.1 β₂ u huW).symm)
    have hPh (K : ℕ) : ∀ hK : K ≤ M,
        czFanoutPhase K (fun p ↦ wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩)
          (fun p ↦ wT ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩) (fβ β₁) =
        czFanoutPhase K (fun p ↦ wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩)
          (fun p ↦ wT ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩) (fβ β₂) :=
      Nat.recOn K (fun _ ↦ rfl) fun q ih hq ↦ by
        dsimp only [czFanoutPhase, Fin.val_last, Fin.val_castSucc]
        rw [ih (Nat.le_of_succ_le hq), hEqη _ (hO_C ⟨q, hq⟩),
            hEqη _ (hO_disj _ (Or.inr ⟨⟨q, hq⟩, rfl⟩))]
    have hPhM := hPh M le_rfl
    simp only [Fin.eta] at hPhM
    dsimp only [fβ] at hEqη hPhM
    rcases eq_or_ne w qB with rfl | hwB
    · simp only [Function.update_self, hEqη _ (hO_disj _ hwW), hPhM]
    · simp only [Function.update_of_ne hwB, hEqη _ (hO_disj _ hwW)]
/--
`RouterReg`-free 24-plane `bellXHalfVecDyn` step cancelling `C_vec * S_vec * R₀ ──▶ R₀`
in `0 T` for any target count `M` (including `M = 47 + 187 = 234`).
-/
theorem subspaceStep_bellXHalfVec_general {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} (v : Var)
    (qB : Fin 24 → Wire n) (wC : Fin M → Wire n) (wT : Fin 24 → Fin M → Wire n)
    (hwT_inj : ∀ k : Fin 24, Function.Injective (wT k))
    (hB_inj : ∀ k₁ k₂ : Fin 24, k₁ ≠ k₂ → qB k₁ ≠ qB k₂)
    (hbc : ∀ k p, qB k ≠ wC p)
    (hbt_all : ∀ k₁ k₂ p, qB k₁ ≠ wT k₂ p)
    (hc_disj : ∀ k p q, wC p ≠ wT k q)
    (ht_disj : ∀ k₁ k₂ : Fin 24, k₁ ≠ k₂ → ∀ p q : Fin M, wT k₁ p ≠ wT k₂ q)
    (R₀ : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ AtMostOneCtrl wC δ ∧ ∀ k : Fin 24, δ (qB k) = 0) R₀) :
    SubspaceStep (Var := Var)
      ((specFanoutCopyVecCirc M 24 qB wC wT
          hbc (fun k ↦ hbt_all k k) (fun k p ↦ hc_disj k p p)).eval.1 *
        ((portSwapVecCirc M 24 qB wC wT
          hbc (fun k ↦ hbt_all k k) (fun k p ↦ hc_disj k p p)).eval.1 * R₀))
      R₀
      (bellXHalfVecDyn v M 24 qB wC wT (fun k p ↦ hc_disj k p p)) := by
  let s1 (j : Fin 24) :=
      portSwap1Circ M (qB j) wC (wT j) (hbc j) (hbt_all j j) (fun p ↦ hc_disj j p p)
  let u1 (j : Fin 24) :=
      specPortUnextract1Unitary M (qB j) wC (wT j) (hbc j) (hbt_all j j) (fun p ↦ hc_disj j p p)
  let psv (m : ℕ) (hm : m ≤ 24) :=
      portSwapVecCirc M m (fun i ↦ qB ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) wC
    (fun i p ↦ wT ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ p) (fun _ ↦ hbc _) (fun _ ↦ hbt_all _ _)
        (fun _ p ↦ hc_disj _ p p)
  have hModDisj {j₁ j₂ : Fin 24} (hne : j₁ ≠ j₂) (u : Wire n) :
      GenPlaneMod (qB j₁) (wT j₁) u → GenPlaneMod (qB j₂) (wT j₂) u → False := by
    rintro (rfl | ⟨p₁, rfl⟩) (heq | ⟨p₂, heq⟩)
    exacts [hB_inj j₁ j₂ hne heq, hbt_all j₁ j₂ p₂ heq, hbt_all j₂ j₁ p₁ heq.symm,
        ht_disj j₁ j₂ hne p₁ p₂ heq]
  have hC_notMod (j : Fin 24) (p : Fin M) : ¬ GenPlaneMod (qB j) (wT j) (wC p) :=
    fun h ↦ h.elim (fun e ↦ hbc j p e.symm) (fun ⟨q, e⟩ ↦ hc_disj j p q e)
  let Pinv (Q : Fin 24 → Prop) (δ : BitAssignment n) : Prop :=
      AtMostOneCtrl wC δ ∧ ∀ k : Fin 24, Q k → δ (qB k) = 0
  have opS0 (j : Fin 24) := genSwap1_localKetOp (qB j) wC (wT j) (hbc j) (hbt_all j j)
    (fun p ↦ hc_disj j p p) (fun _ ↦ False) (fun _ _ h ↦ h) (fun _ h ↦ h)
  have hS1Keep (j : Fin 24) {Q : Fin 24 → Prop} (hnj : ¬ Q j) (δ : BitAssignment n)
      (hP : Pinv Q δ) :
      PreservesKetPred (Pinv Q) ((s1 j).eval.1.mulVec (ket δ)) := by
    obtain ⟨h1, hq⟩ := hP
    dsimp only [s1]
    rw [portSwap1Circ_mulVec_ket, ket_sr_eq]
    have hC (p : Fin M) := (opS0 j).2.1 δ _ (hC_notMod j p)
    exact preservesKetPred_ket ⟨h1.imp (fun hz p ↦ (hC p).trans (hz p))
        (fun ⟨p₀, hp1, hp0⟩ ↦ ⟨p₀, (hC p₀).trans hp1, fun p hp ↦ (hC p).trans (hp0 p hp)⟩),
      fun k hk ↦
          ((opS0 j).2.1 δ (qB k) fun hm ↦ hModDisj (fun e : j = k ↦
          hnj (e ▸ hk)) _ hm (Or.inl rfl)).trans (hq k hk)⟩
  have hPreS (q : ℕ) : ∀ (hq : q ≤ 24) (jq : Fin 24), q ≤ jq.val →
      ∀ {δ : BitAssignment n}, AtMostOneCtrl wC δ → (∀ k : Fin 24, δ (qB k) = 0) →
      PreservesKetPred (Pinv (· = jq)) ((psv q hq).eval.1.mulVec (ket δ)) :=
    Nat.recOn q
      (fun _ jq _ _ h1 hq0 ↦ by
        simp only [psv, portSwapVecCirc, Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mulVec]
        exact preservesKetPred_ket ⟨h1, fun _ hk ↦ hk ▸ hq0 jq⟩)
      fun q' ih hq jq hle _ h1 hq0 ↦ by
        dsimp only [psv, portSwapVecCirc, Fin.val_last, Fin.val_castSucc]
        rw [eval_seq_mulVec]
        exact preservesKetPred_mulVec_of_ket (hS1Keep ⟨q', hq⟩ (Q := (· = jq))
            (fun e ↦ Nat.ne_of_lt hle (congrArg Fin.val e)))
          (ih (Nat.le_of_succ_le hq) jq (Nat.le_of_succ_le hle) h1 hq0)
  have hCancelStep (q : ℕ) (hq : q < 24) {δ : BitAssignment n} (h1 : AtMostOneCtrl wC δ)
      (hq0 : ∀ k : Fin 24, δ (qB k) = 0) :=
    (hPreS q (Nat.le_of_succ_le hq) ⟨q, hq⟩ le_rfl h1 hq0)
        ((u1 ⟨q, hq⟩).1 * (s1 ⟨q, hq⟩).eval.1) 1 fun α ⟨h1α, h0α⟩ ↦ by
      simpa only [← Matrix.mulVec_mulVec,
          Matrix.one_mulVec] using genUnextract1_portSwap1_ket (qB ⟨q, hq⟩) wC (wT ⟨q, hq⟩)
        (hwT_inj ⟨q, hq⟩) (hbc ⟨q, hq⟩) (hbt_all ⟨q, hq⟩ ⟨q, hq⟩)
            (hc_disj ⟨q, hq⟩) h1α (h0α ⟨q, hq⟩ rfl)
  have hCleanUk (k₀ : Fin 24) (m : ℕ) : ∀ (hm : m ≤ 24), k₀.val < m →
      ∀ {δ : BitAssignment n}, AtMostOneCtrl wC δ → (∀ k : Fin 24, δ (qB k) = 0) →
      PreservesKetPred (fun η ↦ η (qB k₀) = 0) ((u1 k₀).1.mulVec ((psv m hm).eval.1.mulVec (ket δ)))
          :=
    Nat.recOn m (fun _ hk₀ _ _ _ ↦ absurd hk₀ (Nat.not_lt_zero _)) fun q ih hq hk₀ _ h1 hq0 ↦ by
      let jq : Fin 24 := ⟨q, hq⟩
      dsimp only [psv, portSwapVecCirc, Fin.val_last, Fin.val_castSucc]
      rw [eval_seq_mulVec]
      rcases eq_or_ne jq k₀ with rfl | hEq
      · rw [Matrix.mulVec_mulVec, hCancelStep q hq h1 hq0, Matrix.one_mulVec]
        exact preservesKetPred_mono (fun _ h ↦ h.2 jq rfl)
            (hPreS q (Nat.le_of_succ_le hq) jq le_rfl h1 hq0)
      · rw [Matrix.mulVec_mulVec, localKetOp_comm (hModDisj (Ne.symm hEq))
          (genUnextract1_localKetOp (qB k₀) wC (wT k₀) (hbc k₀) (hbt_all k₀ k₀)
            (fun p ↦ hc_disj k₀ p p) _ (hModDisj (Ne.symm hEq)) (hC_notMod jq))
          (genSwap1_localKetOp (qB jq) wC (wT jq) (hbc jq) (hbt_all jq jq)
            (fun p ↦ hc_disj jq p p) _ (hModDisj hEq) (hC_notMod k₀)), ← Matrix.mulVec_mulVec]
        refine preservesKetPred_mulVec_of_ket (fun α hα ↦ ?_) (ih (Nat.le_of_succ_le hq)
          (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk₀) (Fin.val_ne_of_ne hEq).symm) h1 hq0)
        simp only [portSwap1Circ_mulVec_ket, ket_sr_eq]
        exact preservesKetPred_ket (((opS0 jq).2.1 α (qB k₀) fun hm ↦
            hModDisj hEq _ hm (Or.inl rfl)).trans hα)
  have hCancelVec (m : ℕ) : ∀ (hm : m ≤ 24) {δ : BitAssignment n},
      AtMostOneCtrl wC δ → (∀ k : Fin 24, δ (qB k) = 0) →
      ((specPortUnextractVecUnitary M m (fun i ↦ qB ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) wC
        (fun i p ↦ wT ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ p)
        (fun _ ↦ hbc _) (fun _ ↦ hbt_all _ _) (fun _ p ↦ hc_disj _ p p)).1 *
            (psv m hm).eval.1).mulVec (ket δ) = ket δ :=
    Nat.recOn m
      (fun _ _ _ _ ↦ by
        simp only [psv, specPortUnextractVecUnitary, portSwapVecCirc, Circuit.eval_identity,
          Submonoid.coe_one, one_mul, Matrix.one_mulVec])
      fun q ih hq _ h1 hq0 ↦ by
        have hCL := hCancelStep q hq h1 hq0
        dsimp only [psv, specPortUnextractVecUnitary, portSwapVecCirc, Fin.val_last,
            Fin.val_castSucc]
        simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at hCL ⊢
        rw [hCL]
        simpa only [Matrix.one_mulVec,
            ← Matrix.mulVec_mulVec] using ih (Nat.le_of_succ_le hq) h1 hq0
  let SV :=
      (portSwapVecCirc M 24 qB wC wT hbc (fun k ↦ hbt_all k k) (fun k p ↦ hc_disj k p p)).eval.1
  refine subspaceStep_congr_out
    (subspaceStep_bellXHalfVec v M 24 qB wC wT hB_inj hbc hbt_all hc_disj ht_disj (SV * R₀) fun k ↦
        by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact hSupp _ _ fun δ ⟨h1, hq0⟩ ↦ by
        simpa only [SV, psv, ← Matrix.mulVec_mulVec, Fin.eta, Matrix.one_mulVec] using
          (hCleanUk k 24 le_rfl k.isLt h1 hq0)
              ((QRegister.singleton (qB k)).basisOutcomeProjector 0) 1
            fun η hη ↦ by rw [ket_projector_zero, itePos hη, Matrix.one_mulVec]) ?_
  rw [← Matrix.mul_assoc]
  exact (hSupp _ 1 fun δ ⟨h1, hq0⟩ ↦ by
    rw [Matrix.one_mulVec]
    simpa only [psv, Fin.eta] using hCancelVec 24 le_rfl h1 hq0).trans (Matrix.one_mul R₀)
/-! ## Block 3D: `HCNOTSupportedIn` Disjoint Commutation & Predicate-Preservation Gadget -/

inductive HCNOTSupportedIn {n : ℕ} (S : Wire n → Prop) : Circuit n → Prop
  | id : HCNOTSupportedIn S .identity
  | seq {c₁ c₂ : Circuit n} : HCNOTSupportedIn S c₁ → HCNOTSupportedIn S c₂ →
      HCNOTSupportedIn S (c₁ ;;ᶜ c₂)
  | h {q : Wire n} : S q → HCNOTSupportedIn S (Circuit.H q)
  | cnot {c t : Wire n} (hct : c ≠ t) : S c → S t → HCNOTSupportedIn S (Circuit.CNOT c t hct)
theorem HCNOTSupportedIn.toCircSupportedIn {n : ℕ} {S : Wire n → Prop} {c : Circuit n}
    (hc : HCNOTSupportedIn S c) : CircSupportedIn S c := by
  induction hc with
  | id => exact circSupportedIn_id
  | seq _ _ ih₁ ih₂ => exact circSupportedIn_seq ih₁ ih₂
  | h hq => exact circSupportedIn_H hq
  | cnot hct hc0 ht0 => exact circSupportedIn_CNOT hct hc0 ht0
theorem HCNOTSupportedIn.comm_H {n : ℕ} {S : Wire n → Prop} {c : Circuit n}
    (hc : HCNOTSupportedIn S c) {q : Wire n} (hq : ¬ S q) : c.eval.1 * (Circuit.H q).eval.1 =
    (Circuit.H q).eval.1 * c.eval.1 := by
  induction hc with
  | id => simp [Circuit.eval_identity]
  | seq _ _ ih₁ ih₂ =>
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁, ← Matrix.mul_assoc, ih₂, Matrix.mul_assoc]
  | h hq' => exact comm_H_ne fun e ↦ hq (e ▸ hq')
  | cnot hct hc0 ht0 => exact comm_cnot_H_disj hct (fun e ↦ hq (e ▸ hc0)) (fun e ↦ hq (e ▸ ht0))
theorem HCNOTSupportedIn.comm {n : ℕ} {S₁ S₂ : Wire n → Prop} {c₁ c₂ : Circuit n}
    (h₁ : HCNOTSupportedIn S₁ c₁) (h₂ : HCNOTSupportedIn S₂ c₂) (hDisj : ∀ w, S₁ w → ¬ S₂ w) :
    c₁.eval.1 * c₂.eval.1 = c₂.eval.1 * c₁.eval.1 := by
  induction h₂ with
  | id => simp [Circuit.eval_identity]
  | seq _ _ ih₁ ih₂ =>
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [← Matrix.mul_assoc, ih₂, Matrix.mul_assoc, ih₁, ← Matrix.mul_assoc]
  | h hq => exact h₁.comm_H fun hs₁ ↦ hDisj _ hs₁ hq
  | cnot hct hc0 ht0 =>
        exact h₁.toCircSupportedIn (Circuit.CNOT _ _ hct).eval (actsIndepOf_cnot_disj hct (fun hs₁ ↦
        hDisj _ hs₁ hc0) (fun hs₁ ↦ hDisj _ hs₁ ht0))
theorem HCNOTSupportedIn.preservesKetPred {n : ℕ} {S : Wire n → Prop} {c : Circuit n}
    (hc : HCNOTSupportedIn S c) {P : BitAssignment n → Prop} (hKeep : ∀ {u : Wire n}, S u → ∀ α v,
    P α → P (Function.update α u v)) {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P (c.eval.1.mulVec ψ) := by
  induction hc generalizing ψ with
  | id => simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec] using hψ
  | seq _ _ ih₁ ih₂ => exact eval_seq_mulVec _ _ ψ ▸ ih₂ (ih₁ hψ)
  | h hq => exact preservesKetPred_H (hKeep hq) hψ
  | cnot hct _ ht => exact preservesKetPred_CNOT hct (hKeep ht) hψ
theorem hcnotSupportedIn_fixedSwapVec {M n : ℕ} {S : Wire n → Prop} (cVec : Fin M → ZMod 2) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wT : Fin m → Fin M → Wire n) (hbt : ∀ k p, qB k ≠ wT k p),
    (∀ k, S (qB k)) → (∀ k p, cVec p = 1 → S (wT k p)) →
    HCNOTSupportedIn S (fixedSwapVecCirc M m qB cVec wT hbt) := by
  exact fun m ↦ Nat.recOn m (fun _ _ _ _ _ ↦ .id) fun _ ih _ _ _ hq hw ↦
    .seq (ih _ _ _ (fun k ↦ hq k.castSucc) (fun k ↦ hw k.castSucc)) <|
      (Nat.recOn (motive := fun K ↦ ∀ (qb : Wire n) (cV : Fin K → ZMod 2) (wt : Fin K → Wire n)
          (hb : ∀ p, qb ≠ wt p), S qb → (∀ p, cV p = 1 → S (wt p)) →
              HCNOTSupportedIn S (fixedSwap1Circ K qb cV wt hb))
        M (fun _ _ _ _ _ _ ↦ .id) fun _ ih1 _ _ _ _ hq0 hw0 ↦
            .seq (ih1 _ _ _ _ hq0 fun p ↦ hw0 p.castSucc)
          (by split_ifs with hc <;> first | exact .id |
            exact .seq (.cnot _ hq0 (hw0 _ hc)) (.seq (.cnot _ (hw0 _ hc) hq0)
                (.cnot _ hq0 (hw0 _ hc)))))
        _ cVec _ _ (hq _) (hw _)
theorem hcnotSupportedIn_fixedBellVec {M n : ℕ} {S : Wire n → Prop} (cVec : Fin M → ZMod 2) :
    ∀ (m : ℕ) (qH : Fin m → Wire n) (wT : Fin m → Fin M → Wire n) (hht : ∀ k p, qH k ≠ wT k p),
      (∀ k, S (qH k)) → (∀ k p, cVec p = 1 → S (wT k p)) →
          HCNOTSupportedIn S (fixedBellVecCirc M m qH cVec wT hht)
  | 0, _, _, _, _, _ => .id
  | m + 1, _, _, _, hq, hw =>
      .seq (hcnotSupportedIn_fixedBellVec cVec m _ _ _ (fun k ↦ hq k.castSucc)
          (fun k ↦ hw k.castSucc)) (.seq (.h (hq _)) <|
        (Nat.recOn (motive := fun K ↦ ∀ (qh : Wire n) (cV : Fin K → ZMod 2) (wt : Fin K → Wire n)
            (hh : ∀ p, qh ≠ wt p), S qh → (∀ p, cV p = 1 → S (wt p)) →
                HCNOTSupportedIn S (fixedFanoutCirc K qh cV wt hh))
          M (fun _ _ _ _ _ _ ↦ .id) fun _ ih1 _ _ _ _ hq0 hw0 ↦
              .seq (ih1 _ _ _ _ hq0 fun p ↦ hw0 p.castSucc)
            (by split_ifs with hc <;> first | exact .cnot _ hq0 (hw0 _ hc) | exact .id)) _ cVec _ _
                (hq _) (hw _))
theorem hcnotSupportedIn_cFixedPort {M n : ℕ} {S : Wire n → Prop} (qB qH : Fin 24 → Wire n)
    (cVec : Fin M → ZMod 2) (wT : Fin 24 → Fin M → Wire n) (hbt : ∀ b p, qB b ≠ wT b p)
    (hht : ∀ b p, qH b ≠ wT b p) (hqB : ∀ b, S (qB b)) (hqH : ∀ b, S (qH b))
    (hwT : ∀ b p, cVec p = 1 → S (wT b p)) :
    HCNOTSupportedIn S (cFixedPortCirc qB qH cVec wT hbt hht) :=
  .seq (hcnotSupportedIn_fixedSwapVec cVec 24 qB wT hbt hqB hwT)
      (hcnotSupportedIn_fixedBellVec cVec 24 qH wT hht hqH hwT)
/-! ## Block 3F: `SharedPortBWiring`, `uSharedHiConj`, & `sharedPortB_stage5_input_factor` -/

/--
Wire-disjointness bundle for `(rN, rE, cHiN)` used by `uSharedHiConj` and
`pSharedPortBStage5Unload`.
-/
structure SharedPortBWiring {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) : Prop where
  cHiN_inj : ∀ p q : Fin 47, p ≠ q → cHiN p ≠ cHiN q
  rawN_ne_cHiN : ∀ p : Fin 47, rRawHas2 rN ≠ cHiN p
  idx2N_ne_cHiN : ∀ (d : Fin 6) (p : Fin 47), rIdx2 rN d ≠ cHiN p
  cHiN_ne_ctrlE : ∀ (p : Fin 47) (q : Fin 187), cHiN p ≠ rCtrlLo rE q
  cHiN_ne_ctrlN : ∀ p q : Fin 47, cHiN p ≠ rCtrlLo rN q
  cHiN_notModN : ∀ p : Fin 47, ¬ AllPlaneMod rN (cHiN p)
  cHiN_notModE : ∀ p : Fin 47, ¬ AllPlaneMod rE (cHiN p)
  cHiN_notHdrE : ∀ p : Fin 47, ¬ RouterCtrlSet rE (cHiN p)
  pubN_ne_pubE : ∀ {i : Fin (routerWidth 47 6)}, i.val < 1238 →
    ∀ {j : Fin (routerWidth 187 8)}, j.val < 4602 → rN i ≠ rE j
  rN_disj_rE_mod : ∀ (i : Fin (routerWidth 47 6)) (u : Wire n), AllPlaneMod rE u → rN i ≠ u
  ctrlN_disj_rE_hdr : ∀ (p : Fin 47) (u : Wire n), RouterCtrlSet rE u → rCtrlLo rN p ≠ u
  ctrlE_ne_sysN : ∀ (q : Fin 187) (p : Fin 47) (b : Fin 24), rCtrlLo rE q ≠ rSys rN p b
  ctrlE_disj_rN_hdr : ∀ (q : Fin 187) (u : Wire n), RouterCtrlSet rN u → rCtrlLo rE q ≠ u
end QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld

namespace QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Sub5885MuxD1
open PhotochemistrySolution.ProviderCoreFused
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB (rClean690Layout
    val_rClean690Layout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
  (val_wPotIsNN_rPot0Layout val_rBufHi_rElecLayout val_rBufHi_rNucLayout val_rNucLayout_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (val_rElecLayout_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (rCoinExt val_rCoinExt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB (portB_reg_links)
/- ## Section 1: Exact `rHB` Indices on `dLayout` & `714`-Wire Extended Clean Pool -/

theorem hDLayout_eq_7298 : dLayout = 7298 := by
  dsimp [dLayout, SelectCompactAnc.totDimCompactGen, ancWOfScr, scrWLayout]; rw [hSys5616_fused]
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
theorem rw_nuc_hb_lt (b : Fin 24) : 86 + b.val < routerWidth 47 6 := by
  have _ := b.isLt; unfold routerWidth; omega
theorem val_rHB_rNucLayout (b : Fin 24) : (rHB rNucLayout b).val = 5827 + b.val := by
  have _ := b.isLt
  rw [show rHB rNucLayout b = nucRouterWireFn ⟨86 + b.val,
      rw_nuc_hb_lt b⟩ from congrArg rNucLayout.wires (Fin.ext rfl),
    val_nucRouterWireFn]
  dsimp only
  split_ifs <;> omega
theorem clean714_sub24_lt (q : Fin 714) : q.val - 24 < 690 := by omega
/-- `714`-wire clean pool (`rHB rNucLayout` at `0..23`, `rClean690Layout` at `24..713`). -/
def clean714LayoutWireFn (q : Fin 714) : Wire dLayout :=
    if h : q.val < 24 then rHB rNucLayout ⟨q.val, h⟩ else rClean690Layout ⟨q.val - 24,
    clean714_sub24_lt q⟩
theorem val_clean714LayoutWireFn (q : Fin 714) : (clean714LayoutWireFn q).val = if q.val <
    24 then 5827 + q.val else if q.val < 57 then 5680 + (q.val - 24) else 5947 + (q.val - 57) := by
  have _ := q.isLt
  by_cases h24 : q.val < 24
  · simpa only [clean714LayoutWireFn, dite_eq_left h24, ite_eq_left h24] using
      val_rHB_rNucLayout ⟨q.val, h24⟩
  · rw [clean714LayoutWireFn, dite_eq_right h24, ite_eq_right h24, val_rClean690Layout]
    dsimp only; split_ifs <;> omega
theorem clean714LayoutWireFn_inj : Function.Injective clean714LayoutWireFn := fun a b h ↦ by
  have _ := a.isLt; have _ := b.isLt;
  have hv := congrArg Fin.val h; rw [val_clean714LayoutWireFn, val_clean714LayoutWireFn] at hv
  split_ifs at hv <;> exact Fin.ext (by omega)
/-- `714`-wire clean Stage-4 ancilla register on `dLayout` (`rHB rNucLayout ++ rClean690Layout`). -/
def rClean714Layout : QRegister 714 dLayout := ⟨⟨clean714LayoutWireFn, clean714LayoutWireFn_inj⟩⟩
theorem rClean714Layout_apply (q : Fin 714) : rClean714Layout q = clean714LayoutWireFn q := rfl
theorem val_rClean714Layout (q : Fin 714) : (rClean714Layout q).val = if q.val < 24 then 5827 +
    q.val else if q.val < 57 then 5680 +
    (q.val - 24) else 5947 + (q.val - 57) := val_clean714LayoutWireFn q
/- ## Section 2: `rPotZeroNEremPortB151` (`122 + Wp` Wires, `Wp ≤ 738`, `151 + Wp ≤ wWork`) -/

theorem cond_blt_eq_ite {α : Type} (a b : ℕ) (t f : α) : cond (Nat.blt a b) t f = if a <
    b then t else f := by
  by_cases h : a < b
  · rw [Nat.blt_eq.mpr h, Bool.cond_true, ite_eq_left h]
  · rw [Bool.eq_false_iff.mpr (fun ht ↦ h (Nat.blt_eq.mp ht)), Bool.cond_false, ite_eq_right h]
theorem portB151_clean714_lt {Wp : ℕ} (hWp : Wp ≤ 738) (j : Fin (122 + Wp)) :
    j.val - 146 < 714 := by omega
theorem portB24_le_714 : (24 : ℕ) ≤ 714 := by omega
/-- Pure `Bool` index formula for `rPotZeroNEremPortB151` (zero inline proof subterms). -/
def potZeroNEremPortB151Val (j : ℕ) : ℕ :=
    cond (Nat.blt j 1) 7297 (cond (Nat.blt j 33) (5746 + j) (cond (Nat.blt j 81) (5851 + (j - 33))
    (cond (Nat.blt j 122) (7256 + (j - 81)) (cond (Nat.blt j 146) (5779 + (j - 122))
    (cond (Nat.blt j 170) (5827 + (j - 146)) (cond (Nat.blt j 203) (5680 + (j - 170))
    (5947 + (j - 203))))))))
theorem potZeroNEremPortB151Val_lt {Wp : ℕ} (hWp : Wp ≤ 738) (j : Fin (122 + Wp)) :
    potZeroNEremPortB151Val j.val < dLayout := by
  have _ :=
      j.isLt; rw [hDLayout_eq_7298]; unfold potZeroNEremPortB151Val; simp only [cond_blt_eq_ite]
  split_ifs <;> omega
/--
3-port Stage-4 wire map (`122 + Wp` wires, `Wp ≤ 738` ) routing `j = 146..169` via `rHB rNucLayout`
.
-/
def potZeroNEremPortB151WireFn (Wp : ℕ) (hWp : Wp ≤ 738) (j : Fin (122 + Wp)) : Wire dLayout :=
    ⟨potZeroNEremPortB151Val j.val, potZeroNEremPortB151Val_lt hWp j⟩
theorem val_potZeroNEremPortB151WireFn {Wp : ℕ} (hWp : Wp ≤ 738) (j : Fin (122 + Wp)) :
    (potZeroNEremPortB151WireFn Wp hWp j).val = if j.val = 0 then 7297 else if j.val <
    33 then 5746 + j.val else if j.val < 81 then 5851 + (j.val - 33) else if j.val < 122 then 7256 +
    (j.val - 81) else if j.val < 146 then 5779 + (j.val - 122) else if j.val < 170 then 5827 +
    (j.val - 146) else if j.val < 203 then 5680 + (j.val - 170) else 5947 + (j.val - 203) := by
  have _ :=
      j.isLt; change potZeroNEremPortB151Val j.val =
      _; unfold potZeroNEremPortB151Val; simp only [cond_blt_eq_ite]
  split_ifs <;> omega
theorem potZeroNEremPortB151WireFn_eq_split {Wp : ℕ} (hWp : Wp ≤ 738) (j : Fin (122 + Wp)) :
    potZeroNEremPortB151WireFn Wp hWp j = if h : j.val <
    146 then potZeroNEremPortBWireFn 24 portB24_le_714 ⟨j.val, h⟩ else rClean714Layout ⟨j.val - 146,
    portB151_clean714_lt hWp j⟩ := by
  have _ := j.isLt
  refine Fin.ext ?_
  rw [val_potZeroNEremPortB151WireFn hWp j]
  if h146 : j.val < 146 then
    rw [dite_eq_left h146, val_potZeroNEremPortBWireFn portB24_le_714 ⟨j.val, h146⟩];
        dsimp only; split_ifs <;> omega
  else
    rw [dite_eq_right h146, val_rClean714Layout ⟨j.val - 146, portB151_clean714_lt hWp j⟩];
        dsimp only; split_ifs <;> omega
/-- Linear left inverse of `(potZeroNEremPortB151WireFn Wp hWp ·).val`. -/
def invPotZeroNEremPortB151 (w : ℕ) : ℕ :=
    if w = 7297 then 0 else if w < 5715 then 170 + (w - 5680) else if w < 5779 then w -
    5746 else if w < 5810 then 122 + (w - 5779) else if w < 5851 then 146 + (w - 5827) else if w <
    5910 then 33 + (w - 5851) else if w < 7000 then 203 + (w - 5947) else 81 + (w - 7256)
theorem invPotZeroNEremPortB151_val {Wp : ℕ} (hWp : Wp ≤ 738) (j : Fin (122 + Wp)) :
    invPotZeroNEremPortB151 (potZeroNEremPortB151WireFn Wp hWp j).val = j.val := by
  have _ := j.isLt; have hw := val_potZeroNEremPortB151WireFn hWp j
  split_ifs at hw <;> · rw [hw]; dsimp only [invPotZeroNEremPortB151]; split_ifs <;> omega
theorem rPotZeroNEremPortB151_inj {Wp : ℕ}
    (hWp : Wp ≤ 738) : Function.Injective (potZeroNEremPortB151WireFn Wp hWp) :=
  fun a b h ↦
      Fin.ext (by rw [← invPotZeroNEremPortB151_val hWp a, ← invPotZeroNEremPortB151_val hWp b, h])
/-- `(122 + Wp)`-wire 3-port Stage-4 register on `dLayout` (`Wp ≤ 738`, `151 + Wp ≤ wWork`). -/
def rPotZeroNEremPortB151 (Wp : ℕ) (hWp : Wp ≤ 738) : QRegister (122 + Wp) dLayout :=
    ⟨⟨potZeroNEremPortB151WireFn Wp hWp, rPotZeroNEremPortB151_inj hWp⟩⟩
theorem maxWp24_le_738 {Wp : ℕ} (hWp : Wp ≤ 738) : max Wp 24 ≤ 738 := by omega
theorem portB151_reg_links {Wp n : ℕ} (hWp : Wp ≤ 738) (rTot : QRegister dLayout n) :
    let hMax := maxWp24_le_738 hWp; let r := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) hMax)
    (r ⟨4, by omega⟩ = rTot (wPotIsNN rPot0Layout)) ∧ (∀ b : Fin 24, r ⟨57 + b.val, by omega⟩ =
        rTot (rBufHi rElecLayout b)) ∧
    (∀ b : Fin 24, r ⟨122 + b.val, by omega⟩ = rTot (rBufHi rNucLayout b)) ∧
    (∀ (u : Fin (max Wp 24)) (hu : 24 ≤ u.val), r ⟨122 + u.val, by omega⟩ =
        (rTot.compose rClean714Layout) ⟨u.val - 24,
      by omega⟩) := by
  intro hMax r
  have h0 := portB_reg_links (Wp := 0) (by omega) rTot
  have hLow : ∀ (c : ℕ) (hc : c < 146), r ⟨c, by omega⟩ =
      (rTot.compose (rPotZeroNEremPortB (max 0 24) (by omega))) ⟨c, by omega⟩ :=
    fun c hc ↦
        congrArg rTot.wires ((potZeroNEremPortB151WireFn_eq_split hMax ⟨c,
        by omega⟩).trans (dite_eq_left hc))
  refine ⟨(hLow 4 (by omega)).trans h0.1, fun b ↦ (hLow (57 + b.val) (by omega)).trans (h0.2.1 b),
    fun b ↦ (hLow (122 + b.val) (by omega)).trans (h0.2.2.1 b), fun u hu ↦ congrArg rTot.wires ?_⟩
  exact (potZeroNEremPortB151WireFn_eq_split hMax ⟨122 + u.val, by omega⟩).trans
    ((dite_eq_right (show ¬ 122 + u.val <
        146
        by omega)).trans (congrArg rClean714Layout
             (Fin.ext (by dsimp only [Fin.val_mk]; omega))))
/- ## Section 3: Compact `47`-Wire `Hi_N` Scratch Bank `cHiNSub341` (`341 ≤ wWork`) -/

def cHiNSub341Val (p : Fin 47) : ℕ := cond (Nat.blt p.val 12) (5680 + p.val) (6021 + (p.val - 12))
theorem cHiNSub341_val_lt (p : Fin 47) : cHiNSub341Val p < dLayout := by
  have _ := p.isLt
  rw [hDLayout_eq_7298,
    show cHiNSub341Val p = if p.val < 12 then 5680 + p.val else 6021 +
        (p.val - 12) from cond_blt_eq_ite p.val 12 _ _]
  split_ifs <;> omega
/-- `47`-wire `Hi_N` unary scratch bank `[5680..5691] ∪ [6021..6055]` (`341 ≤ wWork`). -/
def cHiNSub341 (p : Fin 47) : Wire dLayout := ⟨cHiNSub341Val p, cHiNSub341_val_lt p⟩
theorem val_cHiNSub341 (p : Fin 47) : (cHiNSub341 p).val = if p.val < 12 then 5680 +
    p.val else 6021 +
    (p.val - 12) := cond_blt_eq_ite p.val 12 _ _
theorem cHiNSub341_inj : Function.Injective cHiNSub341 := fun a b h ↦ by
  have _ := a.isLt; have _ := b.isLt;
  have hv := congrArg Fin.val h; rw [val_cHiNSub341, val_cHiNSub341] at hv
  split_ifs at hv <;> exact Fin.ext (by omega)
theorem cHiNSub341_ne {n : ℕ} (rTot : QRegister dLayout n) (p q : Fin 47)
    (hne : p ≠ q) : rTot (cHiNSub341 p) ≠ rTot (cHiNSub341 q) := fun e ↦
    hne (cHiNSub341_inj (rTot.wires.injective e))
theorem cHiNSub341_disj_rCoinExt {kExt : ℕ} (hk : kExt ≤ 72) (p : Fin 47) (j : Fin kExt)
    : cHiNSub341 p ≠ rCoinExt kExt hk j := fun e ↦ by
  have _ := p.isLt; have _ := j.isLt;
  have hv := congrArg Fin.val e; rw [val_cHiNSub341, val_rCoinExt] at hv
  split_ifs at hv <;> omega
theorem cHiNSub341_scrIdx_lt (p : Fin 47) : (if p.val < 12 then 30 + p.val else 371 +
    (p.val - 12)) < scrLLayout := by have _ := p.isLt; dsimp [scrLLayout]; split_ifs <;> omega
theorem cHiNSub341_isScrLayout (p : Fin 47) : ∃ m : Fin scrLLayout, (m.val < 65 ∨ 105 ≤ m.val) ∧
    cHiNSub341 p = rScrLayout m := by
  have _ := p.isLt
  refine ⟨⟨if p.val < 12 then 30 + p.val else 371 + (p.val - 12), cHiNSub341_scrIdx_lt p⟩,
      by dsimp only; split_ifs <;> omega,
    Fin.ext ?_⟩
  rw [val_cHiNSub341, val_rScrLayout]
  dsimp only; split_ifs <;> omega
theorem cHiNSub341_ne_rCtrlLo_rNucSub (p q : Fin 47) :
    cHiNSub341 p ≠ rCtrlLo rNucSub q := fun e ↦ by
  have :=
      (⟨p.isLt, q.isLt, show 12 ≤ privRank156Sub (18 + q.val) ∧ privRank156Sub (18 + q.val) < 59 by
    unfold privRank156Sub; split_ifs <;> omega⟩ : _ ∧ _ ∧ _)
  have hv := congrArg Fin.val e
  rw [val_cHiNSub341, show (rCtrlLo rNucSub q).val = _ from
    val_nucSubWireFn ⟨basePub 47 6 + 6 + 2 * 6 + q.val, rw_ltCtrlLo q⟩] at hv
  dsimp only [basePub] at hv
  rw [show 1256 + q.val - 1238 = 18 + q.val by omega] at hv; split_ifs at hv <;> omega
theorem cHiNSub341_ne_rCtrlLo_rElecSub (p : Fin 47) (q : Fin 187) :
    cHiNSub341 p ≠ rCtrlLo rElecSub q := fun e ↦ by
  have :=
      (⟨p.isLt, q.isLt, show 16 ≤ privRank454Sub (22 + q.val) ∧ privRank454Sub (22 + q.val) < 203 by
    unfold privRank454Sub; split_ifs <;> omega⟩ : _ ∧ _ ∧ _)
  have hv := congrArg Fin.val e
  rw [val_cHiNSub341, show (rCtrlLo rElecSub q).val = _ from
    val_elecSubWireFn ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩] at hv
  dsimp only [basePub] at hv
  rw [show 4624 + q.val - 4602 = 22 + q.val by omega] at hv; split_ifs at hv <;> omega
theorem cHiNSub341_ne_pubNuc {n : ℕ} {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout}
    (hRegs : ValidMuxD1Stage2Regs rNuc rElec) (rTot : QRegister dLayout n)
    {i : Fin (routerWidth 47 6)} (hi : i.val < 1238) (p : Fin 47) :
    (rTot.compose rNuc) i ≠ rTot (cHiNSub341 p) := fun e ↦ by
  have _ := p.isLt
  have hv : (rNuc i).val = (cHiNSub341 p).val := congrArg Fin.val (rTot.wires.injective e)
  rw [hRegs.pubNuc i hi, val_rNucLayout_eq, val_nucRouterWireFn i, val_cHiNSub341] at hv;
      split_ifs at hv <;> omega
theorem cHiNSub341_ne_pubElec {n : ℕ} {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout}
    (hRegs : ValidMuxD1Stage2Regs rNuc rElec) (rTot : QRegister dLayout n)
    {j : Fin (routerWidth 187 8)} (hj : j.val < 4602) (p : Fin 47) :
    (rTot.compose rElec) j ≠ rTot (cHiNSub341 p) := fun e ↦ by
  have _ := p.isLt
  have hv : (rElec j).val = (cHiNSub341 p).val := congrArg Fin.val (rTot.wires.injective e)
  rw [hRegs.pubElec j hj, val_rElecLayout_eq, val_elecRouterWireFn j, val_cHiNSub341] at hv;
      split_ifs at hv <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream

section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
namespace QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
set_option maxRecDepth 4096
open PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (appendFin
    appendFin_castAdd appendFin_natAdd appendFin_cases)
attribute [local irreducible] systemQubits_frozen
/- ## Section 1: Persistent Router Disjointness & Merged Classical-Control Bell Overlay -/

theorem hne_hA_sys {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) (p : Fin M) : rHA r b ≠
    rSys r p b := (hne_fixed_router r).2.2.1 b p
end QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
set_option maxRecDepth 4096
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X Circuit.T Circuit.S
  PhotochemistrySolution.DynQromUncompA.wrapDyn
  PhotochemistrySolution.KinB.andComputeCircuit
  PhotochemistrySolution.KinB.andUncomputeDyn
  DynCircExt.andUncompute_loc CircExt.andUncomputeFixup_loc
attribute [local irreducible] systemQubits_frozen
theorem qreg_ext_merged0 {k n : ℕ} {r₁ r₂ : QRegister k n} (h : ∀ i, r₁ i = r₂ i) : r₁ = r₂ := by
  cases r₁ with
    | mk f₁ => cases r₂ with
    | mk f₂ => exact congrArg QRegister.mk (Function.Embedding.ext h)
theorem fin2_zero_ne_one_merged0 : (0 : Fin 2) ≠ 1 := fun h ↦ Nat.zero_ne_one (congrArg Fin.val h)
end QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
open PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (appendFin
    appendFin_castAdd appendFin_natAdd appendFin_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (ket_H_apply)
attribute [local irreducible] systemQubits_frozen
theorem topPlaneIdx_lt {m : ℕ} (hm : m + 1 ≤ 24) : 23 - m < 24 := by omega
/-- Bit-plane index `23 - m` peeled from the top of `0..23`. -/
def topPlaneFin (m : ℕ) (hm : m + 1 ≤ 24) : Fin 24 :=
  ⟨23 - m, topPlaneIdx_lt hm⟩
/--
Input ket invariant for `pHBZMerge24Dyn`: both `rHB rN` and `rHB rE` start at `|0⟩^24`, and
`rRawHas2 rN` and `rRawHas2 rE` are mutually exclusive (`NN` vs `EE`).
-/
def HBZMergeInput {M₁ D₁ M₂ D₂ n : ℕ} (rN : RouterReg M₁ D₁ n) (rE : RouterReg M₂ D₂ n)
    (γ : BitAssignment n) : Prop :=
    (∀ b : Fin 24, γ (rHB rN b) = 0) ∧ (∀ b : Fin 24, γ (rHB rE b) = 0) ∧ (γ (rRawHas2 rN) = 1 →
    γ (rRawHas2 rE) = 0)
def fixedFanoutBits {n : ℕ} : (M : ℕ) → (srcVal : ZMod 2) → (cVec : Fin M → ZMod 2) →
    (wTgt : Fin M → Wire n) → BitAssignment n → BitAssignment n
  | 0, _, _, _, β => β
  | M + 1, srcVal, cVec, wTgt, β =>
      let β' := fixedFanoutBits M srcVal (fun p ↦ cVec p.castSucc) (fun p ↦ wTgt p.castSucc) β
      if cVec (Fin.last M) = 1 then
        Function.update β' (wTgt (Fin.last M)) (β' (wTgt (Fin.last M)) + srcVal)
      else β'
theorem fixedFanoutBits_of_ne_tgt {n : ℕ} : ∀ (M : ℕ) (srcVal : ZMod 2) (cVec : Fin M → ZMod 2)
    (wTgt : Fin M → Wire n)
    (β : BitAssignment n) (w : Wire n), (∀ p : Fin M, w ≠ wTgt p) →
        fixedFanoutBits M srcVal cVec wTgt β w = β w
  | 0, _, _, _, _, _, _ => rfl
  | M + 1, srcVal, cVec, wTgt, β, w, hne => by
      dsimp only [fixedFanoutBits]
      split_ifs <;> simp [hne (Fin.last M), fixedFanoutBits_of_ne_tgt M srcVal _ _ β w fun p ↦
          hne p.castSucc]
theorem fixedFanoutCirc_mulVec_ket {n : ℕ} : ∀ (M : ℕ) (qSrc : Wire n) (cVec : Fin M → ZMod 2)
    (wTgt : Fin M → Wire n)
    (hst : ∀ p : Fin M,
      qSrc ≠ wTgt p) (β : BitAssignment n),
          (fixedFanoutCirc M qSrc cVec wTgt hst).eval.1.mulVec (ket β) =
          ket (fixedFanoutBits M (β qSrc) cVec wTgt β)
  | 0, _, _, _, _, β =>
        by simp only [fixedFanoutCirc, fixedFanoutBits, Circuit.eval_identity, Submonoid.coe_one,
             Matrix.one_mulVec]
  | M + 1, qSrc, cVec, wTgt, hst, β => by
      dsimp only [fixedFanoutCirc, fixedFanoutBits]
      rw [eval_seq_mulVec, fixedFanoutCirc_mulVec_ket M qSrc _ _ (fun p ↦ hst p.castSucc) β]
      split_ifs
      · rw [ket_CNOT, fixedFanoutBits_of_ne_tgt M (β qSrc) _ _ β qSrc fun p ↦ hst p.castSucc]
      · simp only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
theorem fixedFanoutBits_zero_src {n : ℕ} : ∀ (M : ℕ) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
    (β : BitAssignment n), fixedFanoutBits M 0 cVec wTgt β = β
  | 0, _, _, _ => rfl
  | M + 1, cVec, wTgt, β => by
    simp only [fixedFanoutBits, fixedFanoutBits_zero_src M (fun p ↦ cVec p.castSucc)
        (fun p ↦ wTgt p.castSucc) β, add_zero,
      Function.update_eq_self, ite_self]
theorem fixedFanoutBits_zero_ctrl {n : ℕ} : ∀ (M : ℕ) (srcVal : ZMod 2) (cVec : Fin M → ZMod 2)
    (wTgt : Fin M → Wire n)
    (β : BitAssignment n), (∀ p : Fin M, cVec p = 0) → fixedFanoutBits M srcVal cVec wTgt β = β
  | 0, _, _, _, _, _ => rfl
  | M + 1, srcVal, cVec, wTgt, β, hz => by
    simp only [fixedFanoutBits, hz (Fin.last M), zero_ne_one, ↓reduceIte,
      fixedFanoutBits_zero_ctrl M srcVal _ _ β fun p ↦ hz p.castSucc]
theorem fixedFanoutBits_update_comm {n : ℕ} : ∀ (M : ℕ) (srcVal : ZMod 2) (cVec : Fin M → ZMod 2)
    (wTgt : Fin M → Wire n) (u : Wire n)
    (val : ZMod 2)
    (_hu : ∀ p : Fin M,
      u ≠ wTgt p) (β : BitAssignment n),
          fixedFanoutBits M srcVal cVec wTgt (Function.update β u val) =
          Function.update (fixedFanoutBits M srcVal cVec wTgt β) u val
  | 0, _, _, _, _, _, _, _ => rfl
  | M + 1, srcVal, cVec, wTgt, u, val, hu, β => by
      dsimp only [fixedFanoutBits]
      rw [fixedFanoutBits_update_comm M srcVal _ _ u val (fun p ↦ hu p.castSucc) β]
      split_ifs
      · rw [Function.update_of_ne (hu (Fin.last M)).symm,
            Function.update_comm (hu (Fin.last M)).symm]
      · rfl
theorem fixedBell1Circ_mulVec_ket_zero {n : ℕ} (M : ℕ) (qH : Wire n) (cVec : Fin M → ZMod 2)
    (wTgt : Fin M → Wire n) (hht : ∀ p, qH ≠ wTgt p) {α : BitAssignment n}
    (hq0 : α qH = 0) : (fixedBell1Circ M qH cVec wTgt hht).eval.1.mulVec (ket α) =
    sqrtHalf • (ket α + ket (Function.update (fixedFanoutBits M 1 cVec wTgt α) qH 1)) := by
  dsimp only [fixedBell1Circ]
  rw [eval_seq_mulVec, ket_H_apply, hq0, show bitSign (0 : ZMod 2) = (1 : ℂ) from rfl, one_smul,
    show Function.update α qH 0 = α from hq0 ▸ Function.update_eq_self qH α,
    Matrix.mulVec_smul, Matrix.mulVec_add, fixedFanoutCirc_mulVec_ket, fixedFanoutCirc_mulVec_ket,
        hq0, fixedFanoutBits_zero_src,
    Function.update_self, fixedFanoutBits_update_comm M 1 cVec wTgt qH 1 hht α]
end QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
open PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self ket_H_apply sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (appendFin
    appendFin_castAdd appendFin_natAdd appendFin_cases HCNOTSupportedIn)
attribute [local irreducible] systemQubits_frozen
theorem hcnotSupportedIn_mono {n : ℕ} {S₁ S₂ : Wire n → Prop} (hImp : ∀ w, S₁ w → S₂ w)
    {c : Circuit n} (hc : HCNOTSupportedIn S₁ c) : HCNOTSupportedIn S₂ c := by
  induction hc with
  | id => exact .id
  | seq _ _ i1 i2 => exact .seq i1 i2
  | h hq => exact .h (hImp _ hq)
  | cnot hct h1 h2 => exact .cnot hct (hImp _ h1) (hImp _ h2)
theorem hcnotSupportedIn_fixedBell1 {M n : ℕ} {S : Wire n → Prop} (qH : Wire n)
    (cVec : Fin M → ZMod 2) (wT : Fin M → Wire n) (hht : ∀ p, qH ≠ wT p) (hq : S qH)
    (hw : ∀ p, S (wT p)) : HCNOTSupportedIn S (fixedBell1Circ M qH cVec wT hht) := by
  exact .seq (.h hq) <|
    (Nat.recOn (motive := fun K ↦ ∀ (cV : Fin K → ZMod 2) (wt : Fin K → Wire n)
        (hh : ∀ p, qH ≠ wt p), (∀ p, S (wt p)) → HCNOTSupportedIn S (fixedFanoutCirc K qH cV wt hh))
      M (fun _ _ _ _ ↦ .id) fun _ ih _ _ _ hwt ↦ .seq (ih _ _ _ fun p ↦ hwt p.castSucc)
        (by split_ifs <;> first | exact .cnot _ hq (hwt _) | exact .id)) cVec wT hht hw
theorem subspaceStep_seq_circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {R₀ R₁ : Operator (2 ^ n)}
    {p : DynamicCircuit Var n} (c : Circuit n)
    (hp : SubspaceStep (Var := Var) R₀ R₁ p) :
    SubspaceStep (Var := Var) R₀ (c.eval.1 * R₁) (.seq p (.circuit c)) := fun M ↦
  Exists.elim (hp (qAssign_obs_map c.eval M)) fun N ⟨hwp, hmat⟩ ↦
    ⟨N, by rw [wp_seq_compile, wp_circuit_constObservable, hwp],
     by simpa only [qAssign_obs_map_mat, conjTranspose_mul, Matrix.mul_assoc] using hmat⟩
end QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
end

namespace QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStage4
set_option maxRecDepth 4096
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ProviderZeroFloor PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.PotOraclePortB
  PhotochemistrySolution.PotOraclePortBStream PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Coin70Lift PhotochemistrySolution.PortBDualBellUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState
attribute [local irreducible] phaseFlipUnitary bSpeciesSwap50 Stage4KinFull.bAxisMux27
theorem clampOneHot_props_portB151 {n Wp : ℕ} (hWp : Wp ≤ 738) (rTot : QRegister dLayout n) :
    let rW := rTot.compose rClean714Layout;
    let rB := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp));
    let st0 := clampOneHot rTot
    (∀ δ (b : Fin 24), (st0 δ (rB ⟨4, by omega⟩) = 0 → st0 δ (rB ⟨122 + b.val, by omega⟩) = 0) ∧
        (st0 δ (rB ⟨4, by omega⟩) = 1
      → st0 δ (rB ⟨57 + b.val, by omega⟩) = 0)) ∧
    (∀ δ (u : Fin (max Wp 24)), 24 ≤ u.val → (∀ q : Fin 714, δ (rW q) = 0) →
        st0 δ (rB ⟨122 + u.val, by omega⟩) = 0) := by
  intro rW rB st0
  obtain ⟨hB4, hB57, hB122, hBHi⟩ := portB151_reg_links hWp rTot
  have hOut (δ : BitAssignment n) (k : Fin (122 + max Wp 24)) (hk : k.val < 57 ∨ 146 ≤ k.val) :
      st0 δ (rB k) = δ (rB k) :=
    (clampOneHot_apply rTot δ).2.2 (rB k)
      (fun j e ↦ absurd (congrArg Fin.val (rB.wires.injective (e.trans (hB122 j).symm)))
          (by dsimp; omega))
      (fun j e ↦ absurd (congrArg Fin.val (rB.wires.injective (e.trans (hB57 j).symm)))
          (by dsimp; omega))
  refine ⟨fun δ b ↦ ?_, fun δ u hu24 hz ↦
    (hOut δ ⟨122 + u.val, by omega⟩
        (Or.inr (Nat.add_le_add_left hu24 122))).trans ((congrArg δ (hBHi u hu24)).trans (hz _))⟩
  obtain ⟨cN, cE, _⟩ := clampOneHot_apply rTot δ
  rw [(hOut δ ⟨4, by omega⟩ (Or.inl (show (4 : ℕ) < 57 by omega))).trans (congrArg δ hB4),
    hB122 b, hB57 b, show st0 = clampOneHot rTot from rfl, cN b, cE b]
  exact ⟨fun h0 ↦ by simp [h0], fun h1 ↦ by simp [h1]⟩
theorem swapHi24Bits_eq_packPortB151St {n Wp : ℕ} (hWp : Wp ≤ 738)
    (rTot : QRegister dLayout n)
    (st0 : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
    (hOneHot : ∀ b : Fin 24,
      (st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨4, by omega⟩) = 0 →
        st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨122 + b.val, by omega⟩) = 0) ∧
      (st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨4, by omega⟩) = 1 →
        st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨57 + b.val, by omega⟩) = 0)) :
    swapHi24Bits rTot (st0 δ) =
      packPortBSt (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp)))
        (Nat.le_max_right Wp 24) st0 δ := by
  let rB := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
  obtain ⟨hB4, hB57, hB122, _⟩ := portB151_reg_links hWp rTot
  obtain ⟨hPZero, _, hP57⟩ := packPortBSt_props rB (Nat.le_max_right Wp 24) st0
  obtain ⟨hSE, hSN, hSO⟩ := swapHi24Bits_apply rTot (st0 δ)
  have hOH' (b : Fin 24) :
      (st0 δ (rTot (wPotIsNN rPot0Layout)) = 0 → st0 δ (rTot (rBufHi rNucLayout b)) = 0) ∧
      (st0 δ (rTot (wPotIsNN rPot0Layout)) = 1 → st0 δ (rTot (rBufHi rElecLayout b)) = 0) := by
    simpa only [hB4, hB122 b, hB57 b] using hOneHot b
  funext w
  if hwN : ∃ b : Fin 24, w = rTot (rBufHi rNucLayout b) then
    obtain ⟨b, rfl⟩ := hwN
    conv_rhs => rw [← hB122 b, hPZero δ b]
    rcases DynCircExt.bit_cases (st0 δ (rTot (wPotIsNN rPot0Layout))) with h | h <;>
      simp [hSN b, h, (hOH' b).1, (hOH' b).2]
  else if hwE : ∃ b : Fin 24, w = rTot (rBufHi rElecLayout b) then
    obtain ⟨b, rfl⟩ := hwE
    conv_rhs => rw [← hB57 b, hP57 δ b, hB57 b, hB122 b]
    rcases DynCircExt.bit_cases (st0 δ (rTot (wPotIsNN rPot0Layout))) with h | h <;>
      simp [hSE b, h, (hOH' b).1, (hOH' b).2]
  else
    dsimp only [packPortBSt]
    rw [hSO w (fun b e ↦ hwE ⟨b, e⟩) (fun b e ↦ hwN ⟨b, e⟩),
      writeReg_apply_of_not_mem _ _ _ _ fun ⟨b, hb⟩ ↦
          hwN ⟨b, hb.symm.trans ((congrArg rB.wires (Fin.ext rfl)).trans (hB122 b))⟩,
      writeReg_apply_of_not_mem _ _ _ _ fun ⟨b, hb⟩ ↦
          hwE ⟨b, hb.symm.trans ((congrArg rB.wires (Fin.ext rfl)).trans (hB57 b))⟩]
attribute [local irreducible] clampOneHot packPortBSt
end QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStage4
end
end

noncomputable section

open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution
  PhotochemistrySolution.PotOracleGen PhotochemistrySolution.Word73PotPool
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
/- ## Section 1: Pairwise Disjointness Bundles (Leg1, Leg2, CoulOW) -/

theorem openCoordDistSq_le_195075 (a b : Fin 3 → Fin 256) : openCoordDistSq a b ≤ 195075 :=
    openBoxDist3DSq_le a b
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

namespace QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
open Operator PhotochemistrySolution PhotochemistrySolution.SplitRouterSeqBell26k
theorem supportedOn_mono_sorted {n : ℕ} {P Q : BitAssignment n → Prop} {R : Operator (2 ^ n)}
    (hPQ : ∀ β, P β → Q β) (hR : SupportedOn P R) : SupportedOn Q R :=
  fun A B hAB ↦ hR A B fun β hP ↦ hAB β (hPQ β hP)
end QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.Stage2QromMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PrimitiveGate hiding s
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder
/-! ### Part 1: Split Header `pUMsbHdrZG` (definitional split before `[local irreducible]`) -/
/--
Suffix-zero `rUMsb` portion of `pHdrD1ZG` (`D - 2` `TempAND`s; leaves `rNotMin` & `rNotMax`
untouched so `rNotMin[0..3]` can host 4 temporary linear slice wires during `pStreamXorLoadEqHi`).
-/
def pUMsbHdrZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) : ComputeProg n :=
  let hu := (hne_zg_hdr r).2.2; let dTop : Fin D := ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩;
  let dSub : Fin D := ⟨D - 2, hdr_lt2 hD2⟩; let hNeTS : dTop ≠ dSub := hdr_top_ne_sub hD2;
  let pInitTop :=
      ComputeProg.seq (.cnot (rIdx1 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.1 dTop))
      (.seq (.cnot (rIdx2 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.2.1 dTop))
      (.seq (.cnot (rHas1 r) (rUMsb r dTop) (hu.2.2.2.1 dTop))
      (.seq (.cnot (rRawHas2 r) (rUMsb r dTop) (hu.2.2.2.2.1 dTop))
      (.seq (.cnot (rHas1 r) (rUMsb r dSub) (hu.2.2.2.1 dSub)) (.cnot (rUMsb r dTop) (rUMsb r dSub)
      (rUMsb_ne_of_ne r hNeTS))))))
  .seq pInitTop (pUMsbDownLoop true r (D - 2) (hdr_lt2 hD2))
theorem pHdrD1ZG_eq_seq {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) :
    pHdrD1ZG hD2 r = .seq (pNotFlagsZG r D le_rfl) (pUMsbHdrZG hD2 r) := rfl
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  DynQromUncompA.remeasureIf DynQromUncompA.fwdCirc
def UMsbHdrSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    PubCtrlSet r w ∨ ∃ d : Fin D, w = rUMsb r d
theorem progSupportedIn_pUMsbHdrZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) :
    ProgSupportedIn (UMsbHdrSet r) (pUMsbHdrZG hD2 r) := by
  have h1 : UMsbHdrSet r (rHas1 r) := .inl ⟨_, by dsimp; omega, rfl⟩
  have h2 : UMsbHdrSet r (rRawHas2 r) := .inl ⟨_, by dsimp; omega, rfl⟩
  exact ⟨⟨⟨.inl ⟨_, by simp; omega, rfl⟩,
      .inr ⟨_, rfl⟩⟩,
      ⟨.inl ⟨_, by simp; omega, rfl⟩,
          .inr ⟨_, rfl⟩⟩,
      ⟨h1, .inr ⟨_, rfl⟩⟩, ⟨h2, .inr ⟨_, rfl⟩⟩, ⟨h1, .inr ⟨_, rfl⟩⟩, ⟨.inr ⟨_, rfl⟩,
          .inr ⟨_, rfl⟩⟩⟩,
    progSupportedIn_pUMsbDownLoop true r h1 h2 (fun d ↦
        .inl ⟨_, by simp; omega, rfl⟩)
      (fun d ↦ .inl ⟨_, by simp; omega, rfl⟩) (fun d ↦ .inr ⟨d, rfl⟩)
          (D - 2) (hdr_lt2 hD2)⟩
/--
Unconditional restoration outside `rUMsb` for `pUMsbStep` (holds on EVERY basis state `η`,
without requiring `rUMsb` clean).
-/
theorem fwdBits_pUMsbStep_of_ne_uMsb {M D n : ℕ} (r : RouterReg M D n) (m : ℕ) (hm : m + 1 < D)
    (η : BitAssignment n) {w : Wire n} (hw : ∀ d : Fin D, w ≠ rUMsb r d) :
    (pUMsbStep true r m hm).fwdBits η w = η w := by
  let dk : Fin D := ⟨m + 1, hm⟩
  let dk1 : Fin D := ⟨m, Nat.lt_of_succ_lt hm⟩
  let hu := (hne_zg_hdr r).2.2
  let η₁ := Function.update η (rIdx2 r dk) (1 + diffBit true r η dk)
  let η₂ := Function.update η₁ (rUMsb r dk1) (η₁ (rUMsb r dk1) + η₁ (rUMsb r dk) * η₁ (rIdx2 r dk))
  have hPre : (pUMsbPre true r dk).fwdBits η = η₁ := funext fun u ↦ by
    dsimp [pUMsbPre, diffBit, ComputeProg.fwdBits, η₁]
    exact if h : u = rIdx2 r dk then by
      subst h; simp only [Function.update_self, Function.update_of_ne (hu.2.1 dk),
          Function.update_of_ne (hu.2.2.1 dk)]
      exact zmod2_pre_true _ _ _ _
    else by simp only [Function.update_of_ne h]
  have hAnd : (ComputeProg.andGate (rUMsb r dk) (rIdx2 r dk) (rUMsb r dk1) (rUMsb_ne_rIdx2 r dk dk)
      (rUMsb_ne_of_ne r (hdr_succ_ne m hm)).symm (rUMsb_ne_rIdx2 r dk1 dk).symm).fwdBits
      ((pUMsbPre true r dk).fwdBits η) = η₂ := hPre ▸ rfl
  rw [show (pUMsbStep true r m hm).fwdBits η w =
      (ComputeProg.cnot (rUMsb r dk1) (rUMsb r dk) (rUMsb_ne_of_ne r (hdr_succ_ne m hm))).fwdBits
        ((pUMsbPost true r dk).fwdBits η₂) w by rw [← hAnd]; rfl]
  dsimp [pUMsbPost, ComputeProg.fwdBits]
  rw [Function.update_of_ne (hw dk)]
  if h2 : w = rIdx2 r dk then
    subst h2
    rw [Function.update_self, Function.update_of_ne (hu.1 dk), Function.update_self,
        Function.update_of_ne (hu.2.1 dk),
      Function.update_of_ne (hu.1 dk), Function.update_self, Function.update_of_ne (hu.2.2.1 dk),
      Function.update_of_ne (hu.2.1 dk), Function.update_of_ne (hu.1 dk), Function.update_self,
      show η₂ (rIdx2 r dk) = 1 + diffBit true r η dk from
        (Function.update_of_ne (rUMsb_ne_rIdx2 r dk1 dk).symm _ _).trans (Function.update_self _ _
            _),
      show η₂ (rIdx1 r dk) = η (rIdx1 r dk) from
        (Function.update_of_ne (rr_ne r (by simp [basePub]; omega)) _ _).trans
            (Function.update_of_ne (hu.1 dk) _ _),
      show η₂ (rHas1 r) = η (rHas1 r) from
        (Function.update_of_ne (hu.2.2.2.1 dk1) _ _).trans (Function.update_of_ne (hu.2.1 dk) _ _),
      show η₂ (rRawHas2 r) = η (rRawHas2 r) from
        (Function.update_of_ne (hu.2.2.2.2.1 dk1) _ _).trans (Function.update_of_ne (hu.2.2.1 dk) _
            _)]
    exact zmod2_post_true _ _ _ _
  else
    simp only [η₂, η₁, Function.update_of_ne h2, Function.update_of_ne (hw dk1)]
theorem fwdBits_pUMsbDownLoop_of_ne_uMsb {M D n : ℕ} (r : RouterReg M D n) :
    ∀ (k : ℕ) (hk : k < D) (η : BitAssignment n) {w : Wire n},
      (∀ d : Fin D, w ≠ rUMsb r d) →
      (pUMsbDownLoop true r k hk).fwdBits η w = η w
  | 0, _, _, _, _ => rfl
  | k + 1, hk, η, _, hw => (fwdBits_pUMsbDownLoop_of_ne_uMsb r k (Nat.lt_of_succ_lt hk) _ hw).trans
      (fwdBits_pUMsbStep_of_ne_uMsb r k hk η hw)
/-! ### Part 2: Universal Zero-`TempAND` Helpers & Unconditional `2^n × 2^n` Commutations -/
theorem cleanProj_empty_mul {n : ℕ} (X : Operator (2 ^ n)) : cleanProj (∅ : Finset (Wire n)) * X =
    X := by
  let _ : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  rw [show cleanProj (∅ : Finset (Wire n)) = (1 : Operator (2 ^ n)) from matrix_ext_ket fun β ↦ by
    rw [cleanProj_mulVec_ket, ite_eq_left fun _ h ↦ absurd h (Finset.notMem_empty _),
        Matrix.one_mulVec], Matrix.one_mul]
/-! ### Part 3: `swapPackKE0` & `rPackKE0` on `(M = 187, D = 8)` (`KE = 0`) -/
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage2ZeroGated
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  (ValidZeroGatedSortedRouterInput)
open scoped ComplexOrder MatrixOrder Circuit.Notation
attribute [local semireducible] ComputeProg.fwdBits DynQromUncompA.fwdCirc
theorem fwdBits_pUMsbHdrZG_eq_pHdrD1ZG_uMsb {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n)
    {β : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β)
    (d : Fin D) : (pUMsbHdrZG hD2 r).fwdBits β (rUMsb r d) = (pHdrD1ZG hD2 r).fwdBits β (rUMsb r d)
    := by
  have hNF0 :=
      (fwdBits_pNotFlagsZG r β (fun _ ↦
      hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff r _).mpr (by dsimp; omega)))
    (fun _ ↦ hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff r _).mpr (by dsimp; omega))) D le_rfl).2.2
  rw [pHdrD1ZG_eq_seq]
  refine Stage2ZeroGated.fwdBits_congr_on_supp _ (progSupportedIn_pUMsbHdrZG hD2 r)
      (fun _ hw ↦ ?_) _ (.inr ⟨d, rfl⟩)
  rcases hw with ⟨u, _, rfl⟩ | ⟨d', rfl⟩ <;>
    exact (hNF0 _ (fun d1 ↦ rr_ne r (by simp [basePub, *]; omega))
      (fun d2 ↦ rr_ne r (by simp [basePub, *]; omega))).symm
theorem fwdBits_pHdrD1ZG_notFlags {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n)
    {β : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β)
    (d : Fin D) : (pHdrD1ZG hD2 r).fwdBits β (rNotMin r d) = β (rHas1 r) + β (rIdx1 r d) ∧
    (pHdrD1ZG hD2 r).fwdBits β (rNotMax r d) = β (rRawHas2 r) + β (rIdx2 r d) := by
  obtain ⟨hMin, hMax, _⟩ := fwdBits_pNotFlagsZG r β
    (fun d' ↦
        hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff r _).mpr (by simp [basePub]; omega)))
    (fun d' ↦
        hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff r _).mpr (by simp [basePub]; omega))) D
        le_rfl
  rw [pHdrD1ZG_eq_seq]
  exact ⟨(Stage2ZeroGated.fwdBits_eq_of_not_supp _ (progSupportedIn_pUMsbHdrZG hD2 r) _ fun h ↦ by
      rcases h with ⟨_, _, e⟩ | ⟨d', e⟩
      · have hv := congrArg Fin.val (r.wires.injective e)
        simp [basePub] at hv; omega
      · exact rr_ne r (by simp [basePub]; omega) e).trans ((hMin d).trans
            (ite_eq_left d.isLt)),
    (Stage2ZeroGated.fwdBits_eq_of_not_supp _ (progSupportedIn_pUMsbHdrZG hD2 r) _ fun h ↦ by
      rcases h with ⟨_, _, e⟩ | ⟨d', e⟩
      · have hv := congrArg Fin.val (r.wires.injective e)
        simp [basePub] at hv; omega
      · exact rr_ne r (by simp [basePub]; omega) e).trans ((hMax d).trans
            (ite_eq_left d.isLt))⟩
theorem validPlaneNoNF_of_uMsbHi {M D n : ℕ} (hMD : M < 2 ^ D) (hD2 : 2 ≤ D) (r : RouterReg M D n)
    {β η : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β)
    (hPub : ∀ w, PubCtrlSet r w → η w = β w) (hLo : ∀ p : Fin M, η (rCtrlLo r p) =
    routerCtrlLo r β p) (hHi : ∀ p : Fin M, η (rCtrlHi r p) = routerCtrlHi r β p)
    (hUM : ∀ d : Fin D, 1 ≤ d.val → η (rUMsb r d) = (pUMsbHdrZG hD2 r).fwdBits β (rUMsb r d))
    (hBuf : ∀ b : Fin 24, η (rBufLo r b) = 0 ∧ η (rBufHi r b) = 0 ∧ η (rHA r b) = 0 ∧ η (rHB r b) =
    0) (hClean : (∀ d : Fin D, 1 ≤ d.val → η (rAMsb r d) = 0) ∧ (∀ d : Fin D, η (rCReg r d) = 0) ∧
    η (rAnc r) = 0) (b : Fin 24) : ValidPlaneCtrlMuxD1NoNF (planeOfRouter (rIdx12Alias r) b) η ∧
    ValidPlaneCleanMuxD1 (planeOfRouter (rIdx12Alias r) b) η := by
  let prN := planeOfRouter (rIdx12Alias r) b;
  let prS :=
      planeOfRouter (rHas2Alias r) b; obtain ⟨rN1, rN2, _, rNBL, rNBH, rNHA, rNHB, rNAnc, rNUM,
      rNNMin, rNNMax, rNAM, rNCR, rNCL, rNCH, _⟩ :=
      planeOfRouter_rIdx12Alias_roles r b; obtain ⟨rS1, rS2, _, _, _, _, _, _, rSUM, rSNMin, rSNMax,
      _, _, rSCL, rSCH, _⟩ := planeOfRouter_rHas2Alias_roles r b
  have hAgβ : AgreesBeforeHdr r β β := agreesBeforeHdr_of_eq_outside r hβ.1 fun _ ↦ rfl
  let η0 := (pHdrD1ZG hD2 r).fwdBits β
  let η1 := vecToggleBits (rCtrlHi r) (fun _ p ↦ η0 (rCtrlHi r p) + routerCtrlHi r β p) η0
  let ηS := vecToggleBits (rCtrlLo r) (fun _ p ↦ η1 (rCtrlLo r p) + routerCtrlLo r β p) η1
  have hAlg (x y : ZMod 2) : x + (x + y) = y := by
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hSLo (p : Fin M) : ηS (rCtrlLo r p) = routerCtrlLo r β p :=
    ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ η1).1 p).trans (hAlg _ _)
  have hSHi (p : Fin M) : ηS (rCtrlHi r p) = routerCtrlHi r β p :=
    ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).2 _ fun q ↦
        rr_ne r (by simp; omega)).trans
      (((vecToggleBits_spec (rCtrlHi r) (rCtrlHi_inj_ne r) _ η0).1 p).trans (hAlg _ _))
  have hSOth (w : Wire n) (nL : ∀ p, w ≠ rCtrlLo r p) (nH : ∀ p, w ≠ rCtrlHi r p) : ηS w = η0 w :=
    ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).2 w nL).trans
      ((vecToggleBits_spec (rCtrlHi r) (rCtrlHi_inj_ne r) _ η0).2 w nH)
  have hVS :=
      (valid_plane_zgModeMuxD1 hMD hD2 r hβ hAgβ (fun _ h1 h2 ↦
      absurd h1 (not_le_of_gt h2)) hSLo hSHi hSOth b).1
  obtain ⟨pR1, pR2, pI1, pI2⟩ := pubCtrlSet_roles r
  have tOth {w : Wire n} (h1 : ∀ d : Fin D, w ≠ rIdx1 r d) (h2 : ∀ d : Fin D, w ≠ rIdx2 r d) :
      toggleNotFlags prN η w = η w :=
    toggleNotFlags_other prN η (fun d e ↦ h1 d (e.trans (congrFun rNNMin d)))
        (fun d e ↦ h2 d (e.trans (congrFun rNNMax d)))
  have sPub {w : Wire n} : PubCtrlSet r w → ηS w = β w := fun ⟨u, hu, hw⟩ ↦ hw ▸
    (hSOth _ (fun p ↦ rr_ne r (by simp [basePub]; omega))
      fun p ↦
          rr_ne r (by simp [basePub]; omega)).trans (pub_pHdrD1ZG hD2 r hAgβ _ ⟨u, hu,
          rfl⟩)
  have eH1 : toggleNotFlags prN η (pHas1 prN) = ηS (pHas1 prS) := by
    rw [rN1, rS1, tOth (fun d ↦ rr_ne r (by simp; omega)) fun d ↦
        rr_ne r (by simp; omega), hPub _ pR1, sPub pR1]
  have eH2 : toggleNotFlags prN η (pHas2Eff prN) = ηS (pHas2Eff prS) := by
    rw [rN2, rS2, tOth (fun d ↦ rr_ne r (by simp; omega)) fun d ↦
        rr_ne r (by simp; omega), hPub _ pR2, sPub pR2]
  have eCL (p : Fin M) : toggleNotFlags prN η (pCtrlLo prN p) = ηS (pCtrlLo prS p) := by
    rw [congrFun rNCL p, congrFun rSCL p,
        tOth (fun d ↦ rr_ne r (by simp [basePub]; omega))
      fun d ↦ rr_ne r (by simp [basePub]; omega), hLo p, hSLo p]
  have eCH (p : Fin M) : toggleNotFlags prN η (pCtrlHi prN p) = ηS (pCtrlHi prS p) := by
    rw [congrFun rNCH p, congrFun rSCH p,
        tOth (fun d ↦ rr_ne r (by simp [basePub]; omega))
      fun d ↦ rr_ne r (by simp [basePub]; omega), hHi p, hSHi p]
  have eUM (d : Fin D) (hd1 : 1 ≤ d.val) : toggleNotFlags prN η (pUMsb prN d) = ηS (pUMsb prS d)
      := by
    rw [congrFun rNUM d, congrFun rSUM d,
        tOth (fun d' ↦ rr_ne r (by simp [basePub]; omega))
      fun d' ↦ rr_ne r (by simp [basePub]; omega), hUM d hd1,
      fwdBits_pUMsbHdrZG_eq_pHdrD1ZG_uMsb hD2 r hβ d, hSOth _ (fun p ↦
          rr_ne r (by simp; omega))
        fun p ↦ rr_ne r (by simp; omega)]
  have eN1 (d : Fin D) : toggleNotFlags prN η (pNotMin prN d) = ηS (pNotMin prS d) := by
    rw [toggleNotFlags_notMin prN η d, congrFun rNNMin d, rN1, congrFun rSNMin d, hPub _ (pI1 d),
        hPub _ pR1,
      hSOth _ (fun p ↦ rr_ne r (by simp; omega)) fun p ↦
          rr_ne r (by simp; omega)]
    exact (add_comm _ _).trans (fwdBits_pHdrD1ZG_notFlags hD2 r hβ d).1.symm
  have eN2 (d : Fin D) : toggleNotFlags prN η (pNotMax prN d) = ηS (pNotMax prS d) := by
    rw [toggleNotFlags_notMax prN η d, congrFun rNNMax d, rN2, congrFun rSNMax d, hPub _ (pI2 d),
        hPub _ pR2,
      hSOth _ (fun p ↦ rr_ne r (by simp; omega)) fun p ↦
          rr_ne r (by simp; omega)]
    exact (add_comm _ _).trans (fwdBits_pHdrD1ZG_notFlags hD2 r hβ d).2.symm
  refine ⟨⟨fun h ↦ eH1.trans (hVS.1 (eH2.symm.trans h)), ?_, ?_, ?_⟩, rNBL.symm ▸ (hBuf b).1,
      rNBH.symm ▸ (hBuf b).2.1, rNHA.symm ▸ (hBuf b).2.2.1, rNHB.symm ▸ (hBuf b).2.2.2,
    fun d hd1 ↦ (congrFun rNAM d).symm ▸ hClean.1 d hd1, fun d ↦
        (congrFun rNCR d).symm ▸ hClean.2.1 d, rNAnc.symm ▸ hClean.2.2⟩
  · rw [eH1]; intro z
    exact ⟨fun p ↦ (eCL p).trans ((hVS.2.1 z).1 p), fun d ↦ (eN1 d).trans ((hVS.2.1 z).2.1 d),
        fun d hd1 ↦ (eUM d hd1).trans ((hVS.2.1 z).2.2 d hd1)⟩
  · rw [eH2]; intro z
    exact ⟨fun p ↦ (eCH p).trans ((hVS.2.2.1 z).1 p), fun d ↦ (eN2 d).trans ((hVS.2.2.1 z).2 d)⟩
  · rw [eH1, eH2]; intro o
    rcases hVS.2.2.2 o with ⟨pMin, hc1, hc0, hnm, h1i, h2i⟩
    refine ⟨pMin, (eCL pMin).trans hc1, fun p hp ↦ (eCL p).trans (hc0 p hp), fun d ↦
        (eN1 d).trans (hnm d),
      fun z2 ↦ let ⟨dS, b0, hu_hi⟩ := h1i z2
        ⟨dS, b0, fun d hd1 ↦ (eUM d hd1).trans (hu_hi d hd1)⟩,
      fun o2 ↦ let ⟨pMax, hlt, hd1, hd0, hnm2, dS, b0, b1, hu_hi⟩ := h2i o2
        ⟨pMax, hlt, (eCH pMax).trans hd1, fun p hp ↦ (eCH p).trans (hd0 p hp), fun d ↦
            (eN2 d).trans (hnm2 d), dS, b0, b1, fun d hd1' ↦ (eUM d hd1').trans (hu_hi d hd1')⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
end

section
set_option maxRecDepth 4096

section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
namespace QuantumComputation.Specs.PhotochemistrySolution.PortBSharedPoly
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.PortBDualBellUnld
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
structure Stage1AsymRevPkg (w1 tStage1 : ℕ) (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) where
  o1 : Stage1ZeroNEremLayout w1 decodeCoin
  revAmb : ∀ {Var : Type} {n : ℕ}, Var → QRegister dLayout n → DynamicCircuit Var n
  counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister dLayout n),
    (o1.fwdAmb v rTot).count .T + (revAmb v rTot).count .T = tStage1 ∧
    (revAmb v rTot).count .TOFF = 0
  stepRev : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {kExt n : ℕ} [NeZero (2 ^ n)]
    {X : Operator (2 ^ n)} (hk : kExt ≤ 72) (v : Var) (rTot : QRegister dLayout n),
    DynWires (fun u ↦ ∀ j : Fin kExt, u ≠ (rTot.compose (rCoinExt kExt hk)) j) (revAmb v rTot) →
    (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X →
    SubspaceStep ((rTot.embedUnitary (uStage1Clean_c70 decodeCoin)).1 * X) X (revAmb v rTot)
end QuantumComputation.Specs.PhotochemistrySolution.PortBSharedPoly

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
open scoped ComplexOrder MatrixOrder
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.CoinWrap
  PhotochemistrySolution.Stage1SingleWrap
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
theorem subspaceStep_seq_asym {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₁ R₂ R₃ : Operator (2 ^ n)} {p₁ p₂ : DynamicCircuit Var n}
    (h₁ : SubspaceStep R₁ R₂ p₁) (h₂ : SubspaceStep R₂ R₃ p₂) :
    SubspaceStep R₁ R₃ (.seq p₁ p₂) := fun M ↦
  let ⟨N₂, hw₂, hm₂⟩ := h₂ M
  let ⟨N₁, hw₁, hm₁⟩ := h₁ N₂
  ⟨N₁, by rw [QubitizationWalkSem.wp_seq_compile, hw₂, hw₁], hm₂.trans hm₁⟩
theorem midBnd_of_bilinear {M : ℕ} {midTerms : Fin 32 → List (List ℕ × List ℕ)}
    (hOk : ∀ j, checkBilinearTerms (49 + M) (midTerms j) = true) (j : Fin 32) :
    checkPairsBound (49 + M) (compileBilinearPairs (midTerms j)) = true :=
  (compileBilinearPairs_spec (fun _ ↦ true) rfl (midTerms j) (hOk j)).1
theorem midEval_of_bilinear {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {M : ℕ}
    {coreGates : Fin M → ℕ × ℕ} {coreMask0 coreMask1 : ℕ}
    {midPx : Fin 32 → Bool}
    {midTerms : Fin 32 → List (List ℕ × List ℕ)}
    (hOk : ∀ j, checkBilinearTerms (49 + M) (midTerms j) = true)
    (hEval : ∀ c j, let m40 := zeroNEremOutMask (decodeCoin c)
      xor (midPx j) (evalBilinearBool (midPredBit M coreGates coreMask0 coreMask1 c m40)
        (midTerms j)) = preCnotBit40 m40 (mid32OutIdx j))
    (c : Fin (2 ^ 41)) (j : Fin 32) :
    let m40 := zeroNEremOutMask (decodeCoin c)
    xor (midPx j) (pairsParityBool (midPredBit M coreGates coreMask0 coreMask1 c m40)
      (compileBilinearPairs (midTerms j))) = preCnotBit40 m40 (mid32OutIdx j) :=
  (congrArg (xor (midPx j)) (compileBilinearPairs_spec _
    (midPredBit_zero M coreGates coreMask0 coreMask1 c _) (midTerms j) (hOk j)).2).trans
    (hEval c j)
theorem tailBnd_of_bilinear {M : ℕ} {tailTerms : Fin 5 → List (List ℕ × List ℕ)}
    (hOk : ∀ s : Fin 5, checkBilinearTerms (42 + M + s.val) (tailTerms s) = true) (s : Fin 5) :
    checkPairsBound (42 + M + s.val) (compileBilinearPairs (tailTerms s)) = true :=
  (compileBilinearPairs_spec (fun _ ↦ true) rfl (tailTerms s) (hOk s)).1
theorem tailEval_of_bilinear {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {M : ℕ}
    {coreGates : Fin M → ℕ × ℕ} {tailPx : Fin 5 → Bool}
    {tailTerms : Fin 5 → List (List ℕ × List ℕ)}
    (hOk : ∀ s : Fin 5, checkBilinearTerms (42 + M + s.val)
    (tailTerms s) = true)
    (hEval : ∀ c s, let m40 := zeroNEremOutMask (decodeCoin c)
      xor (tailPx s) (evalBilinearBool (tailPredBit M coreGates c m40) (tailTerms s)) =
        preCnotBit40 m40 (tail5OutIdx s)) (c : Fin (2 ^ 41))
    (s : Fin 5) :
    let m40 := zeroNEremOutMask (decodeCoin c)
    xor (tailPx s) (pairsParityBool (tailPredBit M coreGates c m40)
      (compileBilinearPairs (tailTerms s))) = preCnotBit40 m40 (tail5OutIdx s) :=
  (congrArg (xor (tailPx s)) (compileBilinearPairs_spec _ (tailPredBit_zero M coreGates c _)
    (tailTerms s) (hOk s)).2).trans (hEval c s)
end QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
end

namespace QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
open QuantumComputation.Specs PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.ScreenFermatCore PhotochemistrySolution.Cartesian254
open PhotochemistrySolution.OuterW11Bridge
theorem tier1_speciesZ_eq_mSp (s : Fin 4) : speciesZ s = mSpCart254 s := by
  decide +revert
/-- Partition `{c | P c}` into its `2,048` `w11NatOfCoin` fibers. -/
theorem tier1_card_filter_eq_sum_w11Nat (P : Fin (2 ^ 41) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter P).card =
      ∑ u : Fin 2048, ((Finset.univ : Finset (Fin (2 ^ 41))).filter
        fun c ↦ P c ∧ w11NatOfCoin c = u.val).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ if hp : P c then ?_ else by simp [hp]
  simp only [hp, ↓reduceIte, true_and]
  rw [Finset.sum_eq_single ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
      (fun _ _ hne ↦ ite_eq_right fun hv ↦ hne (Fin.ext hv.symm))
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  exact (ite_eq_left rfl).symm
end QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
/- ## Section 2: Generic `PopBZ30` (`240 T` + `504 T` + `96 T`) Two-State Constructors -/
end
end

noncomputable section

open QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen
  QuantumComputation.Specs.PhotochemistrySolution.Word73PotPool

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Sh14P5

open Real QuantumComputation.Specs PhotochemistrySolution
  PhotochemistrySolution.ClusterPotSlice PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.TelescopeSlice PhotochemistrySolution.EvenOctB70
  PhotochemistrySolution.ScreenFermatCore
open PhotochemistrySolution.PopBernstein PhotochemistrySolution.ZHi30
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen
/--
Alias to `PhotochemistrySolution.PopBernstein.y36PopBernNoClamp` from `CoulPopBernNoClamp34A` .
-/
abbrev y36PopBernNoClampS14 : (ℕ → ℕ) → Bool → ℕ → (Fin 3 → Fin 2048) → ℕ := y36PopBernNoClamp
theorem y36PopBernNoClampS14_eq_clamped_of_lt (word512 : ℕ → ℕ) (yC0 yC1 : ℕ) (isNN : Bool) {d2 : ℕ}
    (hlt : d2 < 194560) (c : Fin 3 → Fin 2048) : y36PopBernNoClampS14 word512 isNN d2 c =
    y36PopBernClamped word512 yC0 yC1 isNN d2 c := by
  have hcl : isClamp95Parts (evenOctIdxT10K isNN d2) = false :=
    Bool.eq_false_iff.mpr fun hc ↦
        absurd ((isClamp95Parts_iff_ge_194560 isNN (by omega)).mp hc) (by omega)
  simp [y36PopBernNoClampS14, y36PopBernNoClamp, y36PopBernClamped, hcl]
/-- Unclamped active control-point range check (`k = 8, idx7 = 95` included via `380 + j`). -/
def checkPopBernCtrlRangesNoClamp (word512 : ℕ → ℕ) (yLoF yHiF yHiF48 yLoT yHiT : ℕ) : Bool :=
  checkPopBernCtrlRanges word512 yLoF yLoF yLoF yHiF yHiF48 yLoT yHiT &&
  natLeB yHiF48 yHiF &&
  allRange 2 4 fun j ↦
    let y := (word512 (380 + j)) >>> 8
    natLeB yLoF y && natLeB y yHiF48 && natLeB yLoT y && natLeB y yHiT
theorem ctrl_bounds_of_ranges_noClamp {word512 : ℕ → ℕ} {yLoF yHiF yHiF48 yLoT yHiT : ℕ}
    (hr : checkPopBernCtrlRangesNoClamp word512 yLoF yHiF yHiF48 yLoT yHiT = true) :
    (∀ {d2 : ℕ}, Is3DBoxDistSq d2 → ∀ c : Fin 3 → Fin 2048, yLoF ≤
    y36PopBernNoClampS14 word512 false d2 c ∧ y36PopBernNoClampS14 word512 false d2 c ≤ yHiF) ∧
    (∀ {d2 : ℕ}, Is3DBoxDistSq d2 → 48 ≤ d2 → ∀ c : Fin 3 → Fin 2048, yLoF ≤
    y36PopBernNoClampS14 word512 false d2 c ∧ y36PopBernNoClampS14 word512 false d2 c ≤ yHiF48) ∧
    (∀ {d2 : ℕ}, Is3DBoxDistSq d2 → ∀ c : Fin 3 → Fin 2048, yLoT ≤
    y36PopBernNoClampS14 word512 true d2 c ∧ y36PopBernNoClampS14 word512 true d2 c ≤ yHiT) := by
  unfold checkPopBernCtrlRangesNoClamp at hr
  simp only [Bool.and_eq_true, natLeB_eq_true] at hr
  rcases hr with ⟨⟨hcr, h48le⟩, h380⟩
  obtain ⟨hbF, hbF48, hbT⟩ := ctrl_bounds_of_ranges hcr
  have hTail (isNN : Bool) {d2 : ℕ} (hd : d2 = 194566 ∨ d2 = 195075) (c : Fin 3 → Fin 2048) :
      yLoF ≤ y36PopBernNoClampS14 word512 isNN d2 c ∧ y36PopBernNoClampS14 word512 isNN d2 c ≤
          yHiF48 ∧ yLoT ≤ y36PopBernNoClampS14 word512 isNN d2 c ∧
          y36PopBernNoClampS14 word512 isNN d2 c ≤ yHiT := by
    have hp : (evenOctIdxT10K isNN d2).1 = 190 ∧ (evenOctIdxT10K isNN d2).2.2 = 8 := by
      rcases hd with rfl | rfl <;>
        simp [(clamp95_eval_194566 isNN).1, (clamp95_eval_195075 isNN).1]
    unfold y36PopBernNoClampS14 y36PopBernNoClamp idx7OfParts
    dsimp only
    rw [hp.1, hp.2]
    have hj :=
        allRange_eq_true (by norm_num) h380 (popBernJ_lt_four (t11OfParts (evenOctIdxT10K isNN d2))
        c)
    simp only [Bool.and_eq_true, natLeB_eq_true] at hj
    exact ⟨hj.1.1.1, hj.1.1.2, hj.1.2, hj.2⟩
  have eqC (b : Bool) {d2 : ℕ} (h : d2 < 194560) (c : Fin 3 → Fin 2048) :=
    (y36PopBernNoClampS14_eq_clamped_of_lt word512 yLoF yLoF b h c).symm
  have hGe (b : Bool) {d2 : ℕ} (h3d : Is3DBoxDistSq d2) (h : ¬d2 < 194560) :=
    hTail b (openDistSq_ge_194560_iff h3d (Nat.le_of_not_lt h))
  exact ⟨fun h3d c ↦ if h : _ < 194560 then eqC false h c ▸ hbF h3d c
      else ⟨(hGe false h3d h c).1, (hGe false h3d h c).2.1.trans h48le⟩,
    fun h3d h48 c ↦ if h : _ < 194560 then eqC false h c ▸ hbF48 h3d h48 c
      else ⟨(hGe false h3d h c).1, (hGe false h3d h c).2.1⟩,
    fun h3d c ↦ if h : _ < 194560 then eqC true h c ▸ hbT h3d c else (hGe true h3d h c).2.2⟩
def pre5OfNat (b : ℕ) : Fin 6 :=
  match b with
  | 0 => 0
  | 1 | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 5
/--
Collapse canonical `Fin 8` bucket (`<1, 1, 2..3, 4..7, 8..15, 16..31, 32..47, >=48`) onto `Pre5` .
-/
def pre5OfFin8 (b : Fin 8) : Fin 6 := pre5OfNat b.val
def mod31OfInt (x : ℤ) : ℕ := (x % (2147483648 : ℤ)).toNat
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Sh14P5
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec (fin8Bin)
def sectorDist3DSq3 (s nn : Bool) (nA pB eA : Fin 3 → Fin 256) : ℕ :=
    cond nn (openBoxDist3DSq nA pB) (cond s (openBoxDist3DSq eA pB) (openBoxDist3DSq nA eA))
def owB2Of3Port (nn : Bool) (nA pB eA : Fin 3 → Fin 256) : Fin 8 :=
    fin8Bin (openCoordDistSq (cond nn pB nA) (cond nn eA pB))
theorem owOpenCoordDistSq_comm (a b : Fin 3 → Fin 256) : openCoordDistSq a b =
    openCoordDistSq b a := by
  have h (i : Fin 3) : PhotochemistrySolution.ZeroNEremSpec.openBoxDist1D (a i) (b i) =
      PhotochemistrySolution.ZeroNEremSpec.openBoxDist1D (b i) (a i) := by
    unfold PhotochemistrySolution.ZeroNEremSpec.openBoxDist1D; omega
  simp only [openCoordDistSq, h]
theorem owLeg2_coords_b2 (nn : Bool) (nA pB eA : Fin 3 → Fin 256) :
    fin8Bin (openCoordDistSq (if nn then eA else nA) pB) = owB2Of3Port nn nA pB eA := by
  cases nn <;> simp [owB2Of3Port, owOpenCoordDistSq_comm]
theorem testBit_two_pow_sub_one_sub : ∀ (M u i : ℕ), u < 2 ^ M → i < M → (2 ^ M - 1 - u).testBit i =
    Bool.not (u.testBit i)
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | M + 1, u, 0, hu, _ => by
      have hp := pow_succ' 2 M
      rcases Nat.mod_two_eq_zero_or_one u with h | h <;>
        simp [Nat.testBit_zero, h, show (2 ^ (M + 1) - 1 - u) % 2 = 1 - u % 2 by omega]
  | M + 1, u, i + 1, hu, hi => by
      have hp := pow_succ' 2 M
      rw [Nat.testBit_succ, Nat.testBit_succ,
        show (2 ^ (M + 1) - 1 - u) / 2 = 2 ^ M - 1 - u / 2 by omega]
      exact testBit_two_pow_sub_one_sub M (u / 2) i (by omega) (by omega)
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
theorem zg47_hM0 : 0 < 47 := by omega
theorem zg187_hM0 : 0 < 187 := by omega
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.Stage2ZeroGated
theorem samePubPriv_trans_ke0 {M D n : ℕ} {r₁ r₂ r₃ : RouterReg M D n} (h12 : SamePubPriv r₁ r₂)
    (h23 : SamePubPriv r₂ r₃) : SamePubPriv r₁ r₃ :=
    ⟨fun u hu ↦ (h12.1 u hu).trans (h23.1 u hu), h12.2.trans h23.2⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
end
end

end ScopedLocalHelpers
end
