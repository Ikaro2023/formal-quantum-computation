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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellSelectD11Core
/-! # Zero-Top-Ancilla `d = 11` Cascade, `227`-Wire Layout, & `23`-Wire Router Simulation Helpers
Refs: Gidney (`10.22331/q-2018-06-18-74`), Berry (`10.22331/q-2019-12-02-208`),
Lee (`10.1103/PRXQuantum.2.030305`). -/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open TwoGearBox CircuitModular GivensOps BlockEncodingCore
open BlockEncodingCircuit SelectSwapQROM GivensCascade
open SelectRouter10 TopIntegrationBridge
open Lac2Fused184Select Lac2Fused184SelectWrap Router10Lac2Select
open Phase2MidSandwich MidReflCtxRetain OneHotSimulates
open PolymorphicFused184Select Lac2ZeroPar183Select CompactFoldedSelect
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
  hiding blockRemWidth
  outRemWidth midRemWidth combARem
open ReordOuter13Bridge StepEncK StepDecK
open CompactStepFast175Core CompactOuter9Bound50Core CompactOuter9Bound50Select
open Balanced160Select Pi145SOSPermBridge LowBitPi145Select
open BellPhaseASelect BellSingletCSwap58 Cat11CompactPhase2Bridge
open PhaseB154Pi145Select TwoGearQPEPhase5
open CompactTuned162StepWalk CompactZeroCmp20OuterParam
open DihedralWalkQPE DihedralWalkQPE.MultiGearQPE
open BellRouter57 BellRouter57Pure NoNegSelect57Pure CompactCore145Bundle
open BellPersistNoNeg BellSelectNoNegPair Select57Slices
open BellPersistCore BellAsymCore BellSuperLegSplice
open CompactStepFast176Select.UnsignedGivens (affineBilinearBitStep
  extendHot0 isCleanBitStep_affineBilinearFormula affinePlaneEffK affineApexEffK
  affineUnsignedBilinearLac2CascadeCtrlUnitary clearHot0Circuit evolve_clearHot0Circuit_ket
  clearHot0Circuit_eval_mul_self clearHot0_zero_of_isOneHot)
open CompactStepFast176Select.OneHotMux
  (clearHot0Circuit_conj_muxCtrlUnitary_eq)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
instance instNeZeroTwoPowD11B (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
instance instDecDisjWiresD11B {k₁ k₂ N : ℕ} (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ N) :
    Decidable (r₁.DisjointWires r₂) :=
  decidable_of_iff (∀ i j, r₁ i ≠ r₂ j) QRegister.disjoint_iff.symm
namespace PhaseBD11CompactCore
theorem localIdx_eq_of_forall {k n₁ n₂ : ℕ} (r₁ : QRegister k n₁) (r₂ : QRegister k n₂) (β₁ :
  BitAssignment n₁) (β₂ : BitAssignment n₂) (h : ∀ i : Fin k, β₁ (r₁ i) = β₂ (r₂ i)) :
  UnsignedGivens.localIdx r₁ β₁ = UnsignedGivens.localIdx r₂ β₂ := congrArg (UnsignedGivens.localIdx
    ⟨⟨id,
  Function.injective_id⟩⟩) (funext h)
theorem topZeroAffineLac2KickRef_ket_of_zero {n B G' : ℕ} (hB : 2 ≤ B) (idxTop idxMid : ℕ) (row :
    Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n) (rCat : QRegister B
    n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0
    rC w_p) (hdk : TopZeroAffineKickDisjoint w_ctrl sub w_v rHot' rCat a0 rC w_p) (β :
    BitAssignment n) (hv0 : β w_v = 0) (ha0 : β a0 = 0) (hC0 : ∀ j : Fin (B - 1), β (rC j) = 0) :
    let hbits := extendHot0 (fun g : Fin G' ↦ β (rHot' g))
    let a_lo := UnsignedGivens.bilinearRowLo B row (β w_ctrl) (β sub) hbits
    let b_mid := UnsignedGivens.bilinearRowBit idxMid row (β w_ctrl) (β sub) hbits
    let b_top := UnsignedGivens.bilinearRowBit idxTop row (β w_ctrl) (β sub) hbits
    let y := UnsignedGivens.localIdx rCat β
    let y_out := UnsignedGivens.signedAddModPerm B a_lo (UnsignedGivens.bilinearRowLo_lt B row
      (β w_ctrl) (β sub)
      hbits) (β w_p) y
    (topZeroAffineLac2KickRef hB idxTop idxMid row w_ctrl sub w_v rHot' rCat a0 rC w_p hd
      hdk).eval.1.mulVec (UnsignedGivens.ket β) = UnsignedGivens.rawPhaseStepVal B a_lo b_mid b_top
        (β w_p) y •
      UnsignedGivens.ket (UnsignedGivens.writeReg β rCat (basisBits B y_out)) := by
  intro hbits a_lo b_mid b_top y y_out
  let bs := topZeroAffineTableBitSteps idxTop idxMid row w_ctrl w_v rHot' rCat a0 rC w_p hdk.hcv
    hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat hdk.hh_cat
    hdk.hctrl_a0 hdk.hv_a0 hdk.hh_a0 hdk.hctrl_C hdk.hv_C hdk.hh_C
  let v_val := β w_ctrl * β sub
  let u_val := β w_ctrl * (1 + β sub)
  let β₁ := Function.update (Function.update β w_v v_val) w_ctrl u_val
  have hβ₁_a0 : β₁ a0 = 0 := by
    dsimp [β₁]
    rw [Function.update_of_ne hdk.hctrl_a0.symm, Function.update_of_ne hdk.hv_a0.symm, ha0]
  have hβ₁_C0 (j : Fin (B - 1)) : β₁ (rC j) = 0 := by
    dsimp [β₁]
    rw [Function.update_of_ne (hdk.hctrl_C j).symm, Function.update_of_ne (hdk.hv_C j).symm, hC0 j]
  have hβ₁_wp : β₁ w_p = β w_p := by
    dsimp [β₁]
    rw [Function.update_of_ne hdk.hctrl_wp.symm, Function.update_of_ne hdk.hv_wp.symm]
  have hβ₁_cat : UnsignedGivens.localIdx rCat β₁ = y :=
    localIdx_eq_of_forall rCat rCat β₁ β fun i ↦ by
      dsimp [β₁]
      rw [Function.update_of_ne (hdk.hctrl_cat i).symm, Function.update_of_ne (hdk.hv_cat i).symm]
  have hβ₁_u : β₁ w_ctrl = u_val := Function.update_self _ _ _
  have hβ₁_v : β₁ w_v = v_val := by dsimp [β₁]
                                    rw [Function.update_of_ne hdk.hcv.symm, Function.update_self]
  have hβ₁_hot : extendHot0 (fun g : Fin G' ↦ β₁ (rHot' g)) = hbits :=
    congrArg extendHot0 (funext fun g ↦ by
      dsimp [β₁]
      rw [Function.update_of_ne (hdk.hh_ctrl g), Function.update_of_ne (hdk.hh_v g)])
  have hk_in := topZeroRawUnsignedPhaseKickRef_ket_of_zero hB rCat a0 rC w_p hd bs β₁ hβ₁_a0 hβ₁_C0
  dsimp only at hk_in
  have hlo_eq : UnsignedGivens.bitSeqVal (bs.bitLo β₁) = a_lo := by
    dsimp [bs, topZeroAffineTableBitSteps, a_lo, UnsignedGivens.bilinearRowLo]
    congr 1
    funext j
    rw [hβ₁_u, hβ₁_v, hβ₁_hot]
  have hmid_eq : (bs.bitMid β₁).val = b_mid := by
    dsimp [bs, topZeroAffineTableBitSteps, b_mid, UnsignedGivens.bilinearRowBit]
    rw [hβ₁_u, hβ₁_v, hβ₁_hot]
  have htop_eq : (bs.bitTop β₁).val = b_top := by
    dsimp [bs, topZeroAffineTableBitSteps, b_top, UnsignedGivens.bilinearRowBit]
    rw [hβ₁_u, hβ₁_v, hβ₁_hot]
  have hperm_eq : UnsignedGivens.signedAddModPerm B (UnsignedGivens.bitSeqVal (bs.bitLo β₁))
    (UnsignedGivens.bitSeqVal_lt _)
      (β₁ w_p) (UnsignedGivens.localIdx rCat β₁) = y_out := by
    dsimp only [y_out]
    rw [signedAddModPerm_congr hlo_eq, hβ₁_wp, hβ₁_cat]
  unfold topZeroAffineLac2KickRef
  dsimp only [UnsignedGivens.inPlaceUVStep, UnsignedGivens.PhasedStep.wrapCircuit]
  simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_identity_mulVec,
    UnsignedGivens.evolve_TOFF_ket,
    UnsignedGivens.evolve_CNOT_ket]
  have hupd_eq : Function.update (Function.update β w_v (β w_v + β w_ctrl * β sub)) w_ctrl
      (Function.update β w_v (β w_v + β w_ctrl * β sub) w_ctrl + Function.update β w_v (β w_v + β
      w_ctrl * β sub) w_v) = β₁ := by
    dsimp only [β₁, u_val, v_val]
    rw [hv0, zero_add, Function.update_of_ne hdk.hcv, Function.update_self]
    congr 1
    ring
  rw [hupd_eq, hk_in, Matrix.mulVec_smul, UnsignedGivens.evolve_CNOT_ket, Matrix.mulVec_smul,
    UnsignedGivens.evolve_TOFF_ket, hperm_eq, hlo_eq, hmid_eq, htop_eq, hβ₁_wp, hβ₁_cat]
  congr 1
  apply congrArg UnsignedGivens.ket
  have hc_nr : w_ctrl ∉ Set.range rCat.wires := fun ⟨i, hi⟩ ↦ hdk.hctrl_cat i hi.symm
  have hv_nr : w_v ∉ Set.range rCat.wires := fun ⟨i, hi⟩ ↦ hdk.hv_cat i hi.symm
  have hs_nr : sub ∉ Set.range rCat.wires := fun ⟨i, hi⟩ ↦ hdk.hsub_cat i hi.symm
  let β₂ := UnsignedGivens.writeReg β₁ rCat (basisBits B y_out)
  have hβ₂_u : β₂ w_ctrl = u_val := by dsimp [β₂]
                                       rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hc_nr,
                                         hβ₁_u]
  have hβ₂_v : β₂ w_v = v_val := by dsimp [β₂]
                                    rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hv_nr,
                                      hβ₁_v]
  have hβ₂_sub : β₂ sub = β sub := by
    dsimp [β₂, β₁]
    rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hs_nr, Function.update_of_ne hdk.hcs.symm,
      Function.update_of_ne hdk.hsv]
  have hrest_u : u_val + v_val = β w_ctrl := by
    dsimp [u_val, v_val]
    have hr : β w_ctrl * (1 + β sub) + β w_ctrl * β sub =
        β w_ctrl + (β w_ctrl * β sub + β w_ctrl * β sub) := by ring
    rw [hr, UnsignedGivens.zmod2_add_self, add_zero]
  have hrest_v : v_val + β w_ctrl * β sub = β w_v := by dsimp [v_val]
                                                        rw [UnsignedGivens.zmod2_add_self, hv0]
  change Function.update (Function.update β₂ w_ctrl (β₂ w_ctrl + β₂ w_v)) w_v (Function.update β₂
      w_ctrl (β₂ w_ctrl + β₂ w_v) w_v + Function.update β₂ w_ctrl (β₂ w_ctrl + β₂ w_v) w_ctrl *
      Function.update β₂ w_ctrl (β₂ w_ctrl + β₂ w_v) sub) = _
  rw [hβ₂_u, hβ₂_v, hrest_u, Function.update_of_ne hdk.hcv.symm, Function.update_self,
    Function.update_of_ne hdk.hcs.symm, hβ₂_v, hβ₂_sub, hrest_v]
  funext w
  by_cases hwv : w = w_v
  · subst hwv
    rw [Function.update_self, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hv_nr]
  · rw [Function.update_of_ne hwv]
    by_cases hwc : w = w_ctrl
    · subst hwc
      rw [Function.update_self, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hc_nr]
    · rw [Function.update_of_ne hwc]
      by_cases hwr : w ∈ Set.range rCat.wires
      · obtain ⟨i, rfl⟩ := hwr
        dsimp [β₂]
        rw [UnsignedGivens.writeReg_apply_reg, UnsignedGivens.writeReg_apply_reg]
      · dsimp [β₂, β₁]
        rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwr,
          UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _
          hwr, Function.update_of_ne hwc, Function.update_of_ne hwv]
attribute [local irreducible] topZeroAffineLac2KickDyn topZeroAffineLac2KickRef
theorem ne_reg_idx {m n : ℕ} (r : QRegister m n) {a b : Fin m} (h : a.val ≠ b.val) : r a ≠ r b :=
  fun e ↦ h (congrArg Fin.val (r.wires.injective e))
theorem ne_reg_slice {m s k n : ℕ} (r : QRegister m n) (hs : s + k ≤ m) (a : Fin m) (j : Fin k) (h :
    a.val ≠ s + j.val) : r a ≠ (r.slice s k hs) j := by rw [QRegister.slice_apply]
                                                        exact ne_reg_idx r h
theorem topZeroPlaneKickDisj {n N k_ctrl G' m : ℕ} (p : ℕ) (hp : p + 1 < N) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl)
    (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac :
    (rSpin.concat rCtrl hsc).DisjointWires rCat) (hdisj : ((rSpin.concat rCtrl hsc).concat rCat
    hac).DisjointWires rWork) :
    let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
    let a0 := rWork ⟨0, by omega⟩
    let rC := rWork.slice 1 10 (by omega)
    TopZeroGidneyDisjoint rCat a0 rC (rPair 0) ∧
      TopZeroAffineKickDisjoint (rPair 1) (rCtrl subIdx) (rWork ⟨11, by omega⟩)
        (rCtrl.compose selHot') rCat a0 rC (rPair 0) :=
  ⟨{ ne_cat_a0 := fun i ↦ UnsignedGivens.ne_cat_work hsc hac hdisj i ⟨0, by omega⟩
     disj_cat_C := QRegister.disjoint_iff.mpr fun i _ ↦ by rw [QRegister.slice_apply]
                                                           exact UnsignedGivens.ne_cat_work hsc hac
                                                             hdisj i _
     ne_a0_C := fun j ↦ ne_reg_slice rWork _ _ j (by
       dsimp
       omega)
     ne_cat_wp := fun i ↦ (UnsignedGivens.ne_spin_cat hsc hac ⟨p, by omega⟩ i).symm
     ne_a0_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p, by omega⟩ ⟨0, by omega⟩).symm
     ne_C_wp := fun _ ↦ by rw [QRegister.slice_apply]
                           exact (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p, by omega⟩ _).symm },
   { hcs := UnsignedGivens.ne_spin_ctrl hsc ⟨p + 1, hp⟩ subIdx
     hcv := UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p + 1, hp⟩ ⟨11, by omega⟩
     hsv := UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨11, by omega⟩
     hh_ctrl := fun g ↦ (UnsignedGivens.ne_spin_ctrl hsc ⟨p + 1, hp⟩ (selHot' g)).symm
     hh_v := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨11, by omega⟩
     hctrl_wp := fun h ↦ by have hv := congrArg Fin.val (rSpin.wires.injective h)
                            simp [GivensOps.pairAdj] at hv
     hv_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p, by omega⟩ ⟨11, by omega⟩).symm
     hh_wp := fun g ↦ (UnsignedGivens.ne_spin_ctrl hsc ⟨p, by omega⟩ (selHot' g)).symm
     hctrl_cat := fun i ↦ UnsignedGivens.ne_spin_cat hsc hac ⟨p + 1, hp⟩ i
     hv_cat := fun i ↦ (UnsignedGivens.ne_cat_work hsc hac hdisj i ⟨11, by omega⟩).symm
     hh_cat := fun g i ↦ UnsignedGivens.ne_ctrl_cat hsc hac (selHot' g) i
     hsub_cat := fun i ↦ UnsignedGivens.ne_ctrl_cat hsc hac subIdx i
     hctrl_a0 := UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p + 1, hp⟩ ⟨0, by omega⟩
     hv_a0 := ne_reg_idx rWork (by
       dsimp
       omega)
     hh_a0 := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨0, by omega⟩
     hsub_a0 := UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨0, by omega⟩
     hctrl_C := fun _ ↦ by rw [QRegister.slice_apply]
                           exact UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p + 1, hp⟩ _
     hv_C := fun j ↦ ne_reg_slice rWork _ _ j (by
       dsimp
       omega)
     hh_C := fun g _ ↦ by rw [QRegister.slice_apply]
                          exact UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) _
     hsub_C := fun _ ↦ by rw [QRegister.slice_apply]
                          exact UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx _ }⟩
/-- Zero-top-ancilla `13`-bit `Lac = 2` plane phase kick (`146 T = 102 + 4 * 11`, `12 ≤ m`). -/
def topZeroLac2PlaneKickDyn {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (p : ℕ) (hp : p + 1 < N)
    (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc :
    rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat :
    QRegister 11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl
    hsc).DisjointWires rCat) (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires
    rWork) : DynamicCircuit Var n :=
  let hdPair := topZeroPlaneKickDisj p hp rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
  topZeroAffineLac2KickDyn v (by decide : 2 ≤ 11) 12 11 row (rPair 1) (rCtrl subIdx)
    (rWork ⟨11, by omega⟩) (rCtrl.compose selHot') rCat (rWork ⟨0, by omega⟩)
    (rWork.slice 1 10 (by omega)) (rPair 0) hdPair.1 hdPair.2
/-- Zero-top-ancilla `Lac = 2` forward Givens plane `DynamicCircuit` (`146 T`, `0 TOFF`). -/
def topZeroLac2PlanePosDyn {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (p : ℕ) (hp : p + 1 < N)
  (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc :
  rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister
  11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
  (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) : DynamicCircuit Var n :=
  UnsignedGivens.framedPlanePosDyn p hp rSpin (topZeroLac2PlaneKickDyn v p hp row rSpin rCtrl hsc
    selHot'
  subIdx rCat rWork hm hac hdisj)
/-- Zero-top-ancilla `Lac = 2` backward Givens plane `DynamicCircuit` (`146 T`, `0 TOFF`). -/
def topZeroLac2PlaneNegDyn {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (p : ℕ) (hp : p + 1 < N)
  (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc :
  rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister
  11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
  (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) : DynamicCircuit Var n :=
  UnsignedGivens.framedPlaneNegDyn p hp rSpin (topZeroLac2PlaneKickDyn v p hp row rSpin rCtrl hsc
    selHot'
  subIdx rCat rWork hm hac hdisj)
theorem ctrlMuxCatalytic_topZeroLac2PlaneKickDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n N
    k_ctrl G' m : ℕ} [NeZero (2 ^ n)] (v : Var) (p : ℕ) (hp : p + 1 < N) (row : Fin (G' + 1) → Bool
    → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork :
    QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) (hdisj :
    ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
    let hpc := UnsignedGivens.disj_sub_ctrl hsc (GivensOps.pairAdj N p hp)
    let hac_pair := UnsignedGivens.disj_sub_cat hsc hac (GivensOps.pairAdj N p hp)
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦ 2 * π * (affinePlaneEffK row selHot'
      subIdx b₁ c : ℝ) / (2 : ℝ) ^ (11 + 3)
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rPair rCat (OneHotMux.disj_sys_cat_of
      hpc
      hac_pair) rCtrl (OneHotMux.disj_sysCat_ctrl_of hpc hac_pair) rWork (fun c ↦
      UnsignedGivens.phaseDiagUnitary (UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c))
        (UnsignedGivens.genKick4_unit (α_fn 0 c)
      (α_fn 1 c))) (topZeroLac2PlaneKickDyn v p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm
      hac hdisj) := by
  intro rPair hpc hac_pair α_fn
  let hdPair := topZeroPlaneKickDisj p hp rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  have hclean := realizesCleanRef_topZeroAffineLac2KickDyn_widen v (by decide : 2 ≤ 11) 12 11 row
    (rPair 1) (rCtrl subIdx) (rWork ⟨11, by omega⟩) (rCtrl.compose selHot') rCat
    (rWork ⟨0, by omega⟩) (rWork.slice 1 10 (by omega)) (rPair 0) hdPair.1 hdPair.2 rWork
    (QRegister.mem_image rWork _ |>.mpr ⟨⟨11, by omega⟩, rfl⟩)
    (QRegister.mem_image rWork _ |>.mpr ⟨⟨0, by omega⟩, rfl⟩)
    (UnsignedGivens.slice_image_subset rWork (by omega)) (UnsignedGivens.ne_cat_work hsc hac hdisj)
  exact OneHotMux.CtrlMuxCatalyticWith.ofRawKick rPair rCat (OneHotMux.disj_sys_cat_of hpc hac_pair)
    rCtrl
    (OneHotMux.disj_sysCat_ctrl_of hpc hac_pair) rWork _ _ hclean (fun b₁ c ↦
      UnsignedGivens.bilinearRowLo 11
    row b₁ (basisBits k_ctrl c subIdx) (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
      (fun _ _ ↦
    UnsignedGivens.bilinearRowLo_lt _ _ _ _ _) (fun b₁ c ↦ UnsignedGivens.bilinearRowBit 11 row b₁
      (basisBits k_ctrl
    c subIdx) (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c))) (fun b₁ c ↦
      UnsignedGivens.bilinearRowBit 12 row
    b₁ (basisBits k_ctrl c subIdx) (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c))) (fun _ _ ↦
    UnsignedGivens.bilinearRowBit_lt _ _ _ _ _) (fun _ _ ↦ UnsignedGivens.bilinearRowBit_lt _ _ _ _
      _)
    (fun β h0 ↦ by
      have hk := topZeroAffineLac2KickRef_ket_of_zero (by decide : 2 ≤ 11) 12 11 row (rPair 1)
        (rCtrl subIdx) (rWork ⟨11, by omega⟩) (rCtrl.compose selHot') rCat
        (rWork ⟨0, by omega⟩) (rWork.slice 1 10 (by omega)) (rPair 0) hdPair.1 hdPair.2 β
        (h0 ⟨11, by omega⟩) (h0 ⟨0, by omega⟩)
        (fun _ ↦ by
          rw [QRegister.slice_apply]
          exact h0 _)
      dsimp only at hk ⊢
      have hsub : β (rCtrl subIdx) = basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) subIdx :=
        (congrFun
        (UnsignedGivens.basisBits_symm_eq (fun j ↦ β (rCtrl j))) subIdx).symm
      have hhot : extendHot0 (fun g : Fin G' ↦ β ((rCtrl.compose selHot') g)) = extendHot0
        (UnsignedGivens.ctrlHotBits selHot' (UnsignedGivens.localIdx rCtrl β)) :=
          congrArg extendHot0
        (UnsignedGivens.compose_hot_bits_eq rCtrl selHot' β)
      have hlo_eq : UnsignedGivens.bilinearRowLo 11 row (β (rPair 1)) (β (rCtrl subIdx)) (extendHot0
        (fun g :
          Fin G' ↦ β ((rCtrl.compose selHot') g))) = UnsignedGivens.bilinearRowLo 11 row (β
            (rPair 1))
          (basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) subIdx) (extendHot0
            (UnsignedGivens.ctrlHotBits selHot'
          (UnsignedGivens.localIdx rCtrl β))) := by rw [hsub, hhot]
      rw [hk, signedAddModPerm_congr hlo_eq]
      · simp only [hsub, hhot]
      · exact UnsignedGivens.bilinearRowLo_lt _ _ _ _ _)
theorem ctrlMuxCatalytic_topZeroLac2PlanePosDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n N
    k_ctrl G' m : ℕ} [NeZero (2 ^ n)] (v : Var) (p : ℕ) (hp : p + 1 < N) (row : Fin (G' + 1) → Bool
    → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork :
    QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) (hdisj :
    ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦ 2 * π * (affinePlaneEffK row selHot'
      subIdx b₁ c : ℝ) / (2 : ℝ) ^ 14
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin
      rCat (OneHotMux.disj_sys_cat_of hsc hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork
        (fun c ↦
      (GivensOps.pairAdj N p hp).embedUnitary (UnsignedGivens.genGivensPosUnitary (α_fn 0 c)
        (α_fn 1 c)))
      (topZeroLac2PlanePosDyn v p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj) :=
      OneHotMux.ctrlMuxCatalytic_framedPlanePos (phaseGradientFineLow 11 3) p hp rSpin rCtrl hsc
        rCat
      rWork hac hdisj (ctrlMuxCatalytic_topZeroLac2PlaneKickDyn v p hp row rSpin rCtrl hsc selHot'
      subIdx rCat rWork hm hac hdisj)
theorem ctrlMuxCatalytic_topZeroLac2PlaneNegDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n N
    k_ctrl G' m : ℕ} [NeZero (2 ^ n)] (v : Var) (p : ℕ) (hp : p + 1 < N) (row : Fin (G' + 1) → Bool
    → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork :
    QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) (hdisj :
    ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦ 2 * π * (affinePlaneEffK row selHot'
      subIdx b₁ c : ℝ) / (2 : ℝ) ^ 14
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin
      rCat (OneHotMux.disj_sys_cat_of hsc hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork
        (fun c ↦
      (GivensOps.pairAdj N p hp).embedUnitary (UnsignedGivens.genGivensNegUnitary (α_fn 0 c)
        (α_fn 1 c)))
      (topZeroLac2PlaneNegDyn v p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj) :=
      OneHotMux.ctrlMuxCatalytic_framedPlaneNeg (phaseGradientFineLow 11 3) p hp rSpin rCtrl hsc
        rCat
      rWork hac hdisj (ctrlMuxCatalytic_topZeroLac2PlaneKickDyn v p hp row rSpin rCtrl hsc selHot'
      subIdx rCat rWork hm hac hdisj)
theorem topZeroApexKickDisj {n N k_ctrl G' m : ℕ} (hN : 1 < N) (rSpin : QRegister N n) (rCtrl :
    QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl) (subIdx :
    Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat
    rCtrl hsc).DisjointWires rCat) (hdisj : ((rSpin.concat rCtrl hsc).concat rCat
    hac).DisjointWires rWork) :
    let rPair0 := rSpin.compose (GivensOps.pairAdj N 0 hN)
    let rCat10 := rCat.compose (locRight 1 10)
    let a0 := rWork ⟨0, by omega⟩
    let rC := rWork.slice 1 9 (by omega)
    TopZeroGidneyDisjoint rCat10 a0 rC (rPair0 0) ∧
      TopZeroAffineKickDisjoint (rWork ⟨11, by omega⟩) (rCtrl subIdx)
        (rWork ⟨10, by omega⟩) (rCtrl.compose selHot') rCat10 a0 rC (rPair0 0) :=
  ⟨{ ne_cat_a0 := fun i ↦ UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) ⟨0, by omega⟩
     disj_cat_C := QRegister.disjoint_iff.mpr fun i _ ↦ by
       rw [QRegister.slice_apply]
       exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) _
     ne_a0_C := fun j ↦ ne_reg_slice rWork _ _ j (by
       dsimp
       omega)
     ne_cat_wp := fun i ↦ (UnsignedGivens.ne_spin_cat hsc hac ⟨0, by omega⟩ (locRight 1 10 i)).symm
     ne_a0_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ ⟨0, by omega⟩).symm
     ne_C_wp := fun _ ↦ by rw [QRegister.slice_apply]
                           exact (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ _).symm },
   { hcs := (UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨11, by omega⟩).symm
     hcv := ne_reg_idx rWork (by
       dsimp
       omega)
     hsv := UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨10, by omega⟩
     hh_ctrl := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨11, by omega⟩
     hh_v := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨10, by omega⟩
     hctrl_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ ⟨11, by omega⟩).symm
     hv_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ ⟨10, by omega⟩).symm
     hh_wp := fun g ↦ (UnsignedGivens.ne_spin_ctrl hsc ⟨0, by omega⟩ (selHot' g)).symm
     hctrl_cat := fun i ↦
       (UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) ⟨11, by omega⟩).symm
     hv_cat := fun i ↦
       (UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) ⟨10, by omega⟩).symm
     hh_cat := fun g i ↦ UnsignedGivens.ne_ctrl_cat hsc hac (selHot' g) (locRight 1 10 i)
     hsub_cat := fun i ↦ UnsignedGivens.ne_ctrl_cat hsc hac subIdx (locRight 1 10 i)
     hctrl_a0 := ne_reg_idx rWork (by
       dsimp
       omega)
     hv_a0 := ne_reg_idx rWork (by
       dsimp
       omega)
     hh_a0 := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨0, by omega⟩
     hsub_a0 := UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨0, by omega⟩
     hctrl_C := fun j ↦ ne_reg_slice rWork _ _ j (by
       dsimp
       omega)
     hv_C := fun j ↦ ne_reg_slice rWork _ _ j (by
       dsimp
       omega)
     hh_C := fun g _ ↦ by rw [QRegister.slice_apply]
                          exact UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) _
     hsub_C := fun _ ↦ by rw [QRegister.slice_apply]
                          exact UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx _ }⟩
/-- Zero-top-ancilla `Lac = 2` Wire-Controlled fused apex (`138 T = 98 + 4 * 10`, `0 TOFF`, `12 ≤
m`). -/
def topZeroLac2ApexCtrlDyn {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (hN : 1 < N) (row0 : Fin (G'
    + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires
    rCtrl) (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat :
    QRegister 11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl
    hsc).DisjointWires rCat) (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires
    rWork) : DynamicCircuit Var n :=
  let hdAp := topZeroApexKickDisj hN rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  let w_act1 := rWork ⟨11, by omega⟩
  UnsignedGivens.framedCtrlApexDyn v hN rSpin rCtrl hsc actIdx w_act1
    (UnsignedGivens.ne_ctrl_work hsc hac hdisj actIdx ⟨11, by omega⟩)
    (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨1, hN⟩ ⟨11, by omega⟩)
    (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ ⟨11, by omega⟩)
    (topZeroAffineLac2KickDyn v (by decide : 2 ≤ 10) 12 10 row0 w_act1 (rCtrl subIdx)
      (rWork ⟨10, by omega⟩) (rCtrl.compose selHot') (rCat.compose (locRight 1 10))
      (rWork ⟨0, by omega⟩) (rWork.slice 1 9 (by omega))
      ((rSpin.compose (GivensOps.pairAdj N 0 hN)) 0) hdAp.1 hdAp.2)
theorem ctrlMuxCatalytic_topZeroLac2ApexCtrlDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n N
    k_ctrl G' m : ℕ} [NeZero (2 ^ n)] (v : Var) (hN : 1 < N) (row0 : Fin (G' + 1) → Bool → ℕ)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (actIdx
    : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let z0 : Fin N := ⟨0, by omega⟩
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦ 2 * π * (affineApexEffK row0 selHot'
      subIdx (basisBits k_ctrl c actIdx * b₁) c : ℝ) / (2 : ℝ) ^ 13
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin rCat (OneHotMux.disj_sys_cat_of
      hsc
      hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork (fun c ↦ (if basisBits k_ctrl c
        actIdx =
      0 then 1 else (QRegister.singleton z0).embedUnitary Qubit.Z) * (GivensOps.pairAdj N 0
      hN).embedUnitary (UnsignedGivens.genGivensPosUnitary (α_fn 0 c) (α_fn 1 c)))
        (topZeroLac2ApexCtrlDyn v
      hN row0 rSpin rCtrl hsc actIdx selHot' subIdx rCat rWork hm hac hdisj) := by
  intro z0 α_fn
  let hdAp := topZeroApexKickDisj hN rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  let w_act1 := rWork ⟨11, by omega⟩
  let w_v := rWork ⟨10, by omega⟩
  let a0 := rWork ⟨0, by omega⟩
  let rPair0 := rSpin.compose (GivensOps.pairAdj N 0 hN)
  let rCat10 := rCat.compose (locRight 1 10)
  let rHot' := rCtrl.compose selHot'
  let rC := rWork.slice 1 9 (by omega)
  let rWorkIn := rWork.slice 0 11 (by omega)
  have hv_mem : w_v ∈ rWorkIn.image := QRegister.mem_image rWorkIn _ |>.mpr
    ⟨⟨10, by decide⟩, by simp [rWorkIn, w_v]⟩
  have ha0_mem : a0 ∈ rWorkIn.image := QRegister.mem_image rWorkIn _ |>.mpr
    ⟨⟨0, by decide⟩, by simp [rWorkIn, a0]⟩
  have hC_sub : rC.image ⊆ rWorkIn.image := fun q hq ↦ by
    obtain ⟨i, rfl⟩ := QRegister.mem_image rC q |>.mp hq
    refine QRegister.mem_image rWorkIn _ |>.mpr ⟨⟨1 + i.val, by omega⟩, ?_⟩
    simp only [rWorkIn, rC, QRegister.slice_apply]
    congr 1
    ext
    dsimp
    omega
  have hclean := realizesCleanRef_topZeroAffineLac2KickDyn_widen v (by decide : 2 ≤ 10) 12 10 row0
    w_act1 (rCtrl subIdx) w_v rHot' rCat10 a0 rC (rPair0 0) hdAp.1 hdAp.2 rWorkIn hv_mem
    ha0_mem hC_sub (fun i _ ↦ by
      rw [QRegister.slice_apply]
      exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) _)
  have hw1_not : w_act1 ∉ rWorkIn.image := by rw [QRegister.mem_image]
                                              rintro ⟨j, hj⟩
                                              dsimp only [rWorkIn, w_act1] at hj
                                              rw [QRegister.slice_apply] at hj
                                              have hv := congrArg Fin.val (rWork.wires.injective hj)
                                              dsimp at hv
                                              omega
  exact OneHotMux.ctrlMuxCatalytic_framedCtrlApex v hN rSpin rCtrl hsc actIdx rCat rWork hac hdisj
    w_act1 (QRegister.mem_image rWork _ |>.mpr ⟨⟨11, by omega⟩, rfl⟩) rWorkIn
    (UnsignedGivens.slice_image_subset rWork (by omega)) hw1_not _ _ hclean
      (topZeroAffineLac2KickRef_phasedPerm (by decide : 2 ≤ 10) 12 10 row0 w_act1 (rCtrl subIdx)
      w_v rHot' rCat10 a0 rC (rPair0 0) hdAp.1 hdAp.2) (fun qc c ↦ UnsignedGivens.bilinearRowLo 10
        row0 qc
      (basisBits k_ctrl c subIdx) (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c))) (fun _ _ ↦
      UnsignedGivens.bilinearRowLo_lt _ _ _ _ _) (fun qc c ↦ UnsignedGivens.bilinearRowBit 10 row0
        qc (basisBits
      k_ctrl c subIdx) (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c))) (fun qc c ↦
        UnsignedGivens.bilinearRowBit
      12 row0 qc (basisBits k_ctrl c subIdx) (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
        (fun _ _ ↦
      UnsignedGivens.bilinearRowBit_lt _ _ _ _ _) (fun _ _ ↦ UnsignedGivens.bilinearRowBit_lt _ _ _
        _ _)
    (fun β h0 ↦ by
      have hv0 : β w_v = 0 := by simpa [rWorkIn, w_v] using h0 ⟨10, by decide⟩
      have ha0 : β a0 = 0 := by simpa [rWorkIn, a0] using h0 ⟨0, by decide⟩
      have hC0 (j : Fin 9) : β (rC j) = 0 := by have h := h0 ⟨1 + j.val, by omega⟩
                                                dsimp only [rWorkIn, rC] at h ⊢
                                                rw [QRegister.slice_apply] at h ⊢
                                                convert h using 2
                                                congr 1
                                                ext
                                                dsimp
                                                omega
      have hk := topZeroAffineLac2KickRef_ket_of_zero (by decide : 2 ≤ 10) 12 10 row0 w_act1 (rCtrl
        subIdx) w_v rHot' rCat10 a0 rC (rPair0 0) hdAp.1 hdAp.2 β hv0 ha0 hC0
      dsimp only at hk ⊢
      have hsub : β (rCtrl subIdx) = basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) subIdx :=
        (congrFun
        (UnsignedGivens.basisBits_symm_eq (fun j ↦ β (rCtrl j))) subIdx).symm
      have hhot : extendHot0 (fun g : Fin G' ↦ β (rHot' g)) = extendHot0 (UnsignedGivens.ctrlHotBits
        selHot'
        (UnsignedGivens.localIdx rCtrl β)) := congrArg extendHot0
          (UnsignedGivens.compose_hot_bits_eq rCtrl selHot' β)
      have hlo_eq : UnsignedGivens.bilinearRowLo 10 row0 (β w_act1) (β (rCtrl subIdx)) (extendHot0
        (fun g :
          Fin G' ↦ β (rHot' g))) = UnsignedGivens.bilinearRowLo 10 row0 (β w_act1) (basisBits k_ctrl
          (UnsignedGivens.localIdx rCtrl β) subIdx) (extendHot0 (UnsignedGivens.ctrlHotBits selHot'
            (UnsignedGivens.localIdx
          rCtrl β))) := by rw [hsub, hhot]
      rw [hk, signedAddModPerm_congr hlo_eq]
      · dsimp only [rPair0, rCat10]
        simp only [hsub, hhot]
      · exact UnsignedGivens.bilinearRowLo_lt _ _ _ _ _)
/-- Zero-top-ancilla `(N - 1)`-plane Wire-Controlled `Lac = 2` cascade (`12 ≤ m`, `0 TOFF`, `2 * (N
- 2) * 146 + 138` `T`). -/
def topZeroLac2CascadeCtrlDyn {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (hN : 1 < N) (table : Fin
  (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc :
  rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin
  k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl
  hsc).DisjointWires rCat) (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
  : DynamicCircuit Var n := UnsignedGivens.genericCascadeDyn hN (fun p hp ↦ topZeroLac2PlanePosDyn v
    p hp
  (fun g b ↦ table g b ⟨p, by omega⟩) rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj) (fun p
  hp ↦ topZeroLac2PlaneNegDyn v p hp (fun g b ↦ table g b ⟨p, by omega⟩) rSpin rCtrl hsc selHot'
  subIdx rCat rWork hm hac hdisj) (topZeroLac2ApexCtrlDyn v hN (fun g b ↦ table g b ⟨0, by omega⟩)
  rSpin rCtrl hsc actIdx selHot' subIdx rCat rWork hm hac hdisj)
@[simp] theorem count_topZeroLac2CascadeCtrlDyn_toff {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var)
    (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n) (rCtrl :
    QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl) (selHot' : QRegister
    G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 12 ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) (hdisj : ((rSpin.concat rCtrl hsc).concat
    rCat hac).DisjointWires rWork) : (topZeroLac2CascadeCtrlDyn v hN table rSpin rCtrl hsc actIdx
    selHot' subIdx rCat rWork hm hac hdisj).count .TOFF = 0 := by
  refine UnsignedGivens.count_genericCascadeDyn_toff hN _ _ _ (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) ?_
  · rw [topZeroLac2PlanePosDyn, UnsignedGivens.count_framedPlanePosDyn_toff]
    simp [topZeroLac2PlaneKickDyn]
  · rw [topZeroLac2PlaneNegDyn, UnsignedGivens.count_framedPlaneNegDyn_toff]
    simp [topZeroLac2PlaneKickDyn]
  · rw [topZeroLac2ApexCtrlDyn, UnsignedGivens.count_framedCtrlApexDyn_toff]
    simp
@[simp] theorem count_topZeroLac2CascadeCtrlDyn_t {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (hN :
    1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister
    k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl) (selHot' : QRegister G'
    k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac
    : (rSpin.concat rCtrl hsc).DisjointWires rCat) (hdisj : ((rSpin.concat rCtrl hsc).concat rCat
    hac).DisjointWires rWork) : (topZeroLac2CascadeCtrlDyn v hN table rSpin rCtrl hsc actIdx selHot'
    subIdx rCat rWork hm hac hdisj).count .T = 2 * (N - 2) * 146 + 138 := by
  refine UnsignedGivens.count_genericCascadeDyn_t hN _ _ _ 146 138 (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) ?_
  · rw [topZeroLac2PlanePosDyn, UnsignedGivens.count_framedPlanePosDyn_t]
    simp [topZeroLac2PlaneKickDyn]
  · rw [topZeroLac2PlaneNegDyn, UnsignedGivens.count_framedPlaneNegDyn_t]
    simp [topZeroLac2PlaneKickDyn]
  · rw [topZeroLac2ApexCtrlDyn, UnsignedGivens.count_framedCtrlApexDyn_t]
    simp
theorem ctrlMuxCatalytic_topZeroLac2CascadeCtrlDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n N
    k_ctrl G' m : ℕ} [NeZero (2 ^ n)] (v : Var) (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N →
    ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11
    n) (rWork : QRegister m n) (hm : 12 ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin rCat (OneHotMux.disj_sys_cat_of
      hsc
    hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork
    (affineUnsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot' subIdx)
    (topZeroLac2CascadeCtrlDyn v hN table rSpin rCtrl hsc actIdx selHot' subIdx rCat rWork hm hac
    hdisj) := by
  let α_pl : ZMod 2 → ℕ → Fin (2 ^ k_ctrl) → ℝ := fun b₁ p c ↦ if hp : p + 1 < N then 2 * π *
    (affinePlaneEffK (fun g b ↦ table g b ⟨p, by omega⟩) selHot' subIdx b₁ c : ℝ) / (2 : ℝ) ^ 14
    else 0
  exact OneHotMux.ctrlMuxCatalytic_genericCascadeDyn hN (phaseGradientFineLow 11 3) rSpin rCtrl hsc
    rCat rWork hac hdisj _ _ _ (α_pl 0) (α_pl 1) _ (fun p hp ↦
    (ctrlMuxCatalytic_topZeroLac2PlanePosDyn v p hp _ rSpin rCtrl hsc selHot' subIdx
      rCat rWork hm hac hdisj).congrUnitary (funext fun c ↦ by simp only [α_pl, hp, ↓reduceDIte]))
    (fun p hp ↦ (ctrlMuxCatalytic_topZeroLac2PlaneNegDyn v p hp _ rSpin rCtrl hsc selHot' subIdx
      rCat rWork hm hac hdisj).congrUnitary (funext fun c ↦ by simp only [α_pl, hp, ↓reduceDIte]))
    (ctrlMuxCatalytic_topZeroLac2ApexCtrlDyn v hN _ rSpin rCtrl hsc actIdx selHot' subIdx rCat
      rWork hm hac hdisj)
attribute [irreducible] topZeroLac2PlaneKickDyn topZeroLac2PlanePosDyn topZeroLac2PlaneNegDyn
attribute [irreducible] topZeroLac2ApexCtrlDyn topZeroLac2CascadeCtrlDyn
/-- Packaged `11 ≤ m` (`d = 11`) `Lac = 2` cascade recycling `wHot0` (`0` extra `T`s). -/
def topZeroLac2CascadeCtrl11Dyn {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (hN : 1 < N) (table :
    Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n) (rCtrlTail : QRegister k_ctrl n) (hsc :
    rSpin.DisjointWires rCtrlTail) (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx :
    Fin k_ctrl) (wHot0 : Wire n) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 11 ≤ m) (hac
    : (rSpin.concat rCtrlTail hsc).DisjointWires rCat) (hWork0 : rWork.DisjointWires
    (QRegister.singleton wHot0)) (hdisjPlus : ((rSpin.concat rCtrlTail hsc).concat rCat
    hac).DisjointWires (rWork.concat (QRegister.singleton wHot0) hWork0)) : DynamicCircuit Var n :=
  let rHot' := rCtrlTail.compose selHot'
  have hne0 (g : Fin G') : rHot' g ≠ wHot0 := by
    simpa [rHot'] using UnsignedGivens.ne_ctrl_work hsc hac hdisjPlus (selHot' g) (Fin.natAdd m 0)
  let cClear0 := clearHot0Circuit rHot' wHot0 hne0
  .seq (.circuit cClear0) (.seq (topZeroLac2CascadeCtrlDyn v hN table rSpin rCtrlTail hsc actIdx
    selHot' subIdx rCat (rWork.concat (QRegister.singleton wHot0) hWork0) (by omega) hac hdisjPlus)
    (.circuit cClear0))
@[simp] theorem count_topZeroLac2CascadeCtrl11Dyn_toff {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var)
    (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n) (rCtrlTail :
    QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrlTail) (actIdx : Fin k_ctrl) (selHot' :
    QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (wHot0 : Wire n) (rCat : QRegister 11 n) (rWork :
    QRegister m n) (hm : 11 ≤ m) (hac : (rSpin.concat rCtrlTail hsc).DisjointWires rCat) (hWork0 :
    rWork.DisjointWires (QRegister.singleton wHot0)) (hdisjPlus : ((rSpin.concat rCtrlTail
    hsc).concat rCat hac).DisjointWires (rWork.concat (QRegister.singleton wHot0) hWork0)) :
    (topZeroLac2CascadeCtrl11Dyn v hN table rSpin rCtrlTail hsc actIdx selHot' subIdx wHot0 rCat
    rWork hm hac hWork0 hdisjPlus).count .TOFF = 0 := by simp [topZeroLac2CascadeCtrl11Dyn]
@[simp] theorem count_topZeroLac2CascadeCtrl11Dyn_t {Var : Type} {n N k_ctrl G' m : ℕ} (v : Var) (hN
    : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n) (rCtrlTail :
    QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrlTail) (actIdx : Fin k_ctrl) (selHot' :
    QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (wHot0 : Wire n) (rCat : QRegister 11 n) (rWork :
    QRegister m n) (hm : 11 ≤ m) (hac : (rSpin.concat rCtrlTail hsc).DisjointWires rCat) (hWork0 :
    rWork.DisjointWires (QRegister.singleton wHot0)) (hdisjPlus : ((rSpin.concat rCtrlTail
    hsc).concat rCat hac).DisjointWires (rWork.concat (QRegister.singleton wHot0) hWork0)) :
    (topZeroLac2CascadeCtrl11Dyn v hN table rSpin rCtrlTail hsc actIdx selHot' subIdx wHot0 rCat
    rWork hm hac hWork0 hdisjPlus).count .T = 2 * (N - 2) * 146 + 138 := by
  simp [topZeroLac2CascadeCtrl11Dyn]
theorem diagProjSimulates_topZeroLac2CascadeCtrl11Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N k_ctrl G' m : ℕ} [NeZero (2 ^ n)] (v : Var) (hN : 1 < N) (table : Fin (G' + 1) → Bool →
    Fin N → ℕ) (rSpin : QRegister N n) (rCtrlTail : QRegister k_ctrl n) (hsc : rSpin.DisjointWires
    rCtrlTail) (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (wHot0 :
    Wire n) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 11 ≤ m) (hac : (rSpin.concat
    rCtrlTail hsc).DisjointWires rCat) (hWork0 : rWork.DisjointWires (QRegister.singleton wHot0))
    (hdisjPlus : ((rSpin.concat rCtrlTail hsc).concat rCat hac).DisjointWires (rWork.concat
    (QRegister.singleton wHot0) hWork0)) :
    let rSC := rSpin.concat rCat (OneHotMux.disj_sys_cat_of hsc hac)
    let rHot' := rCtrlTail.compose selHot'
    let fullHot (β : BitAssignment n) : Fin (G' + 1) → ZMod 2 := Fin.cases (β wHot0) (fun g ↦ β
      (rHot' g))
    let S_valid (β : BitAssignment n) : Prop := (∃ g₀ : Fin (G' + 1), UnsignedGivens.IsOneHotBits g₀
      (fullHot
      β)) ∧ ∀ j : Fin m, β (rWork j) = 0
    ∃ wAff : Fin (2 ^ k_ctrl) → Unitary (2 ^ (N + 11)), DiagProjSimulates (ketPredProj S_valid)
      ((rSC.concat rCtrlTail (OneHotMux.disj_sysCat_ctrl_of hsc hac)).embedUnitary
      (UnsignedGivens.muxCtrlUnitary wAff)) (topZeroLac2CascadeCtrl11Dyn v hN table rSpin rCtrlTail
        hsc
      actIdx selHot' subIdx wHot0 rCat rWork hm hac hWork0 hdisjPlus) ∧ ∀ (c : Fin (2 ^ k_ctrl)) (ψ
      : Fin (2 ^ N) → ℂ), (wAff c).1 *ᵥ prodState ψ (phaseGradientFineLow 11 3) = prodState
      ((affineUnsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot' subIdx c).1 *ᵥ ψ)
      (phaseGradientFineLow 11 3) := by
  intro rSC rHot' fullHot S_valid
  let rWorkPlus := rWork.concat (QRegister.singleton wHot0) hWork0
  have hne0 (g : Fin G') : rHot' g ≠ wHot0 := by
    simpa [rHot', rWorkPlus] using UnsignedGivens.ne_ctrl_work hsc hac hdisjPlus (selHot' g)
      (Fin.natAdd m 0)
  let cClear0 := clearHot0Circuit rHot' wHot0 hne0
  obtain ⟨wAff, hwAff, hcatAff⟩ := ctrlMuxCatalytic_topZeroLac2CascadeCtrlDyn v hN table rSpin
    rCtrlTail hsc actIdx selHot' subIdx rCat rWorkPlus (by omega) hac hdisjPlus
  have hSimAff : DiagProjSimulates (rWorkPlus.basisOutcomeProjector 0) ((rSC.concat rCtrlTail
    (OneHotMux.disj_sysCat_ctrl_of hsc hac)).embedUnitary (UnsignedGivens.muxCtrlUnitary wAff))
    (topZeroLac2CascadeCtrlDyn v hN table rSpin rCtrlTail hsc actIdx selHot' subIdx rCat rWorkPlus
    (by omega) hac hdisjPlus) := DiagProjSimulates.ofGlobalCleanSimulates <|
    GlobalCleanSimulates.ofRealizesEmbedded (OneHotMux.disj_sysCatCtrl_work_of hsc hac hdisjPlus)
      hwAff
  have hClearSq : cClear0.eval * cClear0.eval = 1 := clearHot0Circuit_eval_mul_self rHot' wHot0
    hne0
  have hConj := hSimAff.conjSelfInv cClear0 hClearSq (fun β ↦ ⟨_, evolve_clearHot0Circuit_ket rHot'
    wHot0 hne0 β⟩)
  have hNotSC0 : wHot0 ∉ Set.range rSC.wires := by
    rintro ⟨sc, hsc0⟩
    revert hsc0
    refine Fin.addCases (fun i hsc0 ↦ ?_) (fun j hsc0 ↦ ?_) sc
    · exact UnsignedGivens.ne_spin_work hsc hac hdisjPlus i (Fin.natAdd m 0) (by
        simpa [rSC] using hsc0)
    · exact UnsignedGivens.ne_cat_work hsc hac hdisjPlus j (Fin.natAdd m 0) (by
        simpa [rSC] using hsc0)
  have hNotCtrl0 (j : Fin k_ctrl) : rCtrlTail j ≠ wHot0 := by
    simpa [rWorkPlus] using UnsignedGivens.ne_ctrl_work hsc hac hdisjPlus j (Fin.natAdd m 0)
  rw [clearHot0Circuit_conj_muxCtrlUnitary_eq rSC rCtrlTail (OneHotMux.disj_sysCat_ctrl_of hsc hac)
    selHot' wHot0 hNotSC0 hNotCtrl0 wAff] at hConj
  refine ⟨wAff, hConj.tighten ⟨S_valid, rfl⟩ ?_ ?_, hcatAff⟩
  · apply UnsignedGivens.matrix_ext_ket
    intro β
    classical
    rw [← Matrix.mulVec_mulVec]
    have hket_eq : @UnsignedGivens.ket n = @OneHotSimulates.ket n := rfl
    by_cases hS : S_valid β
    · have ⟨⟨g₀, hg₀⟩, hw0⟩ := hS
      let β₁ := Function.update β wHot0 (β wHot0 + (1 + ∑ g : Fin G', β (rHot' g)))
      have hk1 : cClear0.eval.1.mulVec (UnsignedGivens.ket β) = UnsignedGivens.ket β₁ :=
        evolve_clearHot0Circuit_ket
        rHot' wHot0 hne0 β
      have hP0 : (rWorkPlus.basisOutcomeProjector 0).mulVec (UnsignedGivens.ket β₁) =
        UnsignedGivens.ket β₁ := by
        rw [UnsignedGivens.register_basisOutcomeProjector_zero_ket, ite_eq_left_of_eq_true _ _
          (eq_true ?_)]
        intro idx
        refine Fin.addCases (fun j ↦ ?_) (fun z ↦ ?_) idx
        · dsimp only [rWorkPlus, β₁]
          rw [QRegister.concat_apply_left]
          rw [Function.update_of_ne (fun heq ↦ QRegister.disjoint_iff.mp hWork0 j 0 (heq.trans
            (QRegister.singleton_apply _ _).symm)), hw0 j]
        · fin_cases z
          dsimp only [rWorkPlus, β₁]
          rw [QRegister.concat_apply_right, QRegister.singleton_apply, Function.update_self]
          exact (clearHot0_zero_of_isOneHot hg₀).1
      have hClearMat : cClear0.eval.1 * cClear0.eval.1 = 1 := congrArg Subtype.val hClearSq
      have hk2 : cClear0.eval.1.mulVec (UnsignedGivens.ket β₁) = UnsignedGivens.ket β := by
        rw [← hk1, Matrix.mulVec_mulVec, hClearMat, Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hk1, hP0, hk2, hket_eq,
        ketPredProj_mulVec_ket, ite_posE hS]
    · have hcommP := (show IsDiagProj (ketPredProj S_valid) from ⟨S_valid, rfl⟩).comm hConj.1
      rw [Matrix.mulVec_mulVec, hcommP, ← Matrix.mulVec_mulVec, hket_eq, ketPredProj_mulVec_ket]
      simp only [hS, ↓reduceIte, Matrix.mulVec_zero]
  · apply UnsignedGivens.matrix_ext_ket
    intro β
    classical
    have hket_eq : @UnsignedGivens.ket n = @OneHotSimulates.ket n := rfl
    have hwreg_eq : @UnsignedGivens.writeReg n (N + 11) = @OneHotSimulates.writeReg n (N + 11) :=
      rfl
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hket_eq, ketPredProj_mulVec_ket]
    have hinv (γ : Fin (N + 11) → ZMod 2) : S_valid (UnsignedGivens.writeReg β rSC γ) ↔
      S_valid β := by
      have hf : fullHot (UnsignedGivens.writeReg β rSC γ) = fullHot β := by
        funext k
        cases k using Fin.cases with
        | zero => exact UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hNotSC0
        | succ g =>
            exact UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ fun ⟨sc, hsc_eq⟩ ↦
              QRegister.disjoint_iff.mp (OneHotMux.disj_sysCat_ctrl_of hsc hac) sc
                (selHot' g) hsc_eq
      have hw (j : Fin m) : UnsignedGivens.writeReg β rSC γ (rWork j) = β (rWork j) :=
        UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ fun ⟨sc, hsc_eq⟩ ↦
          QRegister.disjoint_iff.mp
        (OneHotMux.disj_sysCatCtrl_work_of hsc hac hdisjPlus) (Fin.castAdd k_ctrl sc) (Fin.castAdd 1
          j)
        (by simpa [rSC, rWorkPlus, QRegister.concat_apply_left] using hsc_eq)
      simp only [S_valid, hf, hw]
    by_cases hS : S_valid β
    · simp only [hS, ↓reduceIte]
      rw [← hket_eq, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
        QRegister.embedUnitary_val,
        hket_eq, OneHotSimulates.embedMatrix_mulVec_ket, ← hwreg_eq, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Matrix.mulVec_smul, ketPredProj_mulVec_ket]
      simp only [(hinv _).mpr hS, ↓reduceIte]
    · simp only [hS, ↓reduceIte, Matrix.mulVec_zero]
      rw [← hket_eq, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
        QRegister.embedUnitary_val,
        hket_eq, OneHotSimulates.embedMatrix_mulVec_ket, ← hwreg_eq, Matrix.mulVec_sum]
      symm
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      rw [Matrix.mulVec_smul, ketPredProj_mulVec_ket]
      simp only [mt (hinv _).mp hS, ↓reduceIte, smul_zero]
attribute [irreducible] topZeroLac2CascadeCtrl11Dyn
/-- Wire bijection embedding `238` logical `Phase2Bal161Layout` wires into `mCanCore 11 + 11`. -/
def extWireMap11 (idx : Fin 238) : Fin (mCanCore 11 + 11) :=
  let hlt := idx.isLt
  if _h1 : idx.val < 82 then ⟨idx.val, show idx.val < 227 + 11 by omega⟩
  else if _h2 : idx.val < 93 then
    ⟨mCanCore 11 + (idx.val - 82), show 227 + (idx.val - 82) < 227 + 11 by omega⟩
  else ⟨idx.val - 11, show idx.val - 11 < 227 + 11 by omega⟩
theorem extWireMap11_injective : Function.Injective extWireMap11 := by decide +kernel
/-- Extended `238`-wire `Phase2Bal161Layout` on `mCanCore 11 + 11` (`227 + 11`). -/
def extCanLayout11 : Phase2Bal161Layout (mCanCore 11 + 11) := { rFull := ⟨⟨extWireMap11,
  extWireMap11_injective⟩⟩ }
theorem extCanLayout11_lt :
    let L := extCanLayout11
    (∀ i, (L.rSpin i).val < mCanCore 11) ∧ (∀ i, (L.rCtrlTail146 i).val < mCanCore 11) ∧
    (∀ i, (L.rCat11 i).val < mCanCore 11) ∧ (L.wHot0).val < mCanCore 11 ∧
    (∀ i, ((L.rGivens22.slice 0 11 (by decide)) i).val < mCanCore 11) := by decide +kernel
theorem extCan11_hsc : (projReg extCanLayout11.rSpin extCanLayout11_lt.1).DisjointWires
    (projReg extCanLayout11.rCtrlTail146 extCanLayout11_lt.2.1) := by decide +kernel
theorem extCan11_hac :
    let L := extCanLayout11
    let hlt := extCanLayout11_lt
    ((projReg L.rSpin hlt.1).concat (projReg L.rCtrlTail146 hlt.2.1) extCan11_hsc).DisjointWires
      (projReg L.rCat11 hlt.2.2.1) := by decide +kernel
theorem extCan11_hWork0 :
    let L := extCanLayout11
    let hlt := extCanLayout11_lt
    (projReg (L.rGivens22.slice 0 11 (by decide)) hlt.2.2.2.2).DisjointWires
      (QRegister.singleton (⟨(L.wHot0).val, hlt.2.2.2.1⟩ : Wire (mCanCore 11))) := by decide +kernel
theorem extCan11_hdisjPlus :
    let L := extCanLayout11
    let hlt := extCanLayout11_lt
    (((projReg L.rSpin hlt.1).concat (projReg L.rCtrlTail146 hlt.2.1) extCan11_hsc).concat
      (projReg L.rCat11 hlt.2.2.1) extCan11_hac).DisjointWires
      ((projReg (L.rGivens22.slice 0 11 (by decide)) hlt.2.2.2.2).concat
        (QRegister.singleton (⟨(L.wHot0).val, hlt.2.2.2.1⟩ : Wire (mCanCore 11)))
        extCan11_hWork0) := by decide +kernel
/-- Canonical `227`-wire (`mCanCore 11`, `d = 11`) `Lac = 2` cascade for `orbitalOf`. -/
def compactCascadeCan11Dyn (orbitalOf : Fin 145 → Bool → Fin 319) : DynamicCircuit Unit
    (mCanCore 11)
    :=
  let L := extCanLayout11
  let hlt := extCanLayout11_lt
  topZeroLac2CascadeCtrl11Dyn () OneHotMux.h58_gt_1 (p450Bal145OrbitalTable orbitalOf)
    (projReg L.rSpin
    hlt.1) (projReg L.rCtrlTail146 hlt.2.1) extCan11_hsc actIdx146 selHot144 subIdx146
    ⟨(L.wHot0).val, hlt.2.2.2.1⟩ (projReg L.rCat11 hlt.2.2.1) (projReg (L.rGivens22.slice 0 11
    (by decide)) hlt.2.2.2.2) le_rfl
    extCan11_hac extCan11_hWork0 extCan11_hdisjPlus
/-- Pre-cascade Clifford glue on `extCanLayout11`. -/
def compactExtPre11Circuit (actFlipMask : Fin 145 → Bool) (negMask : Fin 145 → Bool) : Circuit
    (mCanCore 11 + 11) :=
  let L := extCanLayout11
  Circuit.seq (flipAct145Circuit actFlipMask L) (Circuit.seq (Circuit.X L.wOne) (Circuit.seq
      (zMaskAct145Circuit negMask L) (Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne
      L.rSelPair8 L.rOneHot145 (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i))))
/-- Post-cascade Clifford glue on `extCanLayout11`. -/
def compactExtPost11Circuit (actFlipMask : Fin 145 → Bool) : Circuit (mCanCore 11 + 11) :=
  let L := extCanLayout11
  Circuit.seq (Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne L.rSelPair8 L.rOneHot145 (fun
      g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i)) (Circuit.seq (Circuit.X L.wOne)
      (flipAct145Circuit actFlipMask L))
theorem inLeft_compactExtGlue11 (actFlipMask : Fin 145 → Bool) (negMask : Fin 145 → Bool) :
    inLeftDynB (mCanCore 11) 11 (dEnc145Dyn () extCanLayout11) = true ∧ inLeftCircuitB (mCanCore 11)
    11 (compactExtPre11Circuit actFlipMask negMask) = true ∧ inLeftCircuitB (mCanCore 11) 11
    (compactExtPost11Circuit actFlipMask) = true ∧ inLeftDynB (mCanCore 11) 11 (dDec145Dyn ()
    extCanLayout11) = true := by
  let L := extCanLayout11
  have hOH : ∀ g : Fin 145, (L.rOneHot145 g).val < mCanCore 11 := by decide +kernel
  have hPair : ∀ i : Fin 8, (L.rSelPair8 i).val < mCanCore 11 := by decide +kernel
  have hAct : L.wAct.val < mCanCore 11 := by decide +kernel
  have hOne : L.wOne.val < mCanCore 11 := by decide +kernel
  have hPh : L.wPh.val < mCanCore 11 := by decide +kernel
  have hFlip : inLeftCircuitB (mCanCore 11) 11 (flipAct145Circuit actFlipMask L) = true :=
    inLeftCircuitB_cnotMaskReg _ _ 145 _ _ _ _ hOH hAct
  have hFan : inLeftCircuitB (mCanCore 11) 11 (Lac2Fused184Select.fanoutActIdxCircuit 8 145
    L.wOne L.rSelPair8 L.rOneHot145 (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i))
    = true := inLeftCircuitB_seq (inLeftCircuitB_xorFiltered _ _ 145 _ _ _ _ hOH hOne)
    (inLeftCircuitB_xorOneHot _ _ 8 145 _ _ _ hPair hOH)
  have hZ : inLeftCircuitB (mCanCore 11) 11 (zMaskAct145Circuit negMask L) = true := by
    simp [zMaskAct145Circuit, CircuitModular.UnsignedGivens.czCircuit, inLeftCircuitB,
      inLeftCircuitB_cnotMaskReg _ _ 145 _ _ _ _ hOH hPh, hPh, hAct]
  have h1 : inLeftDynB (mCanCore 11) 11 (dEnc145Dyn () extCanLayout11) = true := by decide +kernel
  have h4 : inLeftDynB (mCanCore 11) 11 (dDec145Dyn () extCanLayout11) = true := by decide +kernel
  have hX := inLeftCircuitB_single (m := mCanCore 11) (d := 11) .X L.wOne hOne
  dsimp only [L] at hFlip hZ hFan
  dsimp only [L, inLeftCircuitB] at hX
  refine ⟨h1, ?_, ?_, h4⟩
  · dsimp only [compactExtPre11Circuit, inLeftCircuitB]
    rw [hFlip, hX, hZ, hFan]
    rfl
  · dsimp only [compactExtPost11Circuit, inLeftCircuitB]
    rw [hFan, hX, hFlip]
    rfl
end PhaseBD11CompactCore
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
end
