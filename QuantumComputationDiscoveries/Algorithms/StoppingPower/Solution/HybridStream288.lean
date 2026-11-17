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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80PhysBnds

set_option Elab.async false

@[expose] public section

set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModHybridStream288
@[expose] public section
namespace HybridStream288Aux
section ConfigHybridStream288
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice InPlaceStepEngine
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes
open NuclearTwistDisentangleSum288 (permUnitaryBits_inv_eq_self)
open SinglePassNuclearTwist288
local instance (priority := 1000000) instNeZeroTwoPowHybridStream288 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem listGet_append : ∀ (xs ys : List ℕ) (j : ℕ),
    listGet (xs ++ ys) j = if j < xs.length then listGet xs j else listGet ys (j - xs.length)
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp [listGet]
  | _ :: xs, ys, j + 1 => by
      simpa only [List.cons_append, listGet, List.length_cons, Nat.succ_lt_succ_iff,
        Nat.succ_sub_succ_eq_sub] using listGet_append xs ys j
theorem listGet_replicate : ∀ (n v j : ℕ), j < n → listGet (List.replicate n v) j = v
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | n + 1, v, j + 1, h => listGet_replicate n v j (Nat.lt_of_succ_lt_succ h)
def expectedOutWeightsCin {M₀ K : ℕ} (outWires : Fin K → Wire M₀)
    (cinWire : Option (Wire M₀)) : List ℕ :=
  match cinWire with
  | none => expectedOutWeights outWires
  | some cw => forceList (addWeightAt (expectedOutWeights outWires) cw 1)
theorem wSum_expectedOutWeightsCin {M₀ K : ℕ} (outWires : Fin K → Wire M₀)
    (cinWire : Option (Wire M₀)) (β₀ : BitAssignment M₀) :
    wSum (expectedOutWeightsCin outWires cinWire) β₀ =
      (∑ k : Fin K, 2 ^ k.val * (β₀ (outWires k)).val) + optBitVal cinWire β₀ := by
  cases cinWire with
  | none => simp [expectedOutWeightsCin, optBitVal, wSum_expectedOutWeights]
  | some cw =>
      have hlen : (expectedOutWeights outWires).length = M₀ :=
        expectedOutWeightsAux_length outWires K (le_refl K)
      dsimp only [expectedOutWeightsCin, optBitVal]
      rw [forceList_eq, wSum_addWeightAt _ hlen, wSum_expectedOutWeights, one_mul]
theorem runWeightList_append_aux :
    ∀ (cur : ℕ) (s₁ s₂ : List InPlaceStep) (L L₁ : List ℕ),
      runWeightList cur s₁ L = some L₁ →
      runWeightList cur (s₁ ++ s₂) L = runWeightList (cur + s₁.length) s₂ L₁
  | cur, [], s₂, L, L₁, h => by
      cases h
      simp
  | cur, s :: rest, s₂, L, L₁, h => by
      dsimp only [runWeightList, List.cons_append, List.length_cons] at h ⊢
      cases hstep : stepWeightList cur L s with
      | none => simp [hstep] at h
      | some L' =>
          rw [hstep] at h
          dsimp only at h ⊢
          rw [match_forceList_apply (fun x ↦ runWeightList (cur + 1) rest x) L'] at h
          rw [match_forceList_apply (fun x ↦ runWeightList (cur + 1) (rest ++ s₂) x) L',
            show cur + (rest.length + 1) = cur + 1 + rest.length by omega]
          exact runWeightList_append_aux (cur + 1) rest s₂ L' L₁ h
theorem runWeightList_append {cur cur' : ℕ} {s₁ s₂ : List InPlaceStep} {L L₁ : List ℕ}
    (h₁ : runWeightList cur s₁ L = some L₁) (hcur : cur + s₁.length = cur') :
    runWeightList cur (s₁ ++ s₂) L = runWeightList cur' s₂ L₁ :=
  hcur ▸ runWeightList_append_aux cur s₁ s₂ L L₁ h₁
section Csa3Specs
set_option maxRecDepth 200000
theorem fin_injective_of_decide {K M : ℕ} (f : Fin K → Wire M)
    (h : decide (∀ i j : Fin K, f i = f j → i = j) = true) : Function.Injective f :=
  fun i j hij ↦ of_decide_eq_true h i j hij
theorem some_cinNe_of_decide {K M : ℕ} (outW : Fin K → Wire M) (cw₀ : Wire M)
    (h : decide (∀ k : Fin K, cw₀ ≠ outW k) = true) :
    ∀ cw k, some cw₀ = some cw → cw ≠ outW k :=
  fun _ k hcw ↦ Option.some.inj hcw ▸ of_decide_eq_true h k
end Csa3Specs
theorem bitsVal_injective {W : ℕ} {f g : BitAssignment W} (h : bitsVal f = bitsVal g) : f = g :=
  (basisBitsEquiv W).symm.injective <| Fin.ext <| by
    rw [← bitsVal_eq_symm_val, ← bitsVal_eq_symm_val, h]
def weightedBatchVal {B kCore : ℕ} (inCore : Fin (3 * B) → Wire kCore)
    (γ : BitAssignment kCore) : ℕ :=
  ∑ i : Fin B,
    ((γ (inCore ⟨i.val, by omega⟩)).val +
      2 * (γ (inCore ⟨B + i.val, by omega⟩)).val +
      4 * (γ (inCore ⟨2 * B + i.val, by omega⟩)).val)
theorem weightedBatchVal_le {B kCore : ℕ} (inCore : Fin (3 * B) → Wire kCore)
    (γ : BitAssignment kCore) : weightedBatchVal inCore γ ≤ 7 * B := by
  unfold weightedBatchVal
  calc _ ≤ ∑ _i : Fin B, 7 := Finset.sum_le_sum fun i _ ↦ by
        have := ZMod.val_lt (γ (inCore ⟨i.val, by omega⟩))
        have := ZMod.val_lt (γ (inCore ⟨B + i.val, by omega⟩))
        have := ZMod.val_lt (γ (inCore ⟨2 * B + i.val, by omega⟩))
        omega
    _ = 7 * B := by simp [Nat.mul_comm]
def bitXorFn (kCore W : ℕ) (V : BitAssignment kCore → ℕ) (α : BitAssignment (kCore + W)) :
    BitAssignment (kCore + W) := fun idx ↦ if idx.val < kCore then α idx else α idx + (if (V
    (fun q ↦ α (Fin.castAdd W q))).testBit (idx.val - kCore) then 1 else 0)
theorem bitXorFn_involutive (kCore W : ℕ) (V : BitAssignment kCore → ℕ) :
    Function.Involutive (bitXorFn kCore W V) := fun α ↦ funext fun idx ↦ by
  by_cases h : idx.val < kCore
  · simp only [bitXorFn, h, ↓reduceIte]
  · simp only [bitXorFn, Fin.val_castAdd, Fin.is_lt, h, ↓reduceIte,
      add_assoc, CharTwo.add_self_eq_zero, add_zero]
noncomputable def uBitXor (kCore W : ℕ) (V : BitAssignment kCore → ℕ) : Unitary
    (2 ^ (kCore + W)) := Operator.permutationUnitary ((basisBitsEquiv (kCore + W)).trans
    ((Equiv.ofBijective (bitXorFn kCore W V) (bitXorFn_involutive kCore W V).bijective).trans
    (basisBitsEquiv (kCore + W)).symm))
theorem uBitXor_mulVec_basisKet {kCore W n : ℕ} [NeZero (2 ^ n)] (rCore : QRegister kCore n)
    (rAcc : QRegister W n) (hCA : rCore.DisjointWires rAcc) (V : BitAssignment kCore → ℕ)
    (β β' : BitAssignment n) (h_out : ∀ z : Wire n, z ∉ rAcc.image → β' z = β z) (h_in : ∀ j :
    Fin W, β' (rAcc j) = β (rAcc j) + (if (V (fun q ↦ β (rCore q))).testBit j.val then 1 else
    0)) : ((rCore.concat rAcc hCA).embedUnitary (uBitXor kCore W V)).1.mulVec (basisKet β) =
    basisKet β' := by
  let rAct := rCore.concat rAcc hCA
  unfold uBitXor
  refine embedUnitary_perm_mulVec_basisKet rAct _ β β' (fun idx ↦ ?_) fun z hz ↦
    h_out z fun hmA ↦ hz (by
      obtain ⟨j, rfl⟩ := (QRegister.mem_image rAcc z).mp hmA
      exact (QRegister.mem_image rAct _).mpr ⟨Fin.natAdd kCore j, QRegister.concat_apply_right rCore
        rAcc hCA j⟩)
  rw [basisBits_perm_ofBijective (bitXorFn kCore W V) (bitXorFn_involutive kCore W V).bijective]
  have hCoreEq : (fun q : Fin kCore ↦ β (rAct (Fin.castAdd W q))) = fun q ↦ β (rCore q) :=
    funext fun q ↦ by dsimp [rAct]; rw [QRegister.concat_apply_left]
  by_cases h : idx.val < kCore
  · have hr : rAct idx = rCore ⟨idx.val, h⟩ := QRegister.concat_apply_left rCore rAcc hCA ⟨idx.val,
      h⟩
    simp only [bitXorFn, h, ↓reduceIte, hr, h_out _ (hCA.apply_not_mem_right _)]
  · let j : Fin W := ⟨idx.val - kCore, by have := idx.isLt; omega⟩
    have hr : rAct idx = rAcc j := by
      rw [show idx = Fin.natAdd kCore j from Fin.ext (by dsimp [j]; omega)]
      exact QRegister.concat_apply_right rCore rAcc hCA j
    simp only [bitXorFn, h, ↓reduceIte, hCoreEq, hr, h_in j, j]
theorem TargetBlock.toBitXorPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {n W kCore mClean mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : mClean ≤ mWork) (V : BitAssignment kCore → ℕ)
    {fTarget : BitAssignment ((W + kCore) + mClean) → BitAssignment ((W + kCore) + mClean)}
    {p : InPlaceFullAddSlice.TempPhaseProg ((W + kCore) + mClean)}
    (hTB : TargetBlock ((W + kCore) + mClean) W mClean fTarget (fun _ ↦ 0) p)
    (hBits : ∀ β : BitAssignment ((W + kCore) + mClean),
      InPlaceFullAddSlice.cleanRem ((W + kCore) + mClean) mClean β →
      ∀ j : Fin W,
        fTarget β ⟨W - 1 - j.val, by omega⟩ =
          β ⟨W - 1 - j.val, by omega⟩ +
            (if (V (fun q : Fin kCore ↦ β (Fin.castAdd mClean (Fin.natAdd W q)))).testBit j.val
             then 1 else 0)) :
    let rComb := mkModAddCombReg rCore rAcc rWork hCA hCW hAW hmWork
    let dyn := (p.onRegister rComb).toDyn v
    RealizesCleanPair (rCore.concat rAcc hCA) rWork (uBitXor kCore W V) dyn dyn := by
  intro rComb dyn
  let Mtot := (W + kCore) + mClean
  have hrem : mClean ≤ Mtot := Nat.le_add_left mClean (W + kCore)
  let P_small := InPlaceFullAddSlice.projZeroAll mClean
    (InPlaceFullAddSlice.tailScr rComb mClean hrem)
  let P_work := InPlaceFullAddSlice.projZeroAll mWork rWork.wires
  have hPw : P_workᴴ = P_work := InPlaceFullAddSlice.projZeroAll_conjTranspose mWork _
  have hrWork (j : Fin mClean) : rComb (Fin.natAdd (W + kCore) j) = rWork ⟨j.val, by omega⟩ := by
    dsimp only [rComb, mkModAddCombReg]
    rw [QRegister.concat_apply_right, QRegister.slice_apply]
    exact congrArg rWork.wires (Fin.ext (Nat.zero_add j.val))
  have hsub : P_small * P_work = P_work := InPlaceFullAddSlice.matrix_ext_ket fun β ↦ by
    simp only [P_small, P_work, InPlaceFullAddSlice.mul_mulVec_prog,
      InPlaceFullAddSlice.ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · have htw (j : Fin mClean) : β (InPlaceFullAddSlice.tailScr rComb mClean hrem j) = 0 := by
        dsimp only [InPlaceFullAddSlice.tailScr]
        rw [show (⟨(Mtot - mClean) + j.val, _⟩ : Fin Mtot) = Fin.natAdd (W + kCore) j from
          Fin.ext (by dsimp [Mtot]; omega), hrWork j]
        exact hw ⟨j.val, by omega⟩
      simp [hw, htw, InPlaceFullAddSlice.ket_projZeroAll]
    · simp [hw]
  have hMono := InPlaceFullAddSlice.RealizesCleanUnitary.mono_proj
    (InPlaceFullAddSlice.projZeroAll_conjTranspose mClean _) hPw hsub
    (InPlaceFullAddSlice.realizes_of_validCleanRem v rComb p mClean hrem hTB.valid)
  have hUeq : ((p.onRegister rComb).toToffCircuit).eval.1 * P_work =
      ((rCore.concat rAcc hCA).embedUnitary (uBitXor kCore W V)).1 * P_work :=
    InPlaceFullAddSlice.matrix_ext_ket fun β ↦ by
      simp only [P_work, InPlaceFullAddSlice.mul_mulVec_prog, InPlaceFullAddSlice.ket_projZeroAll]
      by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
      · simp only [hw, imp_true_iff, ↓reduceIte, InPlaceFullAddSlice.eval_onRegister_prog_ket]
        let βloc : BitAssignment Mtot := fun idx ↦ β (rComb idx)
        have hCleanLoc : InPlaceFullAddSlice.cleanRem Mtot mClean βloc := fun idx hidx ↦ by
          have hidx' : idx = Fin.natAdd (W + kCore) ⟨idx.val - (W + kCore), by omega⟩ :=
            Fin.ext (by dsimp; omega)
          exact (congrArg βloc hidx').trans ((congrArg β (hrWork _)).trans (hw ⟨_, by omega⟩))
        rw [hTB.sign βloc hCleanLoc]
        simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
        let β' := InPlaceFullAddSlice.writeRegProg β rComb (p.evalBits βloc)
        change basisKet β' = _
        refine (uBitXor_mulVec_basisKet rCore rAcc hCA V β β' (fun z hz ↦ ?_) (fun j ↦ ?_)).symm
        · by_cases hmem : z ∈ Set.range rComb.wires
          · obtain ⟨idx, rfl⟩ := hmem
            dsimp only [β']
            rw [InPlaceFullAddSlice.writeRegProg_apply_reg, hTB.bits βloc hCleanLoc idx]
            have hnW : ¬(idx.val < W) := fun hiW ↦ hz <| by
              rw [mkModAddCombReg_left_acc rCore rAcc rWork hCA hCW hAW hmWork idx hiW]
              exact (QRegister.mem_image rAcc _).mpr ⟨_, rfl⟩
            simp only [hnW, ↓reduceIte, βloc]
          · exact InPlaceFullAddSlice.writeRegProg_apply_of_not_mem _ _ _ _ hmem
        · let idxj : Fin Mtot := ⟨W - 1 - j.val, by omega⟩
          have hCoreIn : (fun q : Fin kCore ↦ βloc (Fin.castAdd mClean (Fin.natAdd W q))) =
              fun q ↦ β (rCore q) := funext fun q ↦ by
            dsimp only [βloc, rComb, mkModAddCombReg]
            rw [QRegister.concat_apply_left, QRegister.concat_apply_right]
          dsimp only [β']
          rw [← (mkModAddCombReg_left_acc rCore rAcc rWork hCA hCW hAW hmWork idxj
              (by dsimp [idxj]; omega)).trans
              (congrArg rAcc.wires (Fin.ext (by dsimp [idxj]; omega))),
            InPlaceFullAddSlice.writeRegProg_apply_reg, hTB.bits βloc hCleanLoc idxj]
          simp only [show idxj.val < W by dsimp [idxj]; omega, ↓reduceIte, idxj,
            hBits βloc hCleanLoc j, hCoreIn, βloc, rComb]
      · simp [hw]
  have hTarget := InPlaceFullAddSlice.RealizesCleanUnitary.congr_unitary hPw hMono hUeq
  have hFwd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rAcc hCA) rWork (uBitXor kCore W V) dyn := fun M_obs ↦ by
    obtain ⟨M_out, hM_out⟩ :=
      InPlaceFullAddSlice.PreservesStoreConst_toDyn v (p.onRegister rComb) M_obs
    refine ⟨M_out, hM_out, ?_⟩
    have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
    rw [← show wp dyn.compile (fun _ ↦ M_obs) default = M_out by dsimp [dyn]; rw [hM_out],
      ← InPlaceFullAddSlice.projZeroAll_eq_basisOutcomeProjector_zero rWork]
    simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
      congrArg Subtype.val hconj
  refine ⟨hFwd, ?_⟩
  rwa [show (uBitXor kCore W V)⁻¹ = uBitXor kCore W V from
    permUnitaryBits_inv_eq_self (bitXorFn kCore W V) (bitXorFn_involutive kCore W V)]
noncomputable def xorOutLoop {M W : ℕ} (hWM : W ≤ M) (outW : Fin W → Wire M)
    (hOutGe : ∀ k : Fin W, W ≤ (outW k).val) :
    (m : ℕ) → m ≤ W → InPlaceFullAddSlice.TempPhaseProg M
  | 0, _ => .nil
  | k + 1, hk =>
      let dst : Wire M := ⟨W - 1 - k, by omega⟩
      let src : Wire M := outW ⟨k, hk⟩
      .seq (xorOutLoop hWM outW hOutGe k (Nat.le_of_succ_le hk))
        (.cliff (.cnot src dst (wire_ne_of_gt (by
          dsimp [dst, src]; have := hOutGe ⟨k, hk⟩; omega))))
@[simp] theorem xorOutLoop_countTempAnd {M W : ℕ} (hWM : W ≤ M) (outW : Fin W → Wire M)
    (hOutGe : ∀ k : Fin W, W ≤ (outW k).val) :
    ∀ (m : ℕ) (hm : m ≤ W), (xorOutLoop hWM outW hOutGe m hm).countTempAnd = 0
  | 0, _ => rfl
  | k + 1, hk => by
      simp [xorOutLoop, InPlaceFullAddSlice.TempPhaseProg.countTempAnd,
        xorOutLoop_countTempAnd hWM outW hOutGe k (Nat.le_of_succ_le hk)]
theorem xorOutLoop_spec {M W rem : ℕ} (hrem : rem ≤ M) (hWM : W ≤ M - rem)
    (outW : Fin W → Wire M) (hOutGe : ∀ k : Fin W, W ≤ (outW k).val)
    (hOutLt : ∀ k : Fin W, (outW k).val < M - rem) :
    ∀ (m : ℕ) (hm : m ≤ W),
      TargetBlock M W rem
        (fun β w ↦
          if _hw : w.val < W then
            if _hkm : W - 1 - w.val < m then
              β w + β (outW ⟨W - 1 - w.val, by omega⟩)
            else β w
          else β w)
        (fun _ ↦ 0)
        (xorOutLoop (by omega) outW hOutGe m hm)
  | 0, _ =>
      ⟨trivial, fun β _ w ↦ by simp [xorOutLoop, InPlaceFullAddSlice.TempPhaseProg.evalBits],
       fun _ _ ↦ rfl⟩
  | k + 1, hk => by
      have ih := xorOutLoop_spec hrem hWM outW hOutGe hOutLt k (Nat.le_of_succ_le hk)
      let dst : Wire M := ⟨W - 1 - k, by omega⟩
      let src : Wire M := outW ⟨k, hk⟩
      have hStep := TargetBlock.seq_cnot_in_target (M := M) (targetEnd := W) (rem := rem)
        hrem src dst (wire_ne_of_gt (by dsimp [dst, src]; have := hOutGe ⟨k, hk⟩; omega))
        (by dsimp [dst]; omega) (hOutGe ⟨k, hk⟩) (hOutLt ⟨k, hk⟩) ih
      refine ⟨hStep.valid, fun β hβ w ↦ ?_, hStep.sign⟩
      dsimp only [xorOutLoop]
      rw [hStep.bits β hβ w]
      by_cases hw : w.val < W
      · by_cases hwd : w = dst
        · subst hwd
          simp only [↓reduceIte, show dst.val < W by dsimp [dst]; omega,
            show ¬(W - 1 - dst.val < k) by dsimp [dst]; omega,
            show W - 1 - dst.val < k + 1 by dsimp [dst]; omega, ↓reduceDIte, src,
            show (⟨W - 1 - dst.val, by omega⟩ : Fin W) = ⟨k, hk⟩ from
              Fin.ext (by dsimp [dst]; omega)]
        · have hne_k : W - 1 - w.val ≠ k := fun heq ↦ hwd (Fin.ext (by dsimp [dst]; omega))
          simp only [hw, hwd, show (W - 1 - w.val < k + 1) ↔ (W - 1 - w.val < k) by omega,
            ↓reduceIte, ↓reduceDIte]
      · simp only [hw, ↓reduceIte]
def selCoreSlice (kCore off len : ℕ) (hSlice : off + len ≤ 14) :
    QRegister (kCore + len) (kCore + 14) :=
  ⟨⟨fun idx ↦
      if h : idx.val < kCore then Fin.castAdd 14 ⟨idx.val, h⟩
      else Fin.natAdd kCore ⟨off + (idx.val - kCore), by have := idx.isLt; omega⟩,
    fun a b hab ↦ Fin.ext <| by
      have hv := congrArg Fin.val hab
      by_cases h1 : a.val < kCore <;> by_cases h2 : b.val < kCore <;>
        simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd, Fin.val_natAdd] at hv
      all_goals omega⟩⟩
theorem disj_slice14 {kCore n : ℕ} {rCore : QRegister kCore n} {rSum14 : QRegister 14 n}
    (hCSum : rCore.DisjointWires rSum14) (off len : ℕ) (hSlice : off + len ≤ 14) :
    rCore.DisjointWires (rSum14.slice off len hSlice) :=
  QRegExt.disjointWires_mono_right hCSum (QRegister.image_compose_subset rSum14 _)
theorem disj_slice14_work {mWork n : ℕ} {rSum14 : QRegister 14 n} {rWork : QRegister mWork n}
    (hSW : rSum14.DisjointWires rWork) (off len : ℕ) (hSlice : off + len ≤ 14) :
    (rSum14.slice off len hSlice).DisjointWires rWork :=
  QRegExt.disjointWires_mono_left hSW (QRegister.image_compose_subset rSum14 _)
theorem compose_selCoreSlice_eq {kCore n : ℕ}
    (rCore : QRegister kCore n) (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14)
    (off len : ℕ) (hSlice : off + len ≤ 14) :
    (rCore.concat rSum14 hCSum).compose (selCoreSlice kCore off len hSlice) =
      rCore.concat (rSum14.slice off len hSlice) (disj_slice14 hCSum off len hSlice) := by
  refine QRegister.ext (Function.Embedding.ext fun idx ↦ ?_)
  have _ := idx.isLt
  by_cases h : idx.val < kCore
  · rw [QRegister.compose_apply]
    change (rCore.concat rSum14 hCSum)
      (if h' : idx.val < kCore then Fin.castAdd 14 ⟨idx.val, h'⟩ else _) = _
    simp only [h, ↓reduceDIte, QRegister.concat_apply_left]
    conv_rhs =>
      rw [show idx = Fin.castAdd len ⟨idx.val, h⟩ from Fin.ext rfl, QRegister.concat_apply_left]
  · let j : Fin len := ⟨idx.val - kCore, by omega⟩
    rw [QRegister.compose_apply]
    change (rCore.concat rSum14 hCSum) (if h' : idx.val < kCore then Fin.castAdd 14 ⟨idx.val,
      h'⟩ else Fin.natAdd kCore ⟨off + (idx.val - kCore), _⟩) = _
    simp only [h, ↓reduceDIte, QRegister.concat_apply_right]
    conv_rhs => rw [show idx = Fin.natAdd kCore j from Fin.ext (by dsimp [j]; omega),
      QRegister.concat_apply_right, QRegister.slice_apply]
theorem liftCleanPair_slice14 {Var : Type} [Fintype Var] [DecidableEq Var] {kCore mWork n : ℕ}
    [NeZero (2 ^ n)] {rCore : QRegister kCore n} {rSum14 : QRegister 14 n}
    {rWork : QRegister mWork n} (hCSum : rCore.DisjointWires rSum14) (off len : ℕ)
    (hSlice : off + len ≤ 14) {u : Unitary (2 ^ (kCore + len))}
    {dFwd dInv : DynamicCircuit Var n} (hp : RealizesCleanPair (rCore.concat (rSum14.slice off
    len hSlice) (disj_slice14 hCSum off len hSlice)) rWork u dFwd dInv) : RealizesCleanPair
    (rCore.concat rSum14 hCSum) rWork ((selCoreSlice kCore off len hSlice).embedUnitary u)
    dFwd dInv := by
  rw [← compose_selCoreSlice_eq rCore rSum14 hCSum off len hSlice] at hp
  exact hp.widenActive
theorem embedUnitary_selCoreSlice_val {kCore n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister kCore n) (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14)
    (off len : ℕ) (hSlice : off + len ≤ 14) (u : Unitary (2 ^ (kCore + len))) : ((rCore.concat
    rSum14 hCSum).embedUnitary ((selCoreSlice kCore off len hSlice).embedUnitary u)).1 =
    ((rCore.concat (rSum14.slice off len hSlice) (disj_slice14 hCSum off len
    hSlice)).embedUnitary u).1 := by
  simp only [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, compose_selCoreSlice_eq]
theorem testBit_two_pow_mul_add :
    ∀ {off : ℕ} (Q R : ℕ), R < 2 ^ off → ∀ (i : ℕ),
      (2 ^ off * Q + R).testBit i = if i < off then R.testBit i else Q.testBit (i - off)
  | 0, Q, R, hR, i => by
      rw [show R = 0 by omega]
      simp
  | off + 1, Q, R, _hR, 0 => by
      rw [show 2 ^ (off + 1) * Q + R = R + (2 ^ off * Q) * 2 by rw [pow_succ]; ring]
      simp only [Nat.zero_lt_succ off, ↓reduceIte, Nat.testBit_zero, Nat.add_mul_mod_self_right]
  | off + 1, Q, R, hR, i + 1 => by
      rw [Nat.testBit_succ, show 2 ^ (off + 1) * Q + R = R + (2 ^ off * Q) * 2 by
          rw [pow_succ]; ring,
        Nat.add_mul_div_right R (2 ^ off * Q) (by decide : 0 < 2), add_comm,
        testBit_two_pow_mul_add Q (R / 2) (by rw [pow_succ] at hR; omega) i]
      by_cases hlt : i < off
      · simp only [hlt, Nat.succ_lt_succ hlt, ↓reduceIte, ← Nat.testBit_succ]
      · simp only [hlt, show ¬(i + 1 < off + 1) by omega, ↓reduceIte, Nat.succ_sub_succ_eq_sub]
def accInvar {n : ℕ} (rSum14 : QRegister 14 n) (A : ℕ) (β₀ β : BitAssignment n) : Prop :=
  (∀ z : Wire n, z ∉ rSum14.image → β z = β₀ z) ∧
  (∀ i : Fin 14, β (rSum14 i) = if A.testBit i.val then 1 else 0)
theorem accInvar_zero {n : ℕ} (rSum14 : QRegister 14 n) (β₀ : BitAssignment n)
    (hz : ∀ i : Fin 14, β₀ (rSum14 i) = 0) : accInvar rSum14 0 β₀ β₀ :=
  ⟨fun _ _ ↦ rfl, fun i ↦ by simp [hz i]⟩
noncomputable def mkAccAssign {n : ℕ} (rSum14 : QRegister 14 n) (A : ℕ)
    (β₀ : BitAssignment n) : BitAssignment n :=
  fun z ↦ if hz : z ∈ rSum14.image then
    if A.testBit (Classical.choose ((QRegister.mem_image rSum14 z).mp hz)).val then 1 else 0
  else β₀ z
theorem mkAccAssign_accInvar {n : ℕ} (rSum14 : QRegister 14 n) (A : ℕ) (β₀ : BitAssignment n) :
    accInvar rSum14 A β₀ (mkAccAssign rSum14 A β₀) := by
  refine ⟨fun z hz ↦ dite_eq_right hz, fun i ↦ ?_⟩
  have hm : rSum14 i ∈ rSum14.image := (QRegister.mem_image rSum14 _).mpr ⟨i, rfl⟩
  have hch : Classical.choose ((QRegister.mem_image rSum14 (rSum14 i)).mp hm) = i :=
    rSum14.wires.injective (Classical.choose_spec ((QRegister.mem_image rSum14 (rSum14 i)).mp hm))
  simp only [mkAccAssign, hm, ↓reduceDIte, hch]
theorem accInvar_step1_bitXor9 {kCore n : ℕ} [NeZero (2 ^ n)] (rCore : QRegister kCore n)
    (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14)
    (V : BitAssignment kCore → ℕ) (β₀ : BitAssignment n) (hInv0 : accInvar rSum14 0 β₀ β₀)
    (hVlt : V (fun q ↦ β₀ (rCore q)) < 2 ^ 9) : ∃ β₁ : BitAssignment n, ((rCore.concat rSum14
    hCSum).embedUnitary ((selCoreSlice kCore 0 9 (by decide)).embedUnitary (uBitXor kCore 9
    V))).1.mulVec (basisKet β₀) = basisKet β₁ ∧ accInvar rSum14 (V (fun q ↦ β₀ (rCore q))) β₀
    β₁ := by
  let hSlice9 : 0 + 9 ≤ 14 := by decide
  let rSlice9 := rSum14.slice 0 9 hSlice9
  let xCore : BitAssignment kCore := fun q ↦ β₀ (rCore q)
  have hInv₁ := mkAccAssign_accInvar rSum14 (V xCore) β₀
  refine ⟨mkAccAssign rSum14 (V xCore) β₀, ?_, hInv₁⟩
  rw [embedUnitary_selCoreSlice_val]
  refine uBitXor_mulVec_basisKet rCore rSlice9 (disj_slice14 hCSum 0 9 hSlice9) V β₀ _
    (fun z hz9 ↦ ?_) (fun j ↦ ?_)
  · by_cases hz14 : z ∈ rSum14.image
    · obtain ⟨i, rfl⟩ := (QRegister.mem_image rSum14 z).mp hz14
      have hge9 : 9 ≤ i.val := by
        by_contra hlt
        refine hz9 ((QRegister.mem_image rSlice9 _).mpr ⟨⟨i.val, by omega⟩, ?_⟩)
        rw [QRegister.slice_apply]
        exact congrArg rSum14.wires (Fin.ext (by simp))
      rw [hInv₁.2 i, Nat.testBit_lt_two_pow (lt_of_lt_of_le hVlt (Nat.pow_le_pow_right (by decide)
        hge9)),
        show β₀ (rSum14 i) = 0 by simpa using hInv0.2 i]
      rfl
    · exact hInv₁.1 z hz14
  · rw [show rSlice9 j = rSum14 ⟨j.val, by omega⟩ by
        rw [QRegister.slice_apply]
        exact congrArg rSum14.wires (Fin.ext (by simp)),
      hInv₁.2 ⟨j.val, by omega⟩, show β₀ (rSum14 ⟨j.val, by omega⟩) = 0 by
        simpa using hInv0.2 ⟨j.val, by omega⟩,
      zero_add]
theorem regVal_slice_of_decomp {n : ℕ} (rSum14 : QRegister 14 n) (off len X R : ℕ)
    (hSlice : off + len ≤ 14) (hR : R < 2 ^ off) (hX : X < 2 ^ len)
    (γ : BitAssignment n)
    (hγ : ∀ i : Fin 14, γ (rSum14 i) = if (2 ^ off * X + R).testBit i.val then 1 else 0) :
    regVal (rSum14.slice off len hSlice) γ = X := by
  have hfn : (fun j : Fin len ↦ γ (rSum14.slice off len hSlice j)) =
      fun j : Fin len ↦ if X.testBit j.val then 1 else 0 := funext fun j ↦ by
    rw [QRegister.slice_apply, hγ ⟨off + j.val, by omega⟩]
    simp only [testBit_two_pow_mul_add X R hR (off + j.val),
      show ¬(off + j.val < off) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [regVal, hfn, bitsVal_eq_of_testBit len X hX]
theorem accInvar_step_sliceModAdd {kCore n : ℕ} [NeZero (2 ^ n)] (rCore : QRegister kCore n)
    (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14) (off len : ℕ)
    (hSlice : off + len ≤ 14) (V : BitAssignment kCore → ℕ) (A : ℕ) (β₀ β : BitAssignment n)
    (hInv : accInvar rSum14 A β₀ β) (_hAlt : A < 2 ^ (off + len))
    (hNoOv : A / 2 ^ off + V (fun q ↦ β₀ (rCore q)) < 2 ^ len) : ∃ β' : BitAssignment n,
    ((rCore.concat rSum14 hCSum).embedUnitary ((selCoreSlice kCore off len
    hSlice).embedUnitary (catModAddUnitary kCore len V))).1.mulVec (basisKet β) = basisKet β'
    ∧ accInvar rSum14 (A + 2 ^ off * V (fun q ↦ β₀ (rCore q))) β₀ β' := by
  let rSlice := rSum14.slice off len hSlice
  let xCore : BitAssignment kCore := fun q ↦ β₀ (rCore q)
  have hCoreβ : (fun q : Fin kCore ↦ β (rCore q)) = xCore :=
    funext fun q ↦ hInv.1 (rCore q) (hCSum.apply_not_mem_right q)
  let A' := A + 2 ^ off * V xCore
  let β' := mkAccAssign rSum14 A' β₀
  have hInv' : accInvar rSum14 A' β₀ β' := mkAccAssign_accInvar rSum14 A' β₀
  refine ⟨β', ?_, hInv'⟩
  rw [embedUnitary_selCoreSlice_val]
  symm
  let Q := A / 2 ^ off + V xCore
  have hQ_lt : Q < 2 ^ len := hNoOv
  let R := A % 2 ^ off
  have hR_lt : R < 2 ^ off := Nat.mod_lt A (Nat.two_pow_pos off)
  have hA_decomp : A = 2 ^ off * (A / 2 ^ off) + R := (Nat.div_add_mod A (2 ^ off)).symm
  have hA'_decomp : A' = 2 ^ off * Q + R := by dsimp [A', Q]; linarith
  have hAdiv_lt : A / 2 ^ off < 2 ^ len := by omega
  refine catModAddUnitary_mulVec_basisKet rCore rSlice (disj_slice14 hCSum off len hSlice) V
    (fun _ ↦ β') β (fun z hzSlice ↦ ?_) ?_
  · by_cases hz14 : z ∈ rSum14.image
    · obtain ⟨i, rfl⟩ := (QRegister.mem_image rSum14 z).mp hz14
      rw [hInv'.2 i, hInv.2 i]
      have hNotInRange : i.val < off ∨ off + len ≤ i.val := by
        by_contra hIn
        refine hzSlice ((QRegister.mem_image rSlice _).mpr ⟨⟨i.val - off, by omega⟩, ?_⟩)
        rw [QRegister.slice_apply]
        exact congrArg rSum14.wires (Fin.ext (by dsimp; omega))
      have htbA := (congrArg (fun n ↦ n.testBit i.val) hA_decomp).trans
        (testBit_two_pow_mul_add (A / 2 ^ off) R hR_lt i.val)
      have htbA' := (congrArg (fun n ↦ n.testBit i.val) hA'_decomp).trans
        (testBit_two_pow_mul_add Q R hR_lt i.val)
      rcases hNotInRange with hlo | hhi
      · simp only [htbA', htbA, hlo, ↓reduceIte]
      · have hlen_le : len ≤ i.val - off := by omega
        simp only [htbA', htbA, show ¬(i.val < off) by omega, ↓reduceIte,
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hQ_lt (Nat.pow_le_pow_right (by decide) hlen_le)),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hAdiv_lt (Nat.pow_le_pow_right (by decide)
            hlen_le))]
    · rw [hInv'.1 z hz14, hInv.1 z hz14]
  · rw [regVal_slice_of_decomp rSum14 off len Q R hSlice hR_lt hNoOv β'
        (fun i ↦ by rw [← hA'_decomp]; exact hInv'.2 i),
      regVal_slice_of_decomp rSum14 off len (A / 2 ^ off) R hSlice hR_lt hAdiv_lt β
        (fun i ↦ by rw [← hA_decomp]; exact hInv.2 i),
      hCoreβ, show Q = A / 2 ^ off + V xCore from rfl, Nat.mod_eq_of_lt hNoOv]
theorem elecAxisBitWire_val {mPayload : ℕ} (w : Fin 3) (r : Fin 6) (e : Fin numElectrons) :
    (elecAxisBitWire (mPayload := mPayload) w r e).val = 18 * e.val + 6 * w.val + r.val := by
  simp [elecAxisBitWire, rElecSlotAxis, QRegExt.idReg]
def threePlaneChunkWire {mPayload : ℕ} (w : Fin 3) (pBase eOff B : ℕ) (hp : pBase + 3 ≤ 6)
    (he : eOff + B ≤ 218) (u : Fin (3 * B)) : Wire (fullSysCoreWires mPayload) :=
  if _h1 : u.val < B then
    elecAxisBitWire w ⟨pBase, by omega⟩
      ⟨eOff + u.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
  else if _h2 : u.val < 2 * B then
    elecAxisBitWire w ⟨pBase + 1, by omega⟩
      ⟨eOff + (u.val - B), by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
  else
    elecAxisBitWire w ⟨pBase + 2, by omega⟩
      ⟨eOff + (u.val - 2 * B), by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
theorem sum_fin218_split3 {a b c ab : ℕ} (hab : a + b = ab) (h : ab + c = 218)
    (f : Fin numElectrons → ℕ) :
    (∑ i : Fin a, f ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin b, f ⟨a + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin c, f ⟨ab + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) =
      ∑ e : Fin numElectrons, f e := by
  subst hab
  let e218 : Fin ((a + b) + c) ≃ Fin numElectrons := finCongr h
  rw [← Equiv.sum_comp e218, Fin.sum_univ_add, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  all_goals refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
theorem weightedBatchVal_threePlaneChunk {mPayload : ℕ} (w : Fin 3) (pBase eOff B : ℕ)
    (hp : pBase + 3 ≤ 6) (he : eOff + B ≤ 218)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    weightedBatchVal (threePlaneChunkWire (mPayload := mPayload) w pBase eOff B hp he) γ =
      ∑ i : Fin B,
        ((γ (elecAxisBitWire (mPayload := mPayload) w ⟨pBase, by omega⟩
            ⟨eOff + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩)).val +
          2 * (γ (elecAxisBitWire (mPayload := mPayload) w ⟨pBase + 1, by omega⟩
            ⟨eOff + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩)).val +
          4 * (γ (elecAxisBitWire (mPayload := mPayload) w ⟨pBase + 2, by omega⟩
            ⟨eOff + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩)).val) := by
  unfold weightedBatchVal
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  rw [show threePlaneChunkWire (mPayload := mPayload) w pBase eOff B hp he ⟨i.val, by omega⟩ =
      elecAxisBitWire (mPayload := mPayload) w ⟨pBase, by omega⟩
        ⟨eOff + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩ from dite_eq_left hi,
    show threePlaneChunkWire (mPayload := mPayload) w pBase eOff B hp he ⟨B + i.val, by omega⟩ =
      elecAxisBitWire (mPayload := mPayload) w ⟨pBase + 1, by omega⟩
        ⟨eOff + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩ by
      dsimp [threePlaneChunkWire]
      split_ifs <;> first | omega | exact congrArg _ (Fin.ext (by dsimp; omega)),
    show threePlaneChunkWire (mPayload := mPayload) w pBase eOff B hp he ⟨2 * B + i.val, by omega⟩ =
      elecAxisBitWire (mPayload := mPayload) w ⟨pBase + 2, by omega⟩
        ⟨eOff + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩ by
      dsimp [threePlaneChunkWire]
      split_ifs <;> first | omega | exact congrArg _ (Fin.ext (by dsimp; omega))]
theorem hybridSixBatch_eq_slot2AxisSum {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ((weightedBatchVal (threePlaneChunkWire
    w 0 0 73 (by decide) (by decide)) γ + 2 ^ 0 * weightedBatchVal (threePlaneChunkWire w 0 73
    72 (by decide) (by decide)) γ) + 2 ^ 0 * weightedBatchVal (threePlaneChunkWire w 0 145 73
    (by decide) (by decide)) γ) + 2 ^ 3 * weightedBatchVal
    (threePlaneChunkWire w 3 0 72 (by decide) (by decide)) γ + 2 ^ 3 * weightedBatchVal
    (threePlaneChunkWire w 3 72 73 (by decide) (by decide)) γ + 2 ^ 3 * weightedBatchVal
    (threePlaneChunkWire w 3 145 73 (by decide) (by decide)) γ = slot2AxisSum w γ := by
  simp only [Nat.pow_zero, one_mul, weightedBatchVal_threePlaneChunk]
  let fLo : Fin numElectrons → ℕ := fun e ↦ (γ (elecAxisBitWire w 0 e)).val + 2 *
      (γ (elecAxisBitWire w 1 e)).val + 4 * (γ (elecAxisBitWire w 2 e)).val
  let fHi : Fin numElectrons → ℕ := fun e ↦ (γ (elecAxisBitWire w 3 e)).val + 2 *
      (γ (elecAxisBitWire w 4 e)).val + 4 * (γ (elecAxisBitWire w 5 e)).val
  have hLo := sum_fin218_split3 (a := 73) (b := 72) (c := 73) (ab := 145) rfl rfl fLo
  have hHi := sum_fin218_split3 (a := 72) (b := 73) (c := 73) (ab := 145) rfl rfl fHi
  trans (∑ e : Fin numElectrons, fLo e) + 8 * (∑ e : Fin numElectrons, fHi e)
  · rw [← hLo, ← hHi]
    dsimp only [fLo, fHi]
    simp only [show ∀ h, (⟨0, h⟩ : Fin 6) = 0 from fun _ ↦ rfl,
      show ∀ h, (⟨0 + 1, h⟩ : Fin 6) = 1 from fun _ ↦ rfl,
      show ∀ h, (⟨0 + 2, h⟩ : Fin 6) = 2 from fun _ ↦ rfl,
      show ∀ h, (⟨3, h⟩ : Fin 6) = 3 from fun _ ↦ rfl,
      show ∀ h, (⟨3 + 1, h⟩ : Fin 6) = 4 from fun _ ↦ rfl,
      show ∀ h, (⟨3 + 2, h⟩ : Fin 6) = 5 from fun _ ↦ rfl]
    ring
  · rw [slot2AxisSum_eq_bitPlane_sum w γ, Fin.sum_univ_six]
    dsimp only [fLo, fHi]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      show (0 : Fin 6).val = 0 from rfl, show (1 : Fin 6).val = 1 from rfl,
      show (2 : Fin 6).val = 2 from rfl, show (3 : Fin 6).val = 3 from rfl,
      show (4 : Fin 6).val = 4 from rfl, show (5 : Fin 6).val = 5 from rfl]
    ring
end ConfigHybridStream288
end HybridStream288Aux
end
end ModHybridStream288

section ModUltraAsymVepTwist288
@[expose] public section
namespace UltraAsymVepTwist288Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end UltraAsymVepTwist288Alt
namespace UltraAsymVepTwist288
section ConfigUltraAsymVepTwist288
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open QRegExt
local instance (priority := 1000000) instNeZeroTwoPowUltraAsymVep (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem realizesClean_of_workspace_subset {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m₁ m₂ n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister k n} {rW₁ : QRegister m₁ n}
    {rW₂ : QRegister m₂ n} {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hSub : rW₁.image ⊆ rW₂.image) (h :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rW₁ u d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rW₂ u d := by
  have hmem (i : Fin m₁) : ∃ j : Fin m₂, rW₂ j = rW₁ i :=
    (QRegister.mem_image rW₂ (rW₁ i)).mp (hSub ((QRegister.mem_image rW₁ _).mpr ⟨i, rfl⟩))
  let qOf : Fin m₁ → Fin m₂ := fun i ↦ Classical.choose (hmem i)
  have hqOf (i : Fin m₁) : rW₂ (qOf i) = rW₁ i := Classical.choose_spec (hmem i)
  let sel : QRegister m₁ m₂ :=
    ⟨⟨qOf, fun i j hij ↦ rW₁.wires.injective ((hqOf i).symm.trans ((congrArg rW₂ hij).trans (hqOf
      j)))⟩⟩
  rw [← (UltraAsymVepTwist288Alt.qreg_ext hqOf : rW₂.compose sel = rW₁)] at h
  exact h.widenWorkspace
theorem asym_embedUnitary_mul_mulVec {k n : ℕ} [NeZero (2 ^ n)] (r : QRegister k n)
    (u₁ u₂ : Unitary (2 ^ k)) (v : Fin (2 ^ n) → ℂ) : (r.embedUnitary (u₁ * u₂)).1.mulVec v =
    (r.embedUnitary u₁).1.mulVec ((r.embedUnitary u₂).1.mulVec v) := by
  rw [r.embedUnitary_mul, Submonoid.coe_mul, Matrix.mulVec_mulVec]
theorem asym_embedUnitary_inv_mulVec_of_eq {k n : ℕ} [NeZero (2 ^ n)] (r : QRegister k n)
    (u : Unitary (2 ^ k)) {v w : Fin (2 ^ n) → ℂ} (h : (r.embedUnitary u).1.mulVec w = v) :
    (r.embedUnitary u⁻¹).1.mulVec v = w := by
  have hm : (r.embedUnitary u⁻¹).1 * (r.embedUnitary u).1 = 1 :=
    congrArg Subtype.val ((r.embedUnitary_mul u⁻¹ u).symm.trans
      ((congrArg r.embedUnitary (inv_mul_cancel u)).trans r.embedUnitary_one))
  rw [← h, Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]
end ConfigUltraAsymVepTwist288
end UltraAsymVepTwist288
end
end ModUltraAsymVepTwist288

section ModCleanZeroSlot2AxisSum288
@[expose] public section
namespace CleanZeroSlot2AxisSum288
theorem zmod2_add_self_cancel (a b : ZMod 2) : a + b + b = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
end CleanZeroSlot2AxisSum288
end
end ModCleanZeroSlot2AxisSum288

section ModZeroSubwireCoinPrep80
@[expose] public section
namespace ZeroSubwireCoinPrep80
section ConfigZeroSubwireCoinPrep80
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowCoin3 {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (sqrtHalf)
open ZeroAncillaUSP hiding ket
open FullSysFullPrepareAndTopConcrete (coreWiresSym selCoin3Sym coreAncSym)
theorem toMatrix_entry00 (M : Mat2Zw) :
    M.toMatrix 0 0 = ((sqrtHalf : ℂ) ^ M.h) * M.m00.toComplex := by
  simp [Mat2Zw.toMatrix]
theorem toMatrix_entry10 (M : Mat2Zw) :
    M.toMatrix 1 0 = ((sqrtHalf : ℂ) ^ M.h) * M.m10.toComplex := by
  simp [Mat2Zw.toMatrix]
theorem wordMatrix2_eq_of_eval (w : List HSTGate) (m : Mat2Zw) (h : evalList w matId = m) :
    wordMatrix2 w = m.toMatrix := by
  rw [wordMatrix2, h]
theorem mul_sqrtHalf_zw {h1 h2 : ℕ} {z1 z2 : Zw} :
    (((sqrtHalf : ℂ) ^ h1) * z1.toComplex) * (((sqrtHalf : ℂ) ^ h2) * z2.toComplex) =
      ((sqrtHalf : ℂ) ^ (h1 + h2)) * (zwMul z1 z2).toComplex := by
  rw [toComplex_zwMul, pow_add]
  ring
def checkAmpWeightErr (z : Zw) (powH aNum aDen wNum wDen errNum errDen : ℤ) : Bool :=
  let p := zwMul z (zwConj z)
  let bigA := aNum * wDen * errDen * p.c0 - wNum * aDen * errDen * powH
  let bigB := aNum * wDen * errDen * p.c1
  let bigR := errNum * aDen * wDen * powH
  leSqrt2Int bigB (bigR - bigA) && leSqrt2Int (-bigB) (bigR + bigA)
theorem amp_weight_err_le (amp : ℂ) (H : ℕ) (z : Zw)
    (aNum aDen wNum wDen errNum errDen : ℕ)
    (hamp : amp = ((sqrtHalf : ℂ) ^ H) * z.toComplex)
    (haDen : 0 < aDen) (hwDen : 0 < wDen) (heDen : 0 < errDen)
    (hchk : checkAmpWeightErr z (Int.ofNat (Nat.pow 2 H))
      (Int.ofNat aNum) (Int.ofNat aDen) (Int.ofNat wNum) (Int.ofNat wDen)
      (Int.ofNat errNum) (Int.ofNat errDen) = true) :
    |((aNum : ℝ) / (aDen : ℝ)) * ‖amp‖ ^ 2 - (wNum : ℝ) / (wDen : ℝ)| ≤
      (errNum : ℝ) / (errDen : ℝ) := by
  let p := zwMul z (zwConj z)
  have hsh_c : (((‖(sqrtHalf : ℂ) ^ H‖ ^ 2 : ℝ) : ℂ)) = (((1 / (2 : ℝ) ^ H : ℝ) : ℂ)) := by
    rw [show (((‖(sqrtHalf : ℂ) ^ H‖ ^ 2 : ℝ) : ℂ)) = ((sqrtHalf : ℂ) ^ H) * star ((sqrtHalf : ℂ) ^
      H) by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq],
      star_pow, MeasureBranchHadamardSem.star_sqrtHalf, ← mul_pow,
      MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
    push_cast
    rw [one_div, inv_pow, one_div]
  have hnorm : ‖amp‖ ^ 2 = ((p.c0 : ℝ) + (p.c1 : ℝ) * √2) / ((2 : ℝ) ^ H) := by
    rw [hamp, norm_mul, mul_pow, Complex.ofReal_injective hsh_c, normSq_zw_eq z]
    dsimp only [p]
    ring
  simp only [checkAmpWeightErr, Bool.and_eq_true, Int.ofNat_eq_natCast, show Nat.pow 2 H =
    2 ^ H from rfl] at hchk
  have hU := leSqrt2Int_sound _ _ hchk.1
  have hL := leSqrt2Int_sound _ _ hchk.2
  push_cast at hU hL
  have hposA : (0 : ℝ) < aDen := by exact_mod_cast haDen
  have hposW : (0 : ℝ) < wDen := by exact_mod_cast hwDen
  have hposE : (0 : ℝ) < errDen := by exact_mod_cast heDen
  have hposH : (0 : ℝ) < (2 : ℝ) ^ H := by positivity
  let D : ℝ := (aDen : ℝ) * (wDen : ℝ) * (errDen : ℝ) * (2 : ℝ) ^ H
  have hprodPos : 0 < D := by positivity
  have hDiff : (((aNum : ℝ) / (aDen : ℝ)) * (((p.c0 : ℝ) + (p.c1 : ℝ) * √2) / (2 : ℝ) ^ H) -
      (wNum : ℝ) / (wDen : ℝ)) * D =
      ((aNum : ℝ) * (wDen : ℝ) * (errDen : ℝ) * (p.c0 : ℝ) -
        (wNum : ℝ) * (aDen : ℝ) * (errDen : ℝ) * (2 : ℝ) ^ H) +
        (aNum : ℝ) * (wDen : ℝ) * (errDen : ℝ) * (p.c1 : ℝ) * √2 := by
    dsimp only [D]
    field_simp [hposA.ne', hposH.ne', hposW.ne']
    ring
  have hErr : ((errNum : ℝ) / (errDen : ℝ)) * D =
      (errNum : ℝ) * (aDen : ℝ) * (wDen : ℝ) * (2 : ℝ) ^ H := by
    dsimp only [D]
    field_simp [hposE.ne']
  rw [hnorm, abs_le]
  refine ⟨le_of_mul_le_mul_right ?_ hprodPos, le_of_mul_le_mul_right (by linarith) hprodPos⟩
  rw [neg_mul]
  linarith
theorem coinHwa : 3 + 1 = 4 := rfl
abbrev wCoin0 : Wire 4 := ⟨0, by decide⟩
abbrev wCoin1 : Wire 4 := ⟨1, by decide⟩
abbrev wCoin2 : Wire 4 := ⟨2, by decide⟩
abbrev wCoinAnc : Wire 4 := ⟨3, by decide⟩
def bits4 (b0 b1 b2 b3 : ZMod 2) : BitAssignment 4 := fun q ↦ if q.val = 0 then b0 else if
    q.val = 1 then b1 else if q.val = 2 then b2 else b3
@[simp] theorem bits4_0 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoin0 = b0 := rfl
@[simp] theorem bits4_1 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoin1 = b1 := rfl
@[simp] theorem bits4_2 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoin2 = b2 := rfl
@[simp] theorem bits4_3 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoinAnc = b3 := rfl
@[simp] theorem upd_bits4_0 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoin0 v = bits4 v b1 b2 b3 :=
  funext fun q ↦ by fin_cases q <;> rfl
@[simp] theorem upd_bits4_1 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoin1 v = bits4 b0 v b2 b3 :=
  funext fun q ↦ by fin_cases q <;> rfl
@[simp] theorem upd_bits4_2 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoin2 v = bits4 b0 b1 v b3 :=
  funext fun q ↦ by fin_cases q <;> rfl
@[simp] theorem upd_bits4_3 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoinAnc v = bits4 b0 b1 b2 v :=
  funext fun q ↦ by fin_cases q <;> rfl
def coin3Bit0 : Fin 8 → ZMod 2
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 1 | ⟨6, _⟩ => 0 | ⟨7, _⟩ => 1
def coin3Bit1 : Fin 8 → ZMod 2
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1 | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 0 | ⟨6, _⟩ => 1 | ⟨7, _⟩ => 1
def coin3Bit2 : Fin 8 → ZMod 2
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 1 | ⟨6, _⟩ => 1 | ⟨7, _⟩ => 1
theorem basisBits_coin3_bits (c : Fin 8) :
    basisBits 3 c ⟨0, by decide⟩ = coin3Bit0 c ∧
    basisBits 3 c ⟨1, by decide⟩ = coin3Bit1 c ∧
    basisBits 3 c ⟨2, by decide⟩ = coin3Bit2 c := by
  rw [basisBits_eq_div_mod, basisBits_eq_div_mod, basisBits_eq_div_mod]
  fin_cases c <;> decide
noncomputable def wIdealRat : Fin 6 → ℝ
  | ⟨0, _⟩ => 3441613 / 100
  | ⟨1, _⟩ => 51871 / 125
  | ⟨2, _⟩ => 231140195423637 / 4294967296
  | ⟨3, _⟩ => 0x10000000000000000000 / 0x341bfdb85de7ae4f
  | ⟨4, _⟩ => 115221930763381 / 4294967296
  | ⟨5, _⟩ => 0
abbrev rCoin3Core (mPayload : ℕ) : QRegister 3 (coreWiresSym mPayload) :=
  (coreAncSym mPayload).compose (selCoin3Sym mPayload)
theorem two_le_max100 (m : ℕ) : 1 + 1 ≤ Nat.max 100 m :=
  le_trans (by decide : 1 + 1 ≤ 100) (Nat.le_max_left 100 m)
end ConfigZeroSubwireCoinPrep80
end ZeroSubwireCoinPrep80
end
end ModZeroSubwireCoinPrep80

section ModWeighted3A2TierBClean80Closure
@[expose] public section
namespace TierClosure
section FastBarrelTierAdapters
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowFast145 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
-- Root solution namespace already active.
open MeasureBranchHadamardSem (ket)
open SpecsAux.SpecMirror
open PosMomSelectSandwich (slotBitProj)
open FullSysFullPrepareAndTopConcrete (corePayloadSym)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle momCoreWires momCoinProj coinBitFin2 iSlot0Mom
  iSlot1Mom iSlot2Mom)
open FullSysCatSegmentBridge (fullSysCoreWires iSlot0 iSlot1 iSlot2)
open OraAndPrepBundle (momCoreWires_eq_fullSysCoreWires coreUnitaryFromFullSys)
theorem uBarrelFast_mul_posSlot2Proj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (hm22 : 22 ≤ mPayload) :
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 * slotBitProj (iSlot2 mPayload) 0 =
      (NuclearTwistRealizes.uBarrelCore true hm22).1 * slotBitProj (iSlot2 mPayload) 0 := by
  refine (?_ : (CoinDispatchedBarrel288.uBarrelFast hmPay).1 * slotBitProj (iSlot2 mPayload) 0 =
    (CoinDispatchedBarrel288.uBarrel hmPay).1 * slotBitProj (iSlot2 mPayload) 0).trans
    (uBarrel_mul_posSlot2Proj hmPay hm22)
  apply matrix_eq_of_mulVec_ket
  intro γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, slotBitProj_mulVec_ket,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  dsimp only [Fin.val_zero]
  by_cases hc2 : γ (iSlot2 mPayload) = 0
  · simp [hc2, CoinDispatchedBarrel288.uBarrelFast_mulVec_ket,
      CoinDispatchedBarrel288.uBarrel_mulVec_ket,
      CoinDispatchedBarrel288.coinBarrelBitFnFast_c2_zero hmPay γ hc2]
  · simp [hc2]
theorem slot0LocalData_barrelFast_ket_eq {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (uBarrelFlag :
    SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))) (hBarrelEq : ∀
    cfg, uBarrelFlag cfg = CoinDispatchedBarrel288.uBarrelFast hmPay)
    (cfg : SpecsAux.SpecMirror.Configuration) (β : BitAssignment (momCoreWires mPayload))
    (_hc0 : β (iSlot0Mom mPayload) = 0) (hc1 : β (iSlot1Mom mPayload) = 0)
    (hc2 : β (iSlot2Mom mPayload) = 1) : (coreUnitaryFromFullSys (uBarrelFlag cfg)).1.mulVec
    (ket β) = ket (MomSlot0LocalAndMomCombine288.swapElec0Bits
    (MomSlot0LocalAndMomCombine288.slot0ElecIdx hmPay β) β) := by
  rw [hBarrelEq cfg]
  refine castNatUnitary_mulVec_ket_at (momCoreWires_eq_fullSysCoreWires mPayload)
    (CoinDispatchedBarrel288.uBarrelFast hmPay)
    (CoinDispatchedBarrel288.coinBarrelBitFnFast hmPay)
    (CoinDispatchedBarrel288.uBarrelFast_mulVec_ket hmPay) β
    (MomSlot0LocalAndMomCombine288.swapElec0Bits (MomSlot0LocalAndMomCombine288.slot0ElecIdx
    hmPay β) β) fun w ↦ ?_
  have hCore4034 : 4034 ≤ fullSysCoreWires mPayload := by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega
  let γ : BitAssignment (fullSysCoreWires mPayload) :=
    fun q ↦ β ⟨q.val, (momCoreWires_eq_fullSysCoreWires mPayload).symm ▸ q.isLt⟩
  have hPay (k : ℕ) (hk : k < mPayload) (hkC : 3954 + k < fullSysCoreWires mPayload) :
      γ ⟨3954 + k, hkC⟩ = β (corePayloadSym mPayload ⟨k, hk⟩) :=
    congrArg β (Fin.ext (by
      dsimp [corePayloadSym, TierClosureAlt.qreg_block_apply,
        TierClosureAlt.qreg_block_wires_apply,
        TierClosureAlt.qreg_whole_wires,
        TierClosureAlt.emb_trans_apply,
        TierClosureAlt.emb_refl_apply,
        TierClosureAlt.emb_mk_apply, SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]))
  have hu36 :
      (∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val) =
        CoinDispatchedBarrel288.Internal.bitsVal (fun j : Fin 36 ↦ γ ⟨3954 + j.val, by omega⟩) :=
    Finset.sum_congr rfl fun j _ ↦
      congrArg (fun z : ZMod 2 ↦ z.val * 2 ^ j.val) (hPay j.val (by omega) (by omega)).symm
  let kIdx := MomSlot0LocalAndMomCombine288.slot0ElecIdx hmPay β
  have hc4 : CoinDispatchedBarrel288.coinBarrelBitFnFast hmPay γ =
      CoinDispatchedBarrel288.swapElec0Bits kIdx γ := by
    dsimp only [CoinDispatchedBarrel288.coinBarrelBitFnFast,
      CoinDispatchedBarrel288.coinBarrelIdxFast]
    simp only [show γ (iSlot1 mPayload) = 0 from (congrArg β (Fin.ext rfl)).trans hc1,
      show γ (iSlot2 mPayload) = 1 from (congrArg β (Fin.ext rfl)).trans hc2,
      show ¬((1 : ZMod 2) = 0) by decide, show ¬((0 : ZMod 2) = 1) by decide, ↓reduceIte]
    refine congrFun (congrArg (@CoinDispatchedBarrel288.swapElec0Bits mPayload) (Fin.ext ?_)) γ
    dsimp only [kIdx, MomSlot0LocalAndMomCombine288.slot0ElecIdx]
    rw [← hu36, congrArg ZMod.val (hPay 36 (by omega) (by omega))]
  rw [hc4, swapElec0Bits_mom_eq_barrel kIdx β w]
noncomputable def mkSlot0LocalDataOfBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (uBarrelFlag : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload)))
    (hBarrelEq : ∀ cfg, uBarrelFlag cfg = CoinDispatchedBarrel288.uBarrelFast hmPay) :
    MomSlot0LocalAndMomCombine288.MomLocalSlotData mPayload 48 0
    (fun cfg ↦ coreUnitaryFromFullSys (uBarrelFlag cfg)) :=
  MomSlot0LocalAndMomCombine288.slot0LocalData hmPay
    (fun cfg ↦ coreUnitaryFromFullSys (uBarrelFlag cfg))
    (fun _ β ↦ MomSlot0LocalAndMomCombine288.slot0ElecIdx hmPay β)
    (fun _ β ↦ MomSlot0LocalAndMomCombine288.slot0ElecIdx_swapElec0Bits hmPay _ β)
    (fun _ _ _ _ _ _ ↦ rfl) (slot0LocalData_barrelFast_ket_eq hmPay uBarrelFlag hBarrelEq)
theorem coreFromFullSys_uBarrelFast_mul_momCoinProj_coin6 {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) : (coreUnitaryFromFullSys (CoinDispatchedBarrel288.uBarrelFast
    hmPay)).1 * momCoinProj mPayload 6 = momCoinProj mPayload 6 := by
  have hFlag : (CoinDispatchedBarrel288.uBarrelFast hmPay).1 * (slotBitProj (iSlot0 mPayload)
      (coinBitFin2 6 0) * slotBitProj (iSlot1 mPayload) (coinBitFin2 6 1) * slotBitProj
      (iSlot2 mPayload) (coinBitFin2 6 2)) = slotBitProj (iSlot0 mPayload) (coinBitFin2 6 0) *
      slotBitProj (iSlot1 mPayload) (coinBitFin2 6 1) * slotBitProj (iSlot2 mPayload)
      (coinBitFin2 6 2) := by
    apply matrix_eq_of_mulVec_ket
    intro γ
    simp only [← Matrix.mulVec_mulVec, slotBitProj_mulVec_ket, Matrix.mulVec_smul,
      show coinBitFin2 6 0 = 0 by decide, show coinBitFin2 6 1 = 1 by decide,
      show coinBitFin2 6 2 = 1 by decide]
    dsimp only [Fin.val_one, Fin.val_zero]
    by_cases hc2 : γ (iSlot2 mPayload) = 1
    · by_cases hc1 : γ (iSlot1 mPayload) = 1
      · by_cases hc0 : γ (iSlot0 mPayload) = 0
        · simp [hc0, hc1, hc2, CoinDispatchedBarrel288.uBarrelFast_mulVec_ket,
            CoinDispatchedBarrel288.coinBarrelBitFnFast, CoinDispatchedBarrel288.coinBarrelIdxFast,
            CoinDispatchedBarrel288.swapElec0Bits]
        · simp [hc0, hc1, hc2]
      · simp [hc1, hc2]
    · simp [hc2]
  simpa only [coreUnitaryFromFullSys, OraAndPrepBundle.castNatOp_val_unitary,
    OraAndPrepBundle.castNatOp_mul, momCoinProj,
    OraAndPrepBundle.castNatOp_slotBitProj _ (iSlot0 mPayload) (iSlot0Mom mPayload) rfl,
    OraAndPrepBundle.castNatOp_slotBitProj _ (iSlot1 mPayload) (iSlot1Mom mPayload) rfl,
    OraAndPrepBundle.castNatOp_slotBitProj _ (iSlot2 mPayload) (iSlot2Mom mPayload) rfl] using
    congrArg (OraAndPrepBundle.castNatOp (momCoreWires_eq_fullSysCoreWires mPayload).symm) hFlag
noncomputable def liftSlot3OfBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (s3 : MomSingleSlotOracle mPayload 48 3) (uBarrelFlag : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (fullSysCoreWires mPayload))) (hBarrelEq : ∀ cfg, uBarrelFlag cfg =
    CoinDispatchedBarrel288.uBarrelFast hmPay) :
    MomSlot0LocalAndMomCombine288.MomLocalSlotData mPayload 48 3
    (fun cfg ↦ coreUnitaryFromFullSys (uBarrelFlag cfg)) :=
  MomSlot0LocalAndMomCombine288.liftOracleWithIdOnCoin s3
    (fun cfg ↦ coreUnitaryFromFullSys (uBarrelFlag cfg))
    (fun cfg ↦ hBarrelEq cfg ▸ coreFromFullSys_uBarrelFast_mul_momCoinProj_coin6 hmPay)
end FastBarrelTierAdapters
end TierClosure
namespace TierBClean80Closure
section ConfigTierBClean80Closure
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 16384
local instance (priority := 1000000) instNeZeroTwoPowTierBClean80 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (FullSysQft654Bundle)
open OraAndPrepBundle (coreUnitaryFromFullSys posCoin01Proj)
open FullSysHoistedSelectStitch (HoistedBarrelSpec)
open GeneralBetaAndAlphaTopEndpoint (zeroMomSlotOracle5)
open TierClosure (uBarrelFast_mul_posSlot2Proj zeroMomLocalSlotData)
noncomputable def tierBBarrel80 : HoistedBarrelSpec 80 288 :=
  FastCoinBarrel288.fastHoistedBarrelSpec145 (le_refl 80)
theorem tierBBarrel80_onP01 (cfg : Configuration) :
    (tierBBarrel80.uBarrel cfg).1 * posCoin01Proj 80 =
      (NuclearTwistRealizes.uBarrelCore true (by decide : 22 ≤ 80)).1 * posCoin01Proj 80 := by
  unfold tierBBarrel80 posCoin01Proj
  rw [FastCoinBarrel288.fastHoistedBarrelSpec145_uBarrel (le_refl 80) cfg, ← Matrix.mul_assoc,
    uBarrelFast_mul_posSlot2Proj (le_refl 80) (by decide : 22 ≤ 80), Matrix.mul_assoc]
noncomputable def tierBL5Zero80 : MomSlot0LocalAndMomCombine288.MomLocalSlotData 80 48 5
    (fun cfg ↦ coreUnitaryFromFullSys (tierBBarrel80.uBarrel cfg)) := zeroMomLocalSlotData
    (fun cfg ↦ coreUnitaryFromFullSys (tierBBarrel80.uBarrel cfg)) (zeroMomSlotOracle5 80 48)
    (fun _ ↦ rfl)
noncomputable def tierBQftFull : FullSysQft654Bundle :=
  DyadicQft64WalkCircuit288.fullSysQft654Bundle288
noncomputable def tierBQftCore : FullSysQft654Bundle :=
  DyadicQft64WalkCircuit288.coreQftHadamardBundle288
theorem tierBQftFull_eq_core_mul_uPre654 :
    tierBQftFull.uQft654 = tierBQftCore.uQft654 * FusedPreDiagFromTwist288.uPre654 :=
  DyadicQft64WalkCircuit288.qft64Ideal654Unitary_eq_core_mul_preDiag
end ConfigTierBClean80Closure
end TierBClean80Closure
end
end ModWeighted3A2TierBClean80Closure

section ModMergedVepLeaf4GridPerturbation
@[expose] public section
namespace MergedVepLeaf4GridPerturbation
section ConfigMergedVepLeaf4GridPerturbation
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 16384
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowLeaf4GridPert (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosSlots24SemanticOracleConcrete80 (coherentSysOp80 QftPreservesCoset3
  qftPreservesCoset3_of_eq_ideal)
open PosSlots24Semantic80Physics (pos80IdealDist)
open PosPostPrep80MergedVep (wCore3967 wCore4029 swapCore3967Fn muSlot2Ideal218)
open MergedVepTopCoinCollapse (mWCore3967Gen mWCoreScrGen swapCoreScrGenFn)
open PosPostPrep80L1Bounds (mergedCoherentOp80_muSlot2Ideal218_eq coherentSysOp80_conjTranspose
  mergedCoherentOp80_conjTranspose)
open Pos24MergedVepPrepAndStitch (mergedPosSlot2BUnitTwosGen)
open TierBClean80Closure (tierBQftFull)
noncomputable def tierBB2RawId (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  coherentSysOp80 tierBQftFull cfg false (pos80IdealDist false)
noncomputable def tierBB2Id (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  mergedPosSlot2BUnitTwosGen ((108 : ℝ) / 109) tierBB2RawId cfg
noncomputable def tierBB4Id (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  coherentSysOp80 tierBQftFull cfg true (pos80IdealDist true)
theorem tierBQftFull_preservesCoset3 : QftPreservesCoset3 tierBQftFull :=
  qftPreservesCoset3_of_eq_ideal tierBQftFull rfl
theorem swapCore3967Fn_eq_swapCoreScrGenFn12 (β : BitAssignment (fullSysCoreWires 80)) :
    swapCore3967Fn β = swapCoreScrGenFn (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ β := by
  funext q
  unfold swapCore3967Fn swapCoreScrGenFn
  rw [show wCore3967 = mWCore3967Gen (le_rfl : 80 ≤ 80) from rfl,
    show wCore4029 = mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ from rfl]
theorem tierBB2Id_isHermitian (cfg : Configuration) : (tierBB2Id cfg).IsHermitian := by
  unfold tierBB2Id tierBB2RawId Matrix.IsHermitian
  rw [← mergedCoherentOp80_muSlot2Ideal218_eq tierBQftFull cfg]
  exact mergedCoherentOp80_conjTranspose tierBQftFull cfg muSlot2Ideal218
theorem tierBB4Id_isHermitian (cfg : Configuration) : (tierBB4Id cfg).IsHermitian :=
  coherentSysOp80_conjTranspose tierBQftFull cfg true (pos80IdealDist true)
end ConfigMergedVepLeaf4GridPerturbation
end MergedVepLeaf4GridPerturbation
end
end ModMergedVepLeaf4GridPerturbation

end QuantumComputation.Specs.StoppingPowerSolution
