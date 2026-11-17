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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.BernsteinPotQuadUnload
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge
set_option exponentiation.threshold 256

noncomputable section
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.XMeasChunkQromUnldA
  PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
  (unitary_inv_comm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (AndBracketProg)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr PgBase.phaseGradientState
    phaseFlipUnitary bSpeciesSwap50
attribute [local irreducible] PhotochemistrySolution.Stage4KinFull.bAxisMux27
theorem circWires_toCircuit_c70 {K : ℕ} {P : Wire K → Prop} :
    ∀ {b : AndBracketProg K}, AndBracketWires P b → CircWires P b.toCircuit
  | .id, _ => trivial
  | .prim _, hc => hc
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨circWires_toCircuit_c70 h₁, circWires_toCircuit_c70 h₂⟩
  | .tempAnd _ _ _ _ _ _ _, ⟨hc₁, hc₂, ha, hb⟩ =>
      ⟨fun | ⟨0, _⟩ => hc₁ | ⟨1, _⟩ => hc₂ | ⟨2, _⟩ => ha,
        circWires_toCircuit_c70 hb,
        fun | ⟨0, _⟩ => hc₁ | ⟨1, _⟩ => hc₂ | ⟨2, _⟩ => ha⟩
theorem circ_comm_embedMatrix_c70 {m n : ℕ} (rC : QRegister m n) (M : Operator (2 ^ m)) :
    ∀ {c : Circuit n}, CircWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) c →
      c.eval.1 * rC.embedMatrix M = rC.embedMatrix M * c.eval.1
  | .identity, _ => by simp [Circuit.eval_identity]
  | .seq _ _, ⟨h₁, h₂⟩ => by
      simpa only [Circuit.eval_seq,
          Submonoid.coe_mul] using (Commute.mul_left (circ_comm_embedMatrix_c70 rC M h₂)
          (circ_comm_embedMatrix_c70 rC M h₁)).eq
  | .gate g reg, hg =>
        reg.embedMatrix_comm_of_disjoint rC (QRegister.disjoint_iff.mpr fun i j e ↦
        hg i j e) g.eval.1 M
theorem projBits_eq_embedMatrix_c70 {m n : ℕ} [NeZero (2 ^ m)] [NeZero (2 ^ n)] (rC : QRegister m n)
    (δ : BitAssignment m) : projBits_c70 rC δ = rC.embedMatrix (projBits_c70 (QRegister.whole m) δ)
    := by
  rw [embedMatrix_projBits_c70,
    show rC.compose (QRegister.whole m) =
        rC from congrArg QRegister.mk (Function.Embedding.ext fun _ ↦ rfl)]
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.Sub5885 PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
/- ## Concatenated Bit-Slice Projectors & Multiplexers -/

/-- Concatenate `γ : BitAssignment k₁` and `ω : BitAssignment k₂` onto `BitAssignment (k₁ + k₂)`. -/
def concatBitsGen {k₁ k₂ : ℕ} (γ : BitAssignment k₁) (ω : BitAssignment k₂) : BitAssignment (k₁ +
    k₂) := Sum.elim γ ω ∘ finSumFinEquiv.symm
@[simp] theorem concatBitsGen_castAdd {k₁ k₂ : ℕ} (γ : BitAssignment k₁) (ω : BitAssignment k₂)
    (i : Fin k₁) : concatBitsGen γ ω
    (Fin.castAdd k₂ i) = γ i :=
        congrArg (Sum.elim γ ω) (finSumFinEquiv.symm_apply_apply (Sum.inl i))
@[simp] theorem concatBitsGen_natAdd {k₁ k₂ : ℕ} (γ : BitAssignment k₁) (ω : BitAssignment k₂)
    (j : Fin k₂) : concatBitsGen γ ω
    (Fin.natAdd k₁ j) = ω j := congrArg (Sum.elim γ ω) (finSumFinEquiv.symm_apply_apply (Sum.inr j))
theorem concatBitsEquiv_left_inv {k₁ k₂ : ℕ} (p : BitAssignment k₁ × BitAssignment k₂) :
    (fun i ↦ concatBitsGen p.1 p.2 (Fin.castAdd k₂ i), fun j ↦
    concatBitsGen p.1 p.2 (Fin.natAdd k₁ j)) = p :=
  Prod.ext (funext fun i ↦ concatBitsGen_castAdd p.1 p.2 i)
      (funext fun j ↦ concatBitsGen_natAdd p.1 p.2 j)
theorem concatBitsEquiv_right_inv {k₁ k₂ : ℕ} (γω : BitAssignment (k₁ + k₂)) :
    concatBitsGen (fun i ↦ γω (Fin.castAdd k₂ i)) (fun j ↦ γω (Fin.natAdd k₁ j)) = γω :=
  funext fun u ↦ (finSumFinEquiv.surjective u).elim fun s hs ↦
      hs ▸ Sum.casesOn s (concatBitsGen_castAdd _ _) (concatBitsGen_natAdd _ _)
/-- Equivalence `(BitAssignment k₁ × BitAssignment k₂) ≃ BitAssignment (k₁ + k₂)`. -/
def concatBitsEquiv (k₁ k₂ : ℕ) :
    (BitAssignment k₁ × BitAssignment k₂) ≃ BitAssignment (k₁ + k₂) where
  toFun p := concatBitsGen p.1 p.2
  invFun γω := (fun i ↦ γω (Fin.castAdd k₂ i), fun j ↦ γω (Fin.natAdd k₁ j))
  left_inv := concatBitsEquiv_left_inv
  right_inv := concatBitsEquiv_right_inv
theorem muxMat_concat_eq_c70 {k₁ k₂ n : ℕ} [NeZero (2 ^ n)] (r₁ : QRegister k₁ n)
    (r₂ : QRegister k₂ n) (hd : r₁.DisjointWires r₂) (U : BitAssignment (k₁ + k₂) → Unitary (2 ^ n))
    (hC₂ : ∀ γ ω ω', (U (concatBitsGen γ ω)).1 * projBits_c70 r₂ ω' = projBits_c70 r₂ ω' *
    (U (concatBitsGen γ ω)).1) : muxMat_c70 (r₁.concat r₂ hd) U = muxMat_c70 r₁ (fun γ ↦
    muxUnitary_c70 r₂ (fun ω ↦ U (concatBitsGen γ ω)) (hC₂ γ)) := by
  unfold muxMat_c70
  rw [← Equiv.sum_comp (concatBitsEquiv k₁ k₂), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  change (∑ ω, (U (concatBitsGen γ ω)).1 * projBits_c70 (r₁.concat r₂ hd) (concatBitsGen γ ω)) =
    (∑ ω, (U (concatBitsGen γ ω)).1 * projBits_c70 r₂ ω) * projBits_c70 r₁ γ
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [show projBits_c70 (r₁.concat r₂ hd) (concatBitsGen γ ω) = projBits_c70 r₁ γ *
      projBits_c70 r₂ ω from
      matrix_ext_ket fun β ↦ by
        have hIff : (∀ u, β ((r₁.concat r₂ hd) u) = concatBitsGen γ ω u) ↔ (∀ i, β (r₁ i) = γ i) ∧
            (∀ j, β (r₂ j) = ω j) :=
          ⟨fun h ↦
              ⟨fun i ↦
              by simpa only [QRegister.concat_apply_left,
                   concatBitsGen_castAdd] using h (Fin.castAdd k₂ i),
            fun j ↦
                by simpa only [QRegister.concat_apply_right,
                     concatBitsGen_natAdd] using h (Fin.natAdd k₁ j)⟩,
           fun ⟨h1, h2⟩ u ↦ (finSumFinEquiv.surjective u).elim fun s hs ↦ hs ▸ Sum.casesOn s
            (fun i ↦
                (congrArg β (QRegister.concat_apply_left r₁ r₂ hd i)).trans ((h1 i).trans
                (concatBitsGen_castAdd γ ω i).symm))
            (fun j ↦
                (congrArg β (QRegister.concat_apply_right r₁ r₂ hd j)).trans ((h2 j).trans
                (concatBitsGen_natAdd γ ω j).symm))⟩
        rw [← Matrix.mulVec_mulVec, projBits_mulVec_ket_c70, projBits_mulVec_ket_c70]
        split_ifs with hA h2 h2'
        · rw [projBits_mulVec_ket_c70, ite_eq_left (hIff.mp hA).1]
        · exact absurd (hIff.mp hA).2 h2
        · rw [projBits_mulVec_ket_c70, ite_eq_right fun h1 ↦ hA (hIff.mpr ⟨h1, h2'⟩)]
        · rw [Matrix.mulVec_zero],
    Matrix.mul_assoc, show projBits_c70 r₁ γ * projBits_c70 r₂ ω = projBits_c70 r₂ ω *
        projBits_c70 r₁ γ by
      rw [projBits_eq_embedMatrix_c70 r₁ γ, projBits_eq_embedMatrix_c70 r₂ ω]
      exact r₁.embedMatrix_comm_of_disjoint r₂ hd _ _, ← Matrix.mul_assoc]
/- ## Generic Outer-Coin Subregister `rOutLayout` & `rCoinExtOut` -/

/-- Physical subregister of `rOuter41Layout` indexed by `rSub : QRegister kOut 41`. -/
def rOutLayout {kOut : ℕ} (rSub : QRegister kOut 41) : QRegister kOut dLayout :=
    rOuter41Layout.compose rSub
theorem val_rOutLayout {kOut : ℕ} (rSub : QRegister kOut 41)
    (j : Fin kOut) : (rOutLayout rSub j).val = 7215 + (rSub j).val := val_rOuter41Layout (rSub j)
theorem val_rOutLayout_bounds {kOut : ℕ} (rSub : QRegister kOut 41) (j : Fin kOut) : 7215 ≤
    (rOutLayout rSub j).val ∧ (rOutLayout rSub j).val <
    7256 := by have hj := (rSub j).isLt; rw [val_rOutLayout]; omega
theorem rCoinExt_disj_rOutLayout {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41) :
    (rCoinExt kExt hk).DisjointWires (rOutLayout rSub) :=
  disj_of_ne fun i j e ↦ by
    have hi := i.isLt; have hb := val_rOutLayout_bounds rSub j
    have hv := congrArg Fin.val e; rw [val_rCoinExt] at hv; omega
/--
Concatenated `(kExt + kOut)` -wire coin register `(rCoinExt kExt hk).concat (rOutLayout rSub)` .
-/
def rCoinExtOut {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41) : QRegister (kExt +
    kOut) dLayout := (rCoinExt kExt hk).concat (rOutLayout rSub) (rCoinExt_disj_rOutLayout hk rSub)
theorem val_rCoinExtOut_bounds {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (u : Fin (kExt + kOut)) : 7215 - kExt ≤ (rCoinExtOut hk rSub u).val ∧
    (rCoinExtOut hk rSub u).val < 7256 := by
  have := u.isLt
  by_cases hlt : u.val < kExt
  · rw [show rCoinExtOut hk rSub u = rCoinExt kExt hk ⟨u.val,
        hlt⟩ from QRegister.concat_apply_left _ _ _ ⟨u.val, hlt⟩, val_rCoinExt]
    omega
  · have := val_rOutLayout_bounds rSub ⟨u.val - kExt, by omega⟩
    rw [(congrArg (rCoinExtOut hk rSub).wires (Fin.ext (by
      dsimp [Fin.natAdd]
      omega))).trans
      (QRegister.concat_apply_right _ _ _ ⟨u.val - kExt, by omega⟩)]
    omega
theorem rCoinExtOut_disj_off {kExt kOut k : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    {r : QRegister k dLayout}
    (hoff4 : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) : (rCoinExtOut hk rSub).DisjointWires r :=
  disj_of_ne fun u i e ↦ by
    have hb := hoffIndex_bounds_layout hoff4 i; have hc := val_rCoinExtOut_bounds hk rSub u
    have hv := congrArg Fin.val e; omega
/- ## Stage-1 / Stage-2 Commutation & Ket Readout on `rOutLayout` -/

theorem wNoHadClean_comm_projBits_rOutLayout {kOut : ℕ} (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (rSub : QRegister kOut 41) (ω : BitAssignment kOut) :
    Commute (wNoHad (uStage1Clean_c70 decode)).1 (projBits_c70 (rOutLayout rSub) ω) := by
  rw [wNoHad, Submonoid.coe_mul, Submonoid.coe_mul]
  refine Commute.mul_left (by
      rw [projBits_eq_embedMatrix_c70 (rOutLayout rSub) ω]
      exact comm_uRouterSwapConj_embedMat_pot rElecLayout (rOutLayout rSub) (fun i j e ↦ by
        have : i.val < 5056 := hEW5056 ▸ i.isLt; have := val_rOutLayout_bounds rSub j
        have hv : (elecRouterWireFn i).val = _ := congrArg Fin.val e
        rw [val_elecRouterWireFn] at hv; split_ifs at hv <;> omega) _)
    (Commute.mul_left (by
        rw [projBits_eq_embedMatrix_c70 (rOutLayout rSub) ω]
        exact comm_uRouterSwapConj_embedMat_pot rNucLayout (rOutLayout rSub) (fun i j e ↦ by
          have : i.val < 1394 := hNW1394 ▸ i.isLt; have := val_rOutLayout_bounds rSub j
          have hv : (nucRouterWireFn i).val = _ := congrArg Fin.val e
          rw [val_nucRouterWireFn] at hv; split_ifs at hv <;> omega) _)
      (matrix_ext_ket fun β ↦ by
        have hFix (γ : BitAssignment dLayout) (j : Fin kOut) :
            DynCircExt.writeReg γ rStage1Clean122_c70 (stage1Clean122Bits_c70 decode (fun i ↦
                γ (rStage1Clean122_c70 i))) (rOutLayout rSub j) = γ (rOutLayout rSub j) := by
          let i82 : Fin (mLayout + 2) := ⟨(rSub j).val, fin41_lt_mLayout (rSub j)⟩
          rw [show rOutLayout rSub j = rStage1Clean122_c70 (Fin.natAdd 40 i82) from
            (Fin.ext (by rw [val_rOutLayout, val_rLcu82Layout])).trans
              (QRegister.concat_apply_right rOut40Layout rLcu82Layout hDisjOut40Lcu82_c70 i82).symm,
            DynCircExt.writeReg_apply_reg]
          exact ite_eq_right (by
            dsimp only [Fin.natAdd]
            omega)
        have hKet (γ : BitAssignment dLayout) : (uStage1Clean_c70 decode).1.mulVec (ket γ) =
            ket (DynCircExt.writeReg γ rStage1Clean122_c70 (stage1Clean122Bits_c70 decode
                (fun i ↦ γ (rStage1Clean122_c70 i)))) := by
          rw [uStage1Clean_c70, QRegister.embedUnitary_val]
          exact embedMatrix_ket_eq_writeReg rStage1Clean122_c70 _ γ (involUnitary_mulVec_ket_c70
              _ _ _)
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, projBits_mulVec_ket_c70, hKet β,
            projBits_mulVec_ket_c70]
        by_cases hc : ∀ j : Fin kOut, β (rOutLayout rSub j) = ω j
        · rw [ite_eq_left hc, hKet β, ite_eq_left (fun j ↦ (hFix β j).trans (hc j))]
        · rw [ite_eq_right hc, Matrix.mulVec_zero, ite_eq_right (fun h' ↦ hc fun j ↦
              (hFix β j).symm.trans (h' j))]))
theorem wNoHad_conj_uStage1Clean_mul_pScr {w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decode) (u4 : Unitary (2 ^ dLayout))
    (hComm : pScr * (preConj o1.uLocal u4).1 = (preConj o1.uLocal u4).1 * pScr) :
    (((wNoHad (uStage1Clean_c70 decode))⁻¹ * u4 * wNoHad (uStage1Clean_c70 decode)).1) *
    pScr = (((wNoHad o1.uLocal)⁻¹ * u4 * wNoHad o1.uLocal).1) * pScr := by
  have hU (u1 : Unitary (2 ^ dLayout)) : uHad82Layout.1 * ((preConj u1 u4).1 * pScr) *
      (uHad82Layout⁻¹).1 =
      ((wNoHad u1)⁻¹ * u4 * wNoHad u1).1 * pScr := by
    rw [← Matrix.mul_assoc _ _ pScr, ← Submonoid.coe_mul,
      show uHad82Layout * preConj u1 u4 = ((wNoHad u1)⁻¹ * u4 * wNoHad u1) *
          uHad82Layout by
            unfold preConj wFull
            group,
      Submonoid.coe_mul]
    simp only [Matrix.mul_assoc]
    rw [(unitary_inv_comm uHad82Layout pScr comm_pScr_uHad82.eq).symm,
      ← Matrix.mul_assoc uHad82Layout.1, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
          Matrix.one_mul]
  rw [← hU (uStage1Clean_c70 decode), ← hU o1.uLocal, preConj_uStage1Clean_mul_c70 o1 u4 hComm]
/-- Raw `BitAssignment kOut` read out from `c : Fin (2 ^ 41)` on `rOutLayout rSub`. -/
def outSubRawBits {kOut : ℕ} (rSub : QRegister kOut 41) (c : Fin (2 ^ 41)) : BitAssignment kOut :=
    fun j ↦ if c.val.testBit (rSub j).val then 1 else 0
theorem routedStage0_rOutLayout {kOut : ℕ} (rSub : QRegister kOut 41) (β : BitAssignment dLayout)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41)
    (j : Fin kOut) : routedStage0 β c z (rOutLayout rSub j) = outSubRawBits rSub c j := by
  rw [routedStage0, writeReg_pack82_eq_outer_inner,
    DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨k, hk⟩ ↦ by
      have := val_rOutLayout_bounds rSub j
      have hv := congrArg Fin.val hk
      rw [val_rInner41Layout] at hv
      omega]
  exact DynCircExt.writeReg_apply_reg β rOuter41Layout (cBits41 c) (rSub j)
theorem cleanScr_routedStage0_ext {β : BitAssignment dLayout} (hScr : CleanScr β)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) : CleanScr (routedStage0 β c z) := fun m ↦ by
  rw [routedStage0, DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ by
    have hm : m.val < 1565 := m.isLt;
    have hv : (rLcu82Layout.wires i).val = (rScrLayout m).val := congrArg Fin.val hi
    rw [val_rLcu82Layout, val_rScrLayout] at hv
    omega]
  exact hScr m
end QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
end
end
