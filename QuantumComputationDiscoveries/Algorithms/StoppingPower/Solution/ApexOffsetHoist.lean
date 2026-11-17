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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.KoffSlot2Apex45
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3OuterShellB

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section HeldMsbInc7ApexWrap288
local instance (priority := 1000000) instNeZeroTwoPow_HeldMsbInc7ApexWrap288 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace HeldMsbInc7ApexWrap288

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open MeasureBranchHadamardSem
  (ket ket_projector_zero ket_projector_one matrix_ext_ket)
open ParametricMulKickAndSlopePG (catShiftUnitary)
open NuclearTwistRealizes
  (RealizesCleanPair
  basisBits_symm_apply
  embedUnitary_idReg_eq
  embedUnitary_inv_eq)
open UltraAsymVepTwist288 (asym_embedUnitary_inv_mulVec_of_eq)
open D3JunctionSpecs288 (subSumM48 subSumM48PG compose_subSumM48PG)
open HeldMsbInc7Sandwich288
  (catShift_mulVec_ket compose_selCM_core14M48PG selCM_core14M48PG)
open Slot2ZeroMuxSignedMul46
  (apexCatModAddZ apexCatModAddZ_mulVec_basisKet embed_apexCatModAddZ_sub natCast_mod_two_pow)

local instance (priority := 1000000)
    instLoc_HeldMsbInc7ApexWrap288_1InstNeZeroTwoPowApex (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)

theorem six_le_six_add (mScr : ℕ) : 0 + 6 ≤ 6 + mScr := by omega

theorem six_add_le_six_add (mScr : ℕ) : 6 + mScr ≤ 6 + mScr := le_rfl

theorem slice6_disj_sliceTail {mScr n : ℕ} (rScr : QRegister (6 + mScr) n) :
    (rScr.slice 0 6 (six_le_six_add mScr)).DisjointWires
      (rScr.slice 6 mScr (six_add_le_six_add mScr)) := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  have hv := congrArg Fin.val (rScr.wires.injective
    (((QRegister.slice_apply rScr 6 mScr _ j).symm.trans hj).trans
      (QRegister.slice_apply rScr 0 6 _ i)))
  have := i.isLt
  dsimp only at hv
  omega

theorem slice6_concat_sliceTail_sub {mScr n : ℕ} (rScr : QRegister (6 + mScr) n) :
    ((rScr.slice 0 6 (six_le_six_add mScr)).concat (rScr.slice 6 mScr (six_add_le_six_add
    mScr)) (slice6_disj_sliceTail rScr)).image ⊆ rScr.image := fun _ hw ↦
  (Finset.mem_union.mp (QRegExt.image_concat _ _ _ ▸ hw)).elim
    (fun h ↦ QRegister.image_compose_subset rScr _ h)
    (fun h ↦ QRegister.image_compose_subset rScr _ h)

/-- Effective `48`-bit bit-vector masking the low `skip` bits `[0 .. skip)` to `0`
(`rfl`-identical to `Slot2ZeroMuxTrunc.mEffBits11` at `skip = 11`,
`Slot2ZeroMuxTrunc36.mEffBits12` at `skip = 12`, and `H3dSharedBankApexOffset38.mEffBits`). -/
abbrev mEffBits (skip : ℕ) (M : Fin 48 → ZMod 2) : Fin 48 → ZMod 2 :=
  fun j ↦ if j.val < skip then 0 else M j

def apexKoffDelta (skip : ℕ) (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) : ℤ :=
    (bitsVal B : ℤ) * (bitsVal (mEffBits skip M) : ℤ) - ((2 ^ 13 : ℤ) * (bitsVal (mEffBits
    skip M) : ℤ) - ((bitsVal (fun j : Fin 47 ↦ mEffBits skip M j.succ) : ℤ) + ((mEffBits skip
    M 0).val : ℤ)))

lemma pg45_replace_props {n : ℕ} [NeZero (2 ^ n)] (rCat : QRegister 48 n)
    (β : BitAssignment n) (d : ℤ) :
    let rCat45 := rCat.slice 0 45 (by decide)
    let mOut : Fin (2 ^ 45) :=
      ⟨(regVal rCat45 β + (d % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45, Nat.mod_lt _ (by positivity)⟩
    let β_out := basisBits n (rCat45.replaceIndex ((basisBitsEquiv n).symm β) mOut)
    (∀ z, z ∉ rCat45.image → β_out z = β z) ∧
    regVal rCat45 β_out = mOut.val ∧
    ((regVal rCat45 β_out : ℤ) - ((regVal rCat45 β : ℤ) + d)) % (2 ^ 45 : ℤ) = 0 := by
  intro rCat45 mOut β_out
  have hout : ∀ z, z ∉ rCat45.image → β_out z = β z := fun z hz ↦ by
    simp only [β_out, rCat45.basisBits_replaceIndex_of_not_mem _ _ z
      (fun ⟨j, hj⟩ ↦ hz ((QRegister.mem_image rCat45 z).mpr ⟨j, hj⟩)), basisBits_symm_apply]
  have hval : regVal rCat45 β_out = mOut.val := by
    rw [regVal, show (fun j ↦ β_out (rCat45 j)) = basisBits 45 mOut from
      funext (rCat45.basisBits_replaceIndex_apply _ mOut), bitsVal_basisBits]
  refine ⟨hout, hval, ?_⟩
  rw [hval, show (mOut.val : ℤ) = ((regVal rCat45 β + (d % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45 : ℕ)
      from rfl, natCast_mod_two_pow 45, Nat.cast_add,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)),
    Int.add_emod_emod, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]

theorem apexCatModAddZ_comm_projector_of_not_mem_cat {kSys n : ℕ} [NeZero (2 ^ n)]
    (rSys : QRegister kSys n) (rCat : QRegister 48 n) (hSC : rSys.DisjointWires rCat)
    (Δ : BitAssignment kSys → ℤ) (w : Wire n) (hw : w ∉ rCat.image) (b : Fin 2) :
    ((rSys.concat rCat hSC).embedUnitary (apexCatModAddZ kSys Δ)).1 *
        (QRegister.singleton w).basisOutcomeProjector b =
      (QRegister.singleton w).basisOutcomeProjector b *
        ((rSys.concat rCat hSC).embedUnitary (apexCatModAddZ kSys Δ)).1 := by
  apply matrix_ext_ket
  intro β
  obtain ⟨hout, _, hm⟩ := pg45_replace_props rCat β (Δ (fun i ↦ β (rSys i)))
  have hev : ((rSys.concat rCat hSC).embedUnitary (apexCatModAddZ kSys Δ)).1.mulVec (ket β) =
      _ • ket _ := apexCatModAddZ_mulVec_basisKet rSys rCat hSC Δ _ β hout hm
  have hproj : ∀ γ : BitAssignment n,
      ((QRegister.singleton w).basisOutcomeProjector b).mulVec (ket γ) =
        if γ w = (b.val : ZMod 2) then ket γ else 0 := fun γ ↦ by
    fin_cases b
    · exact ket_projector_zero w γ
    · exact ket_projector_one w γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hproj, hev, Matrix.mulVec_smul, hproj,
    hout w (fun hm45 ↦ hw (QRegister.image_compose_subset rCat _ hm45))]
  split_ifs
  · exact hev
  · simp only [Matrix.mulVec_zero, smul_zero]

/-- Generic `14 + 48 → ℤ` adapter on `(rSum14 ⧺ rM48)`. -/
abbrev apex62Fn (Δ₀ : (Fin 14 → ZMod 2) → (Fin 48 → ZMod 2) → ℤ) (κ : BitAssignment (14 + 48))
    : ℤ := Δ₀ (fun s : Fin 14 ↦ κ (Fin.castAdd 48 s)) (fun j : Fin 48 ↦ κ (Fin.natAdd 14 j))

/-- Generic `(kC + 14) + 48 → ℤ` adapter on `((rCore ⧺ rSum14) ⧺ rM48)`. -/
abbrev apexCore14M48Fn (Δ₀ : (Fin 14 → ZMod 2) → (Fin 48 → ZMod 2) → ℤ)
    (kC : ℕ) (γ : BitAssignment ((kC + 14) + 48)) : ℤ :=
  Δ₀ (fun s : Fin 14 ↦ γ (Fin.castAdd 48 (Fin.natAdd kC s)))
     (fun j : Fin 48 ↦ γ (Fin.natAdd (kC + 14) j))

abbrev fApexKoff48Fn (skip kC : ℕ) : BitAssignment ((kC + 14) + 48) → ℤ :=
  apexCore14M48Fn (apexKoffDelta skip) kC

structure ApexKoffMulKickSpec (skip mScr tKick : ℕ) where
  dKick : Bool → ∀ {Var : Type} {n : ℕ}, Var →
    (rSum14 : QRegister 14 n) → (rM48 : QRegister 48 n) →
    (rPGTwist : QRegister 48 n) → (rScr : QRegister mScr n) →
    rSum14.DisjointWires rM48 →
    rSum14.DisjointWires rPGTwist →
    rM48.DisjointWires rPGTwist →
    rSum14.DisjointWires rScr →
    rM48.DisjointWires rScr →
    rPGTwist.DisjointWires rScr →
    DynamicCircuit Var n
  hToff : ∀ (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSM : rSum14.DisjointWires rM48) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSScr : rSum14.DisjointWires rScr)
    (hMScr : rM48.DisjointWires rScr) (hPScr : rPGTwist.DisjointWires rScr),
    (dKick isInv v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr).count .TOFF = 0
  hT : ∀ (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSM : rSum14.DisjointWires rM48) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSScr : rSum14.DisjointWires rScr)
    (hMScr : rM48.DisjointWires rScr) (hPScr : rPGTwist.DisjointWires rScr),
    (dKick isInv v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr).count .T ≤ tKick
  hRealizesPair : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSM : rSum14.DisjointWires rM48) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSScr : rSum14.DisjointWires rScr)
    (hMScr : rM48.DisjointWires rScr) (hPScr : rPGTwist.DisjointWires rScr),
    RealizesCleanPair
      ((rSum14.concat rM48 hSM).concat rPGTwist (QRegExt.disjointWires_concat_left hSP hMP))
      rScr
      (apexCatModAddZ (14 + 48) (apex62Fn (apexKoffDelta skip)))
      (dKick false v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr)
      (dKick true v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr)

theorem ApexKoffMulKickSpec.realizesPair_core14M48PG {skip mScr tKick kC : ℕ}
    (kick : ApexKoffMulKickSpec skip mScr tKick) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rCore : QRegister kC n) (rSum14 : QRegister 14 n)
    (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hCSum : rCore.DisjointWires rSum14)
    (hCSM48 : (rCore.concat rSum14 hCSum).DisjointWires rM48) (hExtP48 : ((rCore.concat rSum14
    hCSum).concat rM48 hCSM48).DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSScr : rSum14.DisjointWires rScr) (hMScr : rM48.DisjointWires rScr)
    (hPScr : rPGTwist.DisjointWires rScr) : RealizesCleanPair (((rCore.concat rSum14
    hCSum).concat rM48 hCSM48).concat rPGTwist hExtP48) rScr
    (apexCatModAddZ ((kC + 14) + 48) (fApexKoff48Fn skip kC)) (kick.dKick false v rSum14 rM48
    rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr) (kick.dKick true v rSum14 rM48 rPGTwist rScr
    hSM hSP hMP hSScr hMScr hPScr) := by
  have hp0 := kick.hRealizesPair v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr
  rw [← compose_subSumM48PG rCore rSum14 rM48 rPGTwist hCSum hCSM48 hExtP48 hSM
    (QRegExt.disjointWires_concat_left hSP hMP)] at hp0
  refine hp0.widenActive.congr_unitary ((embed_apexCatModAddZ_sub
    (Δ := apex62Fn (apexKoffDelta skip)) (subSumM48 kC) (subSumM48PG kC)
    fun _ ↦ Fin.ext (by simp [subSumM48PG])).trans
    (congrArg (apexCatModAddZ _) (funext fun γ ↦ ?_)))
  dsimp only [apex62Fn, fApexKoff48Fn, apexCore14M48Fn]
  rw [show (fun s : Fin 14 ↦ γ (subSumM48 kC (Fin.castAdd 48 s))) =
        (fun s ↦ γ (Fin.castAdd 48 (Fin.natAdd kC s))) from
      funext fun s ↦ congrArg γ (Fin.ext (by simp [subSumM48, s.isLt])),
    show (fun j : Fin 48 ↦ γ (subSumM48 kC (Fin.natAdd 14 j))) =
        (fun j ↦ γ (Fin.natAdd (kC + 14) j)) from
      funext fun j ↦ congrArg γ (Fin.ext (by simp [subSumM48, show ¬(14 + j.val < 14) by omega]))]

theorem sub_kC14_lt48 {kC a : ℕ} (h1 : ¬ a < kC + 14) (h2 : a < (kC + 14) + 48) :
    a - (kC + 14) < 48 := by omega

/-- System-state shift on `(kC + 14) + 48` bits applying `+(1 - cBit) * 2 ^ 41 mod 2 ^ 48`
to the trailing `48` `M48` bits while preserving the leading `kC + 14` `(rCore ⧺ rSum14)` bits. -/
noncomputable def shiftMsbInc7Sys (kC : ℕ) (iCtrl : Fin kC)
    (γ : BitAssignment ((kC + 14) + 48)) : BitAssignment ((kC + 14) + 48) :=
  let rRaw := bitsVal (fun j : Fin 48 ↦ γ (Fin.natAdd (kC + 14) j))
  let bBar := 1 - (γ (Fin.castAdd 48 (Fin.castAdd 14 iCtrl))).val
  let mShifted : Fin (2 ^ 48) :=
    ⟨(rRaw + bBar * 2 ^ 41) % 2 ^ 48, Nat.mod_lt _ (Nat.two_pow_pos 48)⟩
  fun idx ↦
    if h : idx.val < kC + 14 then
      γ (Fin.castAdd 48 ⟨idx.val, h⟩)
    else
      basisBits 48 mShifted ⟨idx.val - (kC + 14), sub_kC14_lt48 h idx.isLt⟩

theorem shiftMsbInc7Sys_castAdd (kC : ℕ) (iCtrl : Fin kC)
    (γ : BitAssignment ((kC + 14) + 48)) (q : Fin (kC + 14)) :
    shiftMsbInc7Sys kC iCtrl γ (Fin.castAdd 48 q) = γ (Fin.castAdd 48 q) := by
  dsimp only [shiftMsbInc7Sys]
  split_ifs with h
  · exact congrArg γ (Fin.ext (by simp))
  · exact absurd q.isLt h

theorem shiftMsbInc7Sys_natAdd (kC : ℕ) (iCtrl : Fin kC) (γ : BitAssignment ((kC + 14) + 48))
    (j : Fin 48) : shiftMsbInc7Sys kC iCtrl γ (Fin.natAdd (kC + 14) j) = basisBits 48
    ⟨(bitsVal (fun j' : Fin 48 ↦ γ (Fin.natAdd (kC + 14) j')) + (1 - (γ (Fin.castAdd 48
    (Fin.castAdd 14 iCtrl))).val) * 2 ^ 41) % 2 ^ 48, Nat.mod_lt _ (Nat.two_pow_pos 48)⟩ j
    := by
  dsimp only [shiftMsbInc7Sys]
  split_ifs with h
  · rw [Fin.val_natAdd] at h
    omega
  · refine congrArg (basisBits 48 _) (Fin.ext ?_)
    simp only [Fin.val_natAdd]
    omega

lemma idSlice_disj {N s₁ k₁ s₂ k₂ : ℕ} (h₁ : s₁ + k₁ ≤ N) (h₂ : s₂ + k₂ ≤ N)
    (hd : s₁ + k₁ ≤ s₂) :
    ((QRegExt.idReg N).slice s₁ k₁ h₁).DisjointWires
      ((QRegExt.idReg N).slice s₂ k₂ h₂) := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [QRegister.slice_apply, QRegExt.idReg_apply] at hv
  have := i.isLt
  omega

lemma concat_eq_idSlice {N a b c : ℕ} (hab : a + b ≤ N) (hbc : (a + b) + c ≤ N)
    {r₁ : QRegister b N} (hr₁ : r₁ = (QRegExt.idReg N).slice a b hab)
    (hd : r₁.DisjointWires ((QRegExt.idReg N).slice (a + b) c (by omega))) :
    r₁.concat ((QRegExt.idReg N).slice (a + b) c (by omega)) hd =
      (QRegExt.idReg N).slice a (b + c) (by omega) := by
  subst hr₁
  refine qreg_ext fun idx ↦ Fin.ext ?_
  by_cases h : idx.val < b
  · rw [show idx = Fin.castAdd c ⟨idx.val, h⟩ from Fin.ext rfl, QRegister.concat_apply_left]
    simp [QRegExt.idReg_apply]
  · rw [show idx = Fin.natAdd b ⟨idx.val - b, by omega⟩ from
        Fin.ext (by rw [Fin.val_natAdd, Nat.add_sub_cancel' (Nat.not_lt.mp h)]),
      QRegister.concat_apply_right]
    simp only [QRegister.slice_apply, QRegExt.idReg_apply, Fin.val_natAdd]
    omega

theorem conj_selCM_apexCatModAddZ_eq (kC : ℕ) (iCtrl : Fin kC)
    (Δ_bm : BitAssignment ((kC + 14) + 48) → ℤ) :
    let uI := (selCM_core14M48PG kC).embedUnitary
      (catShiftUnitary kC 48 (fun γ ↦ (1 - (γ iCtrl).val) * 2 ^ (48 - 7)))
    let uM := apexCatModAddZ ((kC + 14) + 48) Δ_bm
    (uI⁻¹ * uM) * uI =
      apexCatModAddZ ((kC + 14) + 48) (fun γ ↦ Δ_bm (shiftMsbInc7Sys kC iCtrl γ)) := by
  intro uI uM
  let N := ((kC + 14) + 48) + 48
  let rCore0 := (QRegExt.idReg N).slice 0 kC (by omega)
  let rSum0 := (QRegExt.idReg N).slice (0 + kC) 14 (by omega)
  let rM0 := (QRegExt.idReg N).slice (0 + (kC + 14)) 48 (by omega)
  let rPG0 := (QRegExt.idReg N).slice (0 + ((kC + 14) + 48)) 48 (by omega)
  have hCS0 : rCore0.DisjointWires rSum0 := idSlice_disj _ _ le_rfl
  have hCM0 : rCore0.DisjointWires rM0 := idSlice_disj _ _ (by omega)
  let rCore14_0 := rCore0.concat rSum0 hCS0
  have hCSM0 : rCore14_0.DisjointWires rM0 :=
    QRegExt.disjointWires_concat_left hCM0 (idSlice_disj _ _ le_rfl)
  let rSys0 := rCore14_0.concat rM0 hCSM0
  have hrSys0 : rSys0 = (QRegExt.idReg N).slice 0 ((kC + 14) + 48) (by omega) :=
    concat_eq_idSlice (by omega) (by omega) (concat_eq_idSlice (by omega) (by omega) rfl hCS0) hCSM0
  have hExtP0 : rSys0.DisjointWires rPG0 := hrSys0 ▸ idSlice_disj _ _ le_rfl
  let rAmb0 := rSys0.concat rPG0 hExtP0
  have hid0 : rAmb0 = QRegExt.idReg N :=
    (concat_eq_idSlice (by omega) (by omega) hrSys0 hExtP0).trans
      (qreg_ext fun _ ↦ Fin.ext (by simp [QRegExt.idReg_apply]))
  let uShift := catShiftUnitary kC 48 (fun γ ↦ (1 - (γ iCtrl).val) * 2 ^ (48 - 7))
  have hEI : rAmb0.embedUnitary uI = (rCore0.concat rM0 hCM0).embedUnitary uShift := by
    dsimp only [uI, uShift]
    rw [← QRegister.embedUnitary_compose,
      compose_selCM_core14M48PG rCore0 rSum0 rM0 rPG0 hCS0 hCSM0 hExtP0 hCM0]
  rw [← embedUnitary_idReg_eq ((uI⁻¹ * uM) * uI), ← embedUnitary_idReg_eq (apexCatModAddZ _ _),
    ← hid0]
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, embedUnitary_inv_eq, hEI,
    ← embedUnitary_inv_eq]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  let rPG45 := rPG0.slice 0 45 (by decide)
  have hSysNot45 : ∀ q, rSys0 q ∉ rPG45.image := fun q h ↦
    (Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hExtP0))
      ((QRegister.mem_image rSys0 _).mpr ⟨q, rfl⟩) (QRegister.image_compose_subset rPG0 _ h)
  let m1 : Fin (2 ^ 48) := ⟨(regVal rM0 β + (1 - (β (rCore0 iCtrl)).val) * 2 ^ (48 - 7)) % 2 ^ 48,
    Nat.mod_lt _ (by positivity)⟩
  let β₁ := basisBits N (rM0.replaceIndex ((basisBitsEquiv N).symm β) m1)
  have hout1 : ∀ z, z ∉ Set.range rM0.wires → β₁ z = β z := fun z hz ↦ by
    simp only [β₁, rM0.basisBits_replaceIndex_of_not_mem _ _ z hz, basisBits_symm_apply]
  have hSysShift : (fun q ↦ β₁ (rSys0 q)) = shiftMsbInc7Sys kC iCtrl (fun q ↦ β (rSys0 q)) := by
    funext q
    by_cases hq : q.val < kC + 14
    · rw [show q = Fin.castAdd 48 ⟨q.val, hq⟩ from Fin.ext rfl, shiftMsbInc7Sys_castAdd,
        QRegister.concat_apply_left]
      exact hout1 _ (fun ⟨j, hj⟩ ↦ hCSM0.ne ⟨q.val, hq⟩ j hj.symm)
    · let j : Fin 48 := ⟨q.val - (kC + 14), sub_kC14_lt48 hq q.isLt⟩
      rw [show q = Fin.natAdd (kC + 14) j from
          Fin.ext (Nat.add_sub_cancel' (Nat.not_lt.mp hq)).symm,
        shiftMsbInc7Sys_natAdd, QRegister.concat_apply_right]
      dsimp only [β₁, m1]
      rw [rM0.basisBits_replaceIndex_apply]
      refine congrArg (fun x : Fin (2 ^ 48) ↦ basisBits 48 x j) (Fin.ext ?_)
      rw [show bitsVal (fun j' : Fin 48 ↦ β (rSys0 (Fin.natAdd (kC + 14) j'))) = regVal rM0 β from
          congrArg bitsVal (funext fun j' ↦ congrArg β (QRegister.concat_apply_right _ _ _ j')),
        show β (rSys0 (Fin.castAdd 48 (Fin.castAdd 14 iCtrl))) = β (rCore0 iCtrl) from
          congrArg β (by rw [QRegister.concat_apply_left, QRegister.concat_apply_left])]
  have hMNot45 : ∀ j, rM0 j ∉ rPG45.image := fun j ↦
    QRegister.concat_apply_right rCore14_0 rM0 hCSM0 j ▸ hSysNot45 _
  have hPG_β₁ : regVal rPG45 β₁ = regVal rPG45 β := regVal_congr rPG45 fun p ↦
    hout1 (rPG45 p) (fun ⟨j, hj⟩ ↦ hMNot45 j (hj ▸ (QRegister.mem_image rPG45 _).mpr ⟨p, rfl⟩))
  let dShifted : ℤ := Δ_bm (fun q ↦ β₁ (rSys0 q))
  let dTarget : ℤ := Δ_bm (shiftMsbInc7Sys kC iCtrl (fun q ↦ β (rSys0 q)))
  obtain ⟨hout2, hpg2_val, hm2⟩ := pg45_replace_props rPG0 β₁ dShifted
  obtain ⟨hout', hpg'_val, hm'⟩ := pg45_replace_props rPG0 β dTarget
  let m2 : Fin (2 ^ 45) := ⟨(regVal rPG45 β₁ + (dShifted % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45,
    Nat.mod_lt _ (by positivity)⟩
  let m' : Fin (2 ^ 45) := ⟨(regVal rPG45 β + (dTarget % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45,
    Nat.mod_lt _ (by positivity)⟩
  have hmOut_eq : m' = m2 := Fin.ext (by simp only [m', m2, dShifted, dTarget, hPG_β₁, hSysShift])
  let β₂ := basisBits N (rPG45.replaceIndex ((basisBitsEquiv N).symm β₁) m2)
  let β' := basisBits N (rPG45.replaceIndex ((basisBitsEquiv N).symm β) m')
  have hFwd_β' : ((rCore0.concat rM0 hCM0).embedUnitary uShift).1.mulVec (ket β') = ket β₂ := by
    dsimp only [uShift]
    rw [catShift_mulVec_ket]
    have hM_β' : regVal rM0 β' = regVal rM0 β := regVal_congr rM0 fun j ↦ hout' (rM0 j) (hMNot45 j)
    have hc_β' : β' (rCore0 iCtrl) = β (rCore0 iCtrl) := hout' (rCore0 iCtrl) (by
      rw [← QRegister.concat_apply_left rCore0 rSum0 hCS0 iCtrl,
        ← QRegister.concat_apply_left rCore14_0 rM0 hCSM0]
      exact hSysNot45 _)
    rw [show (⟨(regVal rM0 β' + (1 - (β' (rCore0 iCtrl)).val) * 2 ^ (48 - 7)) % 2 ^ 48,
        Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ 48)) = m1 from Fin.ext (by
      dsimp [m1]
      rw [hM_β', hc_β'])]
    refine congrArg ket (funext fun z ↦ ?_)
    by_cases hzM : z ∈ Set.range rM0.wires
    · obtain ⟨j, rfl⟩ := hzM
      rw [rM0.basisBits_replaceIndex_apply]
      dsimp only [β₂, rPG45]
      rw [hout2 (rM0 j) (hMNot45 j)]
      exact (rM0.basisBits_replaceIndex_apply _ m1 j).symm
    · rw [rM0.basisBits_replaceIndex_of_not_mem _ _ z hzM, basisBits_symm_apply]
      by_cases hz45 : z ∈ Set.range rPG45.wires
      · obtain ⟨p, rfl⟩ := hz45
        dsimp only [β', β₂]
        rw [rPG45.basisBits_replaceIndex_apply, rPG45.basisBits_replaceIndex_apply, hmOut_eq]
      · have hn45 : z ∉ rPG45.image := fun h ↦ hz45 ((QRegister.mem_image rPG45 z).mp h)
        dsimp only [β', β₂]
        rw [hout' z hn45, hout2 z hn45, hout1 z hzM]
  have hketEq : ∀ γ : BitAssignment N, ket γ = basisKet γ := fun _ ↦ rfl
  rw [show ((rCore0.concat rM0 hCM0).embedUnitary uShift).1.mulVec (ket β) = ket β₁ from
      catShift_mulVec_ket rCore0 rM0 hCM0 _ β,
    hketEq β₁, apexCatModAddZ_mulVec_basisKet rSys0 rPG0 hExtP0 Δ_bm _ β₁ hout2 hm2,
    Matrix.mulVec_smul, ← hketEq β₂,
    asym_embedUnitary_inv_mulVec_of_eq (rCore0.concat rM0 hCM0) uShift hFwd_β',
    hketEq β, apexCatModAddZ_mulVec_basisKet rSys0 rPG0 hExtP0 _ _ β hout' hm', hketEq β']
  refine congrArg (· • basisKet β') (congrArg (DyadicQft64.dyadicTurn 48) ?_)
  dsimp only [dTarget] at hpg'_val
  rw [hpg'_val, hpg2_val]
  dsimp only [dShifted]
  rw [hSysShift, hPG_β₁]

end HeldMsbInc7ApexWrap288
end
end HeldMsbInc7ApexWrap288

section InterWalkRSum42HoistCircuits
local instance (priority := 1000000) instNeZeroTwoPow_InterWalkRSum42HoistCircuits (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
public section
namespace InterWalkRSum42Hoist
set_option backward.isDefEq.respectTransparency true
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm SpecsAux.SpecMirror
open NuclearTwistRealizes (RealizesCleanPair)

theorem widenActivePair_of_eq {Var : Type} [Fintype Var] [DecidableEq Var] {k kAct m n : ℕ}
    [NeZero (2 ^ n)] {r : QRegister k n} {rAct : QRegister kAct n} {sub : QRegister k kAct}
    {rWork : QRegister m n} {U : Unitary (2 ^ k)} {dFwd dInv : DynamicCircuit Var n}
    (heq : r = rAct.compose sub) (h : RealizesCleanPair r rWork U dFwd dInv) :
    RealizesCleanPair rAct rWork (sub.embedUnitary U) dFwd dInv :=
  { fwd := widenActive_of_eq heq h.fwd
    inv := by
      rw [embedUnitary_inv_symm]
      exact widenActive_of_eq heq h.inv }
end InterWalkRSum42Hoist
end
end InterWalkRSum42HoistCircuits

section CommutedRSum42ApexTwistHoist288
local instance (priority := 1000000)
    instNeZeroTwoPow_CommutedRSum42ApexTwistHoist288 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
public section
namespace CommutedRSum42ApexTwistHoist288
local instance (priority := 1000000)
    instLoc_CommutedRSum42ApexTwistHoist288_1InstNeZeroT (k : ℕ) :
    NeZero (2 ^ k) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator Matrix
open SpecsAux.BridgeFermionicComm (permutationUnitary_apply)

theorem mul_permutationUnitary_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (τ : Equiv.Perm (Fin d)) (x y : Fin d) :
    (M * (Operator.permutationUnitary τ).1) x y = M x (τ y) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ y)]
  · simp [permutationUnitary_apply]
  · exact fun _ _ hz ↦ by simp [permutationUnitary_apply, hz]
  · simp

theorem permutationUnitary_mul_apply {d : ℕ} (τ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d) :
    ((Operator.permutationUnitary τ).1 * M) x y = M (τ⁻¹ x) y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ⁻¹ x)]
  · simp [permutationUnitary_apply, τ.apply_symm_apply x]
  · exact fun z _ hz ↦ by
      simp [permutationUnitary_apply,
        show x ≠ τ z from fun h ↦ hz (h ▸ (τ.symm_apply_apply z).symm)]
  · simp
end CommutedRSum42ApexTwistHoist288
end
end CommutedRSum42ApexTwistHoist288

section InterWalkRSum42Hoist
local instance (priority := 1000000) instNeZeroTwoPow_InterWalkRSum42Hoist (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
public section
namespace InterWalkRSum42Hoist
local instance (priority := 1000000)
    instLoc_InterWalkRSum42Hoist_1InstNeZeroTwoPowRSum42 (k : ℕ) :
    NeZero (2 ^ k) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator Matrix
open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux.SpecMirror

theorem PreservesFeature.zero {d : ℕ} {α : Type*} (f : Fin d → α) :
    PreservesFeature f (0 : Operator d) := by
  intro _ _ hne
  simp at hne
end InterWalkRSum42Hoist
end
end InterWalkRSum42Hoist

section GidneySignalRotHoistBridge
local instance (priority := 1000000) instNeZeroTwoPow_GidneySignalRotHoistBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
public section
namespace GidneySignalRotHoistBridge
open Operator

theorem coe_pow_unitary {d : ℕ} (U : Unitary d) :
    ∀ r : ℕ, ((U ^ r : Unitary d) : Operator d) = (U.1) ^ r
  | 0 => rfl
  | r + 1 => by rw [pow_succ, pow_succ, Submonoid.coe_mul, coe_pow_unitary U r]
end GidneySignalRotHoistBridge
end
end GidneySignalRotHoistBridge

section Aux_JunctionProj3DCut
local instance (priority := 1000000) instNeZeroTwoPow_Aux_JunctionProj3DCut (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
public section
public section
namespace Proj3DCut.WhHelper
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding
  dyadicTurn phaseGradKet xAllCircuit count_xAllCircuit_toff count_xAllCircuit_t
open DyadicQft64Engine
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes hiding support_seq_sub
open NuclearTwistMulKickAndBridge288
open ProjZ512QftAndTwist288 hiding
  basisBits_symm_apply fullSysCoreWires_eq_add dyadicDiagUnitary_mulVec_basisKet
  support_seq_sub zmod2_eq_zero_or_one
open FusedVepCore288
open JunctionApexCSA288
local instance (priority := 1000000)
    instLoc_Aux_JunctionProj3DCut_1InstNeZeroTwoPowJunc (k : ℕ) :
    NeZero (2 ^ k) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
lemma qreg_singleton_image {n : ℕ} (w : Wire n) : (QRegister.singleton w).image = {w} := by
  ext u
  simp only [QRegister.mem_image, Finset.mem_singleton]
  refine ⟨fun ⟨i, h⟩ ↦ ?_, fun h ↦ ⟨0, h.symm⟩⟩
  fin_cases i
  exact h.symm
lemma PreservesReg.of_cnotAllCircuit {W M n : ℕ} {rT : QRegister W n} (wNeg : Wire n)
    (rX : QRegister M n) (hwNegX : ∀ i : Fin M, wNeg ≠ rX i) (hwNegT : wNeg ∉ rT.image)
    (hXT : rX.DisjointWires rT) : PreservesReg rT (cnotAllCircuit wNeg rX hwNegX)
    (fun ξ ↦ if ξ wNeg = 1 then flipRegBits rX ξ else ξ) := by
  have hNotX := fun i : Fin W ↦ (disj_symm hXT).apply_not_mem_right i
  refine ⟨cnotAllCircuit_evolve wNeg rX hwNegX, fun ξ d ↦ ?_, fun ξ j ↦ ?_⟩
  · rw [shiftRegInt_outside rT ξ d hwNegT]
    split_ifs
    · funext u
      by_cases huT : u ∈ rT.image
      · rcases (QRegister.mem_image rT u).mp huT with ⟨k, rfl⟩
        rw [flipRegBits_outside rX _ (hNotX k), shiftRegInt_apply_reg, shiftRegInt_apply_reg,
          regVal_congr rT fun i ↦ flipRegBits_outside rX ξ (hNotX i)]
      · rw [shiftRegInt_outside rT _ d huT]
        unfold flipRegBits
        split_ifs
        · simp [shiftRegInt_outside rT ξ d huT]
        · exact shiftRegInt_outside rT ξ d huT
    · rfl
  · split_ifs
    · exact flipRegBits_outside rX ξ (hNotX j)
    · rfl
lemma DiagOn.conj_cnotAllCircuit_of_mem {M n : ℕ} {S : Finset (Wire n)} (wNeg : Wire n)
    (rX : QRegister M n) (hwNegX : ∀ i : Fin M, wNeg ≠ rX i) (hwNegS : wNeg ∈ S)
    {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hA : DiagOn S A) : DiagOn S ((cnotAllCircuit
    wNeg rX hwNegX).inverse.eval.1 * A * (cnotAllCircuit wNeg rX hwNegX).eval.1) := by
  induction M with
  | zero => simpa [cnotAllCircuit, Circuit.inverse, Circuit.eval_identity] using hA
  | succ k ih =>
    dsimp only [cnotAllCircuit]
    simp only [Circuit.inverse_seq, Circuit.eval_seq, Submonoid.coe_mul,
      show (Circuit.CNOT wNeg (rX 0) (hwNegX 0)).inverse = Circuit.CNOT wNeg (rX 0) (hwNegX 0)
        from rfl]
    rw [show ∀ (X Y Z : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
        X * Y * A * (Z * X) = X * (Y * A * Z) * X from fun _ _ _ ↦ by simp only [Matrix.mul_assoc]]
    exact DiagOn.conj_CNOT wNeg (rX 0) (hwNegX 0) hwNegS (ih _ _)
lemma shiftRegInt_zero_eq {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) :
    shiftRegInt rT ξ 0 = ξ :=
  (eq_shiftRegInt_of_outside_and_regVal rT ξ ξ 0 (fun _ _ ↦ rfl)
    (by rw [add_zero, intModFinPow2_nat_lt (regVal_lt_two_pow rT ξ)])).symm
noncomputable def dApexTAdderWithCin {Var : Type} {n : ℕ} (isInv : Bool) (W : ℕ) (v : Var)
    (cin : Wire n) (rU rT rC : QRegister W n) (hcinU : cin ∉ rU.image)
    (hcinT : cin ∉ rT.image) (hcinC : cin ∉ rC.image) (hUT : rU.DisjointWires rT)
    (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) : DynamicCircuit Var n := if isInv
    then dPureConj (xAllCircuit rT) (dApexTail W v (cApexSign true) cin rU rT rC hcinU hcinT
    hcinC hUT hUC hTC) else dApexTail W v (cApexSign false) cin rU rT rC hcinU hcinT hcinC hUT
    hUC hTC
@[scoped simp] lemma count_dApexTAdderWithCin_toff {Var : Type} {n : ℕ} (isInv : Bool) (W : ℕ)
    (v : Var) (cin : Wire n) (rU rT rC : QRegister W n) (hcinU : cin ∉ rU.image)
    (hcinT : cin ∉ rT.image) (hcinC : cin ∉ rC.image) (hUT : rU.DisjointWires rT)
    (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) : (dApexTAdderWithCin isInv W v
    cin rU rT rC hcinU hcinT hcinC hUT hUC hTC).count .TOFF = 0 := by
  cases isInv
  · exact count_dApexTail_toff W v _ (count_cApexSign_toff false) cin rU rT rC hcinU hcinT hcinC
      hUT hUC hTC
  · simp only [dApexTAdderWithCin, ↓reduceIte, count_dPureConj_toff _ (count_xAllCircuit_toff rT)]
    exact count_dApexTail_toff W v _ (count_cApexSign_toff true) cin rU rT rC hcinU hcinT hcinC
      hUT hUC hTC
@[scoped simp] lemma count_dApexTAdderWithCin_t {Var : Type} {n : ℕ} (isInv : Bool) (W : ℕ)
    (v : Var) (cin : Wire n) (rU rT rC : QRegister W n) (hcinU : cin ∉ rU.image)
    (hcinT : cin ∉ rT.image) (hcinC : cin ∉ rC.image) (hUT : rU.DisjointWires rT)
    (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) : (dApexTAdderWithCin isInv W v
    cin rU rT rC hcinU hcinT hcinC hUT hUC hTC).count .T = 4 * W + 1 := by
  cases isInv
  · exact count_dApexTail_t W v _ 1 (count_cApexSign_t false) cin rU rT rC hcinU hcinT hcinC
      hUT hUC hTC
  · simp only [dApexTAdderWithCin, ↓reduceIte, count_dPureConj_t _ (count_xAllCircuit_t rT)]
    exact count_dApexTail_t W v _ 1 (count_cApexSign_t true) cin rU rT rC hcinU hcinT hcinC
      hUT hUC hTC
lemma dApexTAdderWithCin_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (isInv : Bool) (W : ℕ) (v : Var) (cin : Wire n) (rU rT rC : QRegister W n)
    (hcinU : cin ∉ rU.image) (hcinT : cin ∉ rT.image) (hcinC : cin ∉ rC.image)
    (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) :
    ∃ u : Unitary (2 ^ n), CleanUnitaryWp rC u
        (dApexTAdderWithCin isInv W v cin rU rT rC hcinU hcinT hcinC hUT hUC hTC) ∧
      DiagOn (Finset.univ \ rT.image) u.1 ∧
      ∀ ξ : BitAssignment n, (∀ i : Fin W, ξ (rC i) = 0) →
        u.1.mulVec (basisKet ξ) = apexCarryPhase rT ξ
          ((if isInv then (-1 : ℤ) else 1) * (((ξ cin).val + regVal rU ξ : ℕ) : ℤ)) •
          basisKet (shiftRegInt rT ξ
            ((if isInv then (-1 : ℤ) else 1) * (((ξ cin).val + regVal rU ξ : ℕ) : ℤ))) := by
  obtain ⟨u₀, hw₀, hDiag₀, hKet₀⟩ := dApexTail_spec W v (cApexSign isInv) ∅
    (fun _ b ↦ DyadicQft64.dyadicTurn 3 ((if isInv then (-1 : ℤ) else 1) * (b.val : ℤ)))
    (fun _ _ _ _ ↦ rfl) (fun c ξ ↦ by simpa using cApexSign_evolve isInv c ξ)
    cin rU rT rC hcinU hcinT hcinC hUT hUC hTC (by simp)
    (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
  have hU_bound : ∀ ξ : BitAssignment n, (ξ cin).val + regVal rU ξ ≤ 2 ^ W := fun ξ ↦ by
    have := ZMod.val_lt (ξ cin)
    have := regVal_lt_two_pow rU ξ
    omega
  cases isInv
  · refine ⟨u₀, hw₀, hDiag₀, fun ξ hzC ↦ ?_⟩
    rw [hKet₀ ξ hzC]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hU_le := hU_bound ξ
    have hT := regVal_lt_two_pow rT ξ
    refine congrArg (· • _) ?_
    unfold apexCarryPhase
    rw [ZMod.val_natCast_of_lt ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos W)).mpr (by omega)),
      add_comm ((ξ cin).val + regVal rU ξ) (regVal rT ξ), Int.natCast_ediv, Int.natCast_add]
    push_cast
    rfl
  · refine ⟨(xAllCircuit rT).inverse.eval * u₀ * (xAllCircuit rT).eval,
      CleanUnitaryWp.dPureConj (xAllCircuit rT) rC
        (Finset.disjoint_of_subset_left (support_xAllCircuit_sub rT)
          (QRegExt.disjointWires_to_finset hTC)) hw₀,
      by simp only [eval_xAllCircuit_inverse, Submonoid.coe_mul]
         exact DiagOn.conj_xAllCircuit rT hDiag₀, fun ξ hzC ↦ ?_⟩
    simp only [eval_xAllCircuit_inverse, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      xAllCircuit_evolve]
    let ξ₁ := flipRegBits rT ξ
    let U : ℕ := (ξ cin).val + regVal rU ξ
    have hU_le : U ≤ 2 ^ W := hU_bound ξ
    have hT_lt := regVal_lt_two_pow rT ξ
    have hT₁ : regVal rT ξ₁ = 2 ^ W - 1 - regVal rT ξ := by
      dsimp only [ξ₁]
      have := regVal_flipRegBits_add rT ξ
      have := Nat.one_le_two_pow (n := W)
      omega
    have hcin₁ : ξ₁ cin = ξ cin := flipRegBits_outside rT ξ hcinT
    have hU₁ : regVal rU ξ₁ = regVal rU ξ :=
      regVal_congr rU fun i ↦ flipRegBits_outside rT ξ (hUT.apply_not_mem_right i)
    rw [hKet₀ ξ₁ (fun i ↦ (flipRegBits_outside rT ξ
        ((disj_symm hTC).apply_not_mem_right i)).trans (hzC i)),
      Matrix.mulVec_smul, xAllCircuit_evolve, hcin₁, hU₁]
    change DyadicQft64.dyadicTurn 3 (-1 * ((((U + regVal rT ξ₁) / 2 ^ W : ℕ) : ZMod 2).val : ℤ)) •
        basisKet (flipRegBits rT (shiftRegInt rT ξ₁ (U : ℤ))) = _
    have hFlip : flipRegBits rT (shiftRegInt rT ξ₁ (U : ℤ)) = shiftRegInt rT ξ (-(U : ℤ)) := by
      rcases Nat.lt_or_eq_of_le hU_le with hUlt | hEq
      · exact flipRegBits_shiftRegInt_ones_comp rT ξ hUlt
      · rw [hEq, shiftRegInt_congr_mod rT ξ₁ (d₂ := 0) (by simp), shiftRegInt_zero_eq,
          shiftRegInt_congr_mod rT ξ (d₂ := 0) (by simp), shiftRegInt_zero_eq, flipRegBits_self_inv]
    have hT₁_lt := regVal_lt_two_pow rT ξ₁
    rw [hFlip, ZMod.val_natCast_of_lt
      ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos W)).mpr (by omega)), hT₁]
    simp only [↓reduceIte, neg_one_mul]
    unfold apexCarryPhase
    congr 2
    change -(((U + (2 ^ W - 1 - regVal rT ξ)) / 2 ^ W : ℕ) : ℤ) =
      ((regVal rT ξ : ℤ) + -(U : ℤ)) / (2 ^ W : ℤ)
    rcases Nat.lt_or_eq_of_le hU_le with hUlt | hEq
    · rw [ones_comp_carry_eq hT_lt hUlt]
      exact congrArg (· / (2 ^ W : ℤ)) (by ring)
    · rw [hEq, show 2 ^ W + (2 ^ W - 1 - regVal rT ξ) =
          (2 ^ W - 1 - regVal rT ξ) + 1 * 2 ^ W by omega,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt (by omega),
        show (regVal rT ξ : ℤ) + -(((2 ^ W : ℕ) : ℤ)) = (regVal rT ξ : ℤ) + (-1) * (2 ^ W : ℤ) by
          push_cast
          ring,
        Int.add_mul_ediv_right _ _ (by positivity),
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hT_lt)]
      norm_num
noncomputable def dCsa3AxisApexWithQ {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ) (v : Var)
    (rM0 rM1 rM2 : QRegister (m + 1) n) (rQ : QRegister 3 n) (wQc : Wire n)
    (rT : QRegister (m + 1) n) (rScr : QRegister (3 * m + 2) n) (h01 : rM0.DisjointWires rM1)
    (h02 : rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h1Q : rM1.DisjointWires rQ)
    (h1Qc : wQc ∉ rM1.image) (hQQc : wQc ∉ rQ.image) (h1T : rM1.DisjointWires rT)
    (hQT : rQ.DisjointWires rT) (h0S : rM0.DisjointWires rScr) (h1S : rM1.DisjointWires rScr)
    (h2S : rM2.DisjointWires rScr) (hQS : rQ.DisjointWires rScr) (hQcS : wQc ∉ rScr.image)
    (hTS : rT.DisjointWires rScr) : DynamicCircuit Var n :=
  let rC1 := rScr.slice 0 (m + 1) (by omega)
  let rD2 := rScr.slice (m + 1) m (by omega)
  let rCApex := rScr.slice (2 * m + 1) (m + 1) (by omega)
  let rA := rC1.slice 0 m (by omega)
  let rB := rM1.slice 1 m (by omega)
  let hC1_sub : rC1.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
  let hD2_sub : rD2.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
  let hCA_sub : rCApex.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
  let hA_sub : rA.image ⊆ rScr.image := (QRegister.image_compose_subset rC1 _).trans hC1_sub
  let hB_sub : rB.image ⊆ rM1.image := QRegister.image_compose_subset rM1 _
  let hq (i j : Fin 3) (hij : i ≠ j) : rQ i ≠ rQ j := fun h ↦ hij (rQ.wires.injective h)
  let hqc (i : Fin 3) : rQ i ≠ wQc := fun h ↦ hQQc (h ▸ (QRegister.mem_image rQ _).mpr ⟨i, rfl⟩)
  let hAB := (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm h1S))
    hA_sub)) hB_sub
  let hAD := (QRegExt.disjointWires_mono_left (slice_disjoint_of_le rScr 0 (m + 1) (m +
    1) m (by omega) (by omega)
    (by omega))) (QRegister.image_compose_subset rC1 _)
  let hBD := (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h1S) hB_sub))
    hD2_sub
  dFaWrap v (rQ 0) (rQ 1) (rQ 2) wQc (hq 0 1 (by decide)) (hq 0 2 (by decide))
    (hq 1 2 (by decide)) (hqc 0) (hqc 1) (hqc 2)
    (dCsaLayer1 (m + 1) v rM0 rM1 rM2 rC1
      h01 h02 h12 ((QRegExt.disjointWires_mono_right h0S) hC1_sub)
        ((QRegExt.disjointWires_mono_right h1S) hC1_sub) ((QRegExt.disjointWires_mono_right h2S)
        hC1_sub)
      (.seq (.circuit (cApexSign isInv (rC1 ⟨m, by omega⟩)))
        (dFaChain isInv m v wQc rA rB rD2
          (fun h ↦ hQcS (hA_sub h)) (fun h ↦ h1Qc (hB_sub h)) (fun h ↦ hQcS (hD2_sub h))
          hAB hAD hBD
          (dApexTAdderWithCin isInv (m + 1) v (rQ 1) rM1 rT rCApex
            ((disj_symm h1Q).apply_not_mem_right 1)
            (hQT.apply_not_mem_right 1)
            (fun h ↦ (hQS.apply_not_mem_right 1) (hCA_sub h))
            h1T ((QRegExt.disjointWires_mono_right h1S) hCA_sub) ((QRegExt.disjointWires_mono_right
              hTS) hCA_sub)))))
@[scoped simp] lemma count_dCsa3AxisApexWithQ_toff {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ)
    (v : Var) (rM0 rM1 rM2 : QRegister (m + 1) n) (rQ : QRegister 3 n) (wQc : Wire n)
    (rT : QRegister (m + 1) n) (rScr : QRegister (3 * m + 2) n) (h01 : rM0.DisjointWires rM1)
    (h02 : rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h1Q : rM1.DisjointWires rQ)
    (h1Qc : wQc ∉ rM1.image) (hQQc : wQc ∉ rQ.image) (h1T : rM1.DisjointWires rT)
    (hQT : rQ.DisjointWires rT) (h0S : rM0.DisjointWires rScr) (h1S : rM1.DisjointWires rScr)
    (h2S : rM2.DisjointWires rScr) (hQS : rQ.DisjointWires rScr) (hQcS : wQc ∉ rScr.image)
    (hTS : rT.DisjointWires rScr) : (dCsa3AxisApexWithQ isInv m v rM0 rM1 rM2 rQ wQc rT rScr
    h01 h02 h12 h1Q h1Qc hQQc h1T hQT h0S h1S h2S hQS hQcS hTS).count .TOFF = 0 := by
  unfold dCsa3AxisApexWithQ
  dsimp only
  rw [count_dFaWrap_toff, count_dCsaLayer1_toff, count_dyn_seq,
    count_dFaChain_toff, count_dApexTAdderWithCin_toff]
  simp [DynamicCircuit.count]
@[scoped simp] lemma count_dCsa3AxisApexWithQ_t {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ)
    (v : Var) (rM0 rM1 rM2 : QRegister (m + 1) n) (rQ : QRegister 3 n) (wQc : Wire n)
    (rT : QRegister (m + 1) n) (rScr : QRegister (3 * m + 2) n) (h01 : rM0.DisjointWires rM1)
    (h02 : rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h1Q : rM1.DisjointWires rQ)
    (h1Qc : wQc ∉ rM1.image) (hQQc : wQc ∉ rQ.image) (h1T : rM1.DisjointWires rT)
    (hQT : rQ.DisjointWires rT) (h0S : rM0.DisjointWires rScr) (h1S : rM1.DisjointWires rScr)
    (h2S : rM2.DisjointWires rScr) (hQS : rQ.DisjointWires rScr) (hQcS : wQc ∉ rScr.image)
    (hTS : rT.DisjointWires rScr) : (dCsa3AxisApexWithQ isInv m v rM0 rM1 rM2 rQ wQc rT rScr
    h01 h02 h12 h1Q h1Qc hQQc h1T hQT h0S h1S h2S hQS hQcS hTS).count .T = 12 * (m + 1) + 3
    := by
  unfold dCsa3AxisApexWithQ
  dsimp only
  rw [count_dFaWrap_t, count_dCsaLayer1_t, count_dyn_seq,
    count_dFaChain_t, count_dApexTAdderWithCin_t,
    show (DynamicCircuit.circuit (cApexSign isInv
        ((rScr.slice 0 (m + 1) (by omega)) ⟨m, by omega⟩)) :
      DynamicCircuit Var n).count .T = 1 from count_cApexSign_t isInv _]
  omega
theorem dCsa3AxisApexWithQ_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (isInv : Bool) (m : ℕ) (v : Var) (rM0 rM1 rM2 : QRegister (m + 1) n) (rQ : QRegister 3 n)
    (wQc : Wire n) (rT : QRegister (m + 1) n) (rScr : QRegister (3 * m + 2) n)
    (h01 : rM0.DisjointWires rM1) (h02 : rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2)
    (h0Q : rM0.DisjointWires rQ) (h1Q : rM1.DisjointWires rQ) (h2Q : rM2.DisjointWires rQ)
    (h0Qc : wQc ∉ rM0.image) (h1Qc : wQc ∉ rM1.image) (h2Qc : wQc ∉ rM2.image)
    (hQQc : wQc ∉ rQ.image) (h0T : rM0.DisjointWires rT) (h1T : rM1.DisjointWires rT)
    (h2T : rM2.DisjointWires rT) (hQT : rQ.DisjointWires rT) (hQcT : wQc ∉ rT.image)
    (h0S : rM0.DisjointWires rScr) (h1S : rM1.DisjointWires rScr) (h2S : rM2.DisjointWires rScr)
    (hQS : rQ.DisjointWires rScr) (hQcS : wQc ∉ rScr.image) (hTS : rT.DisjointWires rScr) :
    let sgn : ℤ := if isInv then -1 else 1
    let hQcScr : (QRegister.singleton wQc).DisjointWires rScr :=
      QRegExt.disjointWires_of_finset
        (qreg_singleton_image wQc ▸ Finset.disjoint_singleton_left.mpr hQcS)
    ∃ u : Unitary (2 ^ n),
      CleanUnitaryWp ((QRegister.singleton wQc).concat rScr hQcScr) u
        (dCsa3AxisApexWithQ isInv m v rM0 rM1 rM2 rQ wQc rT rScr
          h01 h02 h12 h1Q h1Qc hQQc h1T hQT h0S h1S h2S hQS hQcS hTS) ∧
      DiagOn (Finset.univ \ rT.image) u.1 ∧
      ∀ ξ : BitAssignment n,
        ξ wQc = 0 → (∀ i : Fin (3 * m + 2), ξ (rScr i) = 0) →
        let S : ℕ := (regVal rM0 ξ + (ξ (rQ 0)).val) + (regVal rM1 ξ + (ξ (rQ 1)).val) +
            (regVal rM2 ξ + (ξ (rQ 2)).val)
        u.1.mulVec (basisKet ξ) =
          apexCarryPhase rT ξ (sgn * (S : ℤ)) •
            basisKet (shiftRegInt rT ξ (sgn * (S : ℤ))) := by
  intro sgn hQcScr
  let rC1 := rScr.slice 0 (m + 1) (by omega)
  let rD2 := rScr.slice (m + 1) m (by omega)
  let rCApex := rScr.slice (2 * m + 1) (m + 1) (by omega)
  let rA := rC1.slice 0 m (by omega)
  let rB := rM1.slice 1 m (by omega)
  have hC1_sub : rC1.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
  have hD2_sub : rD2.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
  have hCA_sub : rCApex.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
  have hA_sub : rA.image ⊆ rScr.image := (QRegister.image_compose_subset rC1 _).trans hC1_sub
  have hB_sub : rB.image ⊆ rM1.image := QRegister.image_compose_subset rM1 _
  have hC1_D2 := slice_disjoint_of_le rScr 0 (m + 1) (m + 1) m (by omega) (by omega) (by omega)
  have hC1_CA := slice_disjoint_of_le rScr 0 (m + 1) (2 * m + 1) (m + 1) (by omega) (by omega)
    (by omega)
  have hD2_CA := slice_disjoint_of_le rScr (m + 1) m (2 * m + 1) (m + 1) (by omega) (by omega)
    (by omega)
  have hAB := (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm h1S))
    hA_sub)) hB_sub
  have hAD : rA.DisjointWires rD2 := (QRegExt.disjointWires_mono_left hC1_D2)
    (QRegister.image_compose_subset rC1 _)
  have hBD := (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h1S) hB_sub))
    hD2_sub
  obtain ⟨uAdd, hwAdd, hDiagAdd, hKetAdd⟩ := dApexTAdderWithCin_spec isInv (m + 1) v (rQ 1)
    rM1 rT rCApex ((disj_symm h1Q).apply_not_mem_right 1) (hQT.apply_not_mem_right 1)
    (fun h ↦ (hQS.apply_not_mem_right 1) (hCA_sub h)) h1T ((QRegExt.disjointWires_mono_right h1S)
      hCA_sub)
    ((QRegExt.disjointWires_mono_right hTS) hCA_sub)
  obtain ⟨uFa, hwFa, hDiagFa, hKetFa⟩ := dFaChain_spec isInv m v rT rCApex wQc rA rB rD2
    (fun h ↦ hQcS (hA_sub h)) (fun h ↦ h1Qc (hB_sub h)) (fun h ↦ hQcS (hD2_sub h)) hAB hAD
    hBD hQcT ((QRegExt.disjointWires_mono_left (disj_symm hTS)) hA_sub)
      ((QRegExt.disjointWires_mono_left h1T) hB_sub)
    ((QRegExt.disjointWires_mono_left (disj_symm hTS)) hD2_sub) (fun h ↦ hQcS (hCA_sub h))
    ((QRegExt.disjointWires_mono_left hC1_CA) (QRegister.image_compose_subset rC1 _))
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h1S) hB_sub)) hCA_sub)
      hD2_CA hwAdd hDiagAdd (fun γ ↦
      apexCarryPhase rT γ (sgn * (((γ (rQ 1)).val + regVal rM1 γ : ℕ) : ℤ)))
    (fun γ ↦ sgn * (((γ (rQ 1)).val + regVal rM1 γ : ℕ) : ℤ)) hKetAdd
  let rD2CA := rD2.concat rCApex hD2_CA
  have hD2CA_sub : rD2CA.image ⊆ rScr.image :=
    qreg_image_concat _ _ _ ▸ Finset.union_subset hD2_sub hCA_sub
  let c1Top := rC1 ⟨m, by omega⟩
  let uMid := uFa * (cApexSign isInv c1Top).eval
  have hKetMid : ∀ η : BitAssignment n, (∀ j : Fin (m + (m + 1)), η (rD2CA j) = 0) →
      uMid.1.mulVec (basisKet η) = apexCarryPhase rT η (sgn * (((η (rQ 1)).val + 2 * (η
      wQc).val + regVal rM1 η + 2 * regVal rC1 η : ℕ) : ℤ)) • basisKet (shiftRegInt rT η (sgn
      * (((η (rQ 1)).val + 2 * (η wQc).val + regVal rM1 η + 2 * regVal rC1 η : ℕ) : ℤ))) := by
    intro η hzD2CA
    obtain ⟨γ, coutBit, hγ_out, _, hγ_sum, hγ_ket⟩ := hKetFa η
      (fun i ↦ by simpa [rD2CA, QRegister.concat_apply_left] using hzD2CA (Fin.castAdd (m + 1) i))
      (fun j ↦ by simpa [rD2CA, QRegister.concat_apply_right] using hzD2CA (Fin.natAdd m j))
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, cApexSign_evolve, Matrix.mulVec_smul,
      hγ_ket, smul_smul, ← mul_assoc, DyadicQft64.dyadicTurn_add]
    have hT_γ : regVal rT γ = regVal rT η := congrArg bitsVal (funext fun j ↦ hγ_out (rT j)
      (fun h ↦ (disj_symm h1T).apply_not_mem_right j (hB_sub h))
      (fun h ↦ (hTS.apply_not_mem_right j) (hD2_sub h)))
    rw [show ∀ d : ℤ, apexCarryPhase rT γ d = apexCarryPhase rT η d from fun d ↦ by
        unfold apexCarryPhase
        rw [hT_γ],
      hγ_out (rQ 1) (fun h ↦ (disj_symm h1Q).apply_not_mem_right 1 (hB_sub h))
        (fun h ↦ (hQS.apply_not_mem_right 1) (hD2_sub h))]
    have hC1_sp : regVal rC1 η = regVal rA η + 2 ^ m * (η c1Top).val := regVal_split_last rC1 η
    have hM1_η : regVal rM1 η = (η (rM1 0)).val + 2 * regVal rB η := regVal_succ rM1 η
    have hM1_γ : regVal rM1 γ = (η (rM1 0)).val + 2 * regVal rB γ :=
      hγ_out (rM1 0) (qreg_zero_not_mem_tail rM1)
        (fun h ↦ (h1S.apply_not_mem_right 0) (hD2_sub h)) ▸ regVal_succ rM1 γ
    have hS_z : (((η (rQ 1)).val + 2 * (η wQc).val + regVal rM1 η + 2 * regVal rC1 η : ℕ) : ℤ) =
        (((η (rQ 1)).val + regVal rM1 γ : ℕ) : ℤ) +
          (2 ^ (m + 1) : ℤ) * (((η c1Top).val + coutBit : ℕ) : ℤ) := by
      exact_mod_cast (show (η (rQ 1)).val + 2 * (η wQc).val + regVal rM1 η + 2 * regVal rC1 η =
        ((η (rQ 1)).val + regVal rM1 γ) + 2 ^ (m + 1) * ((η c1Top).val + coutBit) by
        rw [pow_succ', mul_assoc 2 (2 ^ m) ((η c1Top).val + coutBit), Nat.mul_add]
        omega)
    have hSgnAdd : (if isInv = true then -1 else 1) * ((η c1Top).val : ℤ) + sgn * (coutBit : ℤ) =
        sgn * (((η c1Top).val + coutBit : ℕ) : ℤ) := by
      dsimp [sgn]
      ring
    rw [hSgnAdd, apexCarryPhase_add_mul_two_pow, shiftRegInt_add_mul_two_pow, ← hS_z]
  have hC1_D2CA : rC1.DisjointWires rD2CA := QRegExt.disjointWires_of_finset
    (qreg_image_concat _ _ _ ▸ Finset.disjoint_union_right.mpr
      ⟨(QRegExt.disjointWires_to_finset hC1_D2), (QRegExt.disjointWires_to_finset hC1_CA)⟩)
  obtain ⟨uL1, hwL1, hDiagL1, hKetL1⟩ := dCsaLayer1_spec (m + 1) v rT rD2CA rM0 rM1 rM2 rC1
    h01 h02 h12 ((QRegExt.disjointWires_mono_right h0S) hC1_sub) ((QRegExt.disjointWires_mono_right
      h1S) hC1_sub) ((QRegExt.disjointWires_mono_right h2S) hC1_sub)
    h0T h1T h2T ((QRegExt.disjointWires_mono_left (disj_symm hTS)) hC1_sub)
      ((QRegExt.disjointWires_mono_right h0S) hD2CA_sub)
    ((QRegExt.disjointWires_mono_right h1S) hD2CA_sub) ((QRegExt.disjointWires_mono_right h2S)
      hD2CA_sub) hC1_D2CA
    (CleanUnitaryWp.seq_of_diag
      (JunctionApexCSA288.CleanUnitaryWp.circuit (Var := Var) rD2CA (cApexSign isInv c1Top))
      hwFa (diagOn_of_diag_ket _ _ (cApexSign_evolve isInv c1Top)))
    (DiagOn.mul hDiagFa (diagOn_of_diag_ket _ _ (cApexSign_evolve isInv c1Top))) _ _ hKetMid
  let rTot := (QRegister.singleton wQc).concat rScr hQcScr
  have hq_ne : ∀ i j : Fin 3, i ≠ j → rQ i ≠ rQ j := fun _ _ hij h ↦ hij (rQ.wires.injective h)
  have hq_c : ∀ i : Fin 3, rQ i ≠ wQc :=
    fun i h ↦ hQQc (h ▸ (QRegister.mem_image rQ _).mpr ⟨i, rfl⟩)
  have hqNotTot : ∀ j : Fin 3, rQ j ∉ rTot.image := fun j hm ↦ by
    rw [qreg_image_concat, qreg_singleton_image, Finset.mem_union, Finset.mem_singleton] at hm
    exact hm.elim (fun e ↦ hq_c j e) (hQS.apply_not_mem_right j)
  obtain ⟨u, hw, hDiag, hKetFaWrap⟩ := dFaWrap_spec v rT rScr rTot (rQ 0) (rQ 1) (rQ 2) wQc
    (hq_ne 0 1 (by decide)) (hq_ne 0 2 (by decide)) (hq_ne 1 2 (by decide))
    (hq_c 0) (hq_c 1) (hq_c 2)
    (qreg_image_concat _ _ _ ▸ Finset.subset_union_right)
    (by rw [qreg_image_concat, qreg_singleton_image]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _))
    hQcS (hqNotTot 0) (hqNotTot 1) (hqNotTot 2)
    (hQT.apply_not_mem_right 0) (hQT.apply_not_mem_right 1) (hQT.apply_not_mem_right 2) hQcT
    (hwL1.mono_workspace (qreg_image_concat _ _ _ ▸ Finset.union_subset hC1_sub hD2CA_sub)) hDiagL1
  refine ⟨u, hw, hDiag, fun ξ hzQc hzScr ↦ ?_⟩
  let ξ₁ := Function.update (Function.update ξ (rQ 1) (ξ (rQ 1) + ξ (rQ 2) + ξ (rQ 0))) wQc
    (carryBitZMod2 (ξ (rQ 2)) (ξ (rQ 0)) (ξ (rQ 1)))
  have hξ₁_out : ∀ w, w ≠ rQ 1 → w ≠ wQc → ξ₁ w = ξ w := fun w h1 h2 ↦ by
    simp only [ξ₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have hzSub_₁ : ∀ {k} (rSub : QRegister k n), rSub.image ⊆ rScr.image →
      ∀ i : Fin k, ξ₁ (rSub i) = 0 := fun rSub hSub i ↦ by
    have hInS := hSub ((QRegister.mem_image rSub _).mpr ⟨i, rfl⟩)
    rw [hξ₁_out _ (fun h ↦ (hQS.apply_not_mem_right 1) (h ▸ hInS)) (fun h ↦ hQcS (h ▸ hInS))]
    rcases (QRegister.mem_image rScr _).mp hInS with ⟨k, hk⟩
    exact hk ▸ hzScr k
  obtain ⟨η, hη_out, _, hη_sum, hη_ket⟩ :=
    hKetL1 ξ₁ (hzSub_₁ rC1 hC1_sub) (hzSub_₁ rD2CA hD2CA_sub)
  have hReg_₁ : ∀ {k} (r : QRegister k n), r.DisjointWires rQ → wQc ∉ r.image →
      regVal r ξ₁ = regVal r ξ := fun r hrQ hrQc ↦
    congrArg bitsVal (funext fun j ↦ hξ₁_out _ (disj_wire_ne hrQ j 1)
      (fun h ↦ hrQc (h ▸ (QRegister.mem_image r _).mpr ⟨j, rfl⟩)))
  have hT_η : regVal rT η = regVal rT ξ :=
    (congrArg bitsVal (funext fun j ↦ hη_out (rT j) ((disj_symm h1T).apply_not_mem_right j)
      (fun h ↦ (hTS.apply_not_mem_right j) (hC1_sub h)))).trans
      (hReg_₁ rT (disj_symm hQT) hQcT)
  have hTotEq : (η (rQ 1)).val + 2 * (η wQc).val + regVal rM1 η + 2 * regVal rC1 η =
      (regVal rM0 ξ + (ξ (rQ 0)).val) + (regVal rM1 ξ + (ξ (rQ 1)).val) +
      (regVal rM2 ξ + (ξ (rQ 2)).val) := by
    have hQ := carryBitZMod2_val_eq (ξ (rQ 2)) (ξ (rQ 0)) (ξ (rQ 1))
    rw [hη_out (rQ 1) ((disj_symm h1Q).apply_not_mem_right 1)
        (fun h ↦ (hQS.apply_not_mem_right 1) (hC1_sub h)),
      hη_out wQc h1Qc (fun h ↦ hQcS (hC1_sub h))]
    simp only [ξ₁, Function.update_self, Function.update_of_ne (hq_c 1)]
    rw [hReg_₁ rM0 h0Q h0Qc, hReg_₁ rM1 h1Q h1Qc, hReg_₁ rM2 h2Q h2Qc] at hη_sum
    omega
  rw [show ∀ d : ℤ, apexCarryPhase rT η d = apexCarryPhase rT ξ d from fun d ↦ by
      unfold apexCarryPhase
      rw [hT_η], hTotEq] at hη_ket
  exact hKetFaWrap ξ hzQc hη_ket
lemma rCosetB0_disj_rProjAxis {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    (rCosetB0 hm rCore).DisjointWires (rProjAxis rCore w) := by
  refine QRegExt.disjointWires_of_finset (Finset.disjoint_left.mpr fun u hu1 hu2 ↦ ?_)
  rcases (QRegister.mem_image _ u).mp hu1 with ⟨i, rfl⟩
  rcases (QRegister.mem_image _ _).mp hu2 with ⟨j, hj⟩
  unfold rCosetB0 rProjAxis at hj
  rw [slice_apply_eq, slice_apply_eq] at hj
  have hv := congrArg Fin.val (rCore.wires.injective hj)
  dsimp at hv
  have := w.isLt
  have := i.isLt
  have := j.isLt
  omega
def rWhFull {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) : QRegister 8 n :=
  ⟨⟨fun i ↦ if hi : i.val = 0 then rCosetB0 hm rCore w
            else rProjAxis rCore w ⟨8 - i.val, by omega⟩,
    fun i j hij ↦ by
      have := i.isLt
      have := j.isLt
      by_cases hi0 : i.val = 0
      · by_cases hj0 : j.val = 0
        · exact Fin.ext (by omega)
        · simp only [hi0, hj0, ↓reduceDIte] at hij
          exact (disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore w) w _ hij).elim
      · by_cases hj0 : j.val = 0
        · simp only [hi0, hj0, ↓reduceDIte] at hij
          exact (disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore w) w _ hij.symm).elim
        · simp only [hi0, hj0, ↓reduceDIte] at hij
          have hv := congrArg Fin.val ((rProjAxis rCore w).wires.injective hij)
          dsimp at hv
          exact Fin.ext (by omega)⟩⟩
lemma rWhFull_apply_zero {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    rWhFull hm rCore w 0 = rCosetB0 hm rCore w := rfl
lemma rWhFull_apply_pos {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3)
    (i : Fin 8) (hi : i.val ≠ 0) :
    rWhFull hm rCore w i = rProjAxis rCore w ⟨8 - i.val, by omega⟩ := by
  unfold rWhFull
  change (if h : i.val = 0 then _ else _) = _
  simp [hi]
lemma rWhFull_sub_rCore {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    (rWhFull hm rCore w).image ⊆ rCore.image := by
  intro u hu
  rcases (QRegister.mem_image _ u).mp hu with ⟨i, rfl⟩
  by_cases hi : i.val = 0
  · rw [show i = 0 from Fin.ext hi, rWhFull_apply_zero]
    exact rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  · rw [rWhFull_apply_pos hm rCore w i hi]
    exact rProjAxis_sub_rCore rCore w ((QRegister.mem_image _ _).mpr ⟨_, rfl⟩)
lemma rWhFull_disjoint_of_ne {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) :
    (rWhFull hm rCore w₁).DisjointWires (rWhFull hm rCore w₂) := by
  refine QRegExt.disjointWires_of_finset (Finset.disjoint_left.mpr fun u hu1 hu2 ↦ ?_)
  rcases (QRegister.mem_image _ u).mp hu1 with ⟨i, rfl⟩
  rcases (QRegister.mem_image _ _).mp hu2 with ⟨j, hj⟩
  by_cases hi : i.val = 0
  · rw [show i = 0 from Fin.ext hi, rWhFull_apply_zero] at hj
    by_cases hj0 : j.val = 0
    · rw [show j = 0 from Fin.ext hj0, rWhFull_apply_zero] at hj
      exact hne ((rCosetB0 hm rCore).wires.injective hj).symm
    · rw [rWhFull_apply_pos hm rCore w₂ j hj0] at hj
      exact disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore w₂) w₁ _ hj.symm
  · rw [rWhFull_apply_pos hm rCore w₁ i hi] at hj
    by_cases hj0 : j.val = 0
    · rw [show j = 0 from Fin.ext hj0, rWhFull_apply_zero] at hj
      exact disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore w₁) w₂ _ hj
    · rw [rWhFull_apply_pos hm rCore w₂ j hj0] at hj
      exact disj_wire_ne (rProjAxis_disjoint_of_ne rCore hne.symm) _ _ hj
lemma rWhFull_idReg_apply {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) (i : Fin 8) :
    rCore (rWhFull hm (QRegExt.idReg (fullSysCoreWires mPayload)) w i) =
      rWhFull hm rCore w i := by
  by_cases hi : i.val = 0
  · rw [show i = 0 from Fin.ext hi, rWhFull_apply_zero, rWhFull_apply_zero]
    simp [rCosetB0, QRegister.slice, QRegExt.idReg]
  · rw [rWhFull_apply_pos hm _ w i hi, rWhFull_apply_pos hm _ w i hi]
    simp [rProjAxis, QRegister.slice, QRegExt.idReg]
lemma regVal_rWhFull_slice_idReg {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) (s l : ℕ) (hsl : s + l ≤ 8)
    (ξ : BitAssignment n) : regVal ((rWhFull hm rCore w).slice s l hsl) ξ = regVal ((rWhFull
    hm (QRegExt.idReg (fullSysCoreWires mPayload)) w).slice s l hsl) (fun q ↦ ξ (rCore q)) :=
  congrArg bitsVal (funext fun j ↦ by
    rw [slice_apply_eq, slice_apply_eq]
    exact congrArg ξ (rWhFull_idReg_apply hm rCore w _).symm)
lemma fin_sum_univ_seven {M : Type*} [AddCommMonoid M] (f : Fin 7 → M) :
    (∑ i : Fin 7, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_six]
  abel
lemma regVal_wh_telescope {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) (ξ : BitAssignment n) :
    (∑ k : Fin 7, (2 ^ k.val : ℤ) *
      (regVal ((rWhFull hm rCore w).slice 0 (8 - k.val) (by omega)) ξ : ℤ)) +
    (regVal ((rWhFull hm rCore w).slice 0 7 (by decide)) ξ : ℤ) =
    128 * ((ξ (rCosetB0 hm rCore w)).val : ℤ) + 128 * ((ξ (rProjAxis rCore w 1)).val : ℤ) +
    256 * (((ξ (rProjAxis rCore w 2)).val : ℤ) + ((ξ (rProjAxis rCore w 3)).val : ℤ) +
      ((ξ (rProjAxis rCore w 4)).val : ℤ) + ((ξ (rProjAxis rCore w 5)).val : ℤ) +
      ((ξ (rProjAxis rCore w 6)).val : ℤ) + ((ξ (rProjAxis rCore w 7)).val : ℤ)) := by
  rw [fin_sum_univ_seven]
  unfold regVal bitsVal rWhFull
  dsimp
  simp only [Fin.sum_univ_eight, fin_sum_univ_seven, Fin.sum_univ_six,
    Fin.sum_univ_five, Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two]
  dsimp
  ring
def cSSign {n : ℕ} (isInv : Bool) (c : Wire n) : Circuit n :=
  if isInv then (Circuit.S c).inverse else Circuit.S c
@[scoped simp] lemma count_cSSign_toff {n : ℕ} (isInv : Bool) (c : Wire n) :
    (cSSign isInv c).count .TOFF = 0 := isInv.casesOn rfl rfl
@[scoped simp] lemma count_cSSign_t {n : ℕ} (isInv : Bool) (c : Wire n) :
    (cSSign isInv c).count .T = 0 := isInv.casesOn rfl rfl
lemma cSSign_evolve {n : ℕ} (isInv : Bool) (c : Wire n) (ξ : BitAssignment n) :
    (cSSign isInv c).eval.1.mulVec (basisKet ξ) = DyadicQft64.dyadicTurn 48
    ((if isInv then (-1 : ℤ) else 1) * (2 ^ 46 : ℤ) * ((ξ c).val : ℤ)) • basisKet ξ := by
  cases isInv
  · change (Circuit.S c).eval.1.mulVec (basisKet ξ) =
      DyadicQft64.dyadicTurn 48 (1 * (2 ^ 46 : ℤ) * ((ξ c).val : ℤ)) • basisKet ξ
    rw [(PhasePerm.gateS c).evolve ξ,
      ← JunctionApexCSA288.dyadicTurn_scale_pow 41 7]
    exact congrArg (fun z ↦ DyadicQft64.dyadicTurn 48 z • basisKet ξ) (by ring)
  · change (Circuit.S c).inverse.eval.1.mulVec (basisKet ξ) =
      DyadicQft64.dyadicTurn 48 ((-1) * (2 ^ 46 : ℤ) * ((ξ c).val : ℤ)) • basisKet ξ
    rw [(PhasePerm.gateSDag c).evolve ξ,
      ← JunctionApexCSA288.dyadicTurn_scale_pow 41 7]
    exact congrArg (fun z ↦ DyadicQft64.dyadicTurn 48 z • basisKet ξ) (by ring)
def cWhTopAxis {n : ℕ} (isInv : Bool) (q top : Wire n) (hne : q ≠ top) : Circuit n :=
  cSSign isInv q ;;ᶜ
    Circuit.CNOT q top hne ;;ᶜ
    cApexSign (!isInv) top ;;ᶜ
    Circuit.CNOT q top hne
@[scoped simp] lemma count_cWhTopAxis_toff {n : ℕ} (isInv : Bool) (q top : Wire n)
    (hne : q ≠ top) : (cWhTopAxis isInv q top hne).count .TOFF = 0 := isInv.casesOn rfl rfl
@[scoped simp] lemma count_cWhTopAxis_t {n : ℕ} (isInv : Bool) (q top : Wire n)
    (hne : q ≠ top) : (cWhTopAxis isInv q top hne).count .T = 1 := isInv.casesOn rfl rfl
lemma cWhTopAxis_evolve {n : ℕ} (isInv : Bool) (q top : Wire n) (hne : q ≠ top)
    (ξ : BitAssignment n) : (cWhTopAxis isInv q top hne).eval.1.mulVec (basisKet ξ) =
    DyadicQft64.dyadicTurn 48 ((if isInv then (-1 : ℤ) else 1) * (2 ^ 45 : ℤ) * ((2 * ((ξ
    q).val : ℤ) - 1) * ((ξ top).val : ℤ) + ((ξ q).val : ℤ))) • basisKet ξ := by
  have hRestore : Function.update (Function.update ξ top (ξ top + ξ q)) top
      (ξ top + ξ q + Function.update ξ top (ξ top + ξ q) q) = ξ :=
    funext fun u ↦ by
      by_cases hu : u = top
      · subst hu
        simp [Function.update_of_ne hne]
      · simp [Function.update_of_ne hu]
  unfold cWhTopAxis
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, cSSign_evolve,
    evolve_CNOT_basisKet, cApexSign_evolve, Matrix.mulVec_smul, smul_smul,
    Function.update_self,
    (JunctionApexCSA288.dyadicTurn_scale_pow 45 3 _).symm,
    DyadicQft64.dyadicTurn_add]
  rw [hRestore]
  refine congrArg (fun x ↦ DyadicQft64.dyadicTurn 48 x • basisKet ξ) ?_
  rw [zmod2_add_val_int (ξ top) (ξ q)]
  cases isInv
  all_goals
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    ring
lemma regVal_flip_plus_bit_eq {W n : ℕ} (r : QRegister W n) (q : Wire n)
    (hq : q ∉ r.image) (ξ : BitAssignment n) :
    let ξ_f := if ξ q = 1 then flipRegBits r ξ else ξ
    ((regVal r ξ_f + (ξ_f q).val : ℕ) : ℤ) =
      (1 - 2 * ((ξ q).val : ℤ)) * (regVal r ξ : ℤ) + ((ξ q).val : ℤ) * (2 ^ W : ℤ) := by
  intro ξ_f
  have hqf : ξ_f q = ξ q := by
    dsimp [ξ_f]
    split_ifs
    · exact flipRegBits_outside r ξ hq
    · rfl
  rw [hqf]
  rcases zmod2_eq_zero_or_one (ξ q) with h0 | h1
  · simp [ξ_f, h0]
  · have hadd := regVal_flipRegBits_add r ξ
    simp only [ξ_f, h1, ↓reduceIte, show (1 : ZMod 2).val = 1 from rfl]
    push_cast
    zify [Nat.one_le_two_pow (n := W)] at hadd
    linarith
def whStg7Exp {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let sgn : ℤ := if isInv then -1 else 1
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (-sgn) * (2 ^ 39 : ℤ) * 128 * wfBitVal hm γ *
    (∑ w : Fin 3, ((γ (rCosetB0 hm rId w)).val : ℤ) * ((γ (rProjAxis rId w 7)).val : ℤ))
noncomputable def uWhStg7Cat {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool) : Unitary
    (2 ^ (fullSysCoreWires mPayload + 48)) := (rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whStg7Exp hm isInv))
lemma uWhStg7Cat_inv_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (uWhStg7Cat hm false)⁻¹ = uWhStg7Cat hm true := by
  rw [uWhStg7Cat, uWhStg7Cat, ← QRegister.embedUnitary_inv, DyadicQft64.dyadicDiagUnitary_inv]
  refine congrArg _ (congrArg _ (funext fun γ ↦ ?_))
  simp only [whStg7Exp, Bool.false_eq_true, ↓reduceIte]
  ring
def whStgTopExp {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let sgn : ℤ := if isInv then -1 else 1
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let W : ℕ := 7 - k.val
  sgn * (2 ^ 45 : ℤ) *
    (∑ w : Fin 3,
      let q_w : ℤ := wfBitVal hm γ * ((γ (rProjAxis rId w ⟨k.val, by omega⟩)).val : ℤ)
      let t_w : ℤ := ((γ (rWhFull hm rId w ⟨W, by omega⟩)).val : ℤ)
      (2 * q_w - 1) * t_w + q_w)
def whStgLowShift {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let sgn : ℤ := if isInv then -1 else 1
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let W : ℕ := 7 - k.val
  (-sgn) *
    (∑ w : Fin 3,
      let q_w : ℤ := wfBitVal hm γ * ((γ (rProjAxis rId w ⟨k.val, by omega⟩)).val : ℤ)
      (1 - 2 * q_w) * (regVal ((rWhFull hm rId w).slice 0 W (by omega)) γ : ℤ) +
        q_w * (2 ^ W : ℤ))
noncomputable def uWhStgCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) (isInv : Bool) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  uApexShift45 (fullSysCoreWires mPayload) (7 - k.val) (by omega) (whStgLowShift hm k isInv) *
    (rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whStgTopExp hm k isInv))
lemma uWhStgCat_inv_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) :
    (uWhStgCat hm k false)⁻¹ = uWhStgCat hm k true := by
  rw [uWhStgCat, uWhStgCat, _root_.mul_inv_rev, uApexShift45_inv, ← QRegister.embedUnitary_inv,
    DyadicQft64.dyadicDiagUnitary_inv,
    show (fun γ ↦ -whStgLowShift hm k false γ) = whStgLowShift hm k true from funext fun γ ↦ by
      simp only [whStgLowShift, Bool.false_eq_true, ↓reduceIte]
      ring,
    show (fun γ ↦ -whStgTopExp hm k false γ) = whStgTopExp hm k true from funext fun γ ↦ by
      simp only [whStgTopExp, Bool.false_eq_true, ↓reduceIte]
      ring]
  exact uApexShift45_comm_coreDiag (fullSysCoreWires mPayload) (7 - k.val) _ 48
    (whStgTopExp hm k true) (whStgLowShift hm k true)
def whRemTopExp {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let sgn : ℤ := if isInv then -1 else 1
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  sgn *
    (∑ w : Fin 3,
      ((2 ^ 45 : ℤ) * ((γ (rCosetB0 hm rId w)).val : ℤ) +
       (2 ^ 45 : ℤ) * ((γ (rProjAxis rId w 1)).val : ℤ) +
       (2 ^ 46 : ℤ) *
         (((γ (rProjAxis rId w 2)).val : ℤ) +
          ((γ (rProjAxis rId w 3)).val : ℤ) +
          ((γ (rProjAxis rId w 4)).val : ℤ) +
          ((γ (rProjAxis rId w 5)).val : ℤ) +
          ((γ (rProjAxis rId w 6)).val : ℤ) +
          ((γ (rProjAxis rId w 7)).val : ℤ))))
def whRemLowShift {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let sgn : ℤ := if isInv then -1 else 1
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (-sgn) * (∑ w : Fin 3, (regVal ((rWhFull hm rId w).slice 0 7 (by decide)) γ : ℤ))
noncomputable def uWhRemCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool) : Unitary
    (2 ^ (fullSysCoreWires mPayload + 48)) := uApexShift45 (fullSysCoreWires mPayload) 7
    (by decide) (whRemLowShift hm isInv) * (rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whRemTopExp hm isInv))
lemma uWhRemCat_inv_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (uWhRemCat hm false)⁻¹ = uWhRemCat hm true := by
  rw [uWhRemCat, uWhRemCat, _root_.mul_inv_rev, uApexShift45_inv, ← QRegister.embedUnitary_inv,
    DyadicQft64.dyadicDiagUnitary_inv,
    show (fun γ ↦ -whRemLowShift hm false γ) = whRemLowShift hm true from funext fun γ ↦ by
      simp only [whRemLowShift, Bool.false_eq_true, ↓reduceIte]
      ring,
    show (fun γ ↦ -whRemTopExp hm false γ) = whRemTopExp hm true from funext fun γ ↦ by
      simp only [whRemTopExp, Bool.false_eq_true, ↓reduceIte]
      ring]
  exact uApexShift45_comm_coreDiag (fullSysCoreWires mPayload) 7 (by decide) 48
    (whRemTopExp hm true) (whRemLowShift hm true)
noncomputable def whStg7Diag8 (b : Fin 2) : Unitary 256 :=
  ⟨Matrix.diagonal fun u : Fin 256 ↦ omega512 (-128 * (b.val : ℤ) * (bit8 u 7 : ℤ)), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ star_mul_omega512_self _)⟩
def whSliceVal8 (k : Fin 7) (b : Fin 2) (u : Fin 256) : ℤ :=
  match k.val with
  | 0 => (b.val : ℤ) + 2 * (bit8 u 7 : ℤ) + 4 * (bit8 u 6 : ℤ) + 8 * (bit8 u 5 : ℤ) +
         16 * (bit8 u 4 : ℤ) + 32 * (bit8 u 3 : ℤ) + 64 * (bit8 u 2 : ℤ) + 128 * (bit8 u 1 : ℤ)
  | 1 => (b.val : ℤ) + 2 * (bit8 u 7 : ℤ) + 4 * (bit8 u 6 : ℤ) + 8 * (bit8 u 5 : ℤ) +
         16 * (bit8 u 4 : ℤ) + 32 * (bit8 u 3 : ℤ) + 64 * (bit8 u 2 : ℤ)
  | 2 => (b.val : ℤ) + 2 * (bit8 u 7 : ℤ) + 4 * (bit8 u 6 : ℤ) + 8 * (bit8 u 5 : ℤ) +
         16 * (bit8 u 4 : ℤ) + 32 * (bit8 u 3 : ℤ)
  | 3 => (b.val : ℤ) + 2 * (bit8 u 7 : ℤ) + 4 * (bit8 u 6 : ℤ) + 8 * (bit8 u 5 : ℤ) +
         16 * (bit8 u 4 : ℤ)
  | 4 => (b.val : ℤ) + 2 * (bit8 u 7 : ℤ) + 4 * (bit8 u 6 : ℤ) + 8 * (bit8 u 5 : ℤ)
  | 5 => (b.val : ℤ) + 2 * (bit8 u 7 : ℤ) + 4 * (bit8 u 6 : ℤ)
  | _ => (b.val : ℤ) + 2 * (bit8 u 7 : ℤ)
lemma whSliceVal8_symm {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    let rId := QRegExt.idReg (fullSysCoreWires mPayload)
    whSliceVal8 k ⟨(γ (rCosetB0 hm rId w)).val, ZMod.val_lt _⟩
      ((basisBitsEquiv 8).symm (fun i ↦ γ (rProjAxis rId w i))) =
      (regVal ((rWhFull hm rId w).slice 0 (8 - k.val) (by omega)) γ : ℤ) := by
  intro rId
  have hb := bit8_symm_eq (fun i ↦ γ (rProjAxis rId w i))
  fin_cases k
  all_goals
    unfold whSliceVal8 regVal bitsVal rWhFull
    dsimp
    simp only [Fin.sum_univ_eight, fin_sum_univ_seven, Fin.sum_univ_six,
      Fin.sum_univ_five, Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two, hb]
    dsimp
    ring
noncomputable def whGatedDiag8 (k : Fin 7) (b : Fin 2) : Unitary 256 :=
  ⟨Matrix.diagonal fun u : Fin 256 ↦
    omega512 ((2 ^ k.val : ℤ) * (bit8 u ⟨k.val, by omega⟩ : ℤ) * whSliceVal8 k b u), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ star_mul_omega512_self _)⟩
def whUngatedExp {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (-(2 ^ (38 + k.val) : ℤ)) *
    (∑ w : Fin 3, (regVal ((rWhFull hm rId w).slice 0 (8 - k.val) (by omega)) γ : ℤ))
noncomputable def uWhUngatedCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whUngatedExp hm k)
noncomputable def uWhRemCore {mPayload : ℕ} (hm : 22 ≤ mPayload) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := DyadicQft64.dyadicDiagUnitary
    (fullSysCoreWires mPayload) 48 (fun γ ↦ ∑ k : Fin 7, -whUngatedExp hm k γ)

lemma regVal_slice_congr_wh {M s l₁ l₂ n : ℕ} (r : QRegister M n)
    (h₁ : s + l₁ ≤ M) (h₂ : s + l₂ ≤ M) (hEq : l₁ = l₂) (ξ : BitAssignment n) :
    regVal (r.slice s l₁ h₁) ξ = regVal (r.slice s l₂ h₂) ξ := hEq ▸ rfl
lemma regVal_rWhFull_split_top {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) (k : Fin 7)
    (ξ : BitAssignment n) :
    (regVal ((rWhFull hm rCore w).slice 0 (8 - k.val) (by omega)) ξ : ℤ) =
      (regVal ((rWhFull hm rCore w).slice 0 (7 - k.val) (by omega)) ξ : ℤ) +
        (2 ^ (7 - k.val) : ℤ) * ((ξ (rWhFull hm rCore w ⟨7 - k.val, by omega⟩)).val : ℤ) := by
  let W := 7 - k.val
  have h8 : 8 - k.val = W + 1 := by
    have := k.isLt
    omega
  let rSl := (rWhFull hm rCore w).slice 0 (W + 1) (by omega)
  rw [regVal_slice_congr_wh (rWhFull hm rCore w) _ (by omega) h8 ξ, regVal_split_last rSl ξ,
    show rSl.slice 0 W (by omega) = (rWhFull hm rCore w).slice 0 W (by omega) from
      qreg_ext_local fun i ↦ congrArg (rWhFull hm rCore w) (Fin.ext (by simp)),
    show rSl ⟨W, Nat.lt_succ_self W⟩ = rWhFull hm rCore w ⟨W, by omega⟩ from
      congrArg (rWhFull hm rCore w) (Fin.ext (by simp))]
  push_cast
  rfl

lemma uWhRemCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (uWhRemCat hm false) (uWhRemCore hm) := by
  have hProd := (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whRemTopExp hm false))).mul
    (uApexShift45_intertwinesLocal (fullSysCoreWires mPayload) 7
      (by decide) (whRemLowShift hm false) U_cat_48 hcol0)
  suffices hEff :
      DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
          (fun γ ↦ (2 ^ (45 - 7) : ℤ) * whRemLowShift hm false γ) *
        DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whRemTopExp hm false) =
      uWhRemCore hm from hEff ▸ hProd
  rw [dyadicDiagUnitary_mul, uWhRemCore]
  refine dyadicDiagUnitary_congr _ 48 fun γ ↦ ?_
  have ht0 := regVal_wh_telescope hm (QRegExt.idReg _) 0 γ
  have ht1 := regVal_wh_telescope hm (QRegExt.idReg _) 1 γ
  have ht2 := regVal_wh_telescope hm (QRegExt.idReg _) 2 γ
  unfold whRemTopExp whRemLowShift whUngatedExp
  simp only [Bool.false_eq_true, ↓reduceIte, Fin.sum_univ_three, fin_sum_univ_seven]
    at ht0 ht1 ht2 ⊢
  dsimp at ht0 ht1 ht2 ⊢
  linear_combination -(2 ^ 38 : ℤ) * (ht0 + ht1 + ht2)
lemma whUngatedExp_congr_outside_le {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (k : Fin 7) (w' : Fin 3) (j : Fin 8) (hjk : j.val ≤ k.val)
    (γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload))
    (hOut : ∀ u, u ≠ rProjAxis (QRegExt.idReg _) w' j → γ₁ u = γ₂ u) :
    whUngatedExp hm k γ₁ = whUngatedExp hm k γ₂ := by
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦
    congrArg Nat.cast (congrArg bitsVal (funext fun idx ↦ hOut _ fun hEq ↦ ?_)))
  rw [slice_apply_eq] at hEq
  have := idx.isLt
  have := k.isLt
  by_cases hi0 : idx.val = 0
  · rw [show (⟨0 + idx.val, by omega⟩ : Fin 8) = 0 from Fin.ext (by simpa using hi0),
      rWhFull_apply_zero] at hEq
    exact disj_wire_ne (rCosetB0_disj_rProjAxis hm rId w') w j hEq
  · rw [rWhFull_apply_pos hm rId w _ (by simpa using hi0)] at hEq
    by_cases hww : w = w'
    · subst hww
      have hv := congrArg Fin.val ((rProjAxis rId w).wires.injective hEq)
      dsimp at hv
      omega
    · exact disj_wire_ne (rProjAxis_disjoint_of_ne rId hww) _ j hEq
lemma uWhRemCore_cancel_all {mPayload : ℕ} (hm : 22 ≤ mPayload) : uWhRemCore hm *
    (uWhUngatedCore hm 0 * (uWhUngatedCore hm 1 * (uWhUngatedCore hm 2 * (uWhUngatedCore hm 3
    * (uWhUngatedCore hm 4 * (uWhUngatedCore hm 5 * uWhUngatedCore hm 6)))))) = 1 := by
  unfold uWhRemCore uWhUngatedCore
  simp only [dyadicDiagUnitary_mul]
  refine (dyadicDiagUnitary_congr _ 48 (e₂ := fun _ ↦ 0) fun γ ↦ ?_).trans
    (Subtype.ext (matrix_ext_basisKet fun γ ↦ ?_))
  · rw [fin_sum_univ_seven]
    ring
  · rw [dyadicDiagUnitary_mulVec_basisKet, DyadicQft64.dyadicTurn_zero, one_smul,
      OneMemClass.coe_one, Matrix.one_mulVec]
lemma wireHadamard8_mulVec_state (u : Fin 256) (m : Fin 8) (n_k : ℕ) (hnk : n_k = m.val + 1)
    (Φ : Fin 256 → ℤ) (hΦ : ∀ w₁ w₂ : Fin 256, (∀ r : Fin 8, m.val < r.val → bit8 w₁ r = bit8
    w₂ r) → Φ w₁ = Φ w₂) (c : ℂ) : ((wireHadamard8 m).1.mulVec fun w ↦ if ∀ r : Fin 8, r.val <
    n_k → bit8 w r = bit8 u r then c * omega512 (Φ w) else 0) = fun z ↦ if ∀ r : Fin 8, r.val
    < m.val → bit8 z r = bit8 u r then (c * (1 / (√2 : ℂ))) * omega512
    (Φ z + ((256 * bit8 z m * bit8 u m : ℕ) : ℤ)) else 0 := by
  subst hnk
  let ψ_in : Fin 256 → ℂ := fun w ↦
    if ∀ r : Fin 8, r.val < m.val + 1 → bit8 w r = bit8 u r then c * omega512 (Φ w) else 0
  have hInv : (wireHadamard8 m).1.mulVec ψ_in =
      ((stageDiag8 m)⁻¹).1.mulVec ((stageDiag8 m * wireHadamard8 m).1.mulVec ψ_in) := by
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel_left]
  rw [hInv, stageStep8_mulVec_state u m (m.val + 1) rfl Φ hΦ c]
  funext z
  have hInvDiag : ((stageDiag8 m)⁻¹).1 =
      Matrix.diagonal (fun w : Fin 256 ↦ star (omega512 (stageRowExp512 m w))) := by
    change (stageDiag8 m).1ᴴ = _
    unfold stageDiag8
    rw [Matrix.diagonal_conjTranspose]
    rfl
  rw [hInvDiag, Matrix.mulVec_diagonal, star_omega512]
  split_ifs with hz_low
  · rw [show stageRowExp512 m z =
        ((2 ^ (8 - m.val) * bit8 z m * (u.val % 2 ^ m.val) : ℕ) : ℤ) by
      unfold stageRowExp512
      rw [z_mod_eq_of_low_bits_eq m hz_low], mul_left_comm (omega512 _), ← omega512_add]
    congr 2
    have hcombZ : ((256 * bit8 u m + 2 ^ (8 - m.val) * (u.val % 2 ^ m.val) : ℕ) : ℤ) =
        ((2 ^ (8 - m.val) * (u.val % 2 ^ (m.val + 1)) : ℕ) : ℤ) := by
      exact_mod_cast (show 256 * bit8 u m + 2 ^ (8 - m.val) * (u.val % 2 ^ m.val) =
          2 ^ (8 - m.val) * (u.val % 2 ^ (m.val + 1)) by
        have := u.isLt
        unfold bit8
        fin_cases m
        all_goals
          dsimp
          omega)
    push_cast at hcombZ ⊢
    linear_combination -(bit8 z m : ℤ) * hcombZ
  · exact mul_zero _
def DepAbove (bound : ℕ) (Φ : Fin 256 → ℤ) : Prop :=
  ∀ w₁ w₂ : Fin 256, (∀ r : Fin 8, bound < r.val → bit8 w₁ r = bit8 w₂ r) → Φ w₁ = Φ w₂

lemma whSliceVal8_congr_gt (k : Fin 7) (b : Fin 2) (w₁ w₂ : Fin 256)
    (hgt : ∀ r : Fin 8, k.val < r.val → bit8 w₁ r = bit8 w₂ r) :
    whSliceVal8 k b w₁ = whSliceVal8 k b w₂ := by
  fin_cases k
  · simp only [whSliceVal8, hgt 7 (by decide), hgt 6 (by decide), hgt 5 (by decide),
      hgt 4 (by decide), hgt 3 (by decide), hgt 2 (by decide), hgt 1 (by decide)]
  · simp only [whSliceVal8, hgt 7 (by decide), hgt 6 (by decide), hgt 5 (by decide),
      hgt 4 (by decide), hgt 3 (by decide), hgt 2 (by decide)]
  · simp only [whSliceVal8, hgt 7 (by decide), hgt 6 (by decide), hgt 5 (by decide),
      hgt 4 (by decide), hgt 3 (by decide)]
  · simp only [whSliceVal8, hgt 7 (by decide), hgt 6 (by decide), hgt 5 (by decide),
      hgt 4 (by decide)]
  · simp only [whSliceVal8, hgt 7 (by decide), hgt 6 (by decide), hgt 5 (by decide)]
  · simp only [whSliceVal8, hgt 7 (by decide), hgt 6 (by decide)]
  · simp only [whSliceVal8, hgt 7 (by decide)]

lemma whGatedStep8_mulVec_state (b : Fin 2) (u : Fin 256) (k : Fin 7) (m : Fin 8)
    (hkm : m.val = k.val) (n_k : ℕ) (hnk : n_k = m.val + 1)
    (Φ : Fin 256 → ℤ) (hΦ : DepAbove m.val Φ) (c : ℂ) :
    (wireHadamard8 m).1.mulVec ((whGatedDiag8 k b).1.mulVec fun w ↦
      if ∀ r : Fin 8, r.val < n_k → bit8 w r = bit8 u r then c * omega512 (Φ w) else 0) =
    fun z ↦
      if ∀ r : Fin 8, r.val < m.val → bit8 z r = bit8 u r then
        (c * (1 / (√2 : ℂ))) *
          omega512 (Φ z + (2 ^ k.val : ℤ) * (bit8 u m : ℤ) * whSliceVal8 k b z +
            ((256 * bit8 z m * bit8 u m : ℕ) : ℤ))
      else 0 := by
  subst hnk
  let ψ_in : Fin 256 → ℂ := fun w ↦
    if ∀ r : Fin 8, r.val < m.val + 1 → bit8 w r = bit8 u r then c * omega512 (Φ w) else 0
  have hm_eq : (⟨k.val, by omega⟩ : Fin 8) = m := Fin.ext hkm.symm
  have hDiagStep : (whGatedDiag8 k b).1.mulVec ψ_in = fun w ↦
      if ∀ r : Fin 8, r.val < m.val + 1 → bit8 w r = bit8 u r then
        c * omega512 (Φ w + (2 ^ k.val : ℤ) * (bit8 u m : ℤ) * whSliceVal8 k b w) else 0 := by
    funext w
    change (Matrix.diagonal _).mulVec ψ_in w = _
    rw [Matrix.mulVec_diagonal]
    dsimp only [ψ_in]
    split_ifs with hw
    · rw [hm_eq, hw m (Nat.lt_succ_self m.val),
        ← mul_assoc, mul_comm (omega512 _) c, mul_assoc, ← omega512_add, add_comm (Φ w)]
    · exact mul_zero _
  change (wireHadamard8 m).1.mulVec ((whGatedDiag8 k b).1.mulVec ψ_in) = _
  rw [hDiagStep]
  exact wireHadamard8_mulVec_state u m (m.val + 1) rfl _ (fun w₁ w₂ hgt ↦ by
    rw [hΦ w₁ w₂ hgt, whSliceVal8_congr_gt k b w₁ w₂ (fun r hr ↦ hgt r (hkm ▸ hr))]) c

lemma stageStep8_mulVec_ungrouped (u : Fin 256) (m : Fin 8) (n_k : ℕ) (hnk : n_k = m.val + 1)
    (Φ : Fin 256 → ℤ) (hΦ : DepAbove m.val Φ) (c : ℂ) :
    (stageDiag8 m).1.mulVec ((wireHadamard8 m).1.mulVec fun w ↦
      if ∀ r : Fin 8, r.val < n_k → bit8 w r = bit8 u r then c * omega512 (Φ w) else 0) =
    fun z ↦
      if ∀ r : Fin 8, r.val < m.val → bit8 z r = bit8 u r then
        (c * (1 / (√2 : ℂ))) *
          omega512 (Φ z + ((2 ^ (8 - m.val) * bit8 z m * (u.val % 2 ^ (m.val + 1)) : ℕ) : ℤ))
      else 0 := by
  rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul]
  exact stageStep8_mulVec_state u m n_k hnk Φ hΦ c

lemma depAbove_whGated {bn : ℕ} (k : Fin 7) (m : Fin 8) (hkm : m.val = k.val)
    (hbm : bn < m.val) (b : Fin 2) (u : Fin 256) {Φ : Fin 256 → ℤ} (hΦ : DepAbove bn Φ) :
    DepAbove bn (fun z ↦ Φ z + (2 ^ k.val : ℤ) * (bit8 u m : ℤ) * whSliceVal8 k b z +
      ((256 * bit8 z m * bit8 u m : ℕ) : ℤ)) := fun w₁ w₂ h ↦ by
  dsimp only
  rw [hΦ w₁ w₂ h, whSliceVal8_congr_gt k b w₁ w₂ (fun r hr ↦ h r (Nat.lt_trans hbm (hkm ▸ hr))),
    h m hbm]

lemma depAbove_stage {bn : ℕ} (m : Fin 8) (hbm : bn < m.val) (u : Fin 256)
    {Ψ : Fin 256 → ℤ} (hΨ : DepAbove bn Ψ) : DepAbove bn
    (fun z ↦ Ψ z + ((2 ^ (8 - m.val) * bit8 z m * (u.val % 2 ^ (m.val + 1)) : ℕ) : ℤ)) :=
  fun w₁ w₂ h ↦ by
    dsimp only
    rw [hΨ w₁ w₂ h, h m hbm]

lemma diag8_mulVec_single (d : Fin 256 → ℤ) (u : Fin 256) :
    (Matrix.diagonal fun w : Fin 256 ↦ omega512 (d w)).mulVec (Pi.single u 1) =
      fun w ↦ if ∀ r : Fin 8, r.val < 8 → bit8 w r = bit8 u r then
        (1 : ℂ) * omega512 (d u) else 0 := by
  funext w
  rw [Matrix.diagonal_mulVec_single]
  by_cases hwu : w = u
  · subst hwu
    simp
  · rw [Pi.single_eq_of_ne hwu,
      ite_neg_8 (fun hall ↦ hwu (fin256_eq_of_bit8_eq fun r ↦ hall r r.isLt))]

lemma omega512_add_period (x q : ℤ) : omega512 (x + 512 * q) = omega512 x := by
  rw [← omega512_emod (x + 512 * q), show x + 512 * q = x + q * 512 by ring,
    Int.add_mul_emod_self_right, omega512_emod]

lemma fin256_mod_step (u : Fin 256) (m : Fin 8) :
    u.val % 2 ^ (m.val + 1) = u.val % 2 ^ m.val + 2 ^ m.val * bit8 u m := by
  unfold bit8
  rw [pow_succ, ← Nat.mod_add_div (u.val % (2 ^ m.val * 2)) (2 ^ m.val),
    Nat.mod_mul_right_mod u.val (2 ^ m.val) 2, Nat.mod_mul_right_div_self u.val (2 ^ m.val) 2]

theorem whEightStage_eq_eightStage (b : Fin 2) : wireHadamard8 0 * whGatedDiag8 0 b *
    (wireHadamard8 1 * whGatedDiag8 1 b) * (wireHadamard8 2 * whGatedDiag8 2 b) *
    (wireHadamard8 3 * whGatedDiag8 3 b) * (wireHadamard8 4 * whGatedDiag8 4 b) *
    (wireHadamard8 5 * whGatedDiag8 5 b) * (wireHadamard8 6 * whGatedDiag8 6 b) *
    (wireHadamard8 7 * whStg7Diag8 b) = wireHadamard8 0 * (stageDiag8 1 * wireHadamard8 1) *
    (stageDiag8 2 * wireHadamard8 2) * (stageDiag8 3 * wireHadamard8 3) *
    (stageDiag8 4 * wireHadamard8 4) * (stageDiag8 5 * wireHadamard8 5) *
    (stageDiag8 6 * wireHadamard8 6) * (stageDiag8 7 * wireHadamard8 7) * preDiag8 b := by
  apply Subtype.ext
  apply @matrix_ext_basisKet 8
  intro βu
  let u := (basisBitsEquiv 8).symm βu
  change _ *ᵥ Pi.single u (1 : ℂ) = _ *ᵥ Pi.single u (1 : ℂ)
  have h0_diag : stageDiag8 0 = 1 := by
    ext i j
    simp only [stageDiag8, OneMemClass.coe_one]
    by_cases hij : i = j
    · subst hij
      simp [stageRowExp512, omega512_zero]
    · simp [hij]
  conv_rhs => rw [show wireHadamard8 0 = stageDiag8 0 * wireHadamard8 0 by rw [h0_diag, one_mul]]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [show (whStg7Diag8 b).1.mulVec (Pi.single u 1) = _ from
      diag8_mulVec_single (fun w ↦ -128 * (b.val : ℤ) * (bit8 w 7 : ℤ)) u,
    show (preDiag8 b).1.mulVec (Pi.single u 1) = _ from
      diag8_mulVec_single (fun w ↦ (b.val : ℤ) * (projPreM9 w : ℤ)) u]
  have hd7 : ∀ bn, bn < 7 →
      DepAbove bn (fun z ↦ -128 * (b.val : ℤ) * (bit8 u 7 : ℤ) +
        ((256 * bit8 z 7 * bit8 u 7 : ℕ) : ℤ)) := fun bn h _ _ hw ↦ by
    dsimp only
    rw [hw 7 h]
  have hd6 := fun bn (h : bn < 6) ↦ depAbove_whGated 6 6 rfl h b u (hd7 bn (by omega))
  have hd5 := fun bn (h : bn < 5) ↦ depAbove_whGated 5 5 rfl h b u (hd6 bn (by omega))
  have hd4 := fun bn (h : bn < 4) ↦ depAbove_whGated 4 4 rfl h b u (hd5 bn (by omega))
  have hd3 := fun bn (h : bn < 3) ↦ depAbove_whGated 3 3 rfl h b u (hd4 bn (by omega))
  have hd2 := fun bn (h : bn < 2) ↦ depAbove_whGated 2 2 rfl h b u (hd3 bn (by omega))
  have hd1 := fun bn (h : bn < 1) ↦ depAbove_whGated 1 1 rfl h b u (hd2 bn (by omega))
  rw [wireHadamard8_mulVec_state u 7 8 rfl _ (fun _ _ _ ↦ rfl),
    whGatedStep8_mulVec_state b u 6 6 rfl (7 : Fin 8).val rfl _ (hd7 6 (by decide)),
    whGatedStep8_mulVec_state b u 5 5 rfl (6 : Fin 8).val rfl _ (hd6 5 (by decide)),
    whGatedStep8_mulVec_state b u 4 4 rfl (5 : Fin 8).val rfl _ (hd5 4 (by decide)),
    whGatedStep8_mulVec_state b u 3 3 rfl (4 : Fin 8).val rfl _ (hd4 3 (by decide)),
    whGatedStep8_mulVec_state b u 2 2 rfl (3 : Fin 8).val rfl _ (hd3 2 (by decide)),
    whGatedStep8_mulVec_state b u 1 1 rfl (2 : Fin 8).val rfl _ (hd2 1 (by decide)),
    whGatedStep8_mulVec_state b u 0 0 rfl (1 : Fin 8).val rfl _ (hd1 0 (by decide))]
  have hs7 := fun bn (h : bn < 7) ↦
    depAbove_stage 7 h u (Ψ := fun _ ↦ (b.val : ℤ) * (projPreM9 u : ℤ)) (fun _ _ _ ↦ rfl)
  have hs6 := fun bn (h : bn < 6) ↦ depAbove_stage 6 h u (hs7 bn (by omega))
  have hs5 := fun bn (h : bn < 5) ↦ depAbove_stage 5 h u (hs6 bn (by omega))
  have hs4 := fun bn (h : bn < 4) ↦ depAbove_stage 4 h u (hs5 bn (by omega))
  have hs3 := fun bn (h : bn < 3) ↦ depAbove_stage 3 h u (hs4 bn (by omega))
  have hs2 := fun bn (h : bn < 2) ↦ depAbove_stage 2 h u (hs3 bn (by omega))
  have hs1 := fun bn (h : bn < 1) ↦ depAbove_stage 1 h u (hs2 bn (by omega))
  rw [stageStep8_mulVec_ungrouped u 7 8 rfl _ (fun _ _ _ ↦ rfl),
    stageStep8_mulVec_ungrouped u 6 (7 : Fin 8).val rfl _ (hs7 6 (by decide)),
    stageStep8_mulVec_ungrouped u 5 (6 : Fin 8).val rfl _ (hs6 5 (by decide)),
    stageStep8_mulVec_ungrouped u 4 (5 : Fin 8).val rfl _ (hs5 4 (by decide)),
    stageStep8_mulVec_ungrouped u 3 (4 : Fin 8).val rfl _ (hs4 3 (by decide)),
    stageStep8_mulVec_ungrouped u 2 (3 : Fin 8).val rfl _ (hs3 2 (by decide)),
    stageStep8_mulVec_ungrouped u 1 (2 : Fin 8).val rfl _ (hs2 1 (by decide)),
    stageStep8_mulVec_ungrouped u 0 (1 : Fin 8).val rfl _ (hs1 0 (by decide))]
  funext z
  simp only [Fin.val_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, ↓reduceIte]
  congr 1
  have hmod1 : u.val % 2 ^ 1 = bit8 u 0 := by simpa [Nat.mod_one] using fin256_mod_step u 0
  have hmod2 : u.val % 2 ^ 2 = _ := (fin256_mod_step u 1).trans (congrArg (· + 2 * bit8 u 1) hmod1)
  have hmod3 : u.val % 2 ^ 3 = _ := (fin256_mod_step u 2).trans (congrArg (· + 4 * bit8 u 2) hmod2)
  have hmod4 : u.val % 2 ^ 4 = _ := (fin256_mod_step u 3).trans (congrArg (· + 8 * bit8 u 3) hmod3)
  have hmod5 : u.val % 2 ^ 5 = _ :=
    (fin256_mod_step u 4).trans (congrArg (· + 16 * bit8 u 4) hmod4)
  have hmod6 : u.val % 2 ^ 6 = _ :=
    (fin256_mod_step u 5).trans (congrArg (· + 32 * bit8 u 5) hmod5)
  have hmod7 : u.val % 2 ^ 7 = _ :=
    (fin256_mod_step u 6).trans (congrArg (· + 64 * bit8 u 6) hmod6)
  have hmod8 : u.val % 2 ^ 8 = _ :=
    (fin256_mod_step u 7).trans (congrArg (· + 128 * bit8 u 7) hmod7)
  change omega512 _ = omega512 _
  rw [← omega512_add_period _ ((b.val : ℤ) * (bit8 u 7 : ℤ))]
  congr 1
  simp only [whSliceVal8, projPreM9,
    show (0 : Fin 7).val = 0 from rfl, show (1 : Fin 7).val = 1 from rfl,
    show (2 : Fin 7).val = 2 from rfl, show (3 : Fin 7).val = 3 from rfl,
    show (4 : Fin 7).val = 4 from rfl, show (5 : Fin 7).val = 5 from rfl,
    show (6 : Fin 7).val = 6 from rfl, show (1 : Fin 8).val = 1 from rfl,
    show (2 : Fin 8).val = 2 from rfl, show (3 : Fin 8).val = 3 from rfl,
    show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl]
  rw [hmod1, hmod2, hmod3, hmod4, hmod5, hmod6, hmod7, hmod8,
    (Nat.mod_eq_of_lt u.isLt).symm.trans hmod8]
  push_cast
  ring
def cWhRemAxisTop {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) : Circuit n :=
  cApexSign isInv (rCosetB0 hm rCore w) ;;ᶜ
    cApexSign isInv (rProjAxis rCore w 1) ;;ᶜ
    cSSign isInv (rProjAxis rCore w 2) ;;ᶜ
    cSSign isInv (rProjAxis rCore w 3) ;;ᶜ
    cSSign isInv (rProjAxis rCore w 4) ;;ᶜ
    cSSign isInv (rProjAxis rCore w 5) ;;ᶜ
    cSSign isInv (rProjAxis rCore w 6) ;;ᶜ
    cSSign isInv (rProjAxis rCore w 7)
@[scoped simp] lemma count_cWhRemAxisTop_toff {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    (cWhRemAxisTop isInv hm rCore w).count .TOFF = 0 := isInv.casesOn rfl rfl
@[scoped simp] lemma count_cWhRemAxisTop_t {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    (cWhRemAxisTop isInv hm rCore w).count .T = 2 := isInv.casesOn rfl rfl
def cWhRemTop {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) : Circuit n :=
  cWhRemAxisTop isInv hm rCore 0 ;;ᶜ
    cWhRemAxisTop isInv hm rCore 1 ;;ᶜ
    cWhRemAxisTop isInv hm rCore 2
@[scoped simp] lemma count_cWhRemTop_toff {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cWhRemTop isInv hm rCore).count .TOFF = 0 := isInv.casesOn rfl rfl
@[scoped simp] lemma count_cWhRemTop_t {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cWhRemTop isInv hm rCore).count .T = 6 := isInv.casesOn rfl rfl
lemma cWhRemTop_evolve {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (ξ : BitAssignment n) :
    (cWhRemTop isInv hm rCore).eval.1.mulVec (basisKet ξ) = DyadicQft64.dyadicTurn 48
    (whRemTopExp hm isInv (fun q ↦ ξ (rCore q))) • basisKet ξ := by
  unfold cWhRemTop cWhRemAxisTop
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, cApexSign_evolve,
    cSSign_evolve, Matrix.mulVec_smul, smul_smul,
    (JunctionApexCSA288.dyadicTurn_scale_pow 45 3 _).symm,
    DyadicQft64.dyadicTurn_add]
  refine congrArg (fun x ↦ DyadicQft64.dyadicTurn 48 x • basisKet ξ) ?_
  unfold whRemTopExp
  dsimp only
  rw [Fin.sum_univ_three]
  simp only [show ∀ w : Fin 3, (fun q ↦ ξ (rCore q)) (rCosetB0 hm (QRegExt.idReg _) w) =
      ξ (rCosetB0 hm rCore w) from fun _ ↦ rfl,
    show ∀ (w : Fin 3) (k : Fin 8), (fun q ↦ ξ (rCore q))
      (rProjAxis (QRegExt.idReg _) w k) = ξ (rProjAxis rCore w k) from fun _ _ ↦ rfl]
  ring
end Proj3DCut.WhHelper
namespace Proj3DCut
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64Engine
open NuclearTwistAndXor654Concrete
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding
  basisBits_symm_apply fullSysCoreWires_eq_add
open FusedVepCore288 JunctionApexCSA288
open InterWalkRSum42Hoist
open Proj3DCut.WhHelper
theorem basisKet_eq_single {m : ℕ} (β : BitAssignment m) :
    basisKet β = Pi.single ((basisBitsEquiv m).symm β) (1 : ℂ) := rfl
theorem mulVec_basisKet_apply {m : ℕ} (M : Operator (2 ^ m)) (β : BitAssignment m)
    (i : Fin (2 ^ m)) : (M.mulVec (basisKet β)) i = M i ((basisBitsEquiv m).symm β) := by
  rw [basisKet_eq_single, Matrix.mulVec_single_one, Matrix.col_apply]
theorem wSlot0_val_eq {mPayload : ℕ} :
    (wSlot0 (QRegExt.idReg (fullSysCoreWires mPayload))).val = 3948 := by
  simp [wSlot0, QRegExt.idReg]
theorem wSlot1_val_eq {mPayload : ℕ} :
    (wSlot1 (QRegExt.idReg (fullSysCoreWires mPayload))).val = 3949 := by
  simp [wSlot1, QRegExt.idReg]
theorem wSlot2_val_eq {mPayload : ℕ} :
    (wSlot2 (QRegExt.idReg (fullSysCoreWires mPayload))).val = 3950 := by
  simp [wSlot2, QRegExt.idReg]
theorem rNucIdx_val_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (j : Fin 8) :
    (rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) j).val = 3960 + j.val := by
  simp [rNucIdx, QRegister.slice, QRegister.compose, QRegExt.idReg]
def posBranchActive {mPayload : ℕ} (γ : BitAssignment (fullSysCoreWires mPayload)) : Bool :=
    decide (γ (wSlot2 (QRegExt.idReg _)) = 0)
def setHighNucBits {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let rN := rNucIdx hm rId
  Function.update (Function.update (Function.update
    (Function.update (Function.update γ (wSlot0 rId) 0) (wSlot1 rId) 0)
    (rN 5) 1) (rN 6) 1) (rN 7) 1
theorem setHighNucBits_apply_of_ne {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) {q : Wire (fullSysCoreWires mPayload)}
    (hs0 : q ≠ wSlot0 (QRegExt.idReg _)) (hs1 : q ≠ wSlot1 (QRegExt.idReg _))
    (h5 : q ≠ rNucIdx hm (QRegExt.idReg _) 5) (h6 : q ≠ rNucIdx hm (QRegExt.idReg _) 6)
    (h7 : q ≠ rNucIdx hm (QRegExt.idReg _) 7) : setHighNucBits hm γ q = γ q := by
  unfold setHighNucBits
  rw [Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
      Function.update_of_ne hs1, Function.update_of_ne hs0]
theorem setHighNucBits_apply_of_val_ne {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) {q : Wire (fullSysCoreWires mPayload)}
    (h : q.val ≠ 3948 ∧ q.val ≠ 3949 ∧ q.val < 3960) : setHighNucBits hm γ q = γ q :=
  setHighNucBits_apply_of_ne hm γ
    (fun e ↦ h.1 ((congrArg Fin.val e).trans wSlot0_val_eq))
    (fun e ↦ h.2.1 ((congrArg Fin.val e).trans wSlot1_val_eq))
    (fun e ↦ absurd ((congrArg Fin.val e).trans (rNucIdx_val_eq hm 5)) (by omega))
    (fun e ↦ absurd ((congrArg Fin.val e).trans (rNucIdx_val_eq hm 6)) (by omega))
    (fun e ↦ absurd ((congrArg Fin.val e).trans (rNucIdx_val_eq hm 7)) (by omega))
theorem vepHighNuc_update567 {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    let rN := rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload))
    vepHighNuc hm
      (Function.update (Function.update (Function.update γ (rN 5) 1) (rN 6) 1) (rN 7) 1) =
      coin0Active γ := by
  intro rN
  let γ' := Function.update (Function.update (Function.update γ (rN 5) 1) (rN 6) 1) (rN 7) 1
  have hne : ∀ {i j : Fin 8}, i.val ≠ j.val → rN i ≠ rN j := fun hij h ↦
    hij (Nat.add_left_cancel
      ((rNucIdx_val_eq hm _).symm.trans ((congrArg Fin.val h).trans (rNucIdx_val_eq hm _))))
  have hlow {w : Wire (fullSysCoreWires mPayload)} (hw : w.val < 3960) : γ' w = γ w := by
    have hlt (j : Fin 8) : w ≠ rN j :=
      fun h ↦ absurd ((congrArg Fin.val h).trans (rNucIdx_val_eq hm j)) (by omega)
    simp only [γ', Function.update_of_ne (hlt 7), Function.update_of_ne (hlt 6),
      Function.update_of_ne (hlt 5)]
  unfold vepHighNuc
  change (coin0Active γ' && (decide (γ' (rN 7) = 1) &&
    (decide (γ' (rN 5) = 1) || (decide (γ' (rN 4) = 1) && decide (γ' (rN 3) = 1)))) &&
    decide (γ' (rN 6) = 1)) = coin0Active γ
  rw [show coin0Active γ' = coin0Active γ by
      unfold coin0Active
      rw [hlow (by simp [wSlot2, QRegExt.idReg]), hlow (by simp [wSlot1, QRegExt.idReg]),
        hlow (by simp [wSlot0, QRegExt.idReg])],
    show γ' (rN 5) = 1 by
      dsimp only [γ']
      rw [Function.update_of_ne (hne (by decide)), Function.update_of_ne (hne (by decide)),
        Function.update_self],
    show γ' (rN 6) = 1 by
      dsimp only [γ']
      rw [Function.update_of_ne (hne (by decide)), Function.update_self],
    show γ' (rN 7) = 1 from Function.update_self (rN 7) 1 _]
  cases coin0Active γ
  all_goals rfl
theorem vepHighNuc_setHighNucBits {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    vepHighNuc hm (setHighNucBits hm γ) = posBranchActive γ := by
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let γ₀ := Function.update (Function.update γ (wSlot0 rId) 0) (wSlot1 rId) 0
  rw [show vepHighNuc hm (setHighNucBits hm γ) = coin0Active γ₀ from vepHighNuc_update567 hm γ₀]
  unfold coin0Active posBranchActive
  have h0 : γ₀ (wSlot0 rId) = 0 := (Function.update_of_ne (fun h ↦ absurd
    (wSlot0_val_eq.symm.trans ((congrArg Fin.val h).trans wSlot1_val_eq)) (by decide)) _ _).trans
    (Function.update_self _ _ _)
  have h1 : γ₀ (wSlot1 rId) = 0 := Function.update_self _ 0 _
  have h2 : γ₀ (wSlot2 rId) = γ (wSlot2 rId) := (Function.update_of_ne (fun h ↦ absurd
    (wSlot2_val_eq.symm.trans ((congrArg Fin.val h).trans wSlot1_val_eq)) (by decide)) _ _).trans
    (Function.update_of_ne (fun h ↦ absurd
      (wSlot2_val_eq.symm.trans ((congrArg Fin.val h).trans wSlot0_val_eq)) (by decide)) _ _)
  dsimp only [rId] at h0 h1 h2 ⊢
  simp [h0, h1, h2]
theorem wireHadamard8_inv (m : Fin 8) : (wireHadamard8 m)⁻¹ = wireHadamard8 m := by
  change ((Circuit.H m : Circuit 8).eval)⁻¹ = (Circuit.H m : Circuit 8).eval
  rw [← Circuit.eval_inverse]
  rfl
noncomputable def uTailLocal8 : Unitary 256 := bitRev8Unitary * wireHadamard8 0
noncomputable def uTail3DCore {mPayload : ℕ} : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (rProjAxis rId 0).embedUnitary uTailLocal8 *
    ((rProjAxis rId 1).embedUnitary uTailLocal8 *
      (rProjAxis rId 2).embedUnitary uTailLocal8)
noncomputable def uCoin0Stage1DMat {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 : Fin 2 → Operator 256) (F_other : Operator 256) : Operator
    (2 ^ (fullSysCoreWires mPayload)) := Matrix.of fun i j ↦ if posBranchActive
    (basisBits _ i) then ((rProjAxis (QRegExt.idReg _) w).embedMatrix (F_c0 (extractCosetP3
    hm (basisBits _ i) w))) i j else ((rProjAxis (QRegExt.idReg _) w).embedMatrix F_other) i
    j
theorem rProjAxis_wire_lt_3948 {mPayload : ℕ} (w : Fin 3) (m : Fin 8) :
    (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w m).val < 3948 := by
  simp [rProjAxis, QRegister.slice, QRegister.compose, QRegExt.idReg]
  omega
def ActHigh3948 {mPayload : ℕ}
    (act : BitAssignment (fullSysCoreWires mPayload) → Bool) : Prop :=
  ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload),
    (∀ q : Wire (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) → act γ₁ = act γ₂

lemma actHigh3948_posBranch {mPayload : ℕ} :
    ActHigh3948 (posBranchActive (mPayload := mPayload)) := fun _ _ h ↦ by
  unfold posBranchActive
  rw [h _ (by simp [wSlot2, QRegExt.idReg])]

lemma actHigh3948_coin0 {mPayload : ℕ} :
    ActHigh3948 (coin0Active (mPayload := mPayload)) := fun _ _ h ↦ by
  unfold coin0Active
  rw [h _ (by simp [wSlot2, QRegExt.idReg]),
    h _ (by simp [wSlot1, QRegExt.idReg]),
    h _ (by simp [wSlot0, QRegExt.idReg])]

noncomputable abbrev uActStage1DMat {mPayload : ℕ}
    (act : BitAssignment (fullSysCoreWires mPayload) → Bool)
    (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 : Fin 2 → Operator 256) (F_other : Operator 256) :
    Operator (2 ^ (fullSysCoreWires mPayload)) :=
  Matrix.of fun i j ↦
    if act (basisBits _ i) then
      ((rProjAxis (QRegExt.idReg _) w).embedMatrix
        (F_c0 (extractCosetP3 hm (basisBits _ i) w))) i j
    else ((rProjAxis (QRegExt.idReg _) w).embedMatrix F_other) i j

theorem act_and_coset_eq_of_embed_rProjAxis_ne_zero {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (w : Fin 3) (A : Operator 256)
    {i j : Fin (2 ^ (fullSysCoreWires mPayload))}
    (hne : ((rProjAxis (QRegExt.idReg _) w).embedMatrix A) i j ≠ 0) :
    act (basisBits _ i) = act (basisBits _ j) ∧
      extractCosetP3 hm (basisBits _ i) = extractCosetP3 hm (basisBits _ j) := by
  have hOut : ∀ q : Wire (fullSysCoreWires mPayload), 3948 ≤ q.val →
      basisBits _ i q = basisBits _ j q := fun q hq ↦ by
    have hnot : q ∉ Set.range (rProjAxis (QRegExt.idReg _) w).wires := by
      rintro ⟨m, rfl⟩
      have := rProjAxis_wire_lt_3948 (mPayload := mPayload) w m
      omega
    by_contra hdiff
    apply hne
    rw [QRegister.embedMatrix_apply_of_agreeOutside]
    have hna : ¬ (rProjAxis (QRegExt.idReg _) w).AgreeOutside i j := fun ha ↦ hdiff (ha q hnot)
    simp only [hna, ↓reduceIte, mul_zero]
  refine ⟨hAct _ _ hOut, funext fun u ↦ ?_⟩
  unfold extractCosetP3 rProjCosetP3
  exact hOut _ (by
    have := u.isLt
    simp [rCosetB0, QRegister.slice, QRegister.compose, QRegExt.idReg]
    omega)

theorem coin0_and_coset_eq_of_embed_rProjAxis_ne_zero {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (w : Fin 3) (A : Operator 256) {i j : Fin (2 ^ (fullSysCoreWires mPayload))}
    (hne : ((rProjAxis (QRegExt.idReg _) w).embedMatrix A) i j ≠ 0) :
    posBranchActive (basisBits _ i) = posBranchActive (basisBits _ j) ∧
      extractCosetP3 hm (basisBits _ i) = extractCosetP3 hm (basisBits _ j) :=
  act_and_coset_eq_of_embed_rProjAxis_ne_zero actHigh3948_posBranch hm w A hne

lemma uActStage1DMat_entry {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 : Fin 2 → Operator 256) (F_other : Operator 256)
    (i j : Fin (2 ^ (fullSysCoreWires mPayload))) :
    uActStage1DMat act hm w F_c0 F_other i j =
      if act (basisBits _ j) then
        ((rProjAxis (QRegExt.idReg _) w).embedMatrix
          (F_c0 (extractCosetP3 hm (basisBits _ j) w))) i j
      else ((rProjAxis (QRegExt.idReg _) w).embedMatrix F_other) i j := by
  simp only [uActStage1DMat, Matrix.of_apply]
  by_cases hL : (if act (basisBits _ i) then
      ((rProjAxis (QRegExt.idReg _) w).embedMatrix
        (F_c0 (extractCosetP3 hm (basisBits _ i) w))) i j
    else ((rProjAxis (QRegExt.idReg _) w).embedMatrix F_other) i j) = 0
  · rw [hL]
    symm
    by_contra hR
    split_ifs at hR with hj
    all_goals
      obtain ⟨hc, he⟩ := act_and_coset_eq_of_embed_rProjAxis_ne_zero hAct hm w _ hR
      simp only [hc, hj, Bool.false_eq_true, ↓reduceIte, he] at hL
      exact hR hL
  · split_ifs at hL with hi
    all_goals
      obtain ⟨hc, he⟩ := act_and_coset_eq_of_embed_rProjAxis_ne_zero hAct hm w _ hL
      simp only [← hc, hi, Bool.false_eq_true, ↓reduceIte, ← he]

lemma uActStage1DMat_mul_term {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (wa wb : Fin 3)
    (F_c0 G_c0 : Fin 2 → Operator 256) (F_other G_other : Operator 256)
    (i k j : Fin (2 ^ (fullSysCoreWires mPayload))) :
    uActStage1DMat act hm wa F_c0 F_other i k *
      uActStage1DMat act hm wb G_c0 G_other k j =
      if act (basisBits _ i) then
        ((rProjAxis (QRegExt.idReg _) wa).embedMatrix
          (F_c0 (extractCosetP3 hm (basisBits _ i) wa))) i k *
        ((rProjAxis (QRegExt.idReg _) wb).embedMatrix
          (G_c0 (extractCosetP3 hm (basisBits _ i) wb))) k j
      else ((rProjAxis (QRegExt.idReg _) wa).embedMatrix F_other) i k *
        ((rProjAxis (QRegExt.idReg _) wb).embedMatrix G_other) k j := by
  simp only [uActStage1DMat, Matrix.of_apply]
  by_cases hi : act (basisBits _ i)
  · simp only [hi, ↓reduceIte]
    by_cases h0 : ((rProjAxis (QRegExt.idReg _) wa).embedMatrix
        (F_c0 (extractCosetP3 hm (basisBits _ i) wa))) i k = 0
    · rw [h0, zero_mul, zero_mul]
    · obtain ⟨hc, he⟩ := act_and_coset_eq_of_embed_rProjAxis_ne_zero hAct hm wa _ h0
      simp only [← hc, hi, ↓reduceIte, ← he]
  · simp only [hi, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : ((rProjAxis (QRegExt.idReg _) wa).embedMatrix F_other) i k = 0
    · rw [h0, zero_mul, zero_mul]
    · obtain ⟨hc, _⟩ := act_and_coset_eq_of_embed_rProjAxis_ne_zero hAct hm wa _ h0
      simp only [← hc, hi, Bool.false_eq_true, ↓reduceIte]

theorem uActStage1DMat_mul {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 G_c0 : Fin 2 → Operator 256) (F_other G_other : Operator 256) :
    uActStage1DMat act hm w F_c0 F_other * uActStage1DMat act hm w G_c0 G_other =
      uActStage1DMat act hm w (fun b ↦ F_c0 b * G_c0 b) (F_other * G_other) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ ↦
    uActStage1DMat_mul_term hAct hm w w F_c0 G_c0 F_other G_other i k j]
  simp only [uActStage1DMat, Matrix.of_apply]
  split_ifs
  all_goals rw [← Matrix.mul_apply, ← QRegister.embedMatrix_mul]
theorem uActStage1DMat_one {mPayload : ℕ}
    (act : BitAssignment (fullSysCoreWires mPayload) → Bool) (hm : 22 ≤ mPayload) (w : Fin 3) :
    uActStage1DMat act hm w (fun _ ↦ 1) 1 = 1 := by
  ext i j
  simp only [uActStage1DMat, Matrix.of_apply, QRegister.embedMatrix_one, ite_self]

theorem uCoin0Stage1DMat_one {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    uCoin0Stage1DMat hm w (fun _ ↦ 1) 1 = 1 :=
  uActStage1DMat_one posBranchActive hm w

theorem uActStage1DMat_mem_unitary {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (w : Fin 3) (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) :
    uActStage1DMat act hm w (fun b ↦ (F_c0 b).1) F_other.1 ∈
      Matrix.unitaryGroup (Fin (2 ^ (fullSysCoreWires mPayload))) ℂ := by
  have hCT : (uActStage1DMat act hm w (fun b ↦ (F_c0 b).1) F_other.1)ᴴ =
      uActStage1DMat act hm w (fun b ↦ ((F_c0 b).1)ᴴ) ((F_other.1)ᴴ) := by
    ext i j
    rw [Matrix.conjTranspose_apply, uActStage1DMat_entry hAct hm w _ _ j i]
    simp only [uActStage1DMat, Matrix.of_apply]
    split_ifs
    all_goals rw [← Matrix.conjTranspose_apply, ← QRegister.embedMatrix_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hCT, uActStage1DMat_mul hAct,
    show (fun b : Fin 2 ↦ (F_c0 b).1 * ((F_c0 b).1)ᴴ) = fun _ ↦ 1 from funext fun b ↦ by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (F_c0 b).2,
    show F_other.1 * (F_other.1)ᴴ = 1 by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp F_other.2,
    uActStage1DMat_one]

noncomputable abbrev uActStage1DCore {mPayload : ℕ}
    (act : BitAssignment (fullSysCoreWires mPayload) → Bool) (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (w : Fin 3) (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  ⟨uActStage1DMat act hm w (fun b ↦ (F_c0 b).1) F_other.1,
    uActStage1DMat_mem_unitary hAct hm w F_c0 F_other⟩

noncomputable abbrev uActStage3D {mPayload : ℕ}
    (act : BitAssignment (fullSysCoreWires mPayload) → Bool) (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uActStage1DCore act hAct hm 0 F_c0 F_other *
    (uActStage1DCore act hAct hm 1 F_c0 F_other * uActStage1DCore act hAct hm 2 F_c0 F_other)

noncomputable def uCoin0Stage1DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  ⟨uCoin0Stage1DMat hm w (fun b ↦ (F_c0 b).1) F_other.1,
    uActStage1DMat_mem_unitary actHigh3948_posBranch hm w F_c0 F_other⟩

noncomputable def uCoin0Stage3D {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := uCoin0Stage1DCore hm 0 F_c0 F_other *
    (uCoin0Stage1DCore hm 1 F_c0 F_other * uCoin0Stage1DCore hm 2 F_c0 F_other)

noncomputable def uProj3DCut1DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := uCoin0Stage1DCore hm w uProjPlus512_1D uTailLocal8

noncomputable def uProj3DCutCore {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uProj3DCut1DCore hm 0 * (uProj3DCut1DCore hm 1 * uProj3DCut1DCore hm 2)

theorem uActStage1DCore_comm_axes {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂)
    (F_c0 G_c0 : Fin 2 → Unitary 256) (F_other G_other : Unitary 256) :
    uActStage1DCore act hAct hm w₁ F_c0 F_other * uActStage1DCore act hAct hm w₂ G_c0 G_other =
      uActStage1DCore act hAct hm w₂ G_c0 G_other *
        uActStage1DCore act hAct hm w₁ F_c0 F_other := by
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  have hDisj : (rProjAxis rId w₁).DisjointWires (rProjAxis rId w₂) :=
    rProjAxis_disjoint_of_ne rId hne
  apply Subtype.ext
  ext i j
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_apply, Matrix.mul_apply]
  change (∑ k, uActStage1DMat act hm w₁ (fun b ↦ (F_c0 b).1) F_other.1 i k *
      uActStage1DMat act hm w₂ (fun b ↦ (G_c0 b).1) G_other.1 k j) =
    ∑ k, uActStage1DMat act hm w₂ (fun b ↦ (G_c0 b).1) G_other.1 i k *
      uActStage1DMat act hm w₁ (fun b ↦ (F_c0 b).1) F_other.1 k j
  rw [Finset.sum_congr rfl fun k _ ↦
      uActStage1DMat_mul_term hAct hm w₁ w₂ _ _ F_other.1 G_other.1 i k j,
    Finset.sum_congr rfl fun k _ ↦
      uActStage1DMat_mul_term hAct hm w₂ w₁ _ _ G_other.1 F_other.1 i k j]
  split_ifs
  all_goals
    rw [← Matrix.mul_apply, ← Matrix.mul_apply,
      QRegister.embedMatrix_comm_of_disjoint (rProjAxis rId w₁) (rProjAxis rId w₂) hDisj]
theorem uActStage3D_mul {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (F_c0 G_c0 : Fin 2 → Unitary 256) (F_other G_other : Unitary 256) :
    uActStage3D act hAct hm F_c0 F_other * uActStage3D act hAct hm G_c0 G_other =
      uActStage3D act hAct hm (fun b ↦ F_c0 b * G_c0 b) (F_other * G_other) := by
  let U (w : Fin 3) := uActStage1DCore act hAct hm w F_c0 F_other
  let V (w : Fin 3) := uActStage1DCore act hAct hm w G_c0 G_other
  have hc {i j : Fin 3} (h : i ≠ j) : U i * V j = V j * U i :=
    uActStage1DCore_comm_axes hAct hm h F_c0 G_c0 F_other G_other
  have hm_ax (w : Fin 3) :
      U w * V w = uActStage1DCore act hAct hm w (fun b ↦ F_c0 b * G_c0 b) (F_other * G_other) :=
    Subtype.ext (by simpa only [Submonoid.coe_mul, U, V, uActStage1DCore] using
      uActStage1DMat_mul hAct hm w (fun b ↦ (F_c0 b).1) (fun b ↦ (G_c0 b).1) F_other.1 G_other.1)
  calc U 0 * (U 1 * U 2) * (V 0 * (V 1 * V 2))
      = U 0 * (U 1 * (U 2 * V 0) * (V 1 * V 2)) := by simp only [mul_assoc]
    _ = U 0 * ((U 1 * V 0) * (U 2 * V 1) * V 2) := by
        rw [hc (by decide)]
        simp only [mul_assoc]
    _ = (U 0 * V 0) * ((U 1 * V 1) * (U 2 * V 2)) := by
        rw [hc (by decide), hc (by decide)]
        simp only [mul_assoc]
    _ = uActStage3D act hAct hm (fun b ↦ F_c0 b * G_c0 b) (F_other * G_other) := by
        rw [hm_ax 0, hm_ax 1, hm_ax 2]
theorem uCoin0Stage3D_mul {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (F_c0 G_c0 : Fin 2 → Unitary 256) (F_other G_other : Unitary 256) :
    uCoin0Stage3D hm F_c0 F_other * uCoin0Stage3D hm G_c0 G_other =
      uCoin0Stage3D hm (fun b ↦ F_c0 b * G_c0 b) (F_other * G_other) :=
  uActStage3D_mul actHigh3948_posBranch hm F_c0 G_c0 F_other G_other
theorem uTail3DCore_eq_uActStage3D {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) :
    (uTail3DCore (mPayload := mPayload)) =
      uActStage3D act hAct hm (fun _ ↦ uTailLocal8) uTailLocal8 := by
  have h1 (w : Fin 3) :
      (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w).embedUnitary uTailLocal8 =
        uActStage1DCore act hAct hm w (fun _ ↦ uTailLocal8) uTailLocal8 :=
    Subtype.ext (Matrix.ext fun _ _ ↦ by simp [uActStage1DMat])
  exact congrArg₂ (· * ·) (h1 0) (congrArg₂ (· * ·) (h1 1) (h1 2))
theorem uTail3DCore_eq_uCoin0Stage3D {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (uTail3DCore (mPayload := mPayload)) = uCoin0Stage3D hm (fun _ ↦ uTailLocal8) uTailLocal8 :=
  uTail3DCore_eq_uActStage3D actHigh3948_posBranch hm
theorem fixesLow3924_uCoin0Stage1DCore (hm : 22 ≤ 80) (w : Fin 3)
    (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) :
    FixesLow3924 h3924_core (uCoin0Stage1DCore hm w F_c0 F_other).1 := by
  intro i j hne
  simp only [uCoin0Stage1DCore, uCoin0Stage1DMat, Matrix.of_apply] at hne
  have hHigh (m : Fin 8) :
      3924 ≤ (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w m).val := by
    simp [rProjAxis, QRegister.slice, QRegister.compose, QRegExt.idReg]
    omega
  split_ifs at hne
  all_goals exact fixesLow3924_embedMatrix_high h3924_core hHigh _ i j hne
theorem uActStage1DCore_mulVec_basisKet {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uActStage1DCore act hAct hm w F_c0 F_other).1.mulVec (basisKet γ) =
      if act γ then
        ((rProjAxis (QRegExt.idReg _) w).embedUnitary (F_c0 (extractCosetP3 hm γ w))).1.mulVec
          (basisKet γ)
      else ((rProjAxis (QRegExt.idReg _) w).embedUnitary F_other).1.mulVec (basisKet γ) := by
  ext i
  rw [mulVec_basisKet_apply]
  change uActStage1DMat act hm w (fun b ↦ (F_c0 b).1) F_other.1 i ((basisBitsEquiv _).symm γ) = _
  rw [uActStage1DMat_entry hAct hm w (fun b ↦ (F_c0 b).1) F_other.1 i,
    basisBits_basisBitsEquiv_symm_eq]
  cases act γ
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, mulVec_basisKet_apply, QRegister.embedUnitary_val]

theorem intertwinesLocalCat_unique_core {kAct mCat : ℕ} (U_cat : Unitary (2 ^ mCat))
    (W_cat : Unitary (2 ^ (kAct + mCat))) {A B : Unitary (2 ^ kAct)} (hA :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat W_cat A) (hB :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat W_cat B) : A = B := by
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (by omega)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  let E_cat := rCat0.embedUnitary U_cat
  let P0 := rCat0.basisOutcomeProjector 0
  have hEinv : E_cat.1ᴴ * E_cat.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp E_cat.2
  have hEq0 : E_cat.1 * (rAct0.embedUnitary A).1 * P0 =
      E_cat.1 * (rAct0.embedUnitary B).1 * P0 := hA.1.symm.trans hB.1
  have hP0Eq : (rAct0.embedUnitary A).1 * P0 = (rAct0.embedUnitary B).1 * P0 := by
    simpa only [← Matrix.mul_assoc, hEinv, Matrix.one_mul] using congrArg (E_cat.1ᴴ * ·) hEq0
  refine Subtype.ext (matrix_ext_basisKet fun γ ↦ ?_)
  let mkPad (δ : BitAssignment kAct) : BitAssignment (kAct + mCat) :=
    fun q ↦ if hq : q.val < kAct then δ ⟨q.val, hq⟩ else 0
  have hproj : P0.mulVec (basisKet (mkPad γ)) = basisKet (mkPad γ) := by
    have hex : rCat0.extractIndex ((basisBitsEquiv (kAct + mCat)).symm (mkPad γ)) = 0 := by
      apply (basisBitsEquiv mCat).injective
      funext j
      change basisBits mCat (rCat0.extractIndex _) j = basisBits mCat 0 j
      rw [QRegister.basisBits_extractIndex, basisBits_basisBitsEquiv_symm_eq]
      dsimp only [mkPad, rCat0, QRegister.block]
      have hlt : ¬ (kAct + j.val < kAct) := by omega
      simp [-Nat.reducePow, hlt, basisBits_zero_at]
    simp only [P0, basisKet_eq_single, QRegister.basisOutcomeProjector_mulVec_single, hex,
      ↓reduceIte]
  ext i
  have hMulEq := congrArg (fun M ↦ (M.mulVec (basisKet (mkPad γ)))
    ((basisBitsEquiv _).symm (mkPad (basisBits kAct i)))) hP0Eq
  simp only [← Matrix.mulVec_mulVec, hproj] at hMulEq
  have hEx : ∀ δ : BitAssignment kAct,
      rAct0.extractIndex ((basisBitsEquiv _).symm (mkPad δ)) = (basisBitsEquiv kAct).symm δ :=
    fun δ ↦ (basisBitsEquiv kAct).injective (funext fun j ↦ by
      rw [Equiv.apply_symm_apply]
      change basisBits kAct (rAct0.extractIndex _) j = δ j
      rw [QRegister.basisBits_extractIndex, basisBits_basisBitsEquiv_symm_eq]
      simp [mkPad, rAct0, QRegister.block, j.isLt])
  have hSide (M : Unitary (2 ^ kAct)) : ((rAct0.embedUnitary M).1.mulVec (basisKet (mkPad γ)))
      ((basisBitsEquiv _).symm (mkPad (basisBits kAct i))) =
      (M.1.mulVec (basisKet γ)) i := by
    rw [mulVec_basisKet_apply, mulVec_basisKet_apply, QRegister.embedUnitary_val,
      QRegister.embedMatrix_apply_of_agreeOutside]
    have hag : rAct0.AgreeOutside ((basisBitsEquiv _).symm (mkPad (basisBits kAct i)))
        ((basisBitsEquiv _).symm (mkPad γ)) := fun q hq ↦ by
      rw [basisBits_basisBitsEquiv_symm_eq, basisBits_basisBitsEquiv_symm_eq]
      simp [mkPad, show ¬ (q.val < kAct) from
        fun hlt ↦ hq ⟨⟨q.val, hlt⟩, Fin.ext (by simp [rAct0, QRegister.block])⟩]
    simp only [hag, ↓reduceIte, mul_one, hEx,
      show (basisBitsEquiv kAct).symm (basisBits kAct i) = i from
        (basisBitsEquiv kAct).symm_apply_apply i]
  exact (hSide A).symm.trans (hMulEq.trans (hSide B))

theorem setHighNucBits_agrees_on_proj_and_coset {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : extractCosetP3 hm (setHighNucBits hm γ)
    = extractCosetP3 hm γ ∧ ∀ (w : Fin 3) (m : Fin 8), setHighNucBits hm γ
    (rProjAxis (QRegExt.idReg _) w m) = γ (rProjAxis (QRegExt.idReg _) w m) := by
  refine ⟨funext fun u ↦ ?_, fun w m ↦ setHighNucBits_apply_of_val_ne hm γ ?_⟩
  · unfold extractCosetP3 rProjCosetP3
    refine setHighNucBits_apply_of_val_ne hm γ ?_
    simp [rCosetB0, QRegister.slice, QRegister.compose, QRegExt.idReg]
    omega
  · have := rProjAxis_wire_lt_3948 (mPayload := mPayload) w m
    omega
theorem uActStage1DCore_diag {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (w : Fin 3)
    (F : Fin 2 → Unitary 256) (d : Fin 2 → Fin 256 → ℂ)
    (hd : ∀ b, (F b).1 = Matrix.diagonal (d b))
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uActStage1DCore act hAct hm w F 1).1.mulVec (basisKet γ) =
      (if act γ then d (extractCosetP3 hm γ w)
        ((basisBitsEquiv 8).symm (fun m ↦ γ (rProjAxis (QRegExt.idReg _) w m))) else 1) •
      basisKet γ := by
  rw [uActStage1DCore_mulVec_basisKet]
  split_ifs
  · exact embedUnitary_diagonal_mulVec_basisKet (rProjAxis (QRegExt.idReg _) w)
      (F (extractCosetP3 hm γ w)) (d (extractCosetP3 hm γ w)) (hd _) γ
  · rw [QRegister.embedUnitary_one, OneMemClass.coe_one, Matrix.one_mulVec, one_smul]

theorem dyadicDiag_setBits_eq_uActStage3D {mPayload : ℕ}
    {act : BitAssignment (fullSysCoreWires mPayload) → Bool} (hAct : ActHigh3948 act)
    (hm : 22 ≤ mPayload) (setBits :
      BitAssignment (fullSysCoreWires mPayload) → BitAssignment (fullSysCoreWires mPayload))
    (hv : ∀ γ, vepHighNuc hm (setBits γ) = act γ)
    (hag : ∀ γ, extractCosetP3 hm (setBits γ) = extractCosetP3 hm γ ∧
      ∀ (w : Fin 3) (m : Fin 8), setBits γ (rProjAxis (QRegExt.idReg _) w m) =
        γ (rProjAxis (QRegExt.idReg _) w m))
    (F : Fin 2 → Unitary 256) (d : Fin 2 → Fin 256 → ℂ)
    (hd : ∀ b, (F b).1 = Matrix.diagonal (d b))
    (E : BitAssignment (fullSysCoreWires mPayload) → ℤ)
    (hVepEq : DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 E =
      uCtrlProj3DStage hm F) :
    DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun γ ↦ E (setBits γ)) =
      uActStage3D act hAct hm F 1 := by
  refine Subtype.ext (matrix_ext_basisKet fun γ ↦ ?_)
  let γ' := setBits γ
  have hAt := congrArg (fun U : Unitary _ ↦ U.1.mulVec (basisKet γ')) hVepEq
  rw [JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet] at hAt ⊢
  obtain ⟨hcos, hax⟩ := hag γ
  unfold uActStage3D
  unfold uCtrlProj3DStage at hAt
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hAt ⊢
  rw [uActStage1DCore_diag hAct hm 2 F d hd γ, Matrix.mulVec_smul, Matrix.mulVec_smul,
    uActStage1DCore_diag hAct hm 1 F d hd γ, Matrix.mulVec_smul,
    uActStage1DCore_diag hAct hm 0 F d hd γ, smul_smul, smul_smul]
  have hV1 : ∀ w : Fin 3, (uCtrlProj1DCore hm w F).1.mulVec (basisKet γ') =
      (if act γ then d (extractCosetP3 hm γ w)
        ((basisBitsEquiv 8).symm (fun m ↦ γ (rProjAxis (QRegExt.idReg _) w m))) else 1) •
      basisKet γ' := fun w ↦ by
    rw [uCtrlProj1DCore_mulVec_basisKet, hv γ, hcos]
    split_ifs
    · have hfn : (fun m ↦ γ' (rProjAxis (QRegExt.idReg _) w m)) =
          (fun m ↦ γ (rProjAxis (QRegExt.idReg _) w m)) := funext (hax w)
      simpa only [hfn] using embedUnitary_diagonal_mulVec_basisKet
        (rProjAxis (QRegExt.idReg _) w) (F (extractCosetP3 hm γ w)) _ (hd _) γ'
    · simp
  rw [hV1 2, Matrix.mulVec_smul, Matrix.mulVec_smul, hV1 1, Matrix.mulVec_smul, hV1 0,
    smul_smul, smul_smul] at hAt
  congr 1
  simpa [basisKet_eq_single, γ'] using congrFun hAt ((basisBitsEquiv _).symm γ')

def cSwap8 (a b : Wire 8) (hab : a ≠ b) : Circuit 8 :=
  Circuit.CNOT a b hab ;;ᶜ (Circuit.CNOT b a hab.symm ;;ᶜ Circuit.CNOT a b hab)
def cTailLocal8 : Circuit 8 :=
  Circuit.H 0 ;;ᶜ
    (cSwap8 0 7 (by decide) ;;ᶜ
      (cSwap8 1 6 (by decide) ;;ᶜ
        (cSwap8 2 5 (by decide) ;;ᶜ cSwap8 3 4 (by decide))))
@[scoped simp]
theorem count_cSwap8_toff (a b : Wire 8) (hab : a ≠ b) : (cSwap8 a b hab).count .TOFF = 0 := rfl
@[scoped simp]
theorem count_cSwap8_t (a b : Wire 8) (hab : a ≠ b) : (cSwap8 a b hab).count .T = 0 := rfl
@[scoped simp] theorem count_cTailLocal8_toff : cTailLocal8.count .TOFF = 0 := rfl
@[scoped simp] theorem count_cTailLocal8_t : cTailLocal8.count .T = 0 := rfl
theorem cSwap8_evolve_basisKet (a b : Wire 8) (hab : a ≠ b) (ξ : BitAssignment 8) :
    (cSwap8 a b hab).eval.1.mulVec (basisKet ξ) =
      basisKet (Function.update (Function.update ξ a (ξ b)) b (ξ a)) := by
  unfold cSwap8
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_CNOT_basisKet]
  congr 1
  funext u
  by_cases hua : u = a
  · subst hua
    simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hab.symm]
    generalize ξ u = x, ξ b = y
    revert x y
    decide
  · by_cases hub : u = b
    · subst hub
      simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hab.symm]
      generalize ξ a = x, ξ u = y
      revert x y
      decide
    · simp [Function.update_of_ne hua, Function.update_of_ne hub]
theorem cTailLocal8_eval_eq : cTailLocal8.eval = uTailLocal8 := by
  unfold cTailLocal8 uTailLocal8
  rw [Circuit.eval_seq]
  refine congrArg (· * wireHadamard8 0) (Subtype.ext (matrix_ext_basisKet fun ξ ↦ ?_))
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, cSwap8_evolve_basisKet]
  unfold bitRev8Unitary
  have hId := embedUnitary_perm_mulVec_basisKet_b2 (QRegExt.idReg 8)
    (Equiv.ofBijective bitRev8Fun bitRev8Fun_involutive.bijective) ξ
    (fun k ↦ ξ ⟨7 - k.val, by omega⟩)
    (fun k ↦ by
      let uIdx : Fin 256 := (basisBitsEquiv 8).symm ξ
      have hu : basisBits 8 uIdx = ξ := (basisBitsEquiv 8).apply_symm_apply ξ
      simp only [QRegExt.idReg, ← hu]
      change basisBits 8 uIdx ⟨7 - k.val, _⟩ =
        basisBits 8 (bitRev8Fun ((basisBitsEquiv 8).symm (basisBitsEquiv 8 uIdx))) k
      rw [(basisBitsEquiv 8).symm_apply_apply, basisBits_eq_div_mod, basisBits_eq_div_mod]
      exact congrArg Nat.cast (bit8_bitRev8Fun uIdx k).symm)
    (fun z hz ↦ False.elim (hz ((QRegister.mem_image _ z).mpr ⟨z, rfl⟩)))
  rw [embedUnitary_idReg_eq] at hId
  rw [hId]
  refine congrArg basisKet (funext fun k ↦ ?_)
  fin_cases k
  all_goals rfl
def cTail_3D {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) : Circuit n :=
  cTailLocal8.onRegister (rProjAxis rCore 2) ;;ᶜ
    (cTailLocal8.onRegister (rProjAxis rCore 1) ;;ᶜ
      cTailLocal8.onRegister (rProjAxis rCore 0))
@[scoped simp]
theorem count_cTail_3D_toff {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cTail_3D rCore).count .TOFF = 0 := by
  unfold cTail_3D
  simp [Circuit.count_seq, Circuit.count_onRegister]
@[scoped simp]
theorem count_cTail_3D_t {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cTail_3D rCore).count .T = 0 := by
  unfold cTail_3D
  simp [Circuit.count_seq, Circuit.count_onRegister]
theorem cTail_3D_eval {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cTail_3D rCore).eval = rCore.embedUnitary uTail3DCore := by
  unfold cTail_3D uTail3DCore
  simp only [Circuit.eval_seq, Circuit.eval_onRegister, cTailLocal8_eval_eq,
    QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, mul_assoc]
  rfl
def dTail_3D {mPayload : ℕ} (isInv : Bool) {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) : DynamicCircuit Var n :=
  if isInv then .circuit (cTail_3D rCore).inverse else .circuit (cTail_3D rCore)
@[scoped simp] theorem count_dTail_3D_toff {mPayload : ℕ} (isInv : Bool) {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dTail_3D isInv (Var := Var) rCore).count .TOFF = 0 := by
  cases isInv
  all_goals simp [dTail_3D]
@[scoped simp] theorem count_dTail_3D_t {mPayload : ℕ} (isInv : Bool) {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dTail_3D isInv (Var := Var) rCore).count .T = 0 := by
  cases isInv
  all_goals simp [dTail_3D]
theorem rCosetB0_wire_bounds {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    3957 ≤ (rCosetB0 hm (QRegExt.idReg (fullSysCoreWires mPayload)) w).val ∧
      (rCosetB0 hm (QRegExt.idReg (fullSysCoreWires mPayload)) w).val < 3960 := by
  simp [rCosetB0, QRegister.slice, QRegister.compose, QRegExt.idReg]
  omega
theorem setHighNucBits_rCosetB0 {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (w : Fin 3) : setHighNucBits hm γ
    (rCosetB0 hm (QRegExt.idReg _) w) = γ (rCosetB0 hm (QRegExt.idReg _) w) :=
  setHighNucBits_apply_of_val_ne hm γ (by
    have := rCosetB0_wire_bounds hm w
    omega)
theorem regVal_rWhFull_slice_setHighNucBits {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (s l : ℕ) (hsl : s + l ≤ 8) (γ : BitAssignment (fullSysCoreWires mPayload)) : regVal
    ((rWhFull hm (QRegExt.idReg _) w).slice s l hsl) (setHighNucBits hm γ) = regVal
    ((rWhFull hm (QRegExt.idReg _) w).slice s l hsl) γ := by
  refine congrArg bitsVal (funext fun j ↦ ?_)
  rw [slice_apply_eq]
  by_cases hi : (⟨s + j.val, by omega⟩ : Fin 8).val = 0
  · rw [show (⟨s + j.val, by omega⟩ : Fin 8) = 0 from Fin.ext hi, rWhFull_apply_zero]
    exact setHighNucBits_rCosetB0 hm γ w
  · rw [rWhFull_apply_pos hm _ w _ hi]
    exact (setHighNucBits_agrees_on_proj_and_coset hm γ).2 w _
theorem whRemTopExp_setHighNucBits {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (isInv : Bool) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    whRemTopExp hm isInv (setHighNucBits hm γ) = whRemTopExp hm isInv γ := by
  obtain ⟨_, hax⟩ := setHighNucBits_agrees_on_proj_and_coset hm γ
  unfold whRemTopExp
  dsimp only
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦ ?_)
  simp only [setHighNucBits_rCosetB0 hm γ w, hax w]
theorem whRemLowShift_setHighNucBits {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (isInv : Bool) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    whRemLowShift hm isInv (setHighNucBits hm γ) = whRemLowShift hm isInv γ := by
  unfold whRemLowShift
  dsimp only
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦ ?_)
  exact congrArg Nat.cast (regVal_rWhFull_slice_setHighNucBits hm w 0 7 _ γ)
def whStg7ExpCoin0 {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  whStg7Exp hm isInv (setHighNucBits hm γ)
noncomputable def uWhStg7CutCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool) : Unitary
    (2 ^ (fullSysCoreWires mPayload + 48)) := (rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whStg7ExpCoin0 hm isInv))
theorem uWhStg7CutCat_inv_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (uWhStg7CutCat hm false)⁻¹ = uWhStg7CutCat hm true := by
  unfold uWhStg7CutCat
  rw [← QRegister.embedUnitary_inv, DyadicQft64.dyadicDiagUnitary_inv]
  have h1 : (fun γ ↦ -whStg7ExpCoin0 hm false γ) = whStg7ExpCoin0 hm true := funext fun γ ↦ by
    unfold whStg7ExpCoin0 whStg7Exp
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  rw [h1]
lemma uCoin0Stage3D_omega512_mulVec {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (F : Fin 2 → Unitary 256) (d : Fin 2 → Fin 256 → ℤ)
    (hd : ∀ b, (F b).1 = Matrix.diagonal (fun u ↦ omega512 (d b u)))
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    let rId := QRegExt.idReg (fullSysCoreWires mPayload)
    (uCoin0Stage3D hm F 1).1.mulVec (basisKet γ) =
      DyadicQft64.dyadicTurn 48 ((2 ^ 39 : ℤ) * wfBitVal hm (setHighNucBits hm γ) *
        ∑ w : Fin 3, d (extractCosetP3 hm γ w)
          ((basisBitsEquiv 8).symm (fun m ↦ γ (rProjAxis rId w m)))) • basisKet γ := by
  intro rId
  have hAx := fun w ↦ uActStage1DCore_diag actHigh3948_posBranch hm w F
    (fun b u ↦ omega512 (d b u)) hd γ
  unfold uCoin0Stage3D
  change (uActStage1DCore posBranchActive actHigh3948_posBranch hm 0 F 1 *
    (uActStage1DCore posBranchActive actHigh3948_posBranch hm 1 F 1 *
      uActStage1DCore posBranchActive actHigh3948_posBranch hm 2 F 1)).1.mulVec (basisKet γ) = _
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hAx 2, Matrix.mulVec_smul, Matrix.mulVec_smul, hAx 1, Matrix.mulVec_smul, hAx 0,
    smul_smul, smul_smul]
  have hv := vepHighNuc_setHighNucBits hm γ
  cases hp : posBranchActive γ
  · simp [wfBitVal, hv, hp, DyadicQft64.dyadicTurn_zero]
  · simp only [wfBitVal, hv, hp, ↓reduceIte, mul_one, Fin.sum_univ_three,
      dyadicTurn48_shift39_int_eq_omega512, ← omega512_add]
    exact congrArg (fun z ↦ omega512 z • basisKet γ) (by ring)
theorem uWhStg7CutCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (U_cat_48 : Unitary (2 ^ 48)) : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
    (uWhStg7CutCat hm false) (uCoin0Stage3D hm whStg7Diag8 1) := by
  suffices hEff : DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
      (whStg7ExpCoin0 hm false) = uCoin0Stage3D hm whStg7Diag8 1 by
    unfold uWhStg7CutCat
    exact hEff ▸ NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48 _
  refine Subtype.ext (matrix_ext_basisKet fun γ ↦ ?_)
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  obtain ⟨_, hax⟩ := setHighNucBits_agrees_on_proj_and_coset hm γ
  rw [JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet,
    uCoin0Stage3D_omega512_mulVec hm whStg7Diag8
      (fun b u ↦ -128 * (b.val : ℤ) * (bit8 u 7 : ℤ)) (fun _ ↦ rfl) γ]
  refine congrArg (fun z ↦ DyadicQft64.dyadicTurn 48 z • basisKet γ) ?_
  unfold whStg7ExpCoin0 whStg7Exp
  dsimp only [rId]
  have hbk : ∀ w : Fin 3,
      bit8 ((basisBitsEquiv 8).symm (fun m ↦ γ (rProjAxis (QRegExt.idReg _) w m))) 7 =
        (γ (rProjAxis (QRegExt.idReg _) w 7)).val :=
    fun w ↦ bit8_symm_eq (fun m ↦ γ (rProjAxis (QRegExt.idReg _) w m)) 7
  have hcos : ∀ w : Fin 3,
      (extractCosetP3 hm γ w).val = (γ (rCosetB0 hm (QRegExt.idReg _) w)).val := fun _ ↦ rfl
  simp only [Bool.false_eq_true, ↓reduceIte, Fin.sum_univ_three,
    setHighNucBits_rCosetB0 hm γ, hax, hbk, hcos]
  ring
def whStgTopExpCoin0 {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  whStgTopExp hm k isInv (setHighNucBits hm γ)
def whStgLowShiftCoin0 {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  whStgLowShift hm k isInv (setHighNucBits hm γ)
noncomputable def uWhStgCutCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) (isInv : Bool) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  uApexShift45 (fullSysCoreWires mPayload) (7 - k.val) (by omega) (whStgLowShiftCoin0 hm k isInv) *
    (rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whStgTopExpCoin0 hm k isInv))
theorem uWhStgCutCat_inv_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7) :
    (uWhStgCutCat hm k false)⁻¹ = uWhStgCutCat hm k true := by
  unfold uWhStgCutCat
  rw [_root_.mul_inv_rev, uApexShift45_inv, ← QRegister.embedUnitary_inv,
    DyadicQft64.dyadicDiagUnitary_inv]
  have h1 : (fun γ ↦ -whStgLowShiftCoin0 hm k false γ) = whStgLowShiftCoin0 hm k true :=
    funext fun γ ↦ by
      unfold whStgLowShiftCoin0 whStgLowShift
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring
  have h2 : (fun γ ↦ -whStgTopExpCoin0 hm k false γ) = whStgTopExpCoin0 hm k true :=
    funext fun γ ↦ by
      unfold whStgTopExpCoin0 whStgTopExp
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring
  rw [h1, h2]
  exact uApexShift45_comm_coreDiag (fullSysCoreWires mPayload) (7 - k.val) _ 48
    (whStgTopExpCoin0 hm k true) (whStgLowShiftCoin0 hm k true)
theorem uWhStgCutCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7)
    (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48 (uWhStgCutCat hm k false)
    (uCoin0Stage3D hm (whGatedDiag8 k) 1 * uWhUngatedCore hm k) := by
  have hProd := (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
      (whStgTopExpCoin0 hm k false))).mul
    (uApexShift45_intertwinesLocal (fullSysCoreWires mPayload) (7 - k.val)
      (by omega) (whStgLowShiftCoin0 hm k false) U_cat_48 hcol0)
  suffices hEff : DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
        (fun γ ↦ (2 ^ (45 - (7 - k.val)) : ℤ) * whStgLowShiftCoin0 hm k false γ) *
      DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
        (whStgTopExpCoin0 hm k false) =
      uCoin0Stage3D hm (whGatedDiag8 k) 1 * uWhUngatedCore hm k by
    unfold uWhStgCutCat
    rw [← hEff]
    exact hProd
  rw [dyadicDiagUnitary_mul]
  refine Subtype.ext (matrix_ext_basisKet fun γ ↦ ?_)
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let γ' := setHighNucBits hm γ
  obtain ⟨_, hax⟩ := setHighNucBits_agrees_on_proj_and_coset hm γ
  have hAlg : whStgTopExp hm k false γ' +
      (2 ^ (45 - (7 - k.val)) : ℤ) * whStgLowShift hm k false γ' =
      whUngatedExp hm k γ' + (2 ^ 39 : ℤ) * wfBitVal hm γ' *
        ∑ w : Fin 3, (2 ^ k.val : ℤ) * ((γ' (rProjAxis rId w ⟨k.val, by omega⟩)).val : ℤ) *
          (regVal ((rWhFull hm rId w).slice 0 (8 - k.val) (by omega)) γ' : ℤ) := by
    have hsp := fun w ↦ regVal_rWhFull_split_top hm rId w k γ'
    unfold whStgTopExp whStgLowShift whUngatedExp
    simp only [Bool.false_eq_true, ↓reduceIte, Fin.sum_univ_three]
    dsimp only [rId] at hsp ⊢
    rw [hsp 0, hsp 1, hsp 2]
    fin_cases k
    all_goals
      dsimp
      ring
  rw [JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  unfold uWhUngatedCore
  rw [JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul,
    uCoin0Stage3D_omega512_mulVec hm (whGatedDiag8 k)
      (fun b u ↦ (2 ^ k.val : ℤ) * (bit8 u ⟨k.val, by omega⟩ : ℤ) * whSliceVal8 k b u)
      (fun _ ↦ rfl) γ,
    smul_smul, DyadicQft64.dyadicTurn_add]
  refine congrArg (fun z ↦ DyadicQft64.dyadicTurn 48 z • basisKet γ) ?_
  dsimp only [whStgTopExpCoin0, whStgLowShiftCoin0]
  change whStgTopExp hm k false γ' +
    (2 ^ (45 - (7 - k.val)) : ℤ) * whStgLowShift hm k false γ' = _
  have hUng : whUngatedExp hm k γ' = whUngatedExp hm k γ :=
    congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦
      congrArg Nat.cast (regVal_rWhFull_slice_setHighNucBits hm w 0 (8 - k.val) _ γ))
  rw [hAlg, hUng]
  dsimp only [γ', rId]
  simp only [Fin.sum_univ_three, hax,
    show ∀ w : Fin 3, regVal ((rWhFull hm (QRegExt.idReg _) w).slice 0 (8 - k.val)
        (by omega)) (setHighNucBits hm γ) =
      regVal ((rWhFull hm (QRegExt.idReg _) w).slice 0 (8 - k.val) (by omega)) γ from
      fun w ↦ regVal_rWhFull_slice_setHighNucBits hm w 0 (8 - k.val) _ γ,
    bit8_symm_eq,
    show ∀ w : Fin 3, extractCosetP3 hm γ w =
      ⟨(γ (rCosetB0 hm (QRegExt.idReg _) w)).val, ZMod.val_lt _⟩ from fun _ ↦ rfl,
    whSliceVal8_symm]

theorem uWhUngatedCore_comm_coin0DiagStage {mPayload : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7)
    (F : Fin 2 → Unitary 256) (hDiag : ∀ b : Fin 2, ∃ d : Fin 256 → ℂ, (F b).1 =
    Matrix.diagonal d) : uCoin0Stage3D hm F 1 * uWhUngatedCore hm k = uWhUngatedCore hm k *
    uCoin0Stage3D hm F 1 := by
  choose d hd using hDiag
  refine Subtype.ext (matrix_ext_basisKet fun γ ↦ ?_)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (uCoin0Stage3D hm F 1).1.mulVec (basisKet γ) = c • basisKet γ := by
    have hAx := fun w ↦ uActStage1DCore_diag actHigh3948_posBranch hm w F d hd γ
    unfold uCoin0Stage3D
    change ∃ c : ℂ, (uActStage1DCore posBranchActive actHigh3948_posBranch hm 0 F 1 *
      (uActStage1DCore posBranchActive actHigh3948_posBranch hm 1 F 1 *
        uActStage1DCore posBranchActive actHigh3948_posBranch hm 2 F 1)).1.mulVec (basisKet γ) = _
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hAx 2, Matrix.mulVec_smul, Matrix.mulVec_smul, hAx 1, Matrix.mulVec_smul, hAx 0,
      smul_smul, smul_smul]
    exact ⟨_, rfl⟩
  unfold uWhUngatedCore
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul, hc,
      Matrix.mulVec_smul,
    JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet, smul_smul, smul_smul, mul_comm]
theorem CondStageSpec_dPureConjX {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ}
    (t : Wire n) {rAct : QRegister mAct n} {rW : QRegister mW n} {S_pres : Finset (Wire n)}
    {H_outer H_inner : BitAssignment n → Prop} {U : Unitary (2 ^ mAct)}
    {dInner : DynamicCircuit Var n} (htW : t ∉ rW.image) (htAct : t ∉ rAct.image)
    (htS : t ∈ S_pres) (hH_step : ∀ ξ, H_outer ξ → H_inner (Function.update ξ t (ξ t + 1)))
    (hsInner : CondStageSpec rAct rW S_pres H_inner U dInner) : CondStageSpec rAct rW S_pres
    H_outer U (FusedVepCore288.dPureConj (Circuit.X t) dInner) := by
  rcases hsInner.exists_u with ⟨uInner, hwInner, hDiagInner, hKetInner⟩
  refine ⟨⟨(Circuit.X t).inverse.eval * uInner * (Circuit.X t).eval,
    CleanUnitaryWp.dPureConj (Circuit.X t) rW (disj_support_X t htW) hwInner,
    by simpa only [eval_X_inverse, Submonoid.coe_mul] using DiagOn.conj_X t hDiagInner,
    fun ξ hzW hHξ ↦ ?_⟩⟩
  have hBank : ClassicalAncBank ∅ {t} (Circuit.X t)
      (fun γ ↦ Function.update γ t (γ t + 1)) (fun γ ↦ Function.update γ t (γ t + 1)) :=
    { evolve := evolve_X_basisKet t
      inv_evolve := fun γ ↦ eval_X_inverse t ▸ evolve_X_basisKet t γ
      left_inv := fun γ ↦ funext fun w ↦ by
        obtain rfl | hw := eq_or_ne w t
        · simp
        · simp [Function.update_of_ne hw]
      fwd_outside := fun γ w hw ↦ Function.update_of_ne (Finset.notMem_singleton.mp hw) _ γ
      inv_outside := fun γ w hw ↦ Function.update_of_ne (Finset.notMem_singleton.mp hw) _ γ
      inv_congr := fun γ₁ γ₂ hEq u hu ↦ by
        rw [Finset.mem_singleton.mp hu]
        simp [hEq t (Finset.mem_union_right _ (Finset.mem_singleton_self t))] }
  refine hBank.conj_elim_embed rAct (Finset.disjoint_singleton_right.mpr htAct) uInner U
    (DiagOn.anti (fun w hw ↦ ?_) hDiagInner) ξ (hKetInner _ (fun i ↦ ?_) (hH_step ξ hHξ))
  · simp only [Finset.empty_union, Finset.mem_singleton] at hw
    exact hw ▸ Finset.mem_union_left _ htS
  · rw [Function.update_of_ne
      (fun h : rW i = t ↦ htW (h ▸ (QRegister.mem_image rW _).mpr ⟨i, rfl⟩))]
    exact hzW i
end Proj3DCut
end
end
end Aux_JunctionProj3DCut
section JunctionProj3DCut
local instance (priority := 1000000) instNeZeroTwoPow_JunctionProj3DCut (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
public section
namespace JunctionProj3DCut
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64Engine
open NuclearTwistAndXor654Concrete
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding
  basisBits_symm_apply fullSysCoreWires_eq_add
open FusedVepCore288 JunctionApexCSA288
open InterWalkRSum42Hoist

/-- Sets the top three nuclear index bits `rNucIdx[5, 6, 7]` of a core bit-assignment to `1`,
reducing `vepHighNuc` to `coin0Active` while preserving all non-nuclear wires. -/
def setHighNucBits {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  let rN := rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload))
  Function.update (Function.update (Function.update γ (rN 5) 1) (rN 6) 1) (rN 7) 1

theorem setHighNucBits_apply_of_ne {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) {q : Wire (fullSysCoreWires mPayload)}
    (h5 : q ≠ rNucIdx hm (QRegExt.idReg _) 5) (h6 : q ≠ rNucIdx hm (QRegExt.idReg _) 6)
    (h7 : q ≠ rNucIdx hm (QRegExt.idReg _) 7) : setHighNucBits hm γ q = γ q := by
  unfold setHighNucBits
  rw [Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5]

theorem rNucIdx_val_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (j : Fin 8) :
    (rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) j).val = 3960 + j.val := by
  simp [rNucIdx, QRegister.slice, QRegister.compose, QRegExt.idReg]

theorem vepHighNuc_setHighNucBits {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    vepHighNuc hm (setHighNucBits hm γ) = coin0Active γ :=
  Proj3DCut.vepHighNuc_update567 hm γ

theorem wireHadamard8_inv (m : Fin 8) : (wireHadamard8 m)⁻¹ = wireHadamard8 m :=
  Proj3DCut.wireHadamard8_inv m
/-- Local `8`-qubit Clifford tail unitary `bitRev8Unitary * wireHadamard8 0` on one `rProjAxis`
block. -/
noncomputable def uTailLocal8 : Unitary 256 := bitRev8Unitary * wireHadamard8 0
/-- Unconditional `3D` Clifford tail unitary applying `uTailLocal8` on all 3 `rProjAxis` blocks
`[3924..3948)`. -/
noncomputable def uTail3DCore {mPayload : ℕ} : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (rProjAxis rId 0).embedUnitary uTailLocal8 *
    ((rProjAxis rId 1).embedUnitary uTailLocal8 *
      (rProjAxis rId 2).embedUnitary uTailLocal8)
/-- Generic `1D` core operator applying `F_c0 (b0_w)` on `rProjAxis w` when `coin == 0` and
`F_other` otherwise. -/
noncomputable def uCoin0Stage1DMat {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 : Fin 2 → Operator 256) (F_other : Operator 256) : Operator
    (2 ^ (fullSysCoreWires mPayload)) := Matrix.of fun i j ↦ if coin0Active (basisBits _ i)
    then ((rProjAxis (QRegExt.idReg _) w).embedMatrix (F_c0 (extractCosetP3 hm (basisBits _
    i) w))) i j else ((rProjAxis (QRegExt.idReg _) w).embedMatrix F_other) i j
theorem rProjAxis_wire_lt_3948 {mPayload : ℕ} (w : Fin 3) (m : Fin 8) :
    (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w m).val < 3948 :=
  Proj3DCut.rProjAxis_wire_lt_3948 w m
theorem uCoin0Stage1DMat_one {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    uCoin0Stage1DMat hm w (fun _ ↦ 1) 1 = 1 :=
  Proj3DCut.uActStage1DMat_one coin0Active hm w
/-- Bundled unitary `1D` core stage applying `F_c0 (b0_w)` on `rProjAxis w` when `coin == 0` and
`F_other` otherwise. -/
noncomputable def uCoin0Stage1DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  ⟨uCoin0Stage1DMat hm w (fun b ↦ (F_c0 b).1) F_other.1,
    Proj3DCut.uActStage1DMat_mem_unitary
      Proj3DCut.actHigh3948_coin0 hm w F_c0 F_other⟩
/-- Bundled `3D` core stage across axes `w = 0, 1, 2`. -/
noncomputable def uCoin0Stage3D {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := uCoin0Stage1DCore hm 0 F_c0 F_other *
    (uCoin0Stage1DCore hm 1 F_c0 F_other * uCoin0Stage1DCore hm 2 F_c0 F_other)
/-- Bundled `1D` core unitary of `JunctionProj3DCut`
(`uProj3DCut1DCore.1 = uProj3DCut1DMat` by `rfl`). -/
noncomputable def uProj3DCut1DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := uCoin0Stage1DCore hm w uProjPlus512_1D uTailLocal8
/-- Full `3D` core unitary of `JunctionProj3DCut` (`uProjPlus512_3D` on `coin == 0`, `uTail3DCore`
otherwise). -/
noncomputable def uProj3DCutCore {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uProj3DCut1DCore hm 0 * (uProj3DCut1DCore hm 1 * uProj3DCut1DCore hm 2)

theorem uCoin0Stage3D_mul {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (F_c0 G_c0 : Fin 2 → Unitary 256) (F_other G_other : Unitary 256) :
    uCoin0Stage3D hm F_c0 F_other * uCoin0Stage3D hm G_c0 G_other =
      uCoin0Stage3D hm (fun b ↦ F_c0 b * G_c0 b) (F_other * G_other) :=
  Proj3DCut.uActStage3D_mul
    Proj3DCut.actHigh3948_coin0 hm F_c0 G_c0 F_other G_other

theorem uTail3DCore_eq_uCoin0Stage3D {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (uTail3DCore (mPayload := mPayload)) = uCoin0Stage3D hm (fun _ ↦ uTailLocal8) uTailLocal8 :=
  Proj3DCut.uTail3DCore_eq_uActStage3D
    Proj3DCut.actHigh3948_coin0 hm

/-- Top dyadic exponent of `Pre_3D` under `coin == 0` control (`setHighNucBits` specialization). -/
def preTopExpCoin0 {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  preTopExp hm isInv (setHighNucBits hm γ)

/-- Low `45`-wire integer shift of `Pre_3D` under `coin == 0` control
(`setHighNucBits` specialization). -/
def preLowShiftCoin0 {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  preLowShift hm isInv (setHighNucBits hm γ)
/-- Catalyzed `Pre_3D` stage unitary under `coin == 0` control. -/
noncomputable def uPre3DCutCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool) : Unitary
    (2 ^ (fullSysCoreWires mPayload + 48)) := uApexShift45 (fullSysCoreWires mPayload) 6
    (by decide) (preLowShiftCoin0 hm isInv) * (rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (preTopExpCoin0 hm isInv))
/-- Top dyadic exponent of `StgS_3D m` under `coin == 0` control
(`setHighNucBits` specialization). -/
def stgTopExpCoin0 {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  stgTopExp hm m isInv (setHighNucBits hm γ)
/-- Low `45`-wire integer shift of `StgS_3D m` (`3 ≤ m`) under `coin == 0` control. -/
def stgLowShiftCoin0 {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) (hm3 : 3 ≤ m.val)
    (isInv : Bool) (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  stgLowShift hm m hm3 isInv (setHighNucBits hm γ)
theorem fin8_sub_two_le_45 (m : Fin 8) : m.val - 2 ≤ 45 := by omega

/-- Catalyzed `StgS_3D m` stage unitary under `coin == 0` control. -/
noncomputable def uStg3DCutCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) (isInv : Bool)
    : Unitary (2 ^ (fullSysCoreWires mPayload + 48)) := if hm3 : 3 ≤ m.val then uApexShift45
    (fullSysCoreWires mPayload) (m.val - 2) (fin8_sub_two_le_45 m)
    (stgLowShiftCoin0 hm m hm3 isInv) * (rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (stgTopExpCoin0 hm m
    isInv)) else (rCoreBlock48 mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary
    (fullSysCoreWires mPayload) 48 (stgTopExpCoin0 hm m isInv))

/-- Catalyzed `15`-stage `coin == 0` controlled prefix unitary before `uTail3DCore`. -/
noncomputable def uProj3DCutPre15Cat {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  let eC (m : Fin 8) := (rCoreBlock48 mPayload).embedUnitary
    (uCoin0Stage3D hm (fun _ ↦ wireHadamard8 m) 1)
  uStg3DCutCat hm 1 false * (eC 1 * (uStg3DCutCat hm 2 false * (eC 2 *
    (uStg3DCutCat hm 3 false * (eC 3 * (uStg3DCutCat hm 4 false * (eC 4 *
      (uStg3DCutCat hm 5 false * (eC 5 * (uStg3DCutCat hm 6 false * (eC 6 *
        (uStg3DCutCat hm 7 false * (eC 7 * uPre3DCutCat hm false)))))))))))))

/-- Catalyzed `JunctionProj3DCut` unitary on `fullSysCoreWires mPayload + 48` (`810 T`). -/
noncomputable def uProj3DCutApexCat {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  (rCoreBlock48 mPayload).embedUnitary uTail3DCore * uProj3DCutPre15Cat hm

theorem setHighNucBits_apply_of_val_ne {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) {q : Wire (fullSysCoreWires mPayload)}
    (h : q.val < 3960) : setHighNucBits hm γ q = γ q :=
  setHighNucBits_apply_of_ne hm γ
    (fun e ↦ absurd ((congrArg Fin.val e).trans (rNucIdx_val_eq hm 5)) (by omega))
    (fun e ↦ absurd ((congrArg Fin.val e).trans (rNucIdx_val_eq hm 6)) (by omega))
    (fun e ↦ absurd ((congrArg Fin.val e).trans (rNucIdx_val_eq hm 7)) (by omega))
theorem setHighNucBits_agrees_on_proj_and_coset {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : extractCosetP3 hm (setHighNucBits hm γ)
    = extractCosetP3 hm γ ∧ ∀ (w : Fin 3) (m : Fin 8), setHighNucBits hm γ
    (rProjAxis (QRegExt.idReg _) w m) = γ (rProjAxis (QRegExt.idReg _) w m) := by
  refine ⟨funext fun u ↦ ?_, fun w m ↦ setHighNucBits_apply_of_val_ne hm γ
    ((rProjAxis_wire_lt_3948 w m).trans (by decide))⟩
  unfold extractCosetP3 rProjCosetP3
  exact setHighNucBits_apply_of_val_ne hm γ (Proj3DCut.rCosetB0_wire_bounds hm u).2

lemma intertwinesLocal_cutApexShiftTop {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (s : ℕ) (hs : s ≤ 45) (low top : BitAssignment (fullSysCoreWires mPayload) → ℤ)
    (F : Fin 2 → Unitary 256) (d : Fin 2 → Fin 256 → ℂ) (hd : ∀ b, (F b).1 = Matrix.diagonal (d b))
    (U_cat_48 : Unitary (2 ^ 48)) (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48)
    (hVep : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (uApexShift45 (fullSysCoreWires mPayload) s hs low *
        (rCoreBlock48 mPayload).embedUnitary
          (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 top))
      (uCtrlProj3DStage hm F)) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (uApexShift45 (fullSysCoreWires mPayload) s hs (fun γ ↦ low (setHighNucBits hm γ)) *
        (rCoreBlock48 mPayload).embedUnitary
          (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
            (fun γ ↦ top (setHighNucBits hm γ))))
      (uCoin0Stage3D hm F 1) := by
  let W_vep := uApexShift45 (fullSysCoreWires mPayload) s hs low *
    (rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 top)
  have hProd := (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
      (fun γ ↦ top (setHighNucBits hm γ)))).mul
    (uApexShift45_intertwinesLocal (fullSysCoreWires mPayload) s hs
      (fun γ ↦ low (setHighNucBits hm γ)) U_cat_48 hcol0)
  have hVepD := (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 top)).mul
    (uApexShift45_intertwinesLocal (fullSysCoreWires mPayload) s hs low U_cat_48 hcol0)
  have hVepEq := Proj3DCut.intertwinesLocalCat_unique_core U_cat_48 W_vep hVepD hVep
  rw [dyadicDiagUnitary_mul] at hVepEq
  have hEff := Proj3DCut.dyadicDiag_setBits_eq_uActStage3D
    Proj3DCut.actHigh3948_coin0 hm (setHighNucBits hm)
    (vepHighNuc_setHighNucBits hm) (setHighNucBits_agrees_on_proj_and_coset hm) F d hd _ hVepEq
  rw [← dyadicDiagUnitary_mul] at hEff
  change NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48 _
    (Proj3DCut.uActStage3D coin0Active Proj3DCut.actHigh3948_coin0 hm F 1)
  exact hEff ▸ hProd
theorem uStg3DCutCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8)
    (hm1 : 1 ≤ m.val) (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48 (uStg3DCutCat hm m false)
    (uCoin0Stage3D hm (fun _ ↦ stageDiag8 m) 1) := by
  have hd : ∀ b : Fin 2, ((fun _ ↦ stageDiag8 m) b).1 =
      Matrix.diagonal (fun k ↦ omega512 (stageRowExp512 m k)) := fun _ ↦ rfl
  have hStg := uStg3DCat_intertwinesLocal hm m hm1 U_cat_48 hcol0
  unfold uStg3DCutCat
  unfold uStg3DCat at hStg
  by_cases hm3 : 3 ≤ m.val
  · simp only [hm3, ↓reduceDIte] at hStg ⊢
    exact intertwinesLocal_cutApexShiftTop hm (m.val - 2) (fin8_sub_two_le_45 m)
      (stgLowShift hm m hm3 false) (stgTopExp hm m false)
      (fun _ ↦ stageDiag8 m) _ hd U_cat_48 hcol0 hStg
  · simp only [hm3, ↓reduceDIte] at hStg ⊢
    have hVepEq := Proj3DCut.intertwinesLocalCat_unique_core U_cat_48
      ((rCoreBlock48 mPayload).embedUnitary
        (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (stgTopExp hm m false)))
      (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48 _) hStg
    have hEff := Proj3DCut.dyadicDiag_setBits_eq_uActStage3D
      Proj3DCut.actHigh3948_coin0 hm (setHighNucBits hm)
      (vepHighNuc_setHighNucBits hm) (setHighNucBits_agrees_on_proj_and_coset hm)
      (fun _ ↦ stageDiag8 m) _ hd _ hVepEq
    change NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      ((rCoreBlock48 mPayload).embedUnitary
        (DyadicQft64.dyadicDiagUnitary _ 48 (fun γ ↦ stgTopExp hm m false (setHighNucBits hm γ))))
      (Proj3DCut.uActStage3D coin0Active
        Proj3DCut.actHigh3948_coin0 hm (fun _ ↦ stageDiag8 m) 1)
    rw [hEff]
    exact NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48 _

theorem uProj3DCutApexCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (uProj3DCutApexCat hm) (uProj3DCutCore hm) := by
  have hPre : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (uPre3DCutCat hm false) (uCoin0Stage3D hm preDiag8 1) :=
    intertwinesLocal_cutApexShiftTop hm 6 (by decide) (preLowShift hm false) (preTopExp hm false)
      preDiag8 _ (fun _ ↦ rfl) U_cat_48 hcol0 (uPre3DCat_intertwinesLocal hm U_cat_48 hcol0)
  have hH (m : Fin 8) := NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary
    U_cat_48 (uCoin0Stage3D hm (fun _ ↦ wireHadamard8 m) 1)
  have hS (m : Fin 8) (hm1 : 1 ≤ m.val) := uStg3DCutCat_intertwinesLocal hm m hm1 U_cat_48 hcol0
  have hTail : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      ((rCoreBlock48 mPayload).embedUnitary uTail3DCore)
      (uCoin0Stage3D hm (fun _ ↦ uTailLocal8) uTailLocal8) := by
    rw [← uTail3DCore_eq_uCoin0Stage3D hm]
    exact NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48 uTail3DCore
  have hProd := ((((((((((((((hPre.mul (hH 7)).mul (hS 7 (by decide))).mul (hH 6)).mul
    (hS 6 (by decide))).mul (hH 5)).mul (hS 5 (by decide))).mul (hH 4)).mul
    (hS 4 (by decide))).mul (hH 3)).mul (hS 3 (by decide))).mul (hH 2)).mul
    (hS 2 (by decide))).mul (hH 1)).mul (hS 1 (by decide))).mul hTail
  simp only [uCoin0Stage3D_mul, mul_one] at hProd
  have h8Eq : (fun b ↦ uTailLocal8 * (stageDiag8 1 * (wireHadamard8 1 *
      (stageDiag8 2 * (wireHadamard8 2 * (stageDiag8 3 * (wireHadamard8 3 *
      (stageDiag8 4 * (wireHadamard8 4 * (stageDiag8 5 * (wireHadamard8 5 *
      (stageDiag8 6 * (wireHadamard8 6 * (stageDiag8 7 *
      (wireHadamard8 7 * preDiag8 b))))))))))))))) = uProjPlus512_1D := by
    funext b
    apply Subtype.ext
    simpa only [uTailLocal8, Submonoid.coe_mul, Matrix.mul_assoc] using
      eightStageProj512_eq_uProjPlus512_1D b
  rw [h8Eq] at hProd
  exact hProd

/-- `3`-`CNOT` `SWAP` on two wires of an `8`-wire local register (`0 T`, `0 .TOFF`). -/
abbrev cSwap8 := Proj3DCut.cSwap8

/-- Local `8`-wire `0-T` Clifford tail circuit
`H 0 ;; SWAP(0,7) ;; SWAP(1,6) ;; SWAP(2,5) ;; SWAP(3,4)`. -/
abbrev cTailLocal8 := Proj3DCut.cTailLocal8

@[simp]
theorem count_cSwap8_toff (a b : Wire 8) (hab : a ≠ b) : (cSwap8 a b hab).count .TOFF = 0 := rfl

@[simp]
theorem count_cSwap8_t (a b : Wire 8) (hab : a ≠ b) : (cSwap8 a b hab).count .T = 0 := rfl

@[simp] theorem count_cTailLocal8_toff : cTailLocal8.count .TOFF = 0 := rfl

@[simp] theorem count_cTailLocal8_t : cTailLocal8.count .T = 0 := rfl

@[simp]
theorem cSwap8_evolve_basisKet (a b : Wire 8) (hab : a ≠ b) (ξ : BitAssignment 8) :
    (cSwap8 a b hab).eval.1.mulVec (basisKet ξ) =
      basisKet (Function.update (Function.update ξ a (ξ b)) b (ξ a)) :=
  Proj3DCut.cSwap8_evolve_basisKet a b hab ξ

theorem cTailLocal8_eval_eq : cTailLocal8.eval = uTailLocal8 :=
  Proj3DCut.cTailLocal8_eval_eq

/-- Catalyzed `Proj3DCut + Xor32` prefix unitary (`818 T`). -/
noncomputable def uPrefixProjCutAndXorCat {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  (rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload) * uProj3DCutApexCat hm

/-- Catalyzed `Junction` prefix unitary with `uProj3DCutApexCat` (`956 T`). -/
noncomputable def uJunctionPrefixCutCat {mPayload : ℕ} (hm : 22 ≤ mPayload) : Unitary
    (2 ^ (fullSysCoreWires mPayload + 48)) := uSlot4ApexCat hm * uPrefixProjCutAndXorCat hm

end JunctionProj3DCut
end
end JunctionProj3DCut

end QuantumComputation.Specs.StoppingPowerSolution
