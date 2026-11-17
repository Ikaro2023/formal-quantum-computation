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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80SpanDefs

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPosPostPrep80Cert
@[expose] public section
namespace PosPostPrep80CertAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end PosPostPrep80CertAlt
namespace PosPostPrep80Cert
section ConfigPosPostPrep80Cert
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowCert {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket)
open ZeroAncillaUSP hiding ket
open PosPostPrep80MergedVep
theorem diagonal_mulVec_ket_cert {N : ℕ} (f : Fin (2 ^ N) → ℂ) (β : BitAssignment N) :
    (Matrix.diagonal f).mulVec (ket β) = f ((basisBitsEquiv N).symm β) • ket β := by
  rw [ket_eq_single_local β, Matrix.diagonal_mulVec_single]
  funext y
  by_cases hy : y = (basisBitsEquiv N).symm β <;> simp [hy]
set_option maxRecDepth 2000
end ConfigPosPostPrep80Cert
end PosPostPrep80Cert
end
end ModPosPostPrep80Cert

section ModMergedVepTopCoinCollapse
@[expose] public section
namespace MergedVepTopCoinCollapse
section Opts
set_option maxRecDepth 262144
set_option backward.isDefEq.respectTransparency true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowTopCollapse (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift (
  NyqGrid3D256 NyqFine3D512 nyq512ProjEquiv3D)
open MeasureBranchHadamardSem (ket)
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysPrepare6Slot (coinSelOutcome)
open FullSysFullPrepareAndTopConcrete (
  selWiresSym coreWiresSym coreAncSym selCoin3Sym coreSysSym coreHadamardUnitary)
open FullSysCatSegmentBridge (
  fullSysCoreWires iSlot2 fullSysQftCoreUnitary coreElecCosetB1Block)
open OraAndPrepBundle (coreUnitaryFromFullSys PosPostPrepCert)
open PosSlots24TopWrapper (PosSlots24DataGen rPosSubLocal)
open NuclearTwistAndXor654Concrete (
  rNucIdx rAnchorIdx wSlot0 wSlot1 wSlot2)
open NuclearTwistRealizes (uTwistParam)
open ProjZ512QftAndTwist288 (
  cfgProjZ512 uProjPlus512_3D uBarrelCore_mulVec_basisKet uXor32Core_mulVec_basisKet)
open PosSlots24BranchConcrete (
  posCoreWires uPosPhase posPhaseBit headPhaseBitSpec tailAndSlackPhaseBitSpec
  wSlot0Core wSlot1Core wSlot2Core)
open PosSlots24SemanticBridge (
  pos24_6_le_80 pos24_22_le_80 pos24_coreWires80_eq pos24_core80_eq_twist80 pos24TailSign
  pos24TailMag30 castUnitaryPow2 pos24ConjCore80 sysBlockAtPayloadGen)
theorem ite_eq_of_pos {α : Type*} {P : Prop} {_h : Decidable P} (hp : P) {a b : α} :
    (if P then a else b) = a := by simp [hp]
theorem ite_eq_of_neg {α : Type*} {P : Prop} {_h : Decidable P} (hp : ¬P) {a b : α} :
    (if P then a else b) = b := by simp [hp]
theorem dite_eq_of_pos {α : Type*} {P : Prop} {_h : Decidable P} (hp : P) {a : P → α}
    {b : ¬P → α} : (if h : P then a h else b h) = a hp := by simp [hp]
theorem dite_eq_of_neg {α : Type*} {P : Prop} {_h : Decidable P} (hp : ¬P) {a : P → α}
    {b : ¬P → α} : (if h : P then a h else b h) = b hp := by simp [hp]
theorem matrix_ext_ket_sym {N : ℕ} {A B : Operator (2 ^ N)}
    (h : ∀ β : BitAssignment N, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have hk : ket (basisBits N j) = (Pi.single j (1 : ℂ) : Fin (2 ^ N) → ℂ) := by
    conv_rhs => rw [← (basisBitsEquiv N).symm_apply_apply j]
    funext x
    simp [ket, basisState]
  simpa only [hk, Matrix.mulVec_single_one, Matrix.col_apply] using
    congrFun (h (basisBits N j)) i
open PosSlots24SemanticOracleConcrete80 (
  coreBetaOf coreIdxOf basisOutcomeProjector_sandwich_apply
  embedMatrix_entry_of_agreeOutside embedMatrix_entry_of_not_agreeOutside
  extendZero extendZero_apply extendZero_of_not_exists sum_extendZero
  entry_zero_of_comm_basisOutcomeProjector uPosPhase_cast_comm_diagonal regVal_eq_of_wire_eq)
abbrev mProj24_sp : QRegister 24 SpecsAux.SpecMirror.systemQubits :=
  QRegister.block 3924 24 (by change 3924 + 24 ≤ 3948; omega)
def mProjGridEquiv24 : Fin (2 ^ 24) ≃ NyqGrid3D256 where
  toFun u w := ⟨(u.val / 2 ^ (8 * w.val)) % 256, by omega⟩
  invFun g := ⟨(g 0).val + 256 * (g 1).val + 65536 * (g 2).val, by
    have h0 := (g 0).isLt
    have h1 := (g 1).isLt
    have h2 := (g 2).isLt
    omega⟩
  left_inv u := by
    ext
    have hu : u.val < 16777216 := Nat.lt_of_lt_of_eq u.isLt (by decide)
    change (u.val / 1) % 256 + 256 * ((u.val / 256) % 256) + 65536 * ((u.val / 65536) % 256) =
      u.val
    omega
  right_inv g := by
    funext w
    have h0 := (g 0).isLt
    have h1 := (g 1).isLt
    have h2 := (g 2).isLt
    fin_cases w <;> ext <;> simp <;> omega
abbrev mMatUnit {m : ℕ} (i j : Fin (2 ^ m)) : Operator (2 ^ m) :=
  Matrix.of fun a b ↦ if a = i ∧ b = j then 1 else 0
noncomputable abbrev mProjBasisGen {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m)) :
    Operator (2 ^ N) := r.embedMatrix (mMatUnit yIdx yIdx)
theorem mProjBasisGen_eq_basisOutcomeProjector {m N : ℕ} (r : QRegister m N)
    (yIdx : Fin (2 ^ m)) : mProjBasisGen r yIdx = r.basisOutcomeProjector yIdx := by
  ext row col
  by_cases hag : r.AgreeOutside row col
  · rw [mProjBasisGen, embedMatrix_entry_of_agreeOutside r _ hag,
      QRegister.basisOutcomeProjector_apply]
    dsimp [mMatUnit]
    by_cases hrc : row = col
    · subst hrc
      by_cases hy : r.extractIndex row = yIdx <;> simp [hy]
    · refine (ite_eq_of_neg ?_).trans (ite_eq_of_neg hrc).symm
      rintro ⟨h1, h2⟩
      refine hrc ((basisBitsEquiv N).injective (funext fun q ↦ ?_))
      by_cases hq : q ∈ Set.range r.wires
      · obtain ⟨i, rfl⟩ := hq
        simpa only [QRegister.basisBits_extractIndex] using
          congrFun (congrArg (basisBits m) (h1.trans h2.symm)) i
      · exact hag q hq
  · rw [mProjBasisGen, embedMatrix_entry_of_not_agreeOutside r _ hag,
      QRegister.basisOutcomeProjector_apply]
    exact (ite_eq_of_neg fun h : row = col ↦ hag (h ▸ fun _ _ ↦ rfl)).symm
noncomputable abbrev mVepGen {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (uFam : (Fin 3 → Fin 2) → Unitary (2 ^ m))
    (H : SpecsAux.SpecMirror.Configuration → Operator (2 ^ N)) : Operator (2 ^ N) :=
  ((1 : ℝ) / (108 * 8) : ℂ) • ∑ bP : Fin 3 → Fin 2, (r.embedUnitary (uFam bP)).1ᴴ *
    (∑ yIdx : Fin (2 ^ m), mProjBasisGen r yIdx *
      H (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) *
    (r.embedUnitary (uFam bP)).1
noncomputable abbrev mVepFromSlot2TwosOp
    (H : SpecsAux.SpecMirror.Configuration → Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  mVepGen mProj24_sp mProjGridEquiv24 uProjPlus512_3D H
noncomputable abbrev mMergedBUnitTwosGen (qRatio : ℝ)
    (b2 : SpecsAux.SpecMirror.Configuration → Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (cfg : SpecsAux.SpecMirror.Configuration) : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  (qRatio : ℂ) • (b2 cfg + mVepFromSlot2TwosOp b2)
def mWCore3967Gen {mPayload : ℕ} (hm80 : 80 ≤ mPayload) : Wire (fullSysCoreWires mPayload) :=
  ⟨3967, by
    dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]
    omega⟩
def mWCoreScrGen {mPayload : ℕ} (hm80 : 80 ≤ mPayload) (jScr : Fin 16) :
    Wire (fullSysCoreWires mPayload) :=
  ⟨4017 + jScr.val, by
    have := jScr.isLt
    dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]
    omega⟩
def swapCoreScrGenFn {mPayload : ℕ} (hm80 : 80 ≤ mPayload) (jScr : Fin 16)
    (β : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  fun q ↦ β (Equiv.swap (mWCore3967Gen hm80) (mWCoreScrGen hm80 jScr) q)
def p80NucVal (p : BitAssignment 80) : ℕ :=
  ∑ i : Fin 8, (p ⟨6 + i.val, by omega⟩).val * 2 ^ i.val
theorem p80NucVal_lt_256 (p : BitAssignment 80) : p80NucVal p < 256 := by
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_right _ ?_)
    (by decide : (∑ i : Fin 8, 1 * 2 ^ i.val) < 256)
  have := ZMod.val_lt (p ⟨6 + i.val, by omega⟩)
  omega
def p80CosetP3 (p : BitAssignment 80) : Fin 3 → Fin 2 :=
  fun w ↦ ⟨(p ⟨3 + w.val, by omega⟩).val, ZMod.val_lt _⟩
def p80SetCosetAndNuc (bP : Fin 3 → Fin 2) (l : Fin 256) (p : BitAssignment 80) :
    BitAssignment 80 :=
  fun j ↦
    if hw : 3 ≤ j.val ∧ j.val < 6 then ((bP ⟨j.val - 3, by omega⟩).val : ZMod 2)
    else if _hl : 6 ≤ j.val ∧ j.val < 14 then (((l.val / 2 ^ (j.val - 6)) % 2 : ℕ) : ZMod 2)
    else p j
def p80SetNucZero (p : BitAssignment 80) : BitAssignment 80 :=
  fun j ↦ if 6 ≤ j.val ∧ j.val < 14 then 0 else p j
theorem p80NucVal_setCosetAndNuc (bP : Fin 3 → Fin 2) (l : Fin 256) (p : BitAssignment 80) :
    p80NucVal (p80SetCosetAndNuc bP l p) = l.val := by
  unfold p80NucVal p80SetCosetAndNuc
  trans (∑ i : Fin 8, ((l.val / 2 ^ i.val) % 2) * 2 ^ i.val)
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := i.isLt
    dsimp only
    rw [dite_eq_of_neg (by omega), dite_eq_of_pos (by omega),
      show 6 + i.val - 6 = i.val by omega, ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))]
  · rw [Fin.sum_univ_eight]
    have := l.isLt
    simp
    omega
theorem p80CosetP3_setCosetAndNuc (bP : Fin 3 → Fin 2) (l : Fin 256) (p : BitAssignment 80) :
    p80CosetP3 (p80SetCosetAndNuc bP l p) = bP := by
  funext w
  ext
  unfold p80CosetP3 p80SetCosetAndNuc
  dsimp only
  rw [dite_eq_of_pos (by omega),
    show (⟨3 + w.val - 3, by omega⟩ : Fin 3) = w from Fin.ext (by dsimp; omega)]
  exact ZMod.val_natCast_of_lt (bP w).isLt
theorem p80SetCosetAndNuc_idem (bP1 bP2 : Fin 3 → Fin 2) (l1 l2 : Fin 256)
    (p : BitAssignment 80) :
    p80SetCosetAndNuc bP1 l1 (p80SetCosetAndNuc bP2 l2 p) = p80SetCosetAndNuc bP1 l1 p := by
  funext j
  unfold p80SetCosetAndNuc
  split_ifs <;> rfl
theorem p80SetCosetAndNuc_self (p : BitAssignment 80) :
    p80SetCosetAndNuc (p80CosetP3 p) ⟨p80NucVal p, p80NucVal_lt_256 p⟩ p = p := by
  funext j
  unfold p80SetCosetAndNuc p80CosetP3
  by_cases hw : 3 ≤ j.val ∧ j.val < 6
  · rw [dite_eq_of_pos hw]
    simpa only [show (⟨3 + (j.val - 3), by omega⟩ : Fin 80) = j from Fin.ext (by dsimp; omega)]
      using ZMod.natCast_zmod_val (p j)
  · by_cases hl : 6 ≤ j.val ∧ j.val < 14
    · rw [dite_eq_of_neg hw, dite_eq_of_pos hl]
      have hdiv (k : Fin 8) :
          (p80NucVal p / 2 ^ k.val) % 2 = (p ⟨6 + k.val, by omega⟩).val := by
        unfold p80NucVal
        rw [Fin.sum_univ_eight]
        have b6 := ZMod.val_lt (p 6)
        have b7 := ZMod.val_lt (p 7)
        have b8 := ZMod.val_lt (p 8)
        have b9 := ZMod.val_lt (p 9)
        have b10 := ZMod.val_lt (p 10)
        have b11 := ZMod.val_lt (p 11)
        have b12 := ZMod.val_lt (p 12)
        have b13 := ZMod.val_lt (p 13)
        fin_cases k <;> simp <;> omega
      have hk := hdiv ⟨j.val - 6, by omega⟩
      dsimp only at hk
      rw [hk, show (⟨6 + (j.val - 6), by omega⟩ : Fin 80) = j from Fin.ext (by dsimp; omega)]
      exact ZMod.natCast_zmod_val (p j)
    · simp [hw, hl]
noncomputable def mergedSliceGen (sysSlice : SpecsAux.SpecMirror.Configuration → BitAssignment 80 →
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) (cfg : SpecsAux.SpecMirror.Configuration)
    (p : BitAssignment 80) : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  if p80NucVal p < 216 then
    sysSlice cfg p
  else
    let bP := p80CosetP3 p
    (mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1ᴴ *
      (∑ yIdx : Fin (2 ^ 24),
        mProjBasisGen mProj24_sp yIdx *
          sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP)))
            (p80SetNucZero p)) *
    (mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1
noncomputable def mergedCoherentOpGen (sysSlice : SpecsAux.SpecMirror.Configuration →
    BitAssignment 80 → Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (cfg : SpecsAux.SpecMirror.Configuration) (mu : BitAssignment 80 → ℝ) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  ∑ p : BitAssignment 80, (mu p : ℂ) • mergedSliceGen sysSlice cfg p
noncomputable abbrev sysBlock80 (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (s0 : Bool) (p : BitAssignment 80) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  sysBlockAtPayloadGen pos24_coreWires80_eq.symm (pos24ConjCore80 qft cfg).1 s0 p
theorem sum_p80_split {M : Type*} [AddCommMonoid M] (f : BitAssignment 80 → M) :
    (∑ p : BitAssignment 80, f p) =
      ∑ bP : Fin 3 → Fin 2, ∑ l : Fin 256,
        ∑ r ∈ Finset.univ.filter (fun p : BitAssignment 80 ↦
            p80CosetP3 p = 0 ∧ p80NucVal p = 0),
          f (p80SetCosetAndNuc bP l r) := by
  let restSet := Finset.univ.filter fun p : BitAssignment 80 ↦
    p80CosetP3 p = 0 ∧ p80NucVal p = 0
  have hRestSelf (r : BitAssignment 80) (hr : r ∈ restSet) : p80SetCosetAndNuc 0 0 r = r := by
    obtain ⟨hc0, hn0⟩ := (Finset.mem_filter.mp hr).2
    simpa only [hc0, show (⟨p80NucVal r, p80NucVal_lt_256 r⟩ : Fin 256) = 0 from Fin.ext hn0]
      using p80SetCosetAndNuc_self r
  rw [← Fintype.sum_prod_type', ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun x _ ↦ p80SetCosetAndNuc x.1.1 x.1.2 x.2)
    (fun _ _ ↦ Finset.mem_univ _) (fun x1 hx1 x2 hx2 heq ↦ ?_) (fun p _ ↦ ?_) (fun _ _ ↦ rfl)
  · refine Prod.ext (Prod.ext ?_ (Fin.ext ?_)) ?_
    · simpa only [p80CosetP3_setCosetAndNuc] using congrArg p80CosetP3 heq
    · simpa only [p80NucVal_setCosetAndNuc] using congrArg p80NucVal heq
    · simpa only [p80SetCosetAndNuc_idem, hRestSelf x1.2 (Finset.mem_product.mp hx1).2,
        hRestSelf x2.2 (Finset.mem_product.mp hx2).2] using congrArg (p80SetCosetAndNuc 0 0) heq
  · exact ⟨((p80CosetP3 p, ⟨p80NucVal p, p80NucVal_lt_256 p⟩), p80SetCosetAndNuc 0 0 p),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p80CosetP3_setCosetAndNuc 0 0 p,
          p80NucVal_setCosetAndNuc 0 0 p⟩⟩,
      (p80SetCosetAndNuc_idem _ _ _ _ p).trans (p80SetCosetAndNuc_self p)⟩
theorem mergedCoherentOpGen_eq_mergedBUnitTwosGen_of_b0Zero
    (sysSlice : SpecsAux.SpecMirror.Configuration → BitAssignment 80 →
      Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (qRatio : ℝ) (mu216 mu218 : BitAssignment 80 → ℝ)
    (hProjIndep : ∀ (zP : NyqFine3D512) (bP : Fin 3 → Fin 2) (l : Fin 256)
      (p : BitAssignment 80), l.val < 216 →
      sysSlice (cfgProjZ512 zP) (p80SetCosetAndNuc bP l p) =
        sysSlice (cfgProjZ512 zP) (p80SetNucZero p))
    (hSupp216 : ∀ p : BitAssignment 80, 216 ≤ p80NucVal p → mu216 p = 0)
    (hB0Zero216 : ∀ p : BitAssignment 80, p80CosetP3 p ≠ 0 → mu216 p = 0)
    (hHostRatio : ∀ p : BitAssignment 80, p80NucVal p < 216 → mu218 p = qRatio * mu216 p)
    (hSupp218 : ∀ p : BitAssignment 80, 218 ≤ p80NucVal p → mu218 p = 0)
    (hVepB0 : ∀ (p : BitAssignment 80) (l : Fin 256),
      216 ≤ p80NucVal p → p80NucVal p < 218 → l.val < 216 →
      mu218 p = (qRatio / 8) * mu216 (p80SetCosetAndNuc 0 l p))
    (cfg : SpecsAux.SpecMirror.Configuration) :
    mergedCoherentOpGen sysSlice cfg mu218 =
      mMergedBUnitTwosGen qRatio
        (fun c ↦ ∑ p : BitAssignment 80, (mu216 p : ℂ) • sysSlice c p) cfg := by
  unfold mergedCoherentOpGen mMergedBUnitTwosGen mVepFromSlot2TwosOp mVepGen
  let uPlus (bP : Fin 3 → Fin 2) := (mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1
  let projB := mProjBasisGen mProj24_sp
  have hDecomp (p : BitAssignment 80) : (mu218 p : ℂ) • mergedSliceGen sysSlice cfg p =
      (if p80NucVal p < 216 then (mu218 p : ℂ) • sysSlice cfg p else 0) +
      (if p80NucVal p < 216 then 0 else (mu218 p : ℂ) • mergedSliceGen sysSlice cfg p) := by
    by_cases hn : p80NucVal p < 216 <;> simp [mergedSliceGen, hn]
  rw [Finset.sum_congr rfl fun p _ ↦ hDecomp p, Finset.sum_add_distrib, smul_add]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hn : p80NucVal p < 216
    · simp [hn, hHostRatio p hn, mul_smul]
    · simp [hn, hSupp216 p (Nat.le_of_not_lt hn)]
  · let restSet := Finset.univ.filter fun p : BitAssignment 80 ↦
      p80CosetP3 p = 0 ∧ p80NucVal p = 0
    let wRest (r : BitAssignment 80) : ℝ :=
      ∑ l : Fin 216, mu216 (p80SetCosetAndNuc 0 (Fin.castLE (by decide) l) r)
    have hL256 (r : BitAssignment 80) :
        (∑ l : Fin 256, mu216 (p80SetCosetAndNuc 0 l r)) = wRest r := by
      rw [← Finset.sum_subset (Finset.subset_univ
        (Finset.univ.image (Fin.castLE (by decide : 216 ≤ 256)))) fun x _ hx ↦
          hSupp216 _ (by
            rw [p80NucVal_setCosetAndNuc]
            exact Nat.le_of_not_lt fun hlt ↦
              hx (Finset.mem_image.mpr ⟨⟨x.val, hlt⟩, Finset.mem_univ _, rfl⟩))]
      dsimp only [wRest]
      exact Finset.sum_image fun _ _ _ _ h ↦ Fin.ext (congrArg (Fin.val : Fin 256 → ℕ) h)
    have hHostSum (zP : NyqFine3D512) :
        (∑ p : BitAssignment 80, (mu216 p : ℂ) • sysSlice (cfgProjZ512 zP) p) =
          ∑ r ∈ restSet, (wRest r : ℂ) • sysSlice (cfgProjZ512 zP) (p80SetNucZero r) := by
      rw [sum_p80_split, Finset.sum_eq_single 0 (fun bP' _ hbne ↦ Finset.sum_eq_zero fun _ _ ↦
        Finset.sum_eq_zero fun _ _ ↦ by
          rw [hB0Zero216 _ (by rw [p80CosetP3_setCosetAndNuc]; exact hbne),
            Complex.ofReal_zero, zero_smul])
        (fun habs ↦ absurd (Finset.mem_univ _) habs), Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [← hL256 r, Complex.ofReal_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      by_cases hl : l.val < 216
      · rw [hProjIndep zP 0 l r hl]
      · rw [hSupp216 _ (by rw [p80NucVal_setCosetAndNuc]; exact Nat.le_of_not_lt hl),
          Complex.ofReal_zero, zero_smul, zero_smul]
    rw [sum_p80_split, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun bP _ ↦ ?_
    let restOp (r : BitAssignment 80) : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
      (uPlus bP)ᴴ * (∑ yIdx : Fin (2 ^ 24), projB yIdx *
        sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP)))
          (p80SetNucZero r)) * uPlus bP
    have hVepVal (k : Fin 256) (r : BitAssignment 80) (hk1 : 216 ≤ k.val) (hk2 : k.val < 218) :
        mu218 (p80SetCosetAndNuc bP k r) = (qRatio / (216 * 8)) * wRest r := by
      have hSum : (∑ _l : Fin 216, mu218 (p80SetCosetAndNuc bP k r)) =
          (qRatio / 8) * wRest r := by
        dsimp only [wRest]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        simpa only [p80SetCosetAndNuc_idem] using hVepB0 (p80SetCosetAndNuc bP k r)
          (Fin.castLE (by decide) l) (by rw [p80NucVal_setCosetAndNuc]; exact hk1)
          (by rw [p80NucVal_setCosetAndNuc]; exact hk2) l.isLt
      have hConst : (∑ _l : Fin 216, mu218 (p80SetCosetAndNuc bP k r)) =
          216 * mu218 (p80SetCosetAndNuc bP k r) := by simp [Finset.sum_const]
      linarith
    have hSliceVep (k : Fin 256) (r : BitAssignment 80) (hk1 : 216 ≤ k.val) :
        mergedSliceGen sysSlice cfg (p80SetCosetAndNuc bP k r) = restOp r := by
      unfold mergedSliceGen
      rw [ite_eq_of_neg (by rw [p80NucVal_setCosetAndNuc]; omega), p80CosetP3_setCosetAndNuc]
      have hNZ : p80SetNucZero (p80SetCosetAndNuc bP k r) =
          p80SetCosetAndNuc bP ⟨0, by decide⟩ r := by
        funext j
        unfold p80SetNucZero p80SetCosetAndNuc
        by_cases hl : 6 ≤ j.val ∧ j.val < 14
        · simp [hl, show ¬(3 ≤ j.val ∧ j.val < 6) by omega]
        · simp [hl]
      simp_rw [hNZ, hProjIndep _ bP ⟨0, by decide⟩ r (by decide)]
      rfl
    rw [Finset.sum_comm]
    trans (∑ r ∈ restSet, (((qRatio / (108 * 8)) * wRest r : ℝ) : ℂ) • restOp r)
    · refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [← Finset.sum_subset (Finset.subset_univ ({216, 217} : Finset (Fin 256)))
        fun l _ hnot ↦ by
          rw [p80NucVal_setCosetAndNuc]
          by_cases hl : l.val < 216
          · simp [hl]
          · have hlLt := l.isLt
            have h216 : l.val ≠ 216 :=
              fun h ↦ hnot (Finset.mem_insert.mpr (Or.inl (Fin.ext h)))
            have h217 : l.val ≠ 217 :=
              fun h ↦ hnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext h))))
            have h0 : mu218 (p80SetCosetAndNuc bP l r) = 0 :=
              hSupp218 (p80SetCosetAndNuc bP l r) (by
                rw [p80NucVal_setCosetAndNuc]
                omega)
            simp [hl, h0],
        Finset.sum_pair (by decide : (216 : Fin 256) ≠ 217),
        p80NucVal_setCosetAndNuc, p80NucVal_setCosetAndNuc,
        ite_eq_of_neg (by decide), ite_eq_of_neg (by decide),
        hSliceVep 216 r (by decide), hSliceVep 217 r (by decide),
        hVepVal 216 r (by decide) (by decide), hVepVal 217 r (by decide) (by decide), ← add_smul]
      exact congrArg (· • restOp r) (by push_cast; ring)
    · have hRHS : (∑ yIdx : Fin (2 ^ 24), projB yIdx *
          ∑ p : BitAssignment 80, (mu216 p : ℂ) •
            sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP))) p) =
          ∑ r ∈ restSet, (wRest r : ℂ) • ∑ yIdx : Fin (2 ^ 24), projB yIdx *
            sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP)))
              (p80SetNucZero r) := by
        refine (Finset.sum_congr rfl fun yIdx _ ↦ ?_).trans
          (Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ ↦ (Finset.smul_sum).symm))
        rw [hHostSum, Matrix.mul_sum]
        exact Finset.sum_congr rfl fun r _ ↦ Matrix.mul_smul _ _ _
      rw [hRHS, Matrix.mul_sum, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      exact congrArg (· • restOp r) (by push_cast; ring)
theorem ancBlockCollapse_symbolic_onRange {K S A : ℕ} (rSys : QRegister S K)
    (rAnc : QRegister A K) (a_c : Fin (2 ^ A)) (ancOf : BitAssignment 80 → Fin (2 ^ A))
    (hAncInj : Function.Injective ancOf)
    (idxOf : BitAssignment 80 → Fin (2 ^ S) → Fin (2 ^ K))
    (hIdxSys : ∀ p80 z, rSys.extractIndex (idxOf p80 z) = z)
    (hIdxAnc : ∀ p80 z, rAnc.extractIndex (idxOf p80 z) = ancOf p80)
    (hUniq : ∀ j p80 z, rSys.extractIndex j = z → rAnc.extractIndex j = ancOf p80 →
      j = idxOf p80 z)
    (hAgreeAnc : ∀ j r, rAnc.AgreeOutside j r ↔ rSys.extractIndex j = rSys.extractIndex r)
    (hSysAgree : ∀ row col, rAnc.extractIndex row = a_c → rAnc.extractIndex col = a_c →
      rSys.AgreeOutside row col)
    (V_eff : Unitary (2 ^ A))
    (hSupp : ∀ b : Fin (2 ^ A), b ∉ Set.range ancOf → V_eff.1 b a_c = 0)
    (M_sym : Operator (2 ^ K))
    (hDiag : ∀ j p80 x, rAnc.extractIndex j ≠ ancOf p80 → V_eff.1 (ancOf p80) a_c ≠ 0 →
      M_sym j (idxOf p80 x) = 0)
    (blk : BitAssignment 80 → Operator (2 ^ S))
    (hBlk : ∀ p80 x' x, V_eff.1 (ancOf p80) a_c ≠ 0 →
      M_sym (idxOf p80 x') (idxOf p80 x) = blk p80 x' x) :
    rAnc.basisOutcomeProjector a_c * ((rAnc.embedMatrix V_eff.1)ᴴ * M_sym *
      rAnc.embedMatrix V_eff.1) * rAnc.basisOutcomeProjector a_c =
    rAnc.basisOutcomeProjector a_c * rSys.embedMatrix (∑ p80 : BitAssignment 80,
      ((‖V_eff.1 (ancOf p80) a_c‖ ^ 2 : ℝ) : ℂ) • blk p80) *
      rAnc.basisOutcomeProjector a_c := by
  ext row col
  rw [basisOutcomeProjector_sandwich_apply, basisOutcomeProjector_sandwich_apply]
  by_cases hr : rAnc.extractIndex row = a_c
  · by_cases hc : rAnc.extractIndex col = a_c
    · simp only [hr, hc, ↓reduceIte, one_mul, mul_one]
      set x' := rSys.extractIndex row
      set x := rSys.extractIndex col
      rw [embedMatrix_entry_of_agreeOutside rSys _ (hSysAgree row col hr hc)]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      let fTerm : BitAssignment 80 → ℂ := fun p80 ↦
        ((‖V_eff.1 (ancOf p80) a_c‖ ^ 2 : ℝ) : ℂ) * blk p80 x' x
      have hInjIdx : Function.Injective (fun p80 : BitAssignment 80 ↦ idxOf p80 x) :=
        fun _ _ h ↦ hAncInj (by simpa only [hIdxAnc] using congrArg rAnc.extractIndex h)
      have hOuter (k : Fin (2 ^ K)) :
          (∑ j, star ((rAnc.embedMatrix V_eff.1) j row) * M_sym j k) *
            (rAnc.embedMatrix V_eff.1) k col =
          extendZero (fun p80 ↦ idxOf p80 x) fTerm k := by
        by_cases hkAgree : rAnc.AgreeOutside k col
        · rw [embedMatrix_entry_of_agreeOutside _ _ hkAgree, hc]
          by_cases hkRange : rAnc.extractIndex k ∈ Set.range ancOf
          · obtain ⟨p80, hp80⟩ := hkRange
            rw [hUniq k p80 x ((hAgreeAnc k col).mp hkAgree) hp80.symm,
              extendZero_apply hInjIdx fTerm p80, hIdxAnc p80 x]
            by_cases hv : V_eff.1 (ancOf p80) a_c = 0
            · simp [fTerm, hv]
            · rw [Finset.sum_eq_single (idxOf p80 x') (fun j _ hjne ↦ ?_)
                (fun habs ↦ absurd (Finset.mem_univ _) habs)]
              · rw [embedMatrix_entry_of_agreeOutside _ _
                  ((hAgreeAnc _ row).mpr (hIdxSys p80 x')),
                  hIdxAnc p80 x', hr, hBlk p80 x' x hv]
                dsimp only [fTerm]
                rw [Complex.star_def, mul_right_comm, mul_comm ((starRingEnd ℂ) _),
                  Complex.mul_conj, Complex.normSq_eq_norm_sq]
              · by_cases hjAgree : rAnc.AgreeOutside j row
                · rw [hDiag j p80 x (fun heqAnc ↦ hjne (hUniq j p80 x'
                    ((hAgreeAnc j row).mp hjAgree) heqAnc)) hv, mul_zero]
                · rw [embedMatrix_entry_of_not_agreeOutside _ _ hjAgree, star_zero, zero_mul]
          · rw [hSupp _ hkRange, mul_zero, extendZero_of_not_exists _ fTerm
              fun ⟨p, hp⟩ ↦ hkRange ⟨p, hp ▸ (hIdxAnc p x).symm⟩]
        · rw [embedMatrix_entry_of_not_agreeOutside _ _ hkAgree, mul_zero,
            extendZero_of_not_exists _ fTerm
              fun ⟨p, hp⟩ ↦ hkAgree (hp ▸ (hAgreeAnc _ col).mpr (hIdxSys p x))]
      rw [Finset.sum_congr rfl fun k _ ↦ hOuter k, sum_extendZero hInjIdx fTerm]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, fTerm]
      rfl
    · simp only [hc, ↓reduceIte, mul_zero]
  · simp only [hr, ↓reduceIte, zero_mul]
theorem zmod2_add_self_cancel (a b : ZMod 2) : (a + b) + b = a := by decide +revert
def xorCosetNucFn (delta : Fin 11 → ZMod 2) (β : BitAssignment (fullSysCoreWires 80)) :
    BitAssignment (fullSysCoreWires 80) :=
  fun q ↦
    if h : 3957 ≤ q.val ∧ q.val < 3968 then β q + delta ⟨q.val - 3957, by omega⟩ else β q
@[local simp] theorem idReg_apply {n : ℕ} (i : Fin n) : QRegExt.idReg n i = i := rfl
@[local simp] theorem ofFin_apply (n : ℕ) (i : Fin n) : QRegExt.ofFin n i = i := rfl
theorem xorCosetNucFn_pos (delta : Fin 11 → ZMod 2)
    (β : BitAssignment (fullSysCoreWires 80)) (q : Wire (fullSysCoreWires 80))
    (hq : 3957 ≤ q.val ∧ q.val < 3968) :
    xorCosetNucFn delta β q = β q + delta ⟨q.val - 3957, by omega⟩ :=
  dite_eq_of_pos hq
theorem xorCosetNucFn_neg (delta : Fin 11 → ZMod 2) (β : BitAssignment (fullSysCoreWires 80))
    (q : Wire (fullSysCoreWires 80)) (hq : ¬(3957 ≤ q.val ∧ q.val < 3968)) :
    xorCosetNucFn delta β q = β q := dite_eq_of_neg hq
theorem conj_comm_of_parts_comm {D : ℕ} (Q Tw Ph P : Operator D) (hP_sa : Pᴴ = P)
    (hQ : Q * P = P * Q) (hTw : Tw * P = P * Tw) (hPh : Ph * P = P * Ph) :
    ((Q * Tw)ᴴ * Ph * (Q * Tw)) * P = P * ((Q * Tw)ᴴ * Ph * (Q * Tw)) := by
  have hOut : (Q * Tw) * P = P * (Q * Tw) := by
    rw [Matrix.mul_assoc, hTw, ← Matrix.mul_assoc, hQ, Matrix.mul_assoc]
  have hOutAdj : (Q * Tw)ᴴ * P = P * (Q * Tw)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP_sa] using (congrArg conjTranspose hOut).symm
  rw [Matrix.mul_assoc _ (Q * Tw) P, hOut, ← Matrix.mul_assoc _ P (Q * Tw),
    Matrix.mul_assoc (Q * Tw)ᴴ _ P, hPh, ← Matrix.mul_assoc (Q * Tw)ᴴ P _, hOutAdj]
  simp only [Matrix.mul_assoc]
theorem xorCosetNucFn_involutive (delta : Fin 11 → ZMod 2) :
    Function.Involutive (xorCosetNucFn delta) := fun β ↦ funext fun q ↦ by
  by_cases h : 3957 ≤ q.val ∧ q.val < 3968
  · rw [xorCosetNucFn_pos delta _ q h, xorCosetNucFn_pos delta _ q h]
    exact zmod2_add_self_cancel (β q) _
  · rw [xorCosetNucFn_neg delta _ q h, xorCosetNucFn_neg delta _ q h]
noncomputable def xorCosetNucPerm (delta : Fin 11 → ZMod 2) :
    Equiv.Perm (Fin (2 ^ (fullSysCoreWires 80))) :=
  (basisBitsEquiv (fullSysCoreWires 80)).trans
    ((Equiv.ofBijective (xorCosetNucFn delta) (xorCosetNucFn_involutive delta).bijective).trans
      (basisBitsEquiv (fullSysCoreWires 80)).symm)
noncomputable def uXorCosetNuc (delta : Fin 11 → ZMod 2) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  Operator.permutationUnitary (xorCosetNucPerm delta)
theorem uXorCosetNuc_mulVec_ket (delta : Fin 11 → ZMod 2)
    (β : BitAssignment (fullSysCoreWires 80)) :
    (uXorCosetNuc delta).1.mulVec (ket β) = ket (xorCosetNucFn delta β) := by
  have hk (γ : BitAssignment (fullSysCoreWires 80)) :
      ket γ = (Pi.single ((basisBitsEquiv _).symm γ) (1 : ℂ) : Fin (2 ^ _) → ℂ) :=
    funext fun _ ↦ by simp [ket, basisState]
  rw [hk β, uXorCosetNuc, Operator.permutationUnitary_mulVec_single]
  have hp : xorCosetNucPerm delta ((basisBitsEquiv _).symm β) =
      (basisBitsEquiv _).symm (xorCosetNucFn delta β) := by
    change (basisBitsEquiv _).symm (xorCosetNucFn delta
      ((basisBitsEquiv _) ((basisBitsEquiv _).symm β))) = _
    rw [(basisBitsEquiv _).apply_symm_apply]
  rw [hp, ← hk]
theorem ket_eq_basisKet_local {k : ℕ} (ξ : BitAssignment k) : ket ξ = basisKet ξ :=
  funext fun _ ↦ by simp [ket, basisKet, basisState]
theorem uTwistParam_mulVec_ket_id {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (c : SpecsAux.SpecMirror.Configuration)
    (β : BitAssignment (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload)) :
    (uTwistParam swapOnSlot2 hm c).1.mulVec (ket β) =
      NuclearTwistRealizes.twistCorePhase swapOnSlot2 hm c β •
        ket (NuclearTwistRealizes.twistCorePermFn swapOnSlot2 hm β) := by
  let rId := QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload)
  rw [ket_eq_basisKet_local,
    ← congrArg Subtype.val (NuclearTwistRealizes.embedUnitary_idReg_eq (uTwistParam _ _ _))]
  refine (NuclearTwistRealizes.uTwistParam_mulVec_basisKet swapOnSlot2 hm c rId β).trans ?_
  rw [← ket_eq_basisKet_local]
  refine congrArg _ (congrArg ket (funext fun z ↦ ?_))
  have hz : z ∈ rId.image := (QRegister.mem_image rId z).mpr ⟨z, rfl⟩
  have hch : Classical.choose ((QRegister.mem_image rId z).mp hz) = z :=
    Classical.choose_spec ((QRegister.mem_image rId z).mp hz)
  simp only [hz, ↓reduceDIte, hch]
  rfl
theorem castUnitaryPow2_mulVec_ket_gen {a b : ℕ} (h : a = b) (U : Unitary (2 ^ a))
    (c : ℂ) (β γ : BitAssignment b)
    (hU : U.1.mulVec (ket (fun q : Wire a ↦ β ⟨q.val, Nat.lt_of_lt_of_eq q.isLt h⟩)) =
      c • ket (fun q : Wire a ↦ γ ⟨q.val, Nat.lt_of_lt_of_eq q.isLt h⟩)) :
    (castUnitaryPow2 h U).1.mulVec (ket β) = c • ket γ := by
  subst h
  exact hU
theorem castUnitaryPow2_comm_proj {a b m : ℕ} (h : a = b) (U : Unitary (2 ^ a))
    (rA : QRegister m a) (rB : QRegister m b) (hr : ∀ i : Fin m, (rA i).val = (rB i).val)
    (o : Fin (2 ^ m))
    (hComm : U.1 * rA.basisOutcomeProjector o = rA.basisOutcomeProjector o * U.1) :
    (castUnitaryPow2 h U).1 * rB.basisOutcomeProjector o =
      rB.basisOutcomeProjector o * (castUnitaryPow2 h U).1 := by
  subst h
  have hEq : rA = rB := QRegister.ext (Function.Embedding.ext fun i ↦ Fin.ext (hr i))
  rwa [← hEq]
lemma twistCoreWires_eq_fullSys (m : ℕ) :
    NuclearTwistAndXor654Concrete.fullSysCoreWires m = fullSysCoreWires m := rfl
noncomputable def uTwist80 (c : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  castUnitaryPow2 (twistCoreWires_eq_fullSys 80) (uTwistParam true pos24_22_le_80 c)
theorem uTwist80_mulVec_ket (c : SpecsAux.SpecMirror.Configuration)
    (β : BitAssignment (fullSysCoreWires 80)) :
    (uTwist80 c).1.mulVec (ket β) =
      NuclearTwistRealizes.twistCorePhase true pos24_22_le_80 c β •
        ket (n := fullSysCoreWires 80)
          (NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 β) :=
  castUnitaryPow2_mulVec_ket_gen (twistCoreWires_eq_fullSys 80)
    (uTwistParam true pos24_22_le_80 c) _ β _
    (uTwistParam_mulVec_ket_id true pos24_22_le_80 c _)
theorem uPosPhase80_mulVec_ket (s2 : Bool)
    (tS : Fin Dyadic128CoulombMath.orbitCount47905 → Bool)
    (tM : Fin Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment (fullSysCoreWires 80)) :
    (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhase s2 tS tM)).1.mulVec (ket β) =
      (if posPhaseBit s2 tS tM (fun q : Wire posCoreWires ↦
          β ⟨q.val, Nat.lt_of_lt_of_eq q.isLt pos24_coreWires80_eq.symm⟩)
        then (-1 : ℂ) else 1) • ket β :=
  castUnitaryPow2_mulVec_ket_gen pos24_coreWires80_eq.symm (uPosPhase s2 tS tM) _ β β
    (PosSlots24BranchConcrete.uPosPhase_mulVec_ket s2 tS tM _)
def tailPhaseOrbitBody (s0 rejBit : Bool)
    (tailSign : Fin Dyadic128CoulombMath.orbitCount47905 → Bool)
    (tailMag30 : Fin Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30))
    (keepVal : ℕ) (dTail : Dyadic128CoulombMath.FineCoord128) : Bool :=
  let rOrbit := Dyadic128CoulombMath.tetRank65 (Dyadic128CoulombMath.canonTriple128 dTail)
  if keepVal < (tailMag30 rOrbit).val then
    if !s0 then !(tailSign rOrbit) else tailSign rOrbit
  else
    rejBit
theorem tailAndSlackPhaseBitSpec_eq_orbitBody (slot2SwappedTo0 : Bool)
    (tailSign : Fin Dyadic128CoulombMath.orbitCount47905 → Bool)
    (tailMag30 : Fin Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) :
    tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β =
      let rCore := QRegExt.ofFin posCoreWires
      let b2 := β (wSlot2Core rCore) == 1
      let b1 := β (wSlot1Core rCore) == 1
      let s0 := β (wSlot0Core rCore) == 1
      if b2 then false
      else if b1 then s0
      else
        let nucOk :=
          !s0 →
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
          (PosSlots24BranchConcrete.rNucIdx rCore) β < 216
        let ancOk :=
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
          (PosSlots24BranchConcrete.rAnchorIdx rCore) β < 218
        let partOk := (s0 && !(β (PosSlots24BranchConcrete.wIsHead rCore) == 1)) →
            _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
              (PosSlots24BranchConcrete.rPartnerIdx rCore) β < 217
        let accept : Bool := !(β (PosSlots24BranchConcrete.wSubReject rCore) == 1) && decide
            nucOk && ancOk && decide partOk
        if !accept then
          β (PosSlots24BranchConcrete.wRejectZero rCore) == 1
        else if β (PosSlots24BranchConcrete.wIsHead rCore) == 1 then
          false
        else
          let iIdx :=
            _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
            (PosSlots24BranchConcrete.rAnchorIdx rCore) β
          let mIdx :=
            _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
            (PosSlots24BranchConcrete.rPartnerIdx rCore) β
          let ySlot2 := if slot2SwappedTo0 then PosSlots24BranchConcrete.slotSubGridCoord64
              (PosSlots24BranchConcrete.rElecSlot rCore 0) β else
              PosSlots24BranchConcrete.slotSubGridCoord64 (PosSlots24BranchConcrete.rElecSlot
              rCore ⟨iIdx % 218, Nat.mod_lt _ (by omega)⟩) β
          let y0 := PosSlots24BranchConcrete.slotSubGridCoord64
            (PosSlots24BranchConcrete.rElecSlot rCore 0) β
          let y1 := PosSlots24BranchConcrete.slotSubGridCoord64
            (PosSlots24BranchConcrete.rElecSlot rCore
              ⟨(mIdx % 217) + 1, by have := Nat.mod_lt mIdx (by omega : 0 < 217); omega⟩) β
          let coset1 := PosSlots24BranchConcrete.parity3OfReg
            (PosSlots24BranchConcrete.rCosetB1 rCore) β
          let coset0 := PosSlots24BranchConcrete.parity3OfReg
            (PosSlots24BranchConcrete.rCosetB0 rCore) β
          let dTail : Dyadic128CoulombMath.FineCoord128 := fun w ↦
            if !s0 then
              ⟨2 * (ySlot2 w).val + (if coset1 w then 1 else 0), by
                have := (ySlot2 w).isLt
                split_ifs <;> omega⟩
            else
              ⟨(2 * (y0 w).val + (if coset0 w then 1 else 0) + 128 -
                (2 * (y1 w).val + (if coset1 w then 1 else 0))) % 128,
                Nat.mod_lt _ (by omega)⟩
          tailPhaseOrbitBody s0 (β (PosSlots24BranchConcrete.wRejectZero rCore) == 1)
            tailSign tailMag30
            (_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
              (PosSlots24BranchConcrete.rTailKeep30 rCore) β) dTail :=
  rfl
theorem wire_not_mem_coreElecCosetB1 {mPayload : ℕ} {hm6 : 6 ≤ mPayload}
    (q : Wire (fullSysCoreWires mPayload))
    (hq : (3924 ≤ q.val ∧ q.val < 3954) ∨ 3957 ≤ q.val) :
    q ∉ Set.range (coreElecCosetB1Block hm6).wires := by
  rintro ⟨idx, hidx⟩
  refine Fin.addCases
    (motive := fun idx ↦ ((coreElecCosetB1Block hm6).wires idx).val = q.val → False)
    (fun a hv ↦ ?_) (fun b hv ↦ ?_) idx (congrArg Fin.val hidx)
  · rw [coreElecCosetB1Block, QRegister.concat_apply_left] at hv
    have ha : a.val < 3924 := a.isLt
    change 0 + a.val = q.val at hv
    omega
  · rw [coreElecCosetB1Block, QRegister.concat_apply_right] at hv
    have hb : b.val < 3 := b.isLt
    change 3954 + b.val = q.val at hv
    omega
abbrev idTw80 : QRegister (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)
    (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) :=
  QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)
abbrev wS2Tw80 : Wire (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) := wSlot2 idTw80
abbrev wS1Tw80 : Wire (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) := wSlot1 idTw80
abbrev wS0Tw80 : Wire (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) := wSlot0 idTw80
abbrev rNucTw80 : QRegister 8 (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) :=
  rNucIdx pos24_22_le_80 idTw80
abbrev rAncTw80 : QRegister 8 (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) :=
  rAnchorIdx pos24_22_le_80 idTw80
def projIndepDelta (p1 p2 : BitAssignment 80) : Fin 11 → ZMod 2 := fun k ↦
  p1 ⟨3 + k.val, by omega⟩ + p2 ⟨3 + k.val, by omega⟩
def goodPred0Core (γ : BitAssignment (fullSysCoreWires 80)) : Prop :=
  γ wS2Tw80 = 0 ∧ γ wS1Tw80 = 0 ∧ γ wS0Tw80 = 0 ∧
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal rNucTw80 γ = 0
open Classical in
noncomputable def pGood0CoreMat : Operator (2 ^ (fullSysCoreWires 80)) :=
  Matrix.diagonal fun x ↦ if goodPred0Core (basisBits _ x) then (1 : ℂ) else 0
def coreBetaTw80 (p0 : BitAssignment 80) (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    BitAssignment (fullSysCoreWires 80) :=
  fun q ↦ coreBetaOf false p0 z ⟨q.val, pos24_coreWires80_eq ▸ q.isLt⟩
open Classical in
theorem pGood0CoreMat_mulVec_ket (γ : BitAssignment (fullSysCoreWires 80)) :
    pGood0CoreMat.mulVec (ket γ) = if goodPred0Core γ then ket γ else 0 := by
  have hk : ket γ = (Pi.single ((basisBitsEquiv _).symm γ) (1 : ℂ) : Fin (2 ^ _) → ℂ) :=
    funext fun _ ↦ by simp [ket, basisState]
  unfold pGood0CoreMat
  rw [hk, Matrix.diagonal_mulVec_single, (basisBitsEquiv _).apply_symm_apply γ]
  split_ifs <;> simp
theorem projIndep_good_beta2 (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    goodPred0Core (coreBetaTw80 (p80SetNucZero p) z) := by
  set p2 := p80SetNucZero p
  refine ⟨PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false p2 z
      ⟨3950, by decide⟩ (by decide) (by decide),
    PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false p2 z
      ⟨3949, by decide⟩ (by decide) (by decide),
    (PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false p2 z
      ⟨3948, by decide⟩ (by decide) (by decide)).trans (by decide), ?_⟩
  unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  let jSub : Fin PosSlots24BranchConcrete.posPayloadWires :=
    ⟨6 + i.val, by change 6 + i.val < 80; clear z; omega⟩
  have hw : (⟨(rNucTw80 i).val, pos24_coreWires80_eq ▸ (rNucTw80 i).isLt⟩ : Wire posCoreWires) =
      rPosSubLocal jSub := Fin.ext (by change 3960 + i.val = 3954 + (6 + i.val); clear z; omega)
  change (coreBetaOf false p2 z _).val * 2 ^ i.val = 0
  rw [hw, PosSlots24SemanticOracleConcrete80.coreBetaOf_payload]
  have hi : 6 ≤ 6 + i.val ∧ 6 + i.val < 14 := by clear z hw; omega
  simp [jSub, p2, p80SetNucZero, hi]
theorem projIndep_mapBeta (bP : Fin 3 → Fin 2) (l : Fin 256) (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    xorCosetNucFn (projIndepDelta (p80SetCosetAndNuc bP l p) (p80SetNucZero p))
      (coreBetaTw80 (p80SetNucZero p) z) = coreBetaTw80 (p80SetCosetAndNuc bP l p) z := by
  set p1 := p80SetCosetAndNuc bP l p
  set p2 := p80SetNucZero p
  set delta := projIndepDelta p1 p2
  have hpcw : posCoreWires = 4034 := rfl
  have hfcw : fullSysCoreWires 80 = 4034 := rfl
  funext q
  let qc : Wire posCoreWires := ⟨q.val, pos24_coreWires80_eq ▸ q.isLt⟩
  by_cases hq : 3957 ≤ q.val ∧ q.val < 3968
  · rw [xorCosetNucFn_pos delta _ q hq]
    let jSub : Fin 80 := ⟨q.val - 3954, by clear z qc; omega⟩
    have hsub : qc = rPosSubLocal jSub :=
      Fin.ext (by change q.val = 3954 + (q.val - 3954); clear z qc; omega)
    change coreBetaOf false p2 z qc + delta ⟨q.val - 3957, by clear hsub z qc; omega⟩ =
      coreBetaOf false p1 z qc
    rw [hsub, PosSlots24SemanticOracleConcrete80.coreBetaOf_payload,
      PosSlots24SemanticOracleConcrete80.coreBetaOf_payload]
    dsimp only [delta, projIndepDelta]
    rw [show (⟨3 + (q.val - 3957), by clear hsub z qc; omega⟩ : Fin 80) = jSub from
      Fin.ext (by dsimp [jSub]; clear hsub z qc; omega)]
    exact (by decide : ∀ x y : ZMod 2, y + (x + y) = x) (p1 jSub) (p2 jSub)
  · rw [xorCosetNucFn_neg delta _ q hq]
    change coreBetaOf false p2 z qc = coreBetaOf false p1 z qc
    by_cases hsub : qc ∈ Set.range rPosSubLocal.wires
    · obtain ⟨j, hj⟩ := hsub
      rw [← hj, PosSlots24SemanticOracleConcrete80.coreBetaOf_payload,
        PosSlots24SemanticOracleConcrete80.coreBetaOf_payload]
      have hqj : q.val = 3954 + j.val := (congrArg Fin.val hj).symm
      simp [p1, p2, p80SetCosetAndNuc, p80SetNucZero,
        show ¬(3 ≤ j.val ∧ j.val < 6) by clear hj qc z; omega,
        show ¬(6 ≤ j.val ∧ j.val < 14) by clear hj qc z; omega]
    · unfold coreBetaOf
      rw [PosSlots24TopWrapper.writeSubBits_apply_not_mem _ _ _ _ (fun j h ↦ hsub ⟨j, h.symm⟩),
        PosSlots24TopWrapper.writeSubBits_apply_not_mem _ _ _ _ (fun j h ↦ hsub ⟨j, h.symm⟩)]
theorem projIndep_commQft (delta : Fin 11 → ZMod 2)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) :
    (uXorCosetNuc delta).1 * (fullSysQftCoreUnitary pos24_6_le_80 qft).1 =
      (fullSysQftCoreUnitary pos24_6_le_80 qft).1 * (uXorCosetNuc delta).1 := by
  let r11 : QRegister 11 (fullSysCoreWires 80) := QRegister.block 3957 11 (by decide)
  let f11 : BitAssignment 11 → BitAssignment 11 := fun b k ↦ b k + delta k
  have hf11 : Function.Bijective f11 :=
    Function.Involutive.bijective fun b ↦ funext fun k ↦ zmod2_add_self_cancel (b k) (delta k)
  let perm11 : Equiv.Perm (Fin (2 ^ 11)) :=
    (basisBitsEquiv 11).trans ((Equiv.ofBijective f11 hf11).trans (basisBitsEquiv 11).symm)
  have hUX_reg : uXorCosetNuc delta = r11.embedUnitary (Operator.permutationUnitary perm11) := by
    apply Subtype.ext
    apply matrix_ext_ket_sym
    intro β
    rw [uXorCosetNuc_mulVec_ket, ket_eq_basisKet_local β, ket_eq_basisKet_local]
    symm
    refine NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet r11 perm11 β
      (xorCosetNucFn delta β) (fun k ↦ ?_) (fun q hnot ↦ ?_)
    · rw [NuclearTwistRealizes.basisBits_perm_ofBijective f11 hf11 _ k]
      have hr11 : (r11 k).val = 3957 + k.val := rfl
      rw [xorCosetNucFn_pos delta β (r11 k) (by omega),
        show (⟨(r11 k).val - 3957, by omega⟩ : Fin 11) = k from Fin.ext (by dsimp; omega)]
    · exact xorCosetNucFn_neg delta β q fun hq ↦
        hnot ((QRegister.mem_image r11 q).mpr ⟨⟨q.val - 3957, by omega⟩,
          Fin.ext (by change 3957 + (q.val - 3957) = q.val; omega)⟩)
  rw [hUX_reg, fullSysQftCoreUnitary, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  exact QRegister.embedMatrix_comm_of_disjoint r11 _
    (QRegister.disjoint_iff.mpr fun i idx heq ↦ wire_not_mem_coreElecCosetB1 (r11 i)
      (Or.inr (by change 3957 ≤ 3957 + i.val; omega)) ⟨idx, heq.symm⟩) _ _
theorem projIndep_good_xor_nuc (bP : Fin 3 → Fin 2) (l : Fin 256) (p : BitAssignment 80)
    (γ : BitAssignment (fullSysCoreWires 80)) (hg : goodPred0Core γ) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal rNucTw80
      (xorCosetNucFn (projIndepDelta (p80SetCosetAndNuc bP l p) (p80SetNucZero p)) γ) =
      l.val := by
  set p1 := p80SetCosetAndNuc bP l p
  set p2 := p80SetNucZero p
  set delta := projIndepDelta p1 p2
  have hbits0 (i : Fin 8) : γ (rNucTw80 i) = 0 := by
    have hsum0 := hg.2.2.2
    unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal at hsum0
    exact ZMod.val_injective 2 ((Nat.mul_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ Nat.zero_le _).mp hsum0 i
        (Finset.mem_univ i))).resolve_right (Nat.two_pow_pos i.val).ne')
  refine
    (?_ : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal rNucTw80
    (xorCosetNucFn delta γ) = p80NucVal p1).trans
    (p80NucVal_setCosetAndNuc bP l p)
  unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal p80NucVal
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (· * 2 ^ i.val) ?_
  have hrn : (rNucTw80 i).val = 3960 + i.val := rfl
  change (xorCosetNucFn delta γ (rNucTw80 i)).val = _
  rw [xorCosetNucFn_pos delta γ (rNucTw80 i) (by omega), hbits0 i, zero_add]
  dsimp only [delta, projIndepDelta]
  rw [show (⟨3 + ((rNucTw80 i).val - 3957), by omega⟩ : Fin 80) = ⟨6 + i.val, by omega⟩ from
    Fin.ext (by dsimp; omega),
    show p2 ⟨6 + i.val, by omega⟩ = 0 by
      simp [p2, p80SetNucZero, show 6 ≤ 6 + i.val ∧ 6 + i.val < 14 by omega], add_zero]
theorem projIndep_twist_on_good (zP : NyqFine3D512) (bP : Fin 3 → Fin 2)
    (l : Fin 256) (p : BitAssignment 80) (hl : l.val < 216)
    (γ : BitAssignment (fullSysCoreWires 80)) (hg : goodPred0Core γ) :
    let delta := projIndepDelta (p80SetCosetAndNuc bP l p) (p80SetNucZero p)
    (uTwist80 (cfgProjZ512 zP)).1.mulVec (ket (xorCosetNucFn delta γ)) =
      (uXorCosetNuc delta).1.mulVec
        ((uTwist80 (cfgProjZ512 zP)).1.mulVec (ket γ)) := by
  intro delta
  have hfcw : fullSysCoreWires 80 = 4034 := rfl
  rw [uTwist80_mulVec_ket, uTwist80_mulVec_ket, Matrix.mulVec_smul,
    uXorCosetNuc_mulVec_ket]
  let η := NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ
  have hBar : NuclearTwistRealizes.barrelBitFn true pos24_22_le_80 (xorCosetNucFn delta γ) =
      xorCosetNucFn delta (NuclearTwistRealizes.barrelBitFn true pos24_22_le_80 γ) := by
    funext q
    have hOut (β : BitAssignment (fullSysCoreWires 80)) (k : Wire (fullSysCoreWires 80))
        (hk : ¬(3957 ≤ k.val ∧ k.val < 3968)) : xorCosetNucFn delta β k = β k :=
      xorCosetNucFn_neg delta β k hk
    have hAct : NuclearTwistRealizes.barrelActive true (xorCosetNucFn delta γ) =
        NuclearTwistRealizes.barrelActive true γ := by
      unfold NuclearTwistRealizes.barrelActive
      rw [hOut γ wS2Tw80 (by decide), hOut γ wS1Tw80 (by decide), hOut γ wS0Tw80 (by decide)]
    have hAnch : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal rAncTw80
      (xorCosetNucFn delta γ) =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal rAncTw80 γ :=
      regVal_eq_of_wire_eq rAncTw80 _ _ fun i ↦ hOut γ _
        (by have := i.isLt; change ¬(3957 ≤ 3968 + i.val ∧ 3968 + i.val < 3968); omega)
    by_cases hq : 3957 ≤ q.val ∧ q.val < 3968
    · rw [NuclearTwistRealizes.barrelBitFn_high_eq true pos24_22_le_80 _ q (by omega),
        xorCosetNucFn_pos delta _ q hq, xorCosetNucFn_pos delta _ q hq,
        NuclearTwistRealizes.barrelBitFn_high_eq true pos24_22_le_80 γ q (by omega)]
    · rw [hOut _ q hq]
      unfold NuclearTwistRealizes.barrelBitFn
      simp only [hAct, hAnch]
      split_ifs with hc
      · dsimp only
        split_ifs
        · exact hOut γ _ (by dsimp only; have := hc.2; omega)
        · exact hOut γ _ (by dsimp only; omega)
        · exact hOut γ q hq
      · exact hOut γ q hq
  have hPermEq : NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 (xorCosetNucFn delta γ) =
      xorCosetNucFn delta η := by
    dsimp only [η]
    unfold NuclearTwistRealizes.twistCorePermFn
    rw [hBar]
    funext q
    unfold xorCosetNucFn NuclearTwistRealizes.xor32BitFn
    by_cases hq : 3957 ≤ q.val ∧ q.val < 3968
    · simp [hq, show ¬ q.val < 3924 by omega]
    · simp [hq]
  have hgη : goodPred0Core η := by
    unfold goodPred0Core η
    have hHi := NuclearTwistRealizes.twistCorePermFn_high_eq true pos24_22_le_80 γ
    rw [hHi wS2Tw80 (by decide), hHi wS1Tw80 (by decide), hHi wS0Tw80 (by decide),
      regVal_eq_of_wire_eq rNucTw80 _ γ fun i ↦
        hHi _ (by change 3924 ≤ 3960 + i.val; omega)]
    exact hg
  have hPhEq : NuclearTwistRealizes.twistCorePhase true pos24_22_le_80 (cfgProjZ512 zP)
      (xorCosetNucFn delta γ) =
      NuclearTwistRealizes.twistCorePhase true pos24_22_le_80 (cfgProjZ512 zP) γ := by
    unfold NuclearTwistRealizes.twistCorePhase
    change NuclearTwistAndXor654Concrete.dyadicTurn 48
        (NuclearTwistRealizes.slot4TotalPhaseExp pos24_22_le_80
          (NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 (xorCosetNucFn delta γ)) +
        NuclearTwistRealizes.slot2TotalPhaseExp (cfgProjZ512 zP) pos24_22_le_80
          (NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 (xorCosetNucFn delta γ))) =
      NuclearTwistAndXor654Concrete.dyadicTurn 48
        (NuclearTwistRealizes.slot4TotalPhaseExp pos24_22_le_80 η +
        NuclearTwistRealizes.slot2TotalPhaseExp (cfgProjZ512 zP) pos24_22_le_80 η)
    rw [hPermEq]
    have hOut (k : Wire (fullSysCoreWires 80)) (hk : ¬(3957 ≤ k.val ∧ k.val < 3968)) :
        xorCosetNucFn delta η k = η k := xorCosetNucFn_neg delta η k hk
    have hs4 (ξ : BitAssignment (fullSysCoreWires 80)) (h0 : ξ wS0Tw80 = 0) :
        NuclearTwistRealizes.slot4TotalPhaseExp pos24_22_le_80 ξ = 0 := by
      unfold NuclearTwistRealizes.slot4TotalPhaseExp
      exact ite_eq_of_neg fun h ↦ absurd (h0.symm.trans h.2.2) (by decide)
    rw [hs4 η hgη.2.2.1, hs4 _ ((hOut wS0Tw80 (by decide)).trans hgη.2.2.1), zero_add, zero_add]
    refine congrArg (NuclearTwistAndXor654Concrete.dyadicTurn 48) ?_
    unfold NuclearTwistRealizes.slot2TotalPhaseExp NuclearTwistRealizes.slot2AxisDelta
    refine Finset.sum_congr rfl fun w _ ↦ congrArg Int.ofNat (congrArg₂ (· * ·) ?_ ?_)
    · exact Finset.sum_congr rfl fun e _ ↦ regVal_eq_of_wire_eq _ _ _ fun j ↦ hOut _ (by
        have he : e.val < 218 := e.isLt
        have hw : w.val < 3 := w.isLt
        have hj : j.val < 6 := j.isLt
        change ¬(3957 ≤ (18 * e.val + 6 * w.val) + j.val ∧ _)
        omega)
    · have hc0_0 : NuclearTwistRealizes.coin0Active η = true :=
        decide_eq_true ⟨hgη.1, hgη.2.1, hgη.2.2.1⟩
      have hc0_1 : NuclearTwistRealizes.coin0Active (xorCosetNucFn delta η) = true := by
        unfold NuclearTwistRealizes.coin0Active
        rw [hOut wS2Tw80 (by decide), hOut wS1Tw80 (by decide), hOut wS0Tw80 (by decide)]
        exact hc0_0
      unfold NuclearTwistRealizes.slot2M48Val
      rw [dite_eq_of_pos ⟨hc0_1, by rw [projIndep_good_xor_nuc bP l p η hgη]; exact hl⟩,
        dite_eq_of_pos ⟨hc0_0, by rw [hgη.2.2.2]; omega⟩,
        ProjZ512QftAndTwist288.nuclearM48_cfgProjZ512_eq,
        ProjZ512QftAndTwist288.nuclearM48_cfgProjZ512_eq]
  rw [hPermEq, hPhEq]
theorem projIndep_phOnGood (tS : Fin Dyadic128CoulombMath.orbitCount47905 → Bool)
    (tM : Fin Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30)) (bP : Fin 3 → Fin 2)
    (l : Fin 256) (p : BitAssignment 80) (hl : l.val < 216)
    (γ : BitAssignment (fullSysCoreWires 80)) (hg : goodPred0Core γ) :
    posPhaseBit true tS tM
      (xorCosetNucFn (projIndepDelta (p80SetCosetAndNuc bP l p) (p80SetNucZero p)) γ) =
      posPhaseBit true tS tM γ := by
  set delta := projIndepDelta (p80SetCosetAndNuc bP l p) (p80SetNucZero p)
  let rCore := QRegExt.ofFin posCoreWires
  let γ' : BitAssignment posCoreWires := xorCosetNucFn delta γ
  let γ0 : BitAssignment posCoreWires := γ
  have hOut (k : Wire posCoreWires) (hk : ¬(3957 ≤ k.val ∧ k.val < 3968)) : γ' k = γ0 k :=
    xorCosetNucFn_neg delta γ k hk
  have hRegOut {m : ℕ} (r : QRegister m posCoreWires)
      (hr : ∀ i : Fin m, ¬(3957 ≤ (r i).val ∧ (r i).val < 3968)) :
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal r γ' =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal r γ0 :=
    regVal_eq_of_wire_eq r γ' γ0 fun i ↦ hOut _ (hr i)
  have hNucCore (η : BitAssignment (fullSysCoreWires 80)) :
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        (PosSlots24BranchConcrete.rNucIdx rCore) η =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal rNucTw80 η := by
    unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun b : ZMod 2 ↦ b.val * 2 ^ i.val)
      (congrArg η (Fin.ext (by change 3954 + (6 + i.val) = 3960 + i.val; omega)))
  have hw2_0 : γ0 (wSlot2Core rCore) = 0 := hg.1
  have hw1_0 : γ0 (wSlot1Core rCore) = 0 := hg.2.1
  have hw0_0 : γ0 (wSlot0Core rCore) = 0 := hg.2.2.1
  have hw2_1 : γ' (wSlot2Core rCore) = 0 := (hOut _ (by decide)).trans hw2_0
  have hw1_1 : γ' (wSlot1Core rCore) = 0 := (hOut _ (by decide)).trans hw1_0
  have hw0_1 : γ' (wSlot0Core rCore) = 0 := (hOut _ (by decide)).trans hw0_0
  have hnuc1 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    (PosSlots24BranchConcrete.rNucIdx rCore) γ' < 216 := by
    rw [hNucCore, projIndep_good_xor_nuc bP l p γ hg]
    exact hl
  have hnuc0 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    (PosSlots24BranchConcrete.rNucIdx rCore) γ0 < 216 := by
    rw [hNucCore, hg.2.2.2]
    omega
  have hslot (e : Fin 218) : PosSlots24BranchConcrete.slotSubGridCoord64
      (PosSlots24BranchConcrete.rElecSlot rCore e) γ' =
      PosSlots24BranchConcrete.slotSubGridCoord64
        (PosSlots24BranchConcrete.rElecSlot rCore e) γ0 :=
    funext fun w ↦ Fin.ext (hRegOut _ fun i ↦ by
      have he := e.isLt
      have hw := w.isLt
      have hi := i.isLt
      change ¬(3957 ≤ 18 * e.val + (6 * w.val + (5 - i.val)) ∧ _)
      omega)
  have hanc := hRegOut (PosSlots24BranchConcrete.rAnchorIdx rCore) fun i ↦ by
    have := i.isLt
    change ¬(3957 ≤ 3954 + (14 + i.val) ∧ 3954 + (14 + i.val) < 3968)
    omega
  have hhead21 : CanonRank7Circuit.fineCoordOfReg21
      (PosSlots24BranchConcrete.rHeadFine21 rCore) γ' =
      CanonRank7Circuit.fineCoordOfReg21 (PosSlots24BranchConcrete.rHeadFine21 rCore) γ0 :=
    funext fun w ↦ Fin.ext (hRegOut _ fun i ↦ by
      have hw := w.isLt
      have hi := i.isLt
      change ¬(3957 ≤ 3954 + (32 + (7 * w.val + i.val)) ∧
        3954 + (32 + (7 * w.val + i.val)) < 3968)
      omega)
  have hkeep30 := hRegOut (PosSlots24BranchConcrete.rTailKeep30 rCore) fun i ↦ by
    have := i.isLt
    change ¬(3957 ≤ 3954 + (32 + i.val) ∧ 3954 + (32 + i.val) < 3968)
    omega
  have hpar1 : PosSlots24BranchConcrete.parity3OfReg
      (PosSlots24BranchConcrete.rCosetB1 rCore) γ' =
      PosSlots24BranchConcrete.parity3OfReg (PosSlots24BranchConcrete.rCosetB1 rCore) γ0 :=
    funext fun w ↦ congrArg (fun b ↦ decide (b = 1)) (hOut _ (by
      have := w.isLt
      change ¬(3957 ≤ 3954 + (0 + w.val) ∧ _)
      omega))
  have hwRej := hOut (PosSlots24BranchConcrete.wSubReject rCore) (by decide)
  have hwIsH := hOut (PosSlots24BranchConcrete.wIsHead rCore) (by decide)
  have hwThr := hOut (PosSlots24BranchConcrete.wHeadThresh rCore) (by decide)
  have hwRejZ := hOut (PosSlots24BranchConcrete.wRejectZero rCore) (by decide)
  dsimp only [rCore] at hw2_0 hw1_0 hw0_0 hw2_1 hw1_1 hw0_1 hnuc1 hnuc0 hslot hanc
  dsimp only [rCore] at hhead21 hkeep30 hpar1 hwRej hwIsH hwThr hwRejZ
  have hHead : headPhaseBitSpec γ' = headPhaseBitSpec γ0 := by
    unfold headPhaseBitSpec
    dsimp only
    simp only [hw2_1, hw1_1, hw0_1, hw2_0, hw1_0, hw0_0, beq_self_eq_true,
      show ((0 : ZMod 2) == 1) = false by decide, ↓reduceIte, Bool.not_false, Bool.true_and,
      imp_true_iff, hnuc1, hnuc0, decide_true, hwRej, hwIsH, hwThr, hanc, hhead21, hslot,
      Bool.true_or]
  have hTail : tailAndSlackPhaseBitSpec true tS tM γ' =
      tailAndSlackPhaseBitSpec true tS tM γ0 := by
    rw [tailAndSlackPhaseBitSpec_eq_orbitBody true tS tM γ',
      tailAndSlackPhaseBitSpec_eq_orbitBody true tS tM γ0]
    dsimp only
    simp only [hw2_1, hw1_1, hw0_1, hw2_0, hw1_0, hw0_0,
      show ((0 : ZMod 2) == 1) = false by decide, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.false_and, false_implies, imp_true_iff, hnuc1, hnuc0, decide_true,
      Bool.and_true, hwRej, hwIsH, hwRejZ, hanc, hslot 0, hpar1, hkeep30]
  unfold posPhaseBit
  rw [hHead, hTail]
theorem sysBlock80_projIndep (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (zP : NyqFine3D512) (bP : Fin 3 → Fin 2) (l : Fin 256) (p : BitAssignment 80)
    (hl : l.val < 216) : sysBlock80 qft (cfgProjZ512 zP) false (p80SetCosetAndNuc bP l p) =
    sysBlock80 qft (cfgProjZ512 zP) false (p80SetNucZero p) := by
  let Q : Operator (2 ^ (fullSysCoreWires 80)) := (fullSysQftCoreUnitary pos24_6_le_80 qft).1
  let Tw : Operator (2 ^ (fullSysCoreWires 80)) := (uTwist80 (cfgProjZ512 zP)).1
  let P_ph : Operator (2 ^ (fullSysCoreWires 80)) :=
    (castUnitaryPow2 pos24_coreWires80_eq.symm
      (uPosPhase true pos24TailSign pos24TailMag30)).1
  let U_fwd : Operator (2 ^ (fullSysCoreWires 80)) := Q * Tw
  let p1 := p80SetCosetAndNuc bP l p
  let p2 := p80SetNucZero p
  let delta := projIndepDelta p1 p2
  let UX := (uXorCosetNuc delta).1
  have hentry (M : Operator (2 ^ (fullSysCoreWires 80)))
      (βa βb : BitAssignment (fullSysCoreWires 80)) :
      M ((basisBitsEquiv _).symm βa) ((basisBitsEquiv _).symm βb) =
        dotProduct (star (ket βa)) (M.mulVec (ket βb)) := by
    have hk (γ : BitAssignment (fullSysCoreWires 80)) :
        ket γ = Pi.single ((basisBitsEquiv _).symm γ) (1 : ℂ) :=
      funext fun _ ↦ by simp [ket, basisState]
    rw [hk βa, hk βb, Matrix.mulVec_single_one]
    simp [dotProduct, Pi.single_apply]
  have hAdjDot (A : Operator (2 ^ (fullSysCoreWires 80)))
      (u v : Fin (2 ^ (fullSysCoreWires 80)) → ℂ) :
      dotProduct (star u) (Aᴴ.mulVec v) = dotProduct (star (A.mulVec u)) v := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
  have hFwdMap (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      U_fwd.mulVec (ket (coreBetaTw80 p1 z)) =
        UX.mulVec (U_fwd.mulVec (ket (coreBetaTw80 p2 z))) := by
    rw [← projIndep_mapBeta bP l p z]
    dsimp only [U_fwd, Q, Tw, UX]
    rw [← Matrix.mulVec_mulVec,
      projIndep_twist_on_good zP bP l p hl _ (projIndep_good_beta2 p z),
      Matrix.mulVec_mulVec, ← projIndep_commQft delta qft]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, p2]
  have hCommP0_qft : Q * pGood0CoreMat = pGood0CoreMat * Q := by
    dsimp only [Q]
    rw [fullSysQftCoreUnitary, QRegister.embedUnitary_val, pGood0CoreMat]
    refine PosMomSelectDynamic.embedMatrix_comm_diagonal_of_outside
      (coreElecCosetB1Block pos24_6_le_80) qft.uQft654.1 _ fun row col hag ↦ ?_
    have hgiff : goodPred0Core (basisBits _ row) ↔ goodPred0Core (basisBits _ col) := by
      unfold goodPred0Core
      rw [hag wS2Tw80 (wire_not_mem_coreElecCosetB1 _ (Or.inl (by decide))),
        hag wS1Tw80 (wire_not_mem_coreElecCosetB1 _ (Or.inl (by decide))),
        hag wS0Tw80 (wire_not_mem_coreElecCosetB1 _ (Or.inl (by decide))),
        regVal_eq_of_wire_eq rNucTw80
          (basisBits (fullSysCoreWires 80) row) (basisBits (fullSysCoreWires 80) col) fun i ↦
            hag _ (wire_not_mem_coreElecCosetB1 _
              (Or.inr (by change 3957 ≤ 3960 + i.val; omega)))]
    by_cases hg : goodPred0Core (basisBits _ row)
    · rw [ite_eq_of_pos hg, ite_eq_of_pos (hgiff.mp hg)]
    · rw [ite_eq_of_neg hg, ite_eq_of_neg (mt hgiff.mpr hg)]
  have hPh_on_P0 : P_ph * UX * pGood0CoreMat = UX * P_ph * pGood0CoreMat :=
    matrix_ext_ket_sym fun γ ↦ by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pGood0CoreMat_mulVec_ket γ]
      by_cases hg : goodPred0Core γ
      · have hBitEq : posPhaseBit true pos24TailSign pos24TailMag30
            (fun q : Wire posCoreWires ↦ xorCosetNucFn delta γ
              ⟨q.val, Nat.lt_of_lt_of_eq q.isLt pos24_coreWires80_eq.symm⟩) =
            posPhaseBit true pos24TailSign pos24TailMag30
              (fun q : Wire posCoreWires ↦
                γ ⟨q.val, Nat.lt_of_lt_of_eq q.isLt pos24_coreWires80_eq.symm⟩) :=
          projIndep_phOnGood pos24TailSign pos24TailMag30 bP l p hl γ hg
        rw [ite_eq_of_pos hg, uXorCosetNuc_mulVec_ket,
          uPosPhase80_mulVec_ket true pos24TailSign pos24TailMag30 (xorCosetNucFn delta γ),
          uPosPhase80_mulVec_ket true pos24TailSign pos24TailMag30 γ,
          Matrix.mulVec_smul, uXorCosetNuc_mulVec_ket]
        exact congrArg
          (fun b : Bool ↦ (if b then (-1 : ℂ) else 1) • ket (xorCosetNucFn delta γ)) hBitEq
      · simp [ite_eq_of_neg hg]
  have hCoreIdx (p0 : BitAssignment 80) (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      coreIdxOf pos24_coreWires80_eq.symm false p0 z =
        (basisBitsEquiv (fullSysCoreWires 80)).symm (coreBetaTw80 p0 z) := by
    apply (basisBitsEquiv (fullSysCoreWires 80)).injective
    funext q
    rw [(basisBitsEquiv (fullSysCoreWires 80)).apply_symm_apply]
    exact (basisBitsEquiv posCoreWires).apply_symm_apply (coreBetaOf false p0 z) ▸ rfl
  have hConjEq : (pos24ConjCore80 qft (cfgProjZ512 zP)).1 = U_fwdᴴ * P_ph * U_fwd := rfl
  ext x' x
  rw [sysBlock80, sysBlock80, PosSlots24SemanticOracleConcrete80.sysBlockAtPayloadGen_apply,
    PosSlots24SemanticOracleConcrete80.sysBlockAtPayloadGen_apply, hConjEq,
    hCoreIdx p1 x', hCoreIdx p1 x, hCoreIdx p2 x', hCoreIdx p2 x,
    hentry (U_fwdᴴ * P_ph * U_fwd), hentry (U_fwdᴴ * P_ph * U_fwd)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mulVec_mulVec (ket (coreBetaTw80 p1 x)),
    ← Matrix.mulVec_mulVec (ket (coreBetaTw80 p2 x)),
    ← Matrix.mulVec_mulVec (ket (coreBetaTw80 p1 x)),
    ← Matrix.mulVec_mulVec (ket (coreBetaTw80 p2 x)),
    hAdjDot U_fwd, hAdjDot U_fwd, hFwdMap x', hFwdMap x]
  have hwP0 : pGood0CoreMat.mulVec (U_fwd.mulVec (ket (coreBetaTw80 p2 x))) =
      U_fwd.mulVec (ket (coreBetaTw80 p2 x)) := by
    dsimp only [U_fwd, Tw]
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hCommP0_qft, ← Matrix.mulVec_mulVec,
      uTwist80_mulVec_ket, Matrix.mulVec_smul, pGood0CoreMat_mulVec_ket]
    have hg0 := projIndep_good_beta2 p x
    have hHi := NuclearTwistRealizes.twistCorePermFn_high_eq true pos24_22_le_80
      (coreBetaTw80 p2 x)
    have hgη : goodPred0Core (NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80
        (coreBetaTw80 p2 x)) := by
      unfold goodPred0Core
      rw [hHi wS2Tw80 (by decide), hHi wS1Tw80 (by decide), hHi wS0Tw80 (by decide),
        regVal_eq_of_wire_eq rNucTw80 _ _ fun i ↦
          hHi _ (by change 3924 ≤ 3960 + i.val; omega)]
      exact hg0
    rw [ite_eq_of_pos hgη]
  have hPhAct : P_ph.mulVec (UX.mulVec (U_fwd.mulVec (ket (coreBetaTw80 p2 x)))) =
      UX.mulVec (P_ph.mulVec (U_fwd.mulVec (ket (coreBetaTw80 p2 x)))) := by
    conv_lhs => rw [← hwP0]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPh_on_P0, ← Matrix.mulVec_mulVec, hwP0,
      ← Matrix.mulVec_mulVec]
  rw [hPhAct, ← hAdjDot UX, Matrix.mulVec_mulVec,
    show UXᴴ * UX = 1 by
      simpa only [UX, Matrix.star_eq_conjTranspose] using
        Unitary.coe_star_mul_self (uXorCosetNuc delta),
    Matrix.one_mulVec]
theorem basisBits_cast_pow2 {a b : ℕ} (h : a = b) (u : Fin (2 ^ a)) (q : Wire b) :
    basisBits b (h ▸ u) q = basisBits a u ⟨q.val, h ▸ q.isLt⟩ := by
  subst h
  rfl
theorem sysBlock80_projDiag (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (s0 : Bool) (p : BitAssignment 80)
    (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hne : mProj24_sp.extractIndex x' ≠ mProj24_sp.extractIndex x) :
    sysBlock80 qft cfg s0 p x' x = 0 := by
  let M_gen := (pos24ConjCore80 qft cfg).1
  let rProjC : QRegister 24 (fullSysCoreWires 80) := QRegister.block 3924 24 (by decide)
  have hCommAll (a : Fin (2 ^ 24)) :
      M_gen * rProjC.basisOutcomeProjector a = rProjC.basisOutcomeProjector a * M_gen := by
    let P := rProjC.basisOutcomeProjector a
    have hDisjQ : (coreElecCosetB1Block pos24_6_le_80).DisjointWires rProjC :=
      QRegister.disjoint_iff.mpr fun idx j h ↦
        wire_not_mem_coreElecCosetB1 (rProjC j) (Or.inl (by
          have := j.isLt
          change 3924 ≤ 3924 + j.val ∧ 3924 + j.val < 3954
          omega)) ⟨idx, h⟩
    let rProjTw : QRegister 24 (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) :=
      QRegister.block 3924 24 (by decide)
    have hDisjTw : (NuclearTwistAndXor654Concrete.rElecCore (QRegExt.ofFin
        (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))).DisjointWires rProjTw :=
      QRegister.disjoint_iff.mpr fun i j hij ↦ by
        have hv := congrArg Fin.val hij
        have hi : i.val < 3924 := i.isLt
        change 0 + i.val = 3924 + j.val at hv
        omega
    have hTwP : (uTwist80 cfg).1 * P = P * (uTwist80 cfg).1 := by
      have hcomm := NuclearTwistRealizes.uTwistParam_comm_highReg_proj true pos24_22_le_80 cfg
        (QRegExt.ofFin (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)) rProjTw hDisjTw a
      rw [PosSlots24SemanticOracleConcrete80.ofFin_embedUnitary_eq] at hcomm
      exact castUnitaryPow2_comm_proj (twistCoreWires_eq_fullSys 80)
        (uTwistParam true pos24_22_le_80 cfg) rProjTw rProjC (fun _ ↦ rfl) a hcomm
    have hConjEq : M_gen = ((fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
        (uTwist80 cfg).1)ᴴ *
        (castUnitaryPow2 pos24_coreWires80_eq.symm
          (uPosPhase true pos24TailSign pos24TailMag30)).1 *
        ((fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
          (uTwist80 cfg).1) := rfl
    rw [hConjEq]
    exact conj_comm_of_parts_comm _ _ _ P
      (QRegister.basisOutcomeProjector_conjTranspose _ _)
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        (coreElecCosetB1Block pos24_6_le_80) rProjC hDisjQ qft.uQft654.1 a)
      hTwP (by
        dsimp only [P]
        rw [QRegister.basisOutcomeProjector_eq_diagonal]
        exact uPosPhase_cast_comm_diagonal pos24_coreWires80_eq.symm true _ _ _)
  have hExtr (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      rProjC.extractIndex (coreIdxOf pos24_coreWires80_eq.symm s0 p z) =
        mProj24_sp.extractIndex z := by
    apply (basisBitsEquiv 24).injective
    funext i
    change basisBits 24 (rProjC.extractIndex (coreIdxOf pos24_coreWires80_eq.symm s0 p z)) i =
      basisBits 24 (mProj24_sp.extractIndex z) i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      PosSlots24SemanticOracleConcrete80.coreIdxOf,
      basisBits_cast_pow2 pos24_coreWires80_eq.symm,
      (basisBitsEquiv posCoreWires).apply_symm_apply]
    exact (congrArg (coreBetaOf s0 p z) (Fin.ext rfl)).trans
      (PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 s0 p z (mProj24_sp i))
  rw [sysBlock80, PosSlots24SemanticOracleConcrete80.sysBlockAtPayloadGen_apply]
  refine entry_zero_of_comm_basisOutcomeProjector rProjC M_gen hCommAll _ _ ?_
  rwa [hExtr x', hExtr x]
theorem diagonal_mulVec_apply {α : Type*} [Fintype α] [DecidableEq α] (d w : α → ℂ) (i : α) :
    (Matrix.diagonal d).mulVec w i = d i * w i := by
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
theorem norm_sum_proj_mul_blockDiag_le_one {S m : ℕ} (r : QRegister m S)
    (A : Fin (2 ^ m) → Operator (2 ^ S)) (hNorm : ∀ y, ‖A y‖ ≤ 1)
    (hDiag : ∀ y i j, r.extractIndex i ≠ r.extractIndex j → A y i j = 0) :
    ‖∑ y : Fin (2 ^ m), r.basisOutcomeProjector y * A y‖ ≤ 1 := by
  let M : Operator (2 ^ S) := ∑ y : Fin (2 ^ m), r.basisOutcomeProjector y * A y
  have hPoint (v : Fin (2 ^ S) → ℂ) (i : Fin (2 ^ S)) : (M.mulVec v) i =
      ((A (r.extractIndex i)).mulVec
        ((r.basisOutcomeProjector (r.extractIndex i)).mulVec v)) i := by
    have hSum : (M.mulVec v) i = ((A (r.extractIndex i)).mulVec v) i := by
      dsimp only [M]
      rw [Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_eq_single (r.extractIndex i)
        (fun y _ hy ↦ by
          rw [QRegister.basisOutcomeProjector_eq_diagonal, ← Matrix.mulVec_mulVec,
            diagonal_mulVec_apply]
          simp [hy.symm])
        (fun habs ↦ absurd (Finset.mem_univ _) habs),
        QRegister.basisOutcomeProjector_eq_diagonal, ← Matrix.mulVec_mulVec, diagonal_mulVec_apply]
      simp
    rw [hSum]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    change A (r.extractIndex i) i j * v j = A (r.extractIndex i) i j *
      ((Matrix.diagonal fun z ↦ if r.extractIndex z = r.extractIndex i then (1 : ℂ)
        else 0).mulVec v j)
    rw [diagonal_mulVec_apply]
    by_cases hji : r.extractIndex j = r.extractIndex i
    · simp [hji]
    · rw [ite_eq_of_neg hji, hDiag _ i j (Ne.symm hji), zero_mul, zero_mul]
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  change ‖(Matrix.toEuclideanLin M) v‖ ≤ 1 * ‖v‖
  rw [one_mul]
  have hsq : ‖(Matrix.toEuclideanLin M) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_fiberwise_of_maps_to (g := r.extractIndex) (fun _ _ ↦ Finset.mem_univ _),
      ← Finset.sum_fiberwise_of_maps_to (g := r.extractIndex) (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    let v_y : EuclideanSpace ℂ (Fin (2 ^ S)) := Matrix.toEuclideanLin (r.basisOutcomeProjector y) v
    have hSub : (∑ i ∈ Finset.univ.filter (fun z ↦ r.extractIndex z = y),
        ‖((Matrix.toEuclideanLin M) v) i‖ ^ 2) ≤ ‖(Matrix.toEuclideanLin (A y)) v_y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans_le
        (Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _)
      change ‖(M.mulVec v) i‖ ^ 2 =
        ‖((A y).mulVec ((r.basisOutcomeProjector y).mulVec v)) i‖ ^ 2
      rw [hPoint v i, (Finset.mem_filter.mp hi).2]
    have hAy : ‖(Matrix.toEuclideanLin (A y)) v_y‖ ≤ ‖v_y‖ :=
      (ContinuousLinearMap.le_opNorm
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A y))) v_y).trans
        (mul_le_of_le_one_left (norm_nonneg v_y) (hNorm y))
    have hVySq : ‖v_y‖ ^ 2 =
        ∑ i ∈ Finset.univ.filter (fun z ↦ r.extractIndex z = y), ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change ‖((r.basisOutcomeProjector y).mulVec v) i‖ ^ 2 = _
      rw [QRegister.basisOutcomeProjector_eq_diagonal, diagonal_mulVec_apply]
      by_cases hi : r.extractIndex i = y <;> simp [hi]
    linarith [pow_le_pow_left₀ (norm_nonneg _) hAy 2]
  nlinarith [norm_nonneg ((Matrix.toEuclideanLin M) v), norm_nonneg v]
theorem norm_unitary_le_one {D : ℕ} (U : Unitary D) : ‖U.1‖ ≤ 1 :=
  NuclearTwistAndXor654Concrete.l2_opNorm_unitary_le_one U
theorem norm_conj_unitary_le_one {D : ℕ} (U : Unitary D) (S : Operator D)
    (hMid : ‖S‖ ≤ 1) : ‖U.1ᴴ * S * U.1‖ ≤ 1 := by
  have hU : ‖U.1‖ ≤ 1 := norm_unitary_le_one U
  have hUadj : ‖U.1ᴴ‖ ≤ 1 := by rwa [← Matrix.star_eq_conjTranspose, norm_star]
  exact ((Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))).trans
    ((mul_le_mul (mul_le_mul hUadj hMid (norm_nonneg _) zero_le_one) hU
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
noncomputable abbrev mergedCoherentOp80 (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (mu : BitAssignment 80 → ℝ) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  mergedCoherentOpGen (fun c' p' ↦ sysBlock80 qft c' false p') cfg mu
noncomputable abbrev coreUnitarySym {mPayload : ℕ}
    (U : Unitary (2 ^ (fullSysCoreWires mPayload))) : Unitary (2 ^ (coreWiresSym mPayload)) :=
  coreUnitaryFromFullSys U
abbrev topCoinPropGen {mPayload mWorkPos : ℕ} (hm80 : 80 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : SpecsAux.SpecMirror.Configuration)
    (post : PosPostPrepCert mPayload)
    (uTwistRef : Configuration → Unitary (2 ^ (fullSysCoreWires mPayload)))
    (posData : PosSlots24DataGen (fullSysCoreWires mPayload) (iSlot2 mPayload) mWorkPos)
    (c : Fin 8) (B : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) : Prop :=
  let P_anc := (coreAncSym mPayload).basisOutcomeProjector
    (coinSelOutcome (selCoin3Sym mPayload) c)
  let U_out := fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) hm80) qft * uTwistRef cfg
  P_anc * (unitaryConj (post.uPosPost * coreHadamardUnitary mPayload)
      (coreUnitaryFromFullSys (unitaryConj U_out (posData.uPosPhase cfg)))).1 * P_anc =
    P_anc * (coreSysSym mPayload).embedMatrix B * P_anc
theorem topCoinPropGen_of_collapse {mPayload mWorkPos : ℕ} (hm80 : 80 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : SpecsAux.SpecMirror.Configuration)
    (post : PosPostPrepCert mPayload) (V_eff : Unitary (2 ^ (selWiresSym mPayload)))
    (uTwistRef : Configuration → Unitary (2 ^ (fullSysCoreWires mPayload)))
    (posData : PosSlots24DataGen (fullSysCoreWires mPayload) (iSlot2 mPayload) mWorkPos)
    (c : Fin 8) (B : Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hVeff : post.uPosPost * coreHadamardUnitary mPayload =
      (coreAncSym mPayload).embedUnitary V_eff)
    (hEq :
      let P_anc := (coreAncSym mPayload).basisOutcomeProjector
        (coinSelOutcome (selCoin3Sym mPayload) c)
      let U_out := fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) hm80) qft * uTwistRef cfg
      P_anc * (((coreAncSym mPayload).embedMatrix V_eff.1)ᴴ *
          (coreUnitarySym (unitaryConj U_out (posData.uPosPhase cfg))).1 *
          (coreAncSym mPayload).embedMatrix V_eff.1) * P_anc =
        P_anc * (coreSysSym mPayload).embedMatrix B * P_anc) :
    topCoinPropGen hm80 qft cfg post uTwistRef posData c B := by
  dsimp only [topCoinPropGen]
  rwa [unitaryConj_val, hVeff, QRegister.embedUnitary_val]
set_option maxRecDepth 512
end Opts
end MergedVepTopCoinCollapse
end
end ModMergedVepTopCoinCollapse

section ModMergedVepCoreSliceClosure
@[expose] public section
namespace MergedVepCoreSliceClosureAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n)
    (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k)
    (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end MergedVepCoreSliceClosureAlt
namespace MergedVepCoreSliceClosure
section ConfigMergedVepCoreSliceClosure
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowCoreSliceClosure (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
theorem msc_congr2 {α β γ : Sort*} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
    (ha : a₁ = a₂) (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ := ha ▸ hb ▸ rfl
theorem msc_ite_pos {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t := ite_eq_left hc
theorem msc_ite_neg {c : Prop} {h : Decidable c} (hnc : ¬ c) {α : Sort*} {t e : α} :
    (if c then t else e) = e := ite_eq_right hnc
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror (
  Configuration electronBits numElectrons projectileBits systemQubits)
open MeasureBranchHadamardSem (ket)
open FullSysCatSegmentBridge (
  fullSysCoreWires fullSysQftCoreUnitary coreCosetB1Block coreElecCosetB1Block)
open SpecsAux.DyadicSubgridToeplitz512AndShift (nyq512ProjEquiv3D)
open PosMomSelectSandwich (slotBitProj)
open NuclearTwistAndXor654Concrete (wSlot0 wSlot1 wSlot2 rNucIdx)
open NuclearTwistRealizes (uTwistParam)
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24SemanticBridge (
  mulUnitaryPow2 pos24_6_le_80 pos24_22_le_80 pos24_coreWires80_eq)
open PosSlots24SemanticOracleConcrete80 (
  QftPreservesCoset3 coreWiresSym80_eq_fullSys hkSym80 coreBetaOf coreIdxOf
  embedMatrix_entry_of_agreeOutside embedMatrix_entry_of_not_agreeOutside rAncFlag80
  entry_zero_of_comm_basisOutcomeProjector regVal_eq_of_wire_eq)
open FullSysFullPrepareAndTopConcrete (coreAncSym)
open OraAndPrepBundle (coreUnitaryFromFullSys)
open ProjZ512QftAndTwist288 (
  cfgProjZ512 projGridEquiv24 uProjPlus512_3D rProjCore extractProj24 extractCosetP3
  vepHighNuc vepHighNuc_iff vepWriteReg uVepTwistRef uVepTwistRef_comm_high_wire
  vepSwapNuc vepSwapNuc_mulVec_basisKet uVepTwistRef_host_eq uVepTwistRef_vep_eq)
open MergedVepTopCoinCollapse (
  mProj24_sp mProjGridEquiv24 mProjBasisGen mProjBasisGen_eq_basisOutcomeProjector
  mWCoreScrGen p80NucVal p80NucVal_lt_256 p80CosetP3 p80SetNucZero mergedSliceGen
  coreUnitarySym)
noncomputable def mscUVepTwistRef {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) := uVepTwistRef hm c
noncomputable def mscUTwistParam {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (c : Configuration) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uTwistParam swapOnSlot2 hm c
noncomputable def mscVepSwapNuc {mPayload : ℕ} (hm : 22 ≤ mPayload) (lVal : Fin (2 ^ 8)) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) := vepSwapNuc hm lVal
abbrev mscRNucCore {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    QRegister 8 (fullSysCoreWires mPayload) := rNucIdx hm (QRegExt.idReg _)
abbrev mscRProjCore {mPayload : ℕ} : QRegister 24 (fullSysCoreWires mPayload) :=
  rProjCore (QRegExt.idReg _)
abbrev mscExtractProj24 {mPayload : ℕ} (γ : BitAssignment (fullSysCoreWires mPayload)) :
    Fin (2 ^ 24) := extractProj24 γ
abbrev mscExtractCosetP3 {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Fin 3 → Fin 2 := extractCosetP3 hm γ
abbrev mscVepHighNuc {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Bool := vepHighNuc hm γ
abbrev mscWSlot0 {mPayload : ℕ} : Wire (fullSysCoreWires mPayload) := wSlot0 (QRegExt.idReg _)
abbrev mscWSlot1 {mPayload : ℕ} : Wire (fullSysCoreWires mPayload) := wSlot1 (QRegExt.idReg _)
abbrev mscWSlot2 {mPayload : ℕ} : Wire (fullSysCoreWires mPayload) := wSlot2 (QRegExt.idReg _)
abbrev mscCoreBeta (s0 : Bool) (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : BitAssignment (fullSysCoreWires 80) :=
  coreBetaOf s0 p z
theorem matrix_ext_of_ket_core {N : ℕ} {A B : Operator (2 ^ N)}
    (h : ∀ β : BitAssignment N, A.mulVec (ket β) = B.mulVec (ket β)) : A = B :=
  MergedVepTopCoinCollapse.matrix_ext_ket_sym h
lemma msc_ket_eq_single {k : ℕ} (γ : BitAssignment k) :
    ket γ = (Pi.single ((basisBitsEquiv k).symm γ) (1 : ℂ) : Fin (2 ^ k) → ℂ) :=
  funext fun _ ↦ by simp [MeasureBranchHadamardSem.ket, basisState]
lemma msc_ket_eq_basisKet {k : ℕ} (γ : BitAssignment k) : ket γ = basisKet γ :=
  msc_ket_eq_single γ
lemma msc_basisBits_symm {k : ℕ} (γ : BitAssignment k) :
    basisBits k ((basisBitsEquiv k).symm γ) = γ :=
  (basisBitsEquiv k).apply_symm_apply γ
lemma msc_diagonal_mulVec_ket {k : ℕ} (d : BitAssignment k → ℂ) (γ : BitAssignment k) :
    (Matrix.diagonal fun u ↦ d (basisBits k u)).mulVec (ket γ) = d γ • ket γ := by
  funext u
  rw [msc_ket_eq_single γ, Matrix.diagonal_mulVec_single, mul_one, msc_basisBits_symm γ,
    Pi.smul_apply, smul_eq_mul]
  by_cases hu : u = (basisBitsEquiv k).symm γ <;> simp [hu]
lemma msc_entry_eq_dotProduct {k : ℕ} (M : Operator (2 ^ k)) (βa βb : BitAssignment k) :
    M ((basisBitsEquiv k).symm βa) ((basisBitsEquiv k).symm βb) =
      dotProduct (star (ket βa)) (M.mulVec (ket βb)) := by
  rw [msc_ket_eq_single βa, msc_ket_eq_single βb, Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]
lemma msc_adj_dotProduct {D : ℕ} (A : Operator D) (u v : Fin D → ℂ) :
    dotProduct (star u) (Aᴴ.mulVec v) = dotProduct (star (A.mulVec u)) v := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
lemma msc_mul2_comm {D : ℕ} (A B P : Operator D) (hA : A * P = P * A) (hB : B * P = P * B) :
    (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
lemma msc_conj3_entry_eq_dotProduct {k : ℕ} (U Ph : Operator (2 ^ k))
    (βa βb : BitAssignment k) :
    (Uᴴ * Ph * U) ((basisBitsEquiv k).symm βa) ((basisBitsEquiv k).symm βb) =
      dotProduct (star (U.mulVec (ket βa))) (Ph.mulVec (U.mulVec (ket βb))) := by
  rw [msc_entry_eq_dotProduct (Uᴴ * Ph * U) βa βb, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, msc_adj_dotProduct, ← Matrix.mulVec_mulVec]
lemma msc_conj_entry_eq_of_proj {K : ℕ} (U1 U2 Ph1 Ph2 P : Operator (2 ^ K))
    (βa βb : BitAssignment K) (hKetA : U1.mulVec (ket βa) = U2.mulVec (ket βa))
    (hKetB : U1.mulVec (ket βb) = U2.mulVec (ket βb)) (hComm : U2 * P = P * U2)
    (hPB : P.mulVec (ket βb) = ket βb) (hPh : Ph1 * P = Ph2 * P) :
    (U1ᴴ * Ph1 * U1) ((basisBitsEquiv K).symm βa) ((basisBitsEquiv K).symm βb) =
      (U2ᴴ * Ph2 * U2) ((basisBitsEquiv K).symm βa) ((basisBitsEquiv K).symm βb) := by
  rw [msc_conj3_entry_eq_dotProduct U1 Ph1 βa βb, msc_conj3_entry_eq_dotProduct U2 Ph2 βa βb,
    hKetA, hKetB]
  have hvP : P.mulVec (U2.mulVec (ket βb)) = U2.mulVec (ket βb) := by
    rw [Matrix.mulVec_mulVec, ← hComm, ← Matrix.mulVec_mulVec, hPB]
  congr 1
  rw [← hvP, Matrix.mulVec_mulVec, hPh, ← Matrix.mulVec_mulVec, hvP]
open Classical in
lemma msc_conj_entry_eq_finset_sum_of_orth_proj {D : ℕ} {J : Type*} {s : Finset J}
    {sA sB : J → Fin D → ℂ} {out : J → ℂ} (U1 Ph1 Ph2 SW : Operator D) (P_B : J → Operator D)
    (α β mid : J → ℂ) (idxa idxb : Fin D) (v0a v0b : Fin D → ℂ) (vHa vHb : J → Fin D → ℂ)
    (hEntry : (U1ᴴ * Ph1 * U1) idxa idxb =
      dotProduct (star (U1.mulVec v0a)) (Ph1.mulVec (U1.mulVec v0b)))
    (hSWUnit : SWᴴ * SW = 1) (hFwdA : U1.mulVec v0a = s.sum sA)
    (hFwdB : U1.mulVec v0b = s.sum sB) (hsA : ∀ y, sA y = α y • SW.mulVec (vHa y))
    (hsB : ∀ y, sB y = β y • SW.mulVec (vHb y)) (hvInA : ∀ y, (P_B y).mulVec (vHa y) = vHa y)
    (hvInB : ∀ y, (P_B y).mulVec (vHb y) = vHb y)
    (hPhSW : ∀ y, Ph1 * (SW * P_B y) = SW * (Ph2 * P_B y))
    (hDComm : ∀ y, Ph2 * P_B y = P_B y * Ph2)
    (hOrth : ∀ {y' y : J}, y' ≠ y → (P_B y')ᴴ * P_B y = 0)
    (hMid : ∀ y, dotProduct (star (vHa y)) (Ph2.mulVec (vHb y)) = mid y)
    (hout : ∀ y, star (α y) * mid y * β y = out y) :
    (U1ᴴ * Ph1 * U1) idxa idxb = s.sum out := by
  have hActSum : Ph1.mulVec (s.sum sB) = s.sum fun y ↦ β y • SW.mulVec (Ph2.mulVec (vHb y)) := by
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [hsB y, Matrix.mulVec_smul]
    congr 1
    rw [← hvInB y, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc Ph1 SW (P_B y), hPhSW y, ← Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvInB y]
  have hPairDot (y' y : J) :
      dotProduct (star (SW.mulVec (vHa y'))) (SW.mulVec (Ph2.mulVec (vHb y))) =
        if y' = y then mid y else 0 := by
    rw [← msc_adj_dotProduct, Matrix.mulVec_mulVec, hSWUnit, Matrix.one_mulVec]
    by_cases hy : y' = y
    · subst hy
      rw [msc_ite_pos rfl, hMid y']
    · rw [msc_ite_neg hy]
      have hR : Ph2.mulVec (vHb y) = (P_B y).mulVec (Ph2.mulVec (vHb y)) := by
        conv_lhs => rw [← hvInB y]
        rw [Matrix.mulVec_mulVec, hDComm y, ← Matrix.mulVec_mulVec]
      rw [← hvInA y', hR, ← msc_adj_dotProduct, Matrix.mulVec_mulVec, hOrth hy,
        Matrix.zero_mulVec, dotProduct_zero]
  rw [hEntry, hFwdA, hFwdB, hActSum, star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun yIdx hyIdx ↦ ?_
  rw [hsA yIdx, dotProduct_sum, Finset.sum_eq_single yIdx]
  · rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      hPairDot yIdx yIdx, msc_ite_pos rfl, ← hout yIdx]
    ring
  · intro y _ hy
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      hPairDot yIdx y, msc_ite_neg (Ne.symm hy)]
    ring
  · exact fun habs ↦ absurd hyIdx habs
lemma msc_comm_basisOutcomeProjector_of_wires {K m : ℕ} (r : QRegister m K)
    (U : Operator (2 ^ K))
    (hWire : ∀ (i : Fin m) (b : Fin 2), U * slotBitProj (r i) b = slotBitProj (r i) b * U)
    (a : Fin (2 ^ m)) :
    U * r.basisOutcomeProjector a = r.basisOutcomeProjector a * U := by
  ext row col
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h0 : U row col = 0
  · simp [h0]
  · have hEq : r.extractIndex row = r.extractIndex col := by
      apply (basisBitsEquiv m).injective
      funext i
      change basisBits m (r.extractIndex row) i = basisBits m (r.extractIndex col) i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      let b : Fin 2 := ⟨(basisBits K col (r i)).val, ZMod.val_lt _⟩
      have hc := congrFun (congrFun (hWire i b) row) col
      unfold slotBitProj at hc
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, msc_ite_pos rfl, mul_one] at hc
      by_cases hrow_b : (basisBits K row (r i)).val = b.val
      · exact ZMod.val_injective 2 hrow_b
      · rw [msc_ite_neg hrow_b, zero_mul] at hc
        exact absurd hc h0
    rw [hEq]
    ring
lemma msc_uVepTwistRef_comm_rAncFlag80 (cfg : Configuration) (a : Fin (2 ^ 86)) :
    (mscUVepTwistRef pos24_22_le_80 cfg).1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (mscUVepTwistRef pos24_22_le_80 cfg).1 :=
  msc_comm_basisOutcomeProjector_of_wires rAncFlag80 (mscUVepTwistRef pos24_22_le_80 cfg).1
    (fun i b ↦ uVepTwistRef_comm_high_wire pos24_22_le_80 cfg (rAncFlag80 i)
      (PosSlots24SemanticOracleConcrete80.rAncFlag80_wire_ge_3948 i) b) a
lemma msc_qft_comm_rAncFlag80 (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (hQft : QftPreservesCoset3 qft) (a : Fin (2 ^ 86)) :
    (fullSysQftCoreUnitary pos24_6_le_80 qft).1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (fullSysQftCoreUnitary pos24_6_le_80 qft).1 := by
  obtain ⟨o3, o83, hfac⟩ :=
    PosSlots24SemanticOracleConcrete80.rAncFlag80_basisOutcomeProjector_factor a
  have h3 : (fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
      (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3 =
      (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3 *
        (fullSysQftCoreUnitary pos24_6_le_80 qft).1 := by
    rw [← PosSlots24SemanticOracleConcrete80.coreElecCosetB1_compose_rCoset3,
      PosSlots24SemanticOracleConcrete80.basisOutcomeProjector_compose_local,
      fullSysQftCoreUnitary, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, hQft o3, QRegister.embedMatrix_mul]
  have h83 := QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
    (coreElecCosetB1Block pos24_6_le_80) PosSlots24SemanticOracleConcrete80.rAncRest83
    PosSlots24SemanticOracleConcrete80.coreElecCosetB1_disjoint_rAncRest83 qft.uQft654.1 o83
  rw [hfac, ← Matrix.mul_assoc, h3, Matrix.mul_assoc]
  dsimp only [fullSysQftCoreUnitary, QRegister.embedUnitary_val]
  rw [h83, ← Matrix.mul_assoc]
lemma msc_coreUnitary_eq_castNatOp_gen {m : ℕ}
    (hSym : fullSysCoreWires m = FullSysFullPrepareAndTopConcrete.coreWiresSym m)
    (U : Unitary (2 ^ (fullSysCoreWires m))) :
    (coreUnitarySym U).1 = OraAndPrepBundle.castNatOp hSym U.1 := by
  unfold coreUnitarySym OraAndPrepBundle.coreUnitaryFromFullSys
  have hgen {a b : ℕ} (h1 : b = a) (h2 : a = b) (W : Unitary (2 ^ a)) :
      (OraAndPrepBundle.castNatUnitary h1.symm W).1 =
        OraAndPrepBundle.castNatOp h2 W.1 := by
    subst h2
    cases Subsingleton.elim h1 rfl
    rfl
  exact hgen (OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires m) hSym U
lemma msc_coreUnitary_eq_castNatOp (U : Unitary (2 ^ (fullSysCoreWires 80))) :
    (coreUnitarySym U).1 = OraAndPrepBundle.castNatOp coreWiresSym80_eq_fullSys U.1 :=
  msc_coreUnitary_eq_castNatOp_gen coreWiresSym80_eq_fullSys U
lemma msc_rAncFlag80_val_eq (i : Fin 86) : (rAncFlag80 i).val = ((coreAncSym 80) i).val := by
  dsimp [rAncFlag80, coreAncSym, MergedVepCoreSliceClosureAlt.qreg_block_apply,
    MergedVepCoreSliceClosureAlt.qreg_block_wires_apply,
    MergedVepCoreSliceClosureAlt.qreg_whole_wires,
    MergedVepCoreSliceClosureAlt.emb_trans_apply,
    MergedVepCoreSliceClosureAlt.emb_refl_apply,
    MergedVepCoreSliceClosureAlt.emb_mk_apply,
    systemQubits, numElectrons, electronBits, projectileBits]
lemma msc_cast_basisBits_symm {a b : ℕ} (h : a = b) (β : BitAssignment a) :
    (h ▸ (basisBitsEquiv a).symm β : Fin (2 ^ b)) =
      (basisBitsEquiv b).symm fun q : Wire b ↦ β ⟨q.val, h ▸ q.isLt⟩ := by
  subst h
  rfl
lemma msc_transport_core_props {kFlag kSym : ℕ} (hSym : kFlag = kSym)
    (rAnc0 : QRegister 86 kFlag) (rAncSym : QRegister 86 kSym)
    (hrAnc : ∀ i : Fin 86, (rAnc0 i).val = (rAncSym i).val) (M0 : Operator (2 ^ kFlag))
    (hDiag0 : ∀ row col : Fin (2 ^ kFlag), rAnc0.extractIndex row ≠ rAnc0.extractIndex col →
      M0 row col = 0)
    (hk : posCoreWires = kFlag) (s0 : Bool) :
    (∀ row col : Fin (2 ^ kSym), rAncSym.extractIndex row ≠ rAncSym.extractIndex col →
      OraAndPrepBundle.castNatOp hSym M0 row col = 0) ∧
    (∀ (p80 : BitAssignment 80) (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)),
      OraAndPrepBundle.castNatOp hSym M0 (coreIdxOf (hk.trans hSym) s0 p80 x')
        (coreIdxOf (hk.trans hSym) s0 p80 x) =
      M0 ((basisBitsEquiv kFlag).symm fun q ↦ coreBetaOf s0 p80 x' ⟨q.val, hk.symm ▸ q.isLt⟩)
        ((basisBitsEquiv kFlag).symm fun q ↦ coreBetaOf s0 p80 x ⟨q.val, hk.symm ▸ q.isLt⟩)) := by
  subst hSym
  subst hk
  rw [← MergedVepCoreSliceClosureAlt.qreg_ext fun i ↦ Fin.ext (hrAnc i)]
  exact ⟨hDiag0, fun _ _ _ ↦ rfl⟩
lemma msc_transport_entry_of_comm (M : Unitary (2 ^ (fullSysCoreWires 80)))
    (hComm : ∀ a : Fin (2 ^ 86), M.1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * M.1)
    (s0 : Bool) (p : BitAssignment 80) (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (coreUnitarySym M).1 (coreIdxOf hkSym80 s0 p x') (coreIdxOf hkSym80 s0 p x) =
      M.1 ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x'))
        ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x)) := by
  have hTr := (msc_transport_core_props coreWiresSym80_eq_fullSys rAncFlag80 (coreAncSym 80)
    msc_rAncFlag80_val_eq M.1 (entry_zero_of_comm_basisOutcomeProjector rAncFlag80 M.1 hComm)
    pos24_coreWires80_eq.symm s0).2 p x' x
  have hkEq : hkSym80 = pos24_coreWires80_eq.symm.trans coreWiresSym80_eq_fullSys :=
    Subsingleton.elim _ _
  have hBetaEq (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      (fun q : Wire (fullSysCoreWires 80) ↦
        coreBetaOf s0 p z ⟨q.val, pos24_coreWires80_eq ▸ q.isLt⟩) = mscCoreBeta s0 p z :=
    funext fun _ ↦ congrArg (coreBetaOf s0 p z) (Fin.ext rfl)
  refine (congrFun (congrFun (msc_coreUnitary_eq_castNatOp M)
    (coreIdxOf hkSym80 s0 p x')) (coreIdxOf hkSym80 s0 p x)).trans ?_
  rwa [hkEq, ← hBetaEq x', ← hBetaEq x]
lemma msc_unitary_adj_mul_self {D : ℕ} (U : Unitary D) : U.1ᴴ * U.1 = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
open Classical in
noncomputable def mscDiagPred {K : ℕ} (P : BitAssignment K → Prop) : Operator (2 ^ K) :=
  Matrix.diagonal fun u ↦ if P (basisBits K u) then (1 : ℂ) else 0
open Classical in
lemma mscDiagPred_mulVec_ket {K : ℕ} (P : BitAssignment K → Prop) (γ : BitAssignment K) :
    (mscDiagPred P).mulVec (ket γ) = (if P γ then (1 : ℂ) else 0) • ket γ :=
  msc_diagonal_mulVec_ket (fun β ↦ if P β then (1 : ℂ) else 0) γ
lemma msc_fullSysQft_pf_congr {mPayload : ℕ} (hm1 hm2 : 6 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) :
    fullSysQftCoreUnitary hm1 qft = fullSysQftCoreUnitary hm2 qft :=
  Subsingleton.elim hm1 hm2 ▸ rfl
lemma msc_mulUnitaryPow2_qft_twist {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (hm22 : 22 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : Configuration)
    (hEq : fullSysCoreWires mPayload = SpecsAux.SpecMirror.systemQubits + 6 + mPayload) :
    (mulUnitaryPow2 (fullSysQftCoreUnitary hm6 qft) (uTwistParam true hm22 cfg) hEq).1 =
      (fullSysQftCoreUnitary hm6 qft * mscUTwistParam true hm22 cfg).1 := by
  cases Subsingleton.elim hEq rfl
  rfl
lemma msc_uVepTwistRef_host_ket {mPayload : ℕ} (hm : 22 ≤ mPayload) (cfg : Configuration)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (hvFalse : mscVepHighNuc hm γ = false) :
    (mscUVepTwistRef hm cfg).1.mulVec (ket γ) =
      (mscUTwistParam true hm cfg).1.mulVec (ket γ) := by
  rw [msc_ket_eq_basisKet]
  exact uVepTwistRef_host_eq hm cfg γ hvFalse
lemma msc_uVepTwistRef_vep_ket {mPayload : ℕ} (hm : 22 ≤ mPayload) (cfg : Configuration)
    (lVal : Fin (2 ^ 8)) (γ : BitAssignment (fullSysCoreWires mPayload))
    (hvTrue : mscVepHighNuc hm γ = true)
    (hNucZ : (mscRNucCore hm).extractIndex ((basisBitsEquiv _).symm γ) = lVal) :
    (mscUVepTwistRef hm cfg).1.mulVec (ket γ) = ∑ yIdx : Fin (2 ^ 24),
      (uProjPlus512_3D (mscExtractCosetP3 hm γ)).1 yIdx (mscExtractProj24 γ) •
      (mscVepSwapNuc hm lVal).1.mulVec ((mscUTwistParam true hm (cfgProjZ512
        (nyq512ProjEquiv3D (projGridEquiv24 yIdx, mscExtractCosetP3 hm γ)))).1.mulVec
        ((mscVepSwapNuc hm lVal).1.mulVec
          (ket (vepWriteReg γ mscRProjCore (basisBits 24 yIdx))))) := by
  unfold mscUVepTwistRef mscUTwistParam mscVepSwapNuc
  rw [msc_ket_eq_basisKet γ]
  refine (uVepTwistRef_vep_eq hm cfg lVal γ hvTrue hNucZ).trans
    (Finset.sum_congr rfl fun yIdx _ ↦ ?_)
  rw [msc_ket_eq_basisKet, Submonoid.coe_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
lemma msc_vepSwapNuc_mulVec_ket {mPayload : ℕ} (hm : 22 ≤ mPayload) (lVal : Fin (2 ^ 8))
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (mscVepSwapNuc hm lVal).1.mulVec (ket γ) = ket (vepWriteReg γ (mscRNucCore hm)
      (basisBits 8 (Equiv.swap 0 lVal
        ((mscRNucCore hm).extractIndex ((basisBitsEquiv _).symm γ))))) := by
  rw [msc_ket_eq_basisKet, msc_ket_eq_basisKet]
  exact vepSwapNuc_mulVec_basisKet hm lVal γ
lemma msc_coreBetaOf_coin0_bits (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    mscCoreBeta false p z mscWSlot2 = 0 ∧ mscCoreBeta false p z mscWSlot1 = 0 ∧
      mscCoreBeta false p z mscWSlot0 = 0 :=
  ⟨PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false p z ⟨3950, by decide⟩
     (by decide) (by decide),
   PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false p z ⟨3949, by decide⟩
     (by decide) (by decide),
   (PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false p z ⟨3948, by decide⟩
     (by decide) (by decide)).trans (by decide)⟩
lemma msc_coreBetaOf_coin1_wSlot0 (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : mscCoreBeta true p z mscWSlot0 = 1 :=
  (PosSlots24SemanticOracleConcrete80.coreBetaOf_mid true p z ⟨3948, by decide⟩
    (by decide) (by decide)).trans (by decide)
lemma msc_uTwistParam_preserves_diag_ge3924 {mPayload : ℕ} (hm22 : 22 ≤ mPayload)
    (cfg : Configuration) (P : BitAssignment (fullSysCoreWires mPayload) → Prop)
    (hCongr : ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload),
      (∀ q : Wire (fullSysCoreWires mPayload), 3924 ≤ q.val → γ₁ q = γ₂ q) →
      (P γ₁ ↔ P γ₂)) :
    (mscUTwistParam true hm22 cfg).1 * mscDiagPred P =
      mscDiagPred P * (mscUTwistParam true hm22 cfg).1 := by
  apply matrix_ext_of_ket_core
  intro γ
  have hTwKet : (mscUTwistParam true hm22 cfg).1.mulVec (ket γ) =
      NuclearTwistRealizes.twistCorePhase true hm22 cfg γ •
        ket (NuclearTwistRealizes.twistCorePermFn true hm22 γ) :=
    MergedVepTopCoinCollapse.uTwistParam_mulVec_ket_id true hm22 cfg γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mscDiagPred_mulVec_ket P γ,
    Matrix.mulVec_smul, hTwKet, Matrix.mulVec_smul, mscDiagPred_mulVec_ket P, smul_comm]
  have hiff := hCongr _ γ (NuclearTwistRealizes.twistCorePermFn_high_eq true hm22 γ)
  by_cases hp : P γ <;> simp [hp, hiff]
lemma msc_qft_preserves_diag_not_in_elecCosetB1 {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (P : BitAssignment (fullSysCoreWires mPayload) → Prop)
    (hCongr : ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload),
      (∀ q : Wire (fullSysCoreWires mPayload),
        q ∉ Set.range (coreElecCosetB1Block hm6).wires → γ₁ q = γ₂ q) → (P γ₁ ↔ P γ₂)) :
    (fullSysQftCoreUnitary hm6 qft).1 * mscDiagPred P =
      mscDiagPred P * (fullSysQftCoreUnitary hm6 qft).1 := by
  ext row col
  unfold mscDiagPred
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hag : (coreElecCosetB1Block hm6).AgreeOutside row col
  · have hiff := hCongr (basisBits _ row) (basisBits _ col) hag
    by_cases hp : P (basisBits _ row)
    · rw [msc_ite_pos hp, msc_ite_pos (hiff.mp hp), mul_one, one_mul]
    · rw [msc_ite_neg hp, msc_ite_neg (mt hiff.mpr hp), mul_zero, zero_mul]
  · rw [fullSysQftCoreUnitary, QRegister.embedUnitary_val,
      embedMatrix_entry_of_not_agreeOutside _ _ hag, zero_mul, mul_zero]
lemma msc_wire_not_in_elecCosetB1 {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload))
    (hq : (3924 ≤ q.val ∧ q.val < 3954) ∨ 3957 ≤ q.val) :
    q ∉ Set.range (coreElecCosetB1Block hm6).wires :=
  MergedVepTopCoinCollapse.wire_not_mem_coreElecCosetB1 (hm6 := hm6) q hq
lemma mscRNuc80_val (i : Fin 8) : (mscRNucCore pos24_22_le_80 i).val = 3960 + i.val := rfl
lemma mscRProj80_val (i : Fin 24) :
    (mscRProjCore (mPayload := 80) i).val = 3924 + i.val ∧
      (mProj24_sp i).val = 3924 + i.val := ⟨rfl, rfl⟩
lemma coreBetaOf_at_sub (s0 : Bool) (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (q : Wire (fullSysCoreWires 80))
    (j : Fin 80) (hq : q.val = 3954 + j.val) :
    mscCoreBeta s0 p z q = p j := by
  have hw : (⟨q.val, q.isLt⟩ : Wire posCoreWires) =
      PosSlots24TopWrapper.rPosSubLocal ⟨j.val, j.isLt⟩ := Fin.ext hq
  exact (congrArg (coreBetaOf s0 p z) hw).trans
    ((PosSlots24SemanticOracleConcrete80.coreBetaOf_payload s0 p z ⟨j.val, j.isLt⟩).trans
      (congrArg p (Fin.ext rfl)))
lemma msc_coreBetaOf_scr_zero (jScr : Fin 16) (p : BitAssignment 80)
    (hpScr : p ⟨63 + jScr.val, by omega⟩ = 0)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    mscCoreBeta false p z (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0 :=
  (coreBetaOf_at_sub false p z _ ⟨63 + jScr.val, by omega⟩
    (by dsimp [mWCoreScrGen]; omega)).trans hpScr
lemma msc_regVal_rNuc_coreBetaOf (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80)
      (mscCoreBeta false p z) = p80NucVal p := by
  unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal p80NucVal
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp only
  rw [coreBetaOf_at_sub false p z _ ⟨6 + i.val, by clear z; omega⟩
    (by clear z; change 3960 + i.val = 3954 + (6 + i.val); omega)]
lemma msc_regVal_posBranch_eq_twist (γ : BitAssignment (fullSysCoreWires 80)) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      (PosSlots24BranchConcrete.rNucIdx (QRegExt.ofFin posCoreWires)) γ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80) γ :=
        by
  unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun w ↦ (γ w).val * 2 ^ i.val)
    (Fin.ext (by change 3954 + (6 + i.val) = 3960 + i.val; omega))
lemma msc_extractCosetP3_coreBetaOf (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    mscExtractCosetP3 pos24_22_le_80 (mscCoreBeta false p z) = p80CosetP3 p :=
  funext fun w ↦ Fin.ext (congrArg ZMod.val (coreBetaOf_at_sub false p z _ ⟨3 + w.val, by omega⟩
    (by change 3957 + w.val = 3954 + (3 + w.val); omega)))
lemma msc_extractProj24_coreBetaOf (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    mscExtractProj24 (mscCoreBeta false p z) = mProj24_sp.extractIndex z := by
  apply (basisBitsEquiv 24).injective
  funext i
  change basisBits 24 (mscExtractProj24 (mscCoreBeta false p z)) i =
    basisBits 24 (mProj24_sp.extractIndex z) i
  unfold mscExtractProj24 extractProj24
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, msc_basisBits_symm]
  have hwCore : (⟨(mscRProjCore (mPayload := 80) i).val,
      (mscRProjCore (mPayload := 80) i).isLt⟩ : Wire posCoreWires) =
      ⟨(mProj24_sp i).val, Nat.lt_trans (mProj24_sp i).isLt
        PosSlots24SemanticOracleConcrete80.lt_sys_4034⟩ :=
    Fin.ext ((mscRProj80_val i).1.trans (mscRProj80_val i).2.symm)
  exact (congrArg (coreBetaOf false p z) hwCore).trans
    (PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 false p z _)
lemma msc_extractNuc_coreBetaOf (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (mscRNucCore pos24_22_le_80).extractIndex
      ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta false p z)) =
      ⟨p80NucVal p, p80NucVal_lt_256 p⟩ := by
  let u := (mscRNucCore pos24_22_le_80).extractIndex
    ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta false p z))
  apply Fin.ext
  have hbit (i : Fin 8) : (basisBits 8 u i).val = (u.val / 2 ^ i.val) % 2 :=
    (congrArg ZMod.val (basisBits_eq_div_mod 8 u i)).trans
      (ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide)))
  have hsum : ∑ i : Fin 8, (basisBits 8 u i).val * 2 ^ i.val = u.val := by
    rw [Fin.sum_univ_eight]
    simp only [hbit]
    have := u.isLt
    simp
    omega
  refine hsum.symm.trans ((?_ : ∑ i : Fin 8, (basisBits 8 u i).val * 2 ^ i.val =
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80)
      (mscCoreBeta false p z)).trans
    (msc_regVal_rNuc_coreBetaOf p z))
  unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [QRegister.basisBits_extractIndex, msc_basisBits_symm]
lemma msc_proj_sandwich_entry_gen {m nSys : ℕ} (rP : QRegister m nSys) (Um : Unitary (2 ^ m))
    (S : Fin (2 ^ m) → Operator (2 ^ nSys))
    (hS : ∀ (yIdx : Fin (2 ^ m)) (a b : Fin (2 ^ nSys)),
      rP.extractIndex a ≠ rP.extractIndex b → S yIdx a b = 0)
    (x' x : Fin (2 ^ nSys)) :
    ((rP.embedUnitary Um).1ᴴ * (∑ yIdx : Fin (2 ^ m), mProjBasisGen rP yIdx * S yIdx) *
      (rP.embedUnitary Um).1) x' x =
    ∑ yIdx : Fin (2 ^ m), star (Um.1 yIdx (rP.extractIndex x')) *
      S yIdx (rP.replaceIndex x' yIdx) (rP.replaceIndex x yIdx) *
      Um.1 yIdx (rP.extractIndex x) := by
  let A : Matrix (Fin (2 ^ nSys)) (Fin (2 ^ nSys)) ℂ := (rP.embedUnitary Um).1
  have hA_ag {u w : Fin (2 ^ nSys)} (h : rP.AgreeOutside u w) :
      A u w = Um.1 (rP.extractIndex u) (rP.extractIndex w) :=
    embedMatrix_entry_of_agreeOutside rP Um.1 h
  have hA_not {u w : Fin (2 ^ nSys)} (h : ¬ rP.AgreeOutside u w) : A u w = 0 :=
    embedMatrix_entry_of_not_agreeOutside rP Um.1 h
  let M_mat : Matrix (Fin (2 ^ nSys)) (Fin (2 ^ nSys)) ℂ := fun a b ↦
    if rP.extractIndex a = rP.extractIndex b then S (rP.extractIndex a) a b else 0
  have hAgRepl (w : Fin (2 ^ nSys)) (y : Fin (2 ^ m)) : rP.AgreeOutside (rP.replaceIndex w y) w :=
    fun q hq ↦ QRegister.basisBits_replaceIndex_of_not_mem rP w y q hq
  have hMidEq : (∑ yIdx : Fin (2 ^ m), mProjBasisGen rP yIdx * S yIdx : Operator (2 ^ nSys)) =
      M_mat := Matrix.ext fun a b ↦ by
    rw [Matrix.sum_apply, Finset.sum_eq_single (rP.extractIndex a)
      (fun yIdx _ hne ↦ by
        rw [mProjBasisGen_eq_basisOutcomeProjector, QRegister.basisOutcomeProjector_eq_diagonal,
          Matrix.diagonal_mul, msc_ite_neg hne.symm, zero_mul])
      (fun habs ↦ absurd (Finset.mem_univ _) habs),
      mProjBasisGen_eq_basisOutcomeProjector, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul, msc_ite_pos rfl, one_mul]
    dsimp only [M_mat]
    by_cases hab : rP.extractIndex a = rP.extractIndex b
    · rw [msc_ite_pos hab]
    · rw [msc_ite_neg hab, hS (rP.extractIndex a) a b hab]
  have hUniq (u w : Fin (2 ^ nSys)) (y : Fin (2 ^ m)) (hag : rP.AgreeOutside u w)
      (hy : rP.extractIndex u = y) : u = rP.replaceIndex w y :=
    (rP.replaceIndex_eq_of_extractIndex_eq_of_agreeOutside w u y hy hag).symm
  let fTerm : Fin (2 ^ m) → ℂ := fun yIdx ↦ star (Um.1 yIdx (rP.extractIndex x')) *
    S yIdx (rP.replaceIndex x' yIdx) (rP.replaceIndex x yIdx) * Um.1 yIdx (rP.extractIndex x)
  have hInj : Function.Injective (fun yIdx : Fin (2 ^ m) ↦ rP.replaceIndex x yIdx) :=
    fun y₁ y₂ h ↦ (QRegister.extractIndex_replaceIndex rP x y₁).symm.trans
      ((congrArg rP.extractIndex h).trans (QRegister.extractIndex_replaceIndex rP x y₂))
  change (Aᴴ * (∑ yIdx : Fin (2 ^ m), mProjBasisGen rP yIdx * S yIdx) * A) x' x = _
  rw [hMidEq, Matrix.mul_apply]
  refine (Finset.sum_congr rfl fun b _ ↦ ?_).trans
    (PosSlots24SemanticOracleConcrete80.sum_extendZero hInj fTerm)
  by_cases hbx : rP.AgreeOutside b x
  · set yIdx := rP.extractIndex b
    rw [hUniq b x yIdx hbx rfl,
      PosSlots24SemanticOracleConcrete80.extendZero_apply hInj fTerm yIdx,
      hA_ag (hAgRepl x yIdx), QRegister.extractIndex_replaceIndex, Matrix.mul_apply]
    congr 1
    refine (Finset.sum_eq_single (rP.replaceIndex x' yIdx) (fun a _ hne ↦ ?_)
      (fun habs ↦ absurd (Finset.mem_univ _) habs)).trans ?_
    · rw [Matrix.conjTranspose_apply]
      dsimp only [M_mat]
      by_cases hax : rP.AgreeOutside a x'
      · rw [msc_ite_neg (by
          rw [QRegister.extractIndex_replaceIndex]
          exact fun hy ↦ hne (hUniq a x' yIdx hax hy)), mul_zero]
      · rw [hA_not hax, star_zero, zero_mul]
    · rw [Matrix.conjTranspose_apply, hA_ag (hAgRepl x' yIdx),
        QRegister.extractIndex_replaceIndex]
      simp only [M_mat, QRegister.extractIndex_replaceIndex, ↓reduceIte]
  · rw [hA_not hbx, mul_zero,
      PosSlots24SemanticOracleConcrete80.extendZero_of_not_exists _ fTerm
        fun ⟨yIdx, hy⟩ ↦ hbx (hy ▸ hAgRepl x yIdx)]
lemma msc_scr_ge_3924 (jScr : Fin 16) :
    3924 ≤ (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr).val := by
  dsimp [mWCoreScrGen]
  omega
lemma msc_scr_ge_3957 (jScr : Fin 16) :
    3957 ≤ (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr).val := by
  dsimp [mWCoreScrGen]
  omega
lemma msc_rNucBranch_ge_3924 (i : Fin 8) :
    3924 ≤ (PosSlots24BranchConcrete.rNucIdx (QRegExt.ofFin posCoreWires) i).val := by
  change 3924 ≤ 3954 + (6 + i.val)
  omega
lemma msc_rNucBranch_ge_3957 (i : Fin 8) :
    3957 ≤ (PosSlots24BranchConcrete.rNucIdx (QRegExt.ofFin posCoreWires) i).val := by
  change 3957 ≤ 3954 + (6 + i.val)
  omega
lemma msc_rNucCore_in_range (i : Fin 8) :
    3960 ≤ (mscRNucCore pos24_22_le_80 i).val ∧ (mscRNucCore pos24_22_le_80 i).val < 3968 := by
  have h1 := mscRNuc80_val i
  have h2 := i.isLt
  omega
def mscPredA (jScr : Fin 16) (γ : BitAssignment (fullSysCoreWires 80)) : Prop :=
  γ mscWSlot2 = 0 ∧ γ mscWSlot1 = 0 ∧ γ mscWSlot0 = 0 ∧
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80) γ <
      216 ∧
    γ (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0
noncomputable def mscCfgY (p : BitAssignment 80) (yIdx : Fin (2 ^ 24)) : Configuration :=
  cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p))
def mscPredB (jScr : Fin 16) (yIdx : Fin (2 ^ 24))
    (η : BitAssignment (fullSysCoreWires 80)) : Prop :=
  η mscWSlot2 = 0 ∧ η mscWSlot1 = 0 ∧ η mscWSlot0 = 0 ∧
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80) η =
      0 ∧
    η (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0 ∧ mscExtractProj24 η = yIdx
noncomputable def mscGammaAct (lVal : Fin (2 ^ 8))
    (η : BitAssignment (fullSysCoreWires 80)) : BitAssignment (fullSysCoreWires 80) :=
  vepWriteReg η (mscRNucCore pos24_22_le_80) (basisBits 8 (Equiv.swap 0 lVal
    ((mscRNucCore pos24_22_le_80).extractIndex ((basisBitsEquiv (fullSysCoreWires 80)).symm η))))
lemma mscGammaAct_out (lVal : Fin (2 ^ 8)) (η : BitAssignment (fullSysCoreWires 80))
    (q : Wire posCoreWires) (hN : ¬(3960 ≤ q.val ∧ q.val < 3968))
    (_hS : ¬(4017 ≤ q.val ∧ q.val < 4033)) : mscGammaAct lVal η q = η q :=
  ProjZ512QftAndTwist288.vepWriteReg_not_mem η (mscRNucCore pos24_22_le_80) _
    ⟨q.val, q.isLt⟩ fun ⟨i, hi⟩ ↦ by
      have hv := congrArg Fin.val hi
      have hr := msc_rNucCore_in_range i
      exact hN ⟨hv ▸ hr.1, hv ▸ hr.2⟩
lemma mscGammaAct_scr_zero (jScr : Fin 16) (lVal : Fin (2 ^ 8))
    (η : BitAssignment (fullSysCoreWires 80))
    (hScr : η (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0) :
    mscGammaAct lVal η (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0 :=
  (ProjZ512QftAndTwist288.vepWriteReg_not_mem η (mscRNucCore pos24_22_le_80) _ _
    fun ⟨i, hi⟩ ↦ by
      have hv := congrArg Fin.val hi
      have h1 := mscRNuc80_val i
      have h2 := i.isLt
      dsimp [mWCoreScrGen] at hv
      omega).trans hScr
lemma msc_qft_comm_vepSwapNuc {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (hm22 : 22 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (lVal : Fin (2 ^ 8)) :
    (fullSysQftCoreUnitary hm6 qft).1 * (mscVepSwapNuc hm22 lVal).1 =
      (mscVepSwapNuc hm22 lVal).1 * (fullSysQftCoreUnitary hm6 qft).1 := by
  rw [fullSysQftCoreUnitary, mscVepSwapNuc, vepSwapNuc,
    QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  refine QRegister.embedMatrix_comm_of_disjoint
    (coreElecCosetB1Block hm6) (rNucIdx hm22 (QRegExt.idReg _)) ?_ _ _
  refine QRegister.disjoint_iff.mpr fun i j hij ↦
    msc_wire_not_in_elecCosetB1 hm6 (rNucIdx hm22 (QRegExt.idReg _) j) (Or.inr ?_) ⟨i, hij⟩
  dsimp [rNucIdx, QRegister.slice, MergedVepCoreSliceClosureAlt.qreg_slice_wires,
    MergedVepCoreSliceClosureAlt.qreg_whole_wires,
    MergedVepCoreSliceClosureAlt.emb_trans_apply,
    MergedVepCoreSliceClosureAlt.emb_refl_apply,
    MergedVepCoreSliceClosureAlt.emb_mk_apply, QRegExt.idReg]
  omega
lemma msc_add_sub_3960 (n : ℕ) (h0 : 3954 ≤ n) (h1 : 6 ≤ n - 3954) :
    3960 + (n - 3954 - 6) = n := by omega
lemma msc_hFwdVep (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : Configuration)
    (p : BitAssignment 80) (hge : 216 ≤ p80NucVal p)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (fullSysQftCoreUnitary pos24_6_le_80 qft *
      mscUVepTwistRef pos24_22_le_80 cfg).1.mulVec (ket (mscCoreBeta false p z)) =
    ∑ yIdx : Fin (2 ^ 24), (uProjPlus512_3D (p80CosetP3 p)).1 yIdx (mProj24_sp.extractIndex z) •
      (mscVepSwapNuc pos24_22_le_80 ⟨p80NucVal p, p80NucVal_lt_256 p⟩).1.mulVec
        ((fullSysQftCoreUnitary pos24_6_le_80 qft *
          mscUTwistParam true pos24_22_le_80 (mscCfgY p yIdx)).1.mulVec
          (ket (mscCoreBeta false (p80SetNucZero p) (mProj24_sp.replaceIndex z yIdx)))) := by
  let lVal : Fin (2 ^ 8) := ⟨p80NucVal p, p80NucVal_lt_256 p⟩
  have hvTrue : mscVepHighNuc pos24_22_le_80 (mscCoreBeta false p z) = true := by
    rw [mscVepHighNuc, vepHighNuc_iff]
    refine ⟨decide_eq_true_eq.mpr (msc_coreBetaOf_coin0_bits p z), ?_⟩
    change 216 ≤
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80)
      (mscCoreBeta false p z)
    rwa [msc_regVal_rNuc_coreBetaOf p z]
  have hComm := msc_qft_comm_vepSwapNuc pos24_6_le_80 pos24_22_le_80 qft lVal
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    msc_uVepTwistRef_vep_ket pos24_22_le_80 cfg lVal _ hvTrue (msc_extractNuc_coreBetaOf p z),
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hComm, Matrix.mul_assoc,
    Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    msc_extractCosetP3_coreBetaOf p z, msc_extractProj24_coreBetaOf p z,
    show projGridEquiv24 yIdx = mProjGridEquiv24 yIdx from funext fun _ ↦ Fin.ext rfl]
  let rP := mscRProjCore (mPayload := 80)
  let rN := mscRNucCore pos24_22_le_80
  let γP := vepWriteReg (mscCoreBeta false p z) rP (basisBits 24 yIdx)
  suffices hSw : (mscVepSwapNuc pos24_22_le_80 lVal).1.mulVec (ket γP) =
      ket (mscCoreBeta false (p80SetNucZero p) (mProj24_sp.replaceIndex z yIdx)) by
    dsimp only [mscCfgY, γP] at hSw ⊢
    rw [hSw]
  have hγP_rN : rN.extractIndex ((basisBitsEquiv (fullSysCoreWires 80)).symm γP) = lVal := by
    dsimp only [lVal]
    rw [← msc_extractNuc_coreBetaOf p z]
    apply (basisBitsEquiv 8).injective
    funext i
    change basisBits 8 _ i = basisBits 8 _ i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      msc_basisBits_symm, msc_basisBits_symm]
    refine ProjZ512QftAndTwist288.vepWriteReg_not_mem _ rP _ (rN i) fun ⟨j, hj⟩ ↦ ?_
    have hv := congrArg Fin.val hj
    have hjLt := j.isLt
    have hiLt := i.isLt
    change 3924 + j.val = 3960 + i.val at hv
    omega
  rw [msc_vepSwapNuc_mulVec_ket, hγP_rN, Equiv.swap_apply_right]
  refine congrArg ket (funext fun q ↦ ?_)
  by_cases hqN : q ∈ Set.range rN.wires
  · obtain ⟨i, rfl⟩ := hqN
    have hb0 : basisBits 8 (0 : Fin (2 ^ 8)) i = 0 := by fin_cases i <;> decide
    rw [ProjZ512QftAndTwist288.vepWriteReg_mem, hb0,
      coreBetaOf_at_sub false (p80SetNucZero p) _ _ ⟨6 + i.val, by have := i.isLt; omega⟩
        ((mscRNuc80_val i).trans (Nat.add_assoc 3954 6 i.val))]
    unfold p80SetNucZero
    exact (msc_ite_pos ⟨Nat.le_add_right 6 i.val, Nat.add_lt_add_left i.isLt 6⟩).symm
  · rw [ProjZ512QftAndTwist288.vepWriteReg_not_mem _ rN _ q hqN]
    dsimp only [γP]
    by_cases hqP : q ∈ Set.range rP.wires
    · obtain ⟨i, rfl⟩ := hqP
      rw [ProjZ512QftAndTwist288.vepWriteReg_mem]
      have hwSys : (⟨(rP i).val, (rP i).isLt⟩ : Wire posCoreWires) =
          ⟨(mProj24_sp i).val, Nat.lt_trans (mProj24_sp i).isLt
            PosSlots24SemanticOracleConcrete80.lt_sys_4034⟩ :=
        Fin.ext ((mscRProj80_val i).1.trans (mscRProj80_val i).2.symm)
      exact ((congrArg (coreBetaOf false _ _) hwSys).trans
        ((PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 _ _ _ _).trans
          (QRegister.basisBits_replaceIndex_apply mProj24_sp z yIdx i))).symm
    · rw [ProjZ512QftAndTwist288.vepWriteReg_not_mem _ rP _ q hqP]
      by_cases hlt : q.val < SpecsAux.SpecMirror.systemQubits
      · have hnotMem : (⟨q.val, hlt⟩ : Wire SpecsAux.SpecMirror.systemQubits) ∉
            Set.range mProj24_sp.wires := fun ⟨i, hi⟩ ↦
          hqP ⟨i, Fin.ext ((mscRProj80_val i).1.trans
            ((mscRProj80_val i).2.symm.trans (congrArg Fin.val hi)))⟩
        exact (PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 false p z ⟨q.val, hlt⟩).trans
          ((QRegister.basisBits_replaceIndex_of_not_mem mProj24_sp z yIdx ⟨q.val, hlt⟩
            hnotMem).symm.trans
            (PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 false (p80SetNucZero p)
              (mProj24_sp.replaceIndex z yIdx) ⟨q.val, hlt⟩).symm)
      · by_cases hmid : q.val < 3954
        · exact (PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false p z ⟨q.val, q.isLt⟩
            (Nat.le_of_not_lt hlt) hmid).trans
            (PosSlots24SemanticOracleConcrete80.coreBetaOf_mid false (p80SetNucZero p)
              (mProj24_sp.replaceIndex z yIdx) ⟨q.val, q.isLt⟩
              (Nat.le_of_not_lt hlt) hmid).symm
        · have hqLt : q.val < 3954 + 80 := q.isLt
          have hsub : q.val - 3954 < 80 := by omega
          have hqeq : q.val = 3954 + (q.val - 3954) := by omega
          have hnot6_14 : ¬(6 ≤ q.val - 3954 ∧ q.val - 3954 < 14) := fun ⟨h1, h2⟩ ↦ by
            let idx : Fin 8 := ⟨q.val - 3954 - 6, Nat.sub_lt_left_of_lt_add h1 h2⟩
            exact hqN ⟨idx, Fin.ext ((mscRNuc80_val idx).trans
              (msc_add_sub_3960 q.val (Nat.le_of_not_lt hmid) h1))⟩
          rw [coreBetaOf_at_sub false p z q ⟨q.val - 3954, hsub⟩ hqeq,
            coreBetaOf_at_sub false (p80SetNucZero p) _ q ⟨q.val - 3954, hsub⟩ hqeq]
          unfold p80SetNucZero
          exact (msc_ite_neg hnot6_14).symm
noncomputable def mscDiagPredB (jScr : Fin 16) (yIdx : Fin (2 ^ 24)) :
    Operator (2 ^ (fullSysCoreWires 80)) :=
  mscDiagPred (mscPredB jScr yIdx)
noncomputable def mscTailAlpha (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (yIdx : Fin (2 ^ 24)) : ℂ :=
  (uProjPlus512_3D (p80CosetP3 p)).1 yIdx (mProj24_sp.extractIndex z)
noncomputable def mscTailVH (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (p : BitAssignment 80) (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (yIdx : Fin (2 ^ 24)) :
    Fin (2 ^ (fullSysCoreWires 80)) → ℂ :=
  (fullSysQftCoreUnitary pos24_6_le_80 qft *
    mscUTwistParam true pos24_22_le_80 (mscCfgY p yIdx)).1.mulVec
    (ket (mscCoreBeta false (p80SetNucZero p) (mProj24_sp.replaceIndex z yIdx)))
lemma msc_tail_hs (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (yIdx : Fin (2 ^ 24)) :
    (uProjPlus512_3D (p80CosetP3 p)).1 yIdx (mProj24_sp.extractIndex z) •
      (mscVepSwapNuc pos24_22_le_80 ⟨p80NucVal p, p80NucVal_lt_256 p⟩).1.mulVec
        ((fullSysQftCoreUnitary pos24_6_le_80 qft *
          mscUTwistParam true pos24_22_le_80 (mscCfgY p yIdx)).1.mulVec
          (ket (mscCoreBeta false (p80SetNucZero p) (mProj24_sp.replaceIndex z yIdx)))) =
    mscTailAlpha p z yIdx •
      (mscVepSwapNuc pos24_22_le_80 ⟨p80NucVal p, p80NucVal_lt_256 p⟩).1.mulVec
        (mscTailVH qft p z yIdx) := rfl
lemma msc_tail_hvIn (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (jScr : Fin 16)
    (p : BitAssignment 80) (hpScr : p ⟨63 + jScr.val, by omega⟩ = 0)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (yIdx : Fin (2 ^ 24)) :
    (mscDiagPredB jScr yIdx).mulVec (mscTailVH qft p z yIdx) = mscTailVH qft p z yIdx := by
  unfold mscDiagPredB mscTailVH
  have hCongrR (γ₁ γ₂ : BitAssignment (fullSysCoreWires 80))
      (h : ∀ q : Wire (fullSysCoreWires 80),
        (3924 ≤ q.val ∧ q.val < 3954) ∨ 3957 ≤ q.val → γ₁ q = γ₂ q) :
      mscPredB jScr yIdx γ₁ ↔ mscPredB jScr yIdx γ₂ := by
    unfold mscPredB
    have hrn := regVal_eq_of_wire_eq (mscRNucCore pos24_22_le_80) γ₁ γ₂ fun i ↦
      h _ (Or.inr (by have := mscRNuc80_val i; omega))
    have hexp : mscExtractProj24 γ₁ = mscExtractProj24 γ₂ := by
      apply (basisBitsEquiv 24).injective
      funext i
      unfold mscExtractProj24 extractProj24
      change basisBits 24 _ i = basisBits 24 _ i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        msc_basisBits_symm, msc_basisBits_symm]
      exact h _ (Or.inl (by
        have := i.isLt
        change 3924 ≤ 3924 + i.val ∧ 3924 + i.val < 3954
        omega))
    rw [h mscWSlot2 (Or.inl (by decide)), h mscWSlot1 (Or.inl (by decide)),
      h mscWSlot0 (Or.inl (by decide)), hrn, h _ (Or.inr (msc_scr_ge_3957 jScr)), hexp]
  have hCommB := msc_mul2_comm _ _ (mscDiagPred (mscPredB jScr yIdx))
    (msc_qft_preserves_diag_not_in_elecCosetB1 pos24_6_le_80 qft _
      fun γ₁ γ₂ h ↦ hCongrR γ₁ γ₂ fun q hq ↦ h q (msc_wire_not_in_elecCosetB1 pos24_6_le_80 q hq))
    (msc_uTwistParam_preserves_diag_ge3924 pos24_22_le_80 (mscCfgY p yIdx) _
      fun γ₁ γ₂ h ↦ hCongrR γ₁ γ₂ fun q hq ↦ h q (by omega))
  have hc0 := msc_coreBetaOf_coin0_bits (p80SetNucZero p) (mProj24_sp.replaceIndex z yIdx)
  have hPredBetaB : mscPredB jScr yIdx
      (mscCoreBeta false (p80SetNucZero p) (mProj24_sp.replaceIndex z yIdx)) := by
    refine ⟨hc0.1, hc0.2.1, hc0.2.2, ?_, ?_, ?_⟩
    · rw [msc_regVal_rNuc_coreBetaOf]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      unfold p80SetNucZero
      rw [msc_ite_pos (by omega : 6 ≤ 6 + i.val ∧ 6 + i.val < 14), ZMod.val_zero, zero_mul]
    · refine msc_coreBetaOf_scr_zero jScr (p80SetNucZero p) ?_ _
      unfold p80SetNucZero
      exact (msc_ite_neg (by omega : ¬(6 ≤ 63 + jScr.val ∧ 63 + jScr.val < 14))).trans hpScr
    · rw [msc_extractProj24_coreBetaOf, QRegister.extractIndex_replaceIndex]
  rw [Submonoid.coe_mul, Matrix.mulVec_mulVec, ← hCommB, ← Matrix.mulVec_mulVec,
    mscDiagPred_mulVec_ket, msc_ite_pos hPredBetaB, one_smul]
open Classical in
lemma msc_tail_hOrth (jScr : Fin 16) {y' y : Fin (2 ^ 24)} (hy : y' ≠ y) :
    (mscDiagPredB jScr y')ᴴ * mscDiagPredB jScr y = 0 := by
  ext r c
  simp only [mscDiagPredB, mscDiagPred, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.zero_apply]
  by_cases hrc : r = c
  · subst hrc
    rw [Matrix.diagonal_apply_eq]
    by_cases h1 : mscPredB jScr y' (basisBits _ r)
    · have h2 : ¬ mscPredB jScr y (basisBits _ r) :=
        fun h ↦ hy (h1.2.2.2.2.2.symm.trans h.2.2.2.2.2)
      simp [h1, h2]
    · simp [h1]
  · exact Matrix.diagonal_apply_ne _ hrc
lemma msc_mergedSliceGen_lt (sysSlice : SpecsAux.SpecMirror.Configuration → BitAssignment 80 →
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) (cfg : SpecsAux.SpecMirror.Configuration)
    (p : BitAssignment 80) (hlt : p80NucVal p < 216)
    (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    mergedSliceGen sysSlice cfg p x' x = sysSlice cfg p x' x := by
  unfold mergedSliceGen
  rw [msc_ite_pos hlt]
lemma msc_mergedSliceGen_ge_sum {sysSlice : SpecsAux.SpecMirror.Configuration → BitAssignment 80 →
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits)}
    {term : Fin (2 ^ 24) → Operator (2 ^ SpecsAux.SpecMirror.systemQubits)}
    (cfg : SpecsAux.SpecMirror.Configuration) (p : BitAssignment 80) (hge : ¬ p80NucVal p < 216)
    (hterm : ∀ yIdx, mProjBasisGen mProj24_sp yIdx *
      sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p)))
        (p80SetNucZero p) = term yIdx)
    (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    mergedSliceGen sysSlice cfg p x' x =
      ((mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p))).1ᴴ *
        (∑ yIdx : Fin (2 ^ 24), term yIdx) *
        (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p))).1) x' x := by
  unfold mergedSliceGen
  rw [msc_ite_neg hge]
  exact congrFun (congrFun (congrArg (fun S ↦ (mProj24_sp.embedUnitary (uProjPlus512_3D
    (p80CosetP3 p))).1ᴴ * S * (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p))).1)
    (Finset.sum_congr rfl fun yIdx _ ↦ hterm yIdx)) x') x
set_option maxRecDepth 512
end ConfigMergedVepCoreSliceClosure
end MergedVepCoreSliceClosure
end
end ModMergedVepCoreSliceClosure

section ModPos24MergedVepPrepAndStitch
set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace Pos24MergedVepPrepAndStitch
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit hiding
  norm_projector_le_one
open TwosCompAndWire0Cancel
open NuclearTwistRealizes
open HoistedSwapSelectBridge hiding unitaryConj unitaryConj_val
open FullSysPosSlots24AndTopConcrete
open PosSlots24MergedVepBound
open SpecsAux.DyadicSubgridToeplitz512AndShift (
  NyqGrid3D256 NyqFine3D512 nyq512ProjEquiv3D)
section ConfigPos24MergedVepPrepAndStitch
set_option maxRecDepth 4096
attribute [local irreducible] smToTwos654SysUnitary
attribute [local irreducible] smToTwosSysUnitary
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowStitch (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem smToTwosSysUnitary_sa : smToTwosSysUnitary.1ᴴ = smToTwosSysUnitary.1 := by
  have h1 : smToTwosSysUnitary.1ᴴ * smToTwosSysUnitary.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self smToTwosSysUnitary
  rw [← Matrix.mul_one smToTwosSysUnitary.1ᴴ, ← smToTwosSys_mul_self_val,
    ← Matrix.mul_assoc, h1, Matrix.one_mul]
theorem smConj_comm_embedMatrix_of_idleTwos {A : Operator (2 ^ systemQubits)}
    (hIdle : ∀ M : Operator (2 ^ 24),
      A * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * A)
    (M : Operator (2 ^ 24)) :
    (smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1) * rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M * (smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1) := by
  let P := rProj24_sp.embedMatrix (fwdPermUnitary projSignedMagToTwos24Equiv).1
  have hUsys : smToTwosSysUnitary.1 = P * smToTwos654SysUnitary.1 :=
    (congrArg Subtype.val smToTwosSysUnitary_eq_proj_mul_elec).trans
      (Submonoid.coe_mul (Matrix.unitaryGroup (Fin (2 ^ systemQubits)) ℂ) _ _)
  have hP_inv : Pᴴ * P = 1 := by
    simpa only [P, QRegister.embedUnitary_val, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self
        (rProj24_sp.embedUnitary (fwdPermUnitary projSignedMagToTwos24Equiv))
  have hAP : A * P = P * A := hIdle _
  have hCollapse : smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1 =
      smToTwos654SysUnitary.1 * A * smToTwos654SysUnitary.1 := by
    have hL : smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1 =
        smToTwosSysUnitary.1ᴴ * A * smToTwosSysUnitary.1 := by
      rw [smToTwosSysUnitary_sa]
    rw [hL, hUsys, conjTranspose_mul, smToTwos654SysUnitary_sa]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A P, hAP, Matrix.mul_assoc P A,
      ← Matrix.mul_assoc Pᴴ P, hP_inv, Matrix.one_mul]
  rw [hCollapse]
  exact MergedVepCoreSliceClosure.msc_mul2_comm _ _ _
    (MergedVepCoreSliceClosure.msc_mul2_comm _ _ _
      (smToTwos654SysUnitary_comm_embedMatrix M) (hIdle M))
    (smToTwos654SysUnitary_comm_embedMatrix M)
noncomputable def mergedPosSlot2WeightGen (qRatio : ℝ) (w2 : Configuration → ℝ)
    (cfg : Configuration) : ℝ := w2 cfg / qRatio
noncomputable def mergedPosSlot2Shift (e2 : Configuration → ℝ) (cfg : Configuration) : ℝ :=
  (109 / 108 : ℝ) * e2 cfg
noncomputable def mergedPosSlot2BUnitTwosGen (qRatio : ℝ)
    (b2 : Configuration → Operator (2 ^ systemQubits)) (cfg : Configuration) :
    Operator (2 ^ systemQubits) :=
  (qRatio : ℂ) • (b2 cfg + vepFromSlot2TwosOp b2)
theorem norm_mergedPosSlot2BUnitTwosGen_le_one {qRatio : ℝ} (hqPos : 0 < qRatio)
    (hqSub : qRatio * (109 / 108 : ℝ) ≤ 1) (b2 : Configuration → Operator (2 ^ systemQubits))
    (hUnit2 : ∀ c, ‖b2 c‖ ≤ 1)
    (hIdleTwos : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)),
      b2 (cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
        rProj24_sp.embedMatrix M * b2 (cfgProjZ512 zP))
    (cfg : Configuration) : ‖mergedPosSlot2BUnitTwosGen qRatio b2 cfg‖ ≤ 1 := by
  have hPMul {i j : Fin (2 ^ 24)} (hij : i ≠ j) :
      projBasisGen rProj24_sp i * projBasisGen rProj24_sp j = 0 := by
    unfold projBasisGen
    rw [← rProj24_sp.embedMatrix_mul, matUnit24_mul, MergedVepTopCoinCollapse.ite_eq_of_neg hij]
    ext a b
    simp [QRegister.embedMatrix_apply]
  have hper_b (bP : Fin 3 → Fin 2) :
      ‖(rProj24_sp.embedUnitary (uProjPlus512_3D bP)).1ᴴ *
        (∑ yIdx : Fin (2 ^ 24),
          projBasisGen rProj24_sp yIdx *
            b2 (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP)))) *
        (rProj24_sp.embedUnitary (uProjPlus512_3D bP)).1‖ ≤ 1 := by
    let A (i : Fin (2 ^ 24)) : Operator (2 ^ systemQubits) :=
      b2 (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 i, bP)))
    let P (i : Fin (2 ^ 24)) : Operator (2 ^ systemQubits) := projBasisGen rProj24_sp i
    have hComm (i : Fin (2 ^ 24)) : A i * P i = P i * A i :=
      hIdleTwos (nyq512ProjEquiv3D (projGridEquiv24 i, bP)) (matUnit24 i i)
    refine MergedVepTopCoinCollapse.norm_conj_unitary_le_one
      (rProj24_sp.embedUnitary (uProjPlus512_3D bP)) _
      (norm_sum_biOrthogonal_le Finset.univ (fun i ↦ P i * A i) zero_le_one
        (fun i _ j _ hij ↦ ?_) (fun i _ j _ hij ↦ ?_) (fun i _ ↦ ?_))
    · have hAdj : (A j)ᴴ * P j = P j * (A j)ᴴ := by
        simpa only [P, Matrix.conjTranspose_mul, (projBasisGen_isHermitian rProj24_sp j).eq] using
          (congrArg Matrix.conjTranspose (hComm j)).symm
      rw [(hComm i).symm, conjTranspose_mul, (projBasisGen_isHermitian rProj24_sp j).eq,
        hAdj, Matrix.mul_assoc (A i), ← Matrix.mul_assoc (P i) (P j), hPMul hij,
        Matrix.zero_mul, Matrix.mul_zero]
    · rw [conjTranspose_mul, (projBasisGen_isHermitian rProj24_sp i).eq,
        Matrix.mul_assoc, ← Matrix.mul_assoc (P i) (P j), hPMul hij,
        Matrix.zero_mul, Matrix.mul_zero]
    · exact (norm_mul_le (P i) (A i)).trans ((mul_le_mul
        (SpecsAux.SpecMirror.SixChannelHamiltonianSplit.norm_projector_le_one
          (P i) (projBasisGen_isHermitian rProj24_sp i) (projBasisGen_idem rProj24_sp i))
        (hUnit2 _) (norm_nonneg _) zero_le_one).trans (one_mul (1 : ℝ)).le)
  have hVep : ‖vepFromSlot2TwosOp b2‖ ≤ 1 / 108 := by
    change ‖vepGen rProj24_sp projGridEquiv24 uProjPlus512_3D b2‖ ≤ 1 / 108
    unfold vepGen
    rw [norm_smul, show ‖((1 : ℝ) / (108 * 8) : ℂ)‖ = (1 : ℝ) / (108 * 8) by norm_num]
    have hinner : ‖∑ bP : Fin 3 → Fin 2, (rProj24_sp.embedUnitary (uProjPlus512_3D bP)).1ᴴ *
        (∑ yIdx : Fin (2 ^ 24),
          projBasisGen rProj24_sp yIdx *
            b2 (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP)))) *
        (rProj24_sp.embedUnitary (uProjPlus512_3D bP)).1‖ ≤ 8 := by
      refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun bP _ ↦ hper_b bP)).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
      norm_num
    linarith [mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (108 * 8))]
  unfold mergedPosSlot2BUnitTwosGen
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqPos]
  have hSum : ‖b2 cfg + vepFromSlot2TwosOp b2‖ ≤ 109 / 108 :=
    ((norm_add_le _ _).trans (add_le_add (hUnit2 cfg) hVep)).trans_eq (by norm_num)
  exact (mul_le_mul_of_nonneg_left hSum (le_of_lt hqPos)).trans hqSub
set_option exponentiation.threshold 256 in
theorem mergedPosSlot2Gen_smConj_eq {qRatio : ℝ} (hqPos : 0 < qRatio) (w2Const : ℝ)
    (b2 : Configuration → Operator (2 ^ systemQubits))
    (hIdleTwos : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)),
      b2 (cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
        rProj24_sp.embedMatrix M * b2 (cfgProjZ512 zP))
    (cfg : Configuration) :
    let B_raw2 : Configuration → Operator (2 ^ systemQubits) :=
      fun c ↦ (w2Const : ℂ) • (smToTwosSysUnitary.1 * b2 c * smToTwosSysUnitary.1)
    ((mergedPosSlot2WeightGen qRatio (fun _ ↦ w2Const) cfg : ℂ) •
      (smToTwosSysUnitary.1 * mergedPosSlot2BUnitTwosGen qRatio b2 cfg * smToTwosSysUnitary.1)) =
      B_raw2 cfg + vepFromSlot2Op B_raw2 := by
  intro B_raw2
  have hConjVep : smToTwosSysUnitary.1 * vepFromSlot2TwosOp b2 * smToTwosSysUnitary.1 =
      vepFromSlot2Op (fun c ↦ smToTwosSysUnitary.1 * b2 c * smToTwosSysUnitary.1) := by
    simpa only [smToTwosSysUnitary_sa] using smToTwosSysUnitary_conj_vepFromSlot2TwosOp b2
      hIdleTwos
  have hVepSmul : vepFromSlot2Op B_raw2 = (w2Const : ℂ) • vepFromSlot2Op
      (fun c ↦ smToTwosSysUnitary.1 * b2 c * smToTwosSysUnitary.1) := by
    unfold vepFromSlot2Op vepGen
    simp_rw [B_raw2, Matrix.mul_smul, ← Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
    rw [← Finset.smul_sum, smul_comm]
  unfold mergedPosSlot2WeightGen mergedPosSlot2BUnitTwosGen
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_add, Matrix.add_mul,
    hConjVep, hVepSmul, smul_add]
  have h1 : (((w2Const / qRatio : ℝ) : ℂ) * (qRatio : ℂ)) = (w2Const : ℂ) := by
    push_cast
    exact div_mul_cancel₀ (w2Const : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt hqPos))
  rw [h1]
end ConfigPos24MergedVepPrepAndStitch
set_option maxRecDepth 2000
end Pos24MergedVepPrepAndStitch
end
end ModPos24MergedVepPrepAndStitch

section ModPosSlots24Semantic80Physics
set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace PosSlots24Semantic80PhysicsAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n)
    (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end PosSlots24Semantic80PhysicsAlt
namespace PosSlots24Semantic80Physics
section ConfigPosSlots24Semantic80Physics
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
instance (priority := 1000000) instNeZeroTwoPowSem80 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit hiding
  norm_projector_le_one
open NuclearTwistRealizes
open FullSysCatSegmentBridge
open HoistedSwapSelectBridge hiding unitaryConj unitaryConj_val
open PosSlots24TopWrapper
open PosSlots24SemanticBridge
open PosSlots24SemanticOracleConcrete80
open PosSlots24BranchConcrete (posCoreWires uPosPhase)
def z2BitOfNat (x i : ℕ) : ZMod 2 := if ((x / 2 ^ i) % 2) == 1 then 1 else 0
def headWitnessPayload80 (b0Val nuc anc : ℕ) (k : Fin 56) (pid : Fin 6) (sm : Fin 8)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  let dH := PosSlots24SemanticBridge.pos24OhPoint (PosSlots24SemanticBridge.pos24HeadU56 k)
      (PosSlots24SemanticBridge.pos24HeadV56 k) (PosSlots24SemanticBridge.pos24HeadW56 k) pid sm
  let dpH := ((dH 0).val % 2) + 2 * ((dH 1).val % 2) + 4 * ((dH 2).val % 2)
  let fineH := (dH 0).val + 128 * (dH 1).val + 16384 * (dH 2).val
  let b1Val := Nat.xor b0Val dpH
  fun q ↦
    let i := q.val
    if i < 3 then z2BitOfNat b1Val i
    else if i < 6 then z2BitOfNat b0Val (i - 3)
    else if i < 14 then z2BitOfNat nuc (i - 6)
    else if i < 22 then z2BitOfNat anc (i - 14)
    else if i < 30 then 0
    else if i == 30 then 1
    else if i == 31 then (if thresh then 1 else 0)
    else if i < 62 then z2BitOfNat fineH (i - 32)
    else if i == 62 then 0
    else if i < 69 then z2BitOfNat k.val (i - 63)
    else if i < 72 then z2BitOfNat pid.val (i - 69)
    else if i < 75 then z2BitOfNat sm.val (i - 72)
    else if i < 79 then 0
    else (if rej0 then 1 else 0)
def tailWitnessPayload80 (b0Val nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  let b1Val := Nat.xor b0Val dp.val
  fun q ↦
    let i := q.val
    if i < 3 then z2BitOfNat b1Val i
    else if i < 6 then z2BitOfNat b0Val (i - 3)
    else if i < 14 then z2BitOfNat nuc (i - 6)
    else if i < 22 then z2BitOfNat anc (i - 14)
    else if i < 30 then z2BitOfNat part (i - 22)
    else if i == 30 then 0
    else if i == 31 then (if thresh then 1 else 0)
    else if i < 62 then z2BitOfNat keep (i - 32)
    else if i == 62 then 0
    else if i < 75 then 0
    else if i < 78 then z2BitOfNat dp.val (i - 75)
    else if i == 78 then 0
    else (if rej0 then 1 else 0)
def pos80SubIdx (off m : ℕ) (h : off + m ≤ 80) (j : Fin m) : Fin 80 :=
  ⟨off + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h⟩
noncomputable def pos80IdealDist (s0 : Bool) (p80 : BitAssignment 80) : ℝ :=
  let b1Val := Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 3 ↦ p80 ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩)
  let b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 3 3 (by decide) j))
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 6 8 (by decide) j))
  let anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j))
  let part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 22 8 (by decide) j))
  let fine30 := Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 30 ↦ p80 (pos80SubIdx 32 30 (by decide) j))
  if p80 62 != 0 then 0
  else if p80 30 == 1 then
    let kVal := Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 6 ↦ p80 (pos80SubIdx 63 6 (by decide) j))
    let pidVal := Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ p80 (pos80SubIdx 69 3 (by decide) j))
    let smVal := Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ p80 (pos80SubIdx 72 3 (by decide) j))
    let remZero := (p80 75 == 0) && (p80 76 == 0) && (p80 77 == 0) && (p80 78 == 0)
    let metaOk := if s0 then (nuc == 0) && decide (anc < 218)
      else decide (b0Val == 0) && decide (nuc < 216) && (anc == 0)
    if hk : kVal < 56 then
      if hp : pidVal < 6 then
        let k : Fin 56 := ⟨kVal, hk⟩
        let pid : Fin 6 := ⟨pidVal, hp⟩
        let sm : Fin 8 := ⟨smVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
        if remZero && metaOk && (part == 0) &&
            (p80 == headWitnessPayload80 b0Val nuc anc k pid sm (p80 31 == 1) (p80 79 == 1)) then
          if s0 then
            (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) /
              (8 * 218 * 48 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat)
          else
            (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) /
              (216 * 48 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat)
        else 0
      else 0
    else 0
  else
    let scratchZero :=
      decide (∀ j : Fin 12, p80 (pos80SubIdx 63 12 (by decide) j) = 0) && (p80 78 == 0)
    let dpVal := Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ p80 (pos80SubIdx 75 3 (by decide) j))
    let dp : Fin 8 := ⟨dpVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
    let metaOk := if s0 then (nuc == 0) && decide (anc < 218) && decide (part < 217)
      else (b0Val == 0) && decide (nuc < 216) && decide (anc < 218) && (part == 0)
    if scratchZero && metaOk && decide (fine30 < PosSlots24SemanticBridge.pos24TailSpan8 dp) &&
        (p80 == tailWitnessPayload80 b0Val nuc anc part dp fine30 (p80 31 == 1) (p80 79 == 1))
        then
      if s0 then
        (1 : ℝ) / (8 * 218 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat)
      else
        (1 : ℝ) / (216 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat)
    else 0
theorem z2BitOfNat_val (x i : ℕ) : (z2BitOfNat x i).val = (x / 2 ^ i) % 2 := by
  unfold z2BitOfNat
  by_cases h : (x / 2 ^ i) % 2 = 1
  · simp [h]
  · simp [show (x / 2 ^ i) % 2 = 0 by omega]
theorem bitsVal_z2BitOfNat (m x : ℕ) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ z2BitOfNat x j.val) = x % 2 ^ m := by
  induction m with
  | zero => simp [Pos24HeadCoordXor80.bitsVal, Nat.mod_one]
  | succ m ih =>
    unfold Pos24HeadCoordXor80.bitsVal at ih ⊢
    rw [Fin.sum_univ_castSucc]
    dsimp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, z2BitOfNat_val, pow_succ, Nat.add_comm, Nat.mul_comm]
    have hdm := Nat.div_add_mod (x % (2 ^ m * 2)) (2 ^ m)
    rwa [Nat.mod_mul_right_div_self x (2 ^ m) 2, Nat.mod_mul_right_mod x (2 ^ m) 2] at hdm
theorem bitsVal_z2BitOfNat_of_lt {m x : ℕ} (hx : x < 2 ^ m) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ z2BitOfNat x j.val) = x := by
  rw [bitsVal_z2BitOfNat, Nat.mod_eq_of_lt hx]
theorem bitsVal_congr {m : ℕ} {f g : BitAssignment m} (h : ∀ j : Fin m, f j = g j) :
    Pos24HeadCoordXor80.bitsVal f = Pos24HeadCoordXor80.bitsVal g :=
  Finset.sum_congr rfl fun j _ ↦ by rw [h j]
theorem tailSpan8_lt_two_pow_30 (dp : Fin 8) : pos24TailSpan8 dp ≤ 2 ^ 30 := by
  fin_cases dp <;> decide
theorem subBitsVal_eq_of_lt (off m x : ℕ) (ho : off + m ≤ 80) (hx : x < 2 ^ m)
    {p : BitAssignment 80} (hp : ∀ j : Fin m,
      p (pos80SubIdx off m ho j) = z2BitOfNat x j.val) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ p (pos80SubIdx off m ho j)) = x :=
  (bitsVal_congr hp).trans (bitsVal_z2BitOfNat_of_lt hx)
theorem headWitnessPayload80_eval_pos80IdealDist (s0 : Bool) (b0Val nuc anc : ℕ) (k : Fin 56)
    (pid : Fin 6) (sm : Fin 8) (thresh rej0 : Bool) (hb0 : b0Val < 8) (hnuc : nuc < 256)
    (hanc : anc < 256) (hmeta : (if s0 then (nuc == 0) && decide (anc < 218) else decide
      (b0Val == 0) && decide (nuc < 216) && (anc == 0)) = true) :
    pos80IdealDist s0 (headWitnessPayload80 b0Val nuc anc k pid sm thresh rej0) =
      if s0 then (pos24HeadWeight56 k : ℝ) / (8 * 218 * 48 * 2 * 2 * pos80Slot4TotNat)
      else (pos24HeadWeight56 k : ℝ) / (216 * 48 * 2 * 2 * pos80Slot2TotNat) := by
  generalize hp : headWitnessPayload80 b0Val nuc anc k pid sm thresh rej0 = p
  replace hp := hp.symm
  have hp62 : (p 62 != 0) = false := by
    rw [hp]
    rfl
  have hp30 : (p 30 == 1) = true := by
    rw [hp]
    rfl
  have hp31 : (p 31 == 1) = thresh := by
    rw [hp]
    cases thresh <;> rfl
  have hp79 : (p 79 == 1) = rej0 := by
    rw [hp]
    cases rej0 <;> rfl
  have hb0_eq := subBitsVal_eq_of_lt 3 3 b0Val (by decide) (by simpa using hb0) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hnuc_eq := subBitsVal_eq_of_lt 6 8 nuc (by decide) (by simpa using hnuc) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hanc_eq := subBitsVal_eq_of_lt 14 8 anc (by decide) (by simpa using hanc) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hpart_eq : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ p (pos80SubIdx 22 8 (by decide) j)) = 0 :=
    (bitsVal_congr (g := fun _ : Fin 8 ↦ (0 : ZMod 2)) fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl).trans (by simp [Pos24HeadCoordXor80.bitsVal])
  have hk_eq := subBitsVal_eq_of_lt 63 6 k.val (by decide)
    (lt_trans k.isLt (by decide)) (p := p) fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hpid_eq := subBitsVal_eq_of_lt 69 3 pid.val (by decide)
    (lt_trans pid.isLt (by decide)) (p := p) fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hsm_eq := subBitsVal_eq_of_lt 72 3 sm.val (by decide) sm.isLt (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hrem : ((p 75 == 0) && (p 76 == 0) && (p 77 == 0) && (p 78 == 0)) = true := by
    rw [hp]
    rfl
  have hpeq : (p == headWitnessPayload80 b0Val nuc anc k pid sm thresh rej0) = true := by
    rw [← hp]
    exact beq_self_eq_true p
  dsimp only [pos80IdealDist]
  rw [hp62, ite_eq_right Bool.noConfusion, hp30, ite_eq_left rfl]
  simp only [hb0_eq, hnuc_eq, hanc_eq, hpart_eq, hk_eq, hpid_eq, hsm_eq,
    k.isLt, pid.isLt, ↓reduceDIte]
  rw [hp31, hp79, hrem, hmeta, show ((0 : ℕ) == 0) = true from rfl, hpeq]
  rfl
theorem tailWitnessPayload80_eval_pos80IdealDist (s0 : Bool) (b0Val nuc anc part : ℕ)
    (dp : Fin 8) (keep : ℕ) (thresh rej0 : Bool) (hb0 : b0Val < 8) (hnuc : nuc < 256)
    (hanc : anc < 256) (hpart : part < 256) (hkeep : keep < pos24TailSpan8 dp)
    (hmeta : (if s0 then (nuc == 0) && decide (anc < 218) && decide (part < 217)
      else (b0Val == 0) && decide (nuc < 216) && decide (anc < 218) && (part == 0)) = true) :
    pos80IdealDist s0 (tailWitnessPayload80 b0Val nuc anc part dp keep thresh rej0) =
      if s0 then (1 : ℝ) / (8 * 218 * 2 * 2 * pos80Slot4TotNat)
      else (1 : ℝ) / (216 * 2 * 2 * pos80Slot2TotNat) := by
  generalize hp : tailWitnessPayload80 b0Val nuc anc part dp keep thresh rej0 = p
  replace hp := hp.symm
  have hp62 : (p 62 != 0) = false := by
    rw [hp]
    rfl
  have hp30 : (p 30 == 1) = false := by
    rw [hp]
    rfl
  have hp31 : (p 31 == 1) = thresh := by
    rw [hp]
    cases thresh <;> rfl
  have hp79 : (p 79 == 1) = rej0 := by
    rw [hp]
    cases rej0 <;> rfl
  have hb0_eq := subBitsVal_eq_of_lt 3 3 b0Val (by decide) (by simpa using hb0) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hnuc_eq := subBitsVal_eq_of_lt 6 8 nuc (by decide) (by simpa using hnuc) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hanc_eq := subBitsVal_eq_of_lt 14 8 anc (by decide) (by simpa using hanc) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hpart_eq := subBitsVal_eq_of_lt 22 8 part (by decide) (by simpa using hpart) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hfine_eq := subBitsVal_eq_of_lt 32 30 keep (by decide)
    (lt_of_lt_of_le hkeep (tailSpan8_lt_two_pow_30 dp)) (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have hdp_eq := subBitsVal_eq_of_lt 75 3 dp.val (by decide) dp.isLt (p := p)
    fun j ↦ by
      rw [hp]
      fin_cases j <;> rfl
  have h12 : ∀ j : Fin 12, p (pos80SubIdx 63 12 (by decide) j) = 0 := fun j ↦ by
    rw [hp]
    fin_cases j <;> rfl
  have hp78 : (p 78 == 0) = true := by
    rw [hp]
    rfl
  have hscr : (decide (∀ j : Fin 12, p (pos80SubIdx 63 12 (by decide) j) = 0) &&
      (p 78 == 0)) = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true h12, hp78⟩
  have hpeq : (p == tailWitnessPayload80 b0Val nuc anc part dp keep thresh rej0) = true := by
    rw [← hp]
    exact beq_self_eq_true p
  dsimp only [pos80IdealDist]
  rw [hp62, ite_eq_right Bool.noConfusion, hp30, ite_eq_right Bool.noConfusion]
  simp only [hscr, hb0_eq, hnuc_eq, hanc_eq, hpart_eq, hfine_eq, hdp_eq]
  rw [hp31, hp79, hmeta, decide_eq_true hkeep, hpeq]
  rfl
abbrev rScratch16Core : QRegister 16 (FullSysCatSegmentBridge.fullSysCoreWires 80) :=
  .block 4017 16 (by decide)
theorem coreElecCosetB1_wire_lt_3957 (i : Fin (3924 + 3)) :
    ((FullSysCatSegmentBridge.coreElecCosetB1Block pos24_6_le_80) i).val < 3957 := by
  refine Fin.addCases
    (motive := fun idx ↦
      ((FullSysCatSegmentBridge.coreElecCosetB1Block pos24_6_le_80) idx).val < 3957)
    (fun a ↦ ?_) (fun b ↦ ?_) i
  · rw [FullSysCatSegmentBridge.coreElecCosetB1Block, QRegister.concat_apply_left]
    have ha : a.val < 3924 := a.isLt
    change 0 + a.val < 3957
    omega
  · rw [FullSysCatSegmentBridge.coreElecCosetB1Block, QRegister.concat_apply_right]
    have hb : b.val < 3 := b.isLt
    change 3954 + b.val < 3957
    omega
theorem zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide
theorem twistCore_eq_of_lt3976 (cfg : SpecsAux.SpecMirror.Configuration)
    (γ₁ γ₂ : BitAssignment (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))
    (h : ∀ q : Fin (NuclearTwistAndXor654Concrete.fullSysCoreWires 80),
      q.val < 3976 → γ₁ q = γ₂ q) :
    NuclearTwistRealizes.twistCorePhase true pos24_22_le_80 cfg γ₁ =
      NuclearTwistRealizes.twistCorePhase true pos24_22_le_80 cfg γ₂ ∧
    ∀ q : Fin (NuclearTwistAndXor654Concrete.fullSysCoreWires 80), q.val < 3976 →
      NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ₁ q =
        NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ₂ q := by
  have hRegEq {m : ℕ} (r : QRegister m (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))
      (β₁ β₂ : BitAssignment (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))
      (hw : ∀ j, β₁ (r j) = β₂ (r j)) : regVal r β₁ = regVal r β₂ := by
    unfold regVal
    exact Finset.sum_congr rfl fun j _ ↦ by
      dsimp only
      rw [hw j]
  have hAct : NuclearTwistRealizes.barrelActive true γ₁ =
      NuclearTwistRealizes.barrelActive true γ₂ := by
    dsimp only [NuclearTwistRealizes.barrelActive, ↓reduceIte]
    rw [h _ (by decide), h _ (by decide), h _ (by decide)]
  have hAnchor := hRegEq (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
    (QRegExt.idReg _)) γ₁ γ₂ fun j ↦ h _ (by
      have := j.isLt
      change 3968 + j.val < 3976
      omega)
  have hBar (q : Fin (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))
      (hq : q.val < 3976) :
      NuclearTwistRealizes.barrelBitFn true pos24_22_le_80 γ₁ q =
        NuclearTwistRealizes.barrelBitFn true pos24_22_le_80 γ₂ q := by
    unfold NuclearTwistRealizes.barrelBitFn
    simp only [hAct, hAnchor]
    split_ifs with hcond
    · dsimp only
      split_ifs
      · exact h _ (by
          dsimp only
          have := hcond.2
          omega)
      · exact h _ (by
          dsimp only
          omega)
      · exact h q hq
    · exact h q hq
  have hPerm (q : Fin (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))
      (hq : q.val < 3976) :
      NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ₁ q =
        NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ₂ q := by
    unfold NuclearTwistRealizes.twistCorePermFn NuclearTwistRealizes.xor32BitFn
    rw [hBar q hq]
  refine ⟨?_, hPerm⟩
  set γ₁' := NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ₁
  set γ₂' := NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ₂
  have hElecLt (e : Fin SpecsAux.SpecMirror.numElectrons) (w : Fin 3)
      (j : Fin SpecsAux.SpecMirror.electronBits) :
      (NuclearTwistAndXor654Concrete.rElecSlotAxis
        (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)) e w j).val <
        3976 := by
    have he : e.val < 218 := e.isLt
    have hw : w.val < 3 := w.isLt
    have hj : j.val < 6 := j.isLt
    change (18 * e.val + 6 * w.val) + j.val < 3976
    omega
  have hS4 : NuclearTwistRealizes.slot4TotalPhaseExp pos24_22_le_80 γ₁' =
      NuclearTwistRealizes.slot4TotalPhaseExp pos24_22_le_80 γ₂' := by
    unfold NuclearTwistRealizes.slot4TotalPhaseExp
    rw [hPerm _ (by decide), hPerm _ (by decide), hPerm _ (by decide)]
    by_cases hcs : γ₂' (NuclearTwistAndXor654Concrete.wSlot2 (QRegExt.idReg _)) = 0 ∧
        γ₂' (NuclearTwistAndXor654Concrete.wSlot1 (QRegExt.idReg _)) = 0 ∧
        γ₂' (NuclearTwistAndXor654Concrete.wSlot0 (QRegExt.idReg _)) = 1
    · rw [ite_eq_left hcs, ite_eq_left hcs]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [hPerm (NuclearTwistAndXor654Concrete.rCosetB1 pos24_22_le_80 (QRegExt.idReg _) w)
          (by
            have := w.isLt
            change 3954 + w.val < 3976
            omega),
        hPerm (NuclearTwistAndXor654Concrete.rCosetB0 pos24_22_le_80 (QRegExt.idReg _) w)
          (by
            have := w.isLt
            change 3957 + w.val < 3976
            omega),
        hRegEq _ _ _ fun j ↦ hPerm _ (hElecLt 0 w j)]
    · rw [ite_eq_right hcs, ite_eq_right hcs]
  have hS2 : NuclearTwistRealizes.slot2TotalPhaseExp cfg pos24_22_le_80 γ₁' =
      NuclearTwistRealizes.slot2TotalPhaseExp cfg pos24_22_le_80 γ₂' := by
    unfold NuclearTwistRealizes.slot2TotalPhaseExp NuclearTwistRealizes.slot2AxisDelta
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hsum : NuclearTwistRealizes.slot2AxisSum w γ₁' =
        NuclearTwistRealizes.slot2AxisSum w γ₂' :=
      Finset.sum_congr rfl fun e _ ↦ hRegEq _ _ _ fun j ↦ hPerm _ (hElecLt e w j)
    have hc0a : NuclearTwistRealizes.coin0Active γ₁' =
        NuclearTwistRealizes.coin0Active γ₂' := by
      unfold NuclearTwistRealizes.coin0Active
      rw [hPerm _ (by decide), hPerm _ (by decide), hPerm _ (by decide)]
    have hnuc := hRegEq (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80
      (QRegExt.idReg _)) γ₁' γ₂' fun j ↦ hPerm _ (by
        have := j.isLt
        change 3960 + j.val < 3976
        omega)
    unfold NuclearTwistRealizes.slot2M48Val
    simp only [hsum, hc0a, hnuc]
  unfold NuclearTwistRealizes.twistCorePhase
  exact congrArg (NuclearTwistAndXor654Concrete.dyadicTurn 48) (congrArg₂ (· + ·) hS4 hS2)
theorem coreElecCosetB1_disjoint_rScratch16Core :
    (FullSysCatSegmentBridge.coreElecCosetB1Block pos24_6_le_80).DisjointWires
      rScratch16Core := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have h1 := coreElecCosetB1_wire_lt_3957 i
  have hj : (rScratch16Core j).val = 4017 + j.val := rfl
  omega
set_option maxRecDepth 65536 in
theorem blk_eq_of_eq_outside_scratch16 (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (s0 : Bool) (p₁ p₂ : BitAssignment 80)
    (heq : ∀ j : Fin 80, ¬(63 ≤ j.val ∧ j.val < 79) → p₁ j = p₂ j) :
    sysBlockAtPayloadGen pos24_coreWires80_eq.symm (pos24ConjCore80 qft cfg).1 s0 p₁ =
      sysBlockAtPayloadGen pos24_coreWires80_eq.symm (pos24ConjCore80 qft cfg).1 s0 p₂ := by
  let N80 := FullSysCatSegmentBridge.fullSysCoreWires 80
  let ket80 := MeasureBranchHadamardSem.ket (n := N80)
  have hScrVal (j : Fin 16) : (rScratch16Core j).val = 4017 + j.val := rfl
  let δ : BitAssignment 16 := fun j ↦ p₁ ⟨63 + j.val, by omega⟩ + p₂ ⟨63 + j.val, by omega⟩
  let f16 : BitAssignment 16 → BitAssignment 16 := fun b j ↦ b j + δ j
  have hf16 : Function.Bijective f16 :=
    Function.Involutive.bijective fun b ↦ funext fun j ↦ by simp [f16, add_assoc]
  let perm16 : Equiv.Perm (Fin (2 ^ 16)) :=
    (basisBitsEquiv 16).trans ((Equiv.ofBijective f16 hf16).trans (basisBitsEquiv 16).symm)
  let U_scr : Unitary (2 ^ N80) :=
    rScratch16Core.embedUnitary (Operator.permutationUnitary perm16)
  let P_scr : Operator (2 ^ N80) := U_scr.1
  let permBits (γ : BitAssignment N80) : BitAssignment N80 := fun q ↦
    if h : 4017 ≤ q.val ∧ q.val < 4033 then γ q + δ ⟨q.val - 4017, by omega⟩ else γ q
  have hPermKet (γ : BitAssignment N80) : P_scr.mulVec (ket80 γ) = ket80 (permBits γ) := by
    dsimp only [ket80]
    rw [MergedVepCoreSliceClosure.msc_ket_eq_basisKet γ,
      MergedVepCoreSliceClosure.msc_ket_eq_basisKet]
    refine NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet rScratch16Core perm16 γ
      (permBits γ) (fun j ↦ ?_) (fun q hnot ↦ ?_)
    · rw [NuclearTwistRealizes.basisBits_perm_ofBijective f16 hf16 _ j]
      dsimp only [f16, permBits]
      rw [dite_eq_left (by
        have := hScrVal j
        have := j.isLt
        omega)]
      exact congrArg (fun idx ↦ γ (rScratch16Core j) + δ idx) (Fin.ext (by
        dsimp
        omega))
    · dsimp only [permBits]
      exact dite_eq_right fun hs ↦ hnot ((QRegister.mem_image rScratch16Core q).mpr
        ⟨⟨q.val - 4017, by omega⟩, Fin.ext (by
          change 4017 + (q.val - 4017) = q.val
          omega)⟩)
  have hP_inv : P_scr * P_scr = 1 :=
    MeasureBranchHadamardSem.matrix_ext_ket fun γ ↦ by
      rw [← Matrix.mulVec_mulVec, hPermKet, hPermKet, Matrix.one_mulVec]
      refine congrArg ket80 (funext fun q ↦ ?_)
      dsimp only [permBits]
      split_ifs <;> simp only [add_assoc, zmod2_add_self, add_zero]
  have hP_sa : P_scrᴴ = P_scr := by
    have h1 := MergedVepCoreSliceClosure.msc_unitary_adj_mul_self U_scr
    rw [← Matrix.mul_one P_scrᴴ, ← hP_inv, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hQftComm : (FullSysCatSegmentBridge.fullSysQftCoreUnitary pos24_6_le_80 qft).1 * P_scr =
      P_scr * (FullSysCatSegmentBridge.fullSysQftCoreUnitary pos24_6_le_80 qft).1 :=
    QRegister.embedMatrix_comm_of_disjoint
      (FullSysCatSegmentBridge.coreElecCosetB1Block pos24_6_le_80) rScratch16Core
      coreElecCosetB1_disjoint_rScratch16Core _ _
  have hTwComm : (MergedVepTopCoinCollapse.uTwist80 cfg).1 * P_scr =
      P_scr * (MergedVepTopCoinCollapse.uTwist80 cfg).1 := by
    apply MeasureBranchHadamardSem.matrix_ext_ket
    intro γ
    dsimp only [ket80] at hPermKet
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPermKet γ,
      MergedVepTopCoinCollapse.uTwist80_mulVec_ket cfg (permBits γ),
      MergedVepTopCoinCollapse.uTwist80_mulVec_ket cfg γ,
      Matrix.mulVec_smul, hPermKet]
    obtain ⟨hPhEq, hPermLt⟩ := twistCore_eq_of_lt3976 cfg (permBits γ) γ fun q hq ↦ by
      dsimp only [permBits]
      exact dite_eq_right (by omega : ¬(4017 ≤ q.val ∧ q.val < 4033))
    rw [hPhEq]
    refine congrArg _ (congrArg MeasureBranchHadamardSem.ket
      (funext fun q ↦ ?_))
    by_cases hq : q.val < 3976
    · rw [hPermLt q hq]
      dsimp only [permBits]
      rw [dite_eq_right (by omega : ¬(4017 ≤ q.val ∧ q.val < 4033))]
    · rw [NuclearTwistRealizes.twistCorePermFn_high_eq true pos24_22_le_80 _ q (by omega)]
      dsimp only [permBits]
      rw [NuclearTwistRealizes.twistCorePermFn_high_eq true pos24_22_le_80 _ q (by omega)]
  have hPhComm : (castUnitaryPow2 pos24_coreWires80_eq.symm
      (uPosPhase true pos24TailSign pos24TailMag30)).1 * P_scr =
      P_scr * (castUnitaryPow2 pos24_coreWires80_eq.symm
        (uPosPhase true pos24TailSign pos24TailMag30)).1 := by
    apply MeasureBranchHadamardSem.matrix_ext_ket
    intro γ
    have hBitEq : PosSlots24BranchConcrete.posPhaseBit true pos24TailSign pos24TailMag30
        (fun q : Wire posCoreWires ↦ permBits γ
          ⟨q.val, Nat.lt_of_lt_of_eq q.isLt pos24_coreWires80_eq.symm⟩) =
        PosSlots24BranchConcrete.posPhaseBit true pos24TailSign pos24TailMag30
          (fun q : Wire posCoreWires ↦
            γ ⟨q.val, Nat.lt_of_lt_of_eq q.isLt pos24_coreWires80_eq.symm⟩) :=
      posPhaseBit_eq_of_eq_outside_scratch16 true pos24TailSign pos24TailMag30 _ _
        fun q hq ↦ by
          dsimp only [permBits]
          exact dite_eq_right hq
    dsimp only [ket80] at hPermKet
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPermKet γ,
      MergedVepTopCoinCollapse.uPosPhase80_mulVec_ket true pos24TailSign pos24TailMag30
        (permBits γ),
      MergedVepTopCoinCollapse.uPosPhase80_mulVec_ket true pos24TailSign pos24TailMag30 γ,
      Matrix.mulVec_smul, hPermKet]
    exact congrArg
      (fun b : Bool ↦ (if b then (-1 : ℂ) else 1) •
        MeasureBranchHadamardSem.ket (permBits γ)) hBitEq
  have hConjEq : (pos24ConjCore80 qft cfg).1 =
      ((FullSysCatSegmentBridge.fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
        (MergedVepTopCoinCollapse.uTwist80 cfg).1)ᴴ *
      (castUnitaryPow2 pos24_coreWires80_eq.symm
        (uPosPhase true pos24TailSign pos24TailMag30)).1 *
      ((FullSysCatSegmentBridge.fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
        (MergedVepTopCoinCollapse.uTwist80 cfg).1) := rfl
  have hConjComm : (pos24ConjCore80 qft cfg).1 * P_scr =
      P_scr * (pos24ConjCore80 qft cfg).1 := by
    rw [hConjEq]
    exact MergedVepTopCoinCollapse.conj_comm_of_parts_comm _ _ _ P_scr hP_sa
      hQftComm hTwComm hPhComm
  have hCoreIdx (p : BitAssignment 80) (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      coreIdxOf pos24_coreWires80_eq.symm s0 p z =
        (basisBitsEquiv N80).symm (MergedVepCoreSliceClosure.mscCoreBeta s0 p z) := by
    apply (basisBitsEquiv N80).injective
    funext q
    rw [(basisBitsEquiv N80).apply_symm_apply]
    exact (basisBitsEquiv posCoreWires).apply_symm_apply (coreBetaOf s0 p z) ▸ rfl
  have hCoreBetaPerm (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      permBits (MergedVepCoreSliceClosure.mscCoreBeta s0 p₁ z) =
        MergedVepCoreSliceClosure.mscCoreBeta s0 p₂ z := funext fun q ↦ by
    have hq_lt : q.val < 4034 := q.isLt
    dsimp only [permBits]
    by_cases hs : 4017 ≤ q.val ∧ q.val < 4033
    · rw [dite_eq_left hs,
        MergedVepCoreSliceClosure.coreBetaOf_at_sub s0 p₁ z q ⟨q.val - 3954, by omega⟩
          (by dsimp; omega),
        MergedVepCoreSliceClosure.coreBetaOf_at_sub s0 p₂ z q ⟨q.val - 3954, by omega⟩
          (by dsimp; omega)]
      have hidx : (⟨63 + (q.val - 4017), by omega⟩ : Fin 80) = ⟨q.val - 3954, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      dsimp only [δ]
      rw [hidx, ← add_assoc, zmod2_add_self, zero_add]
    · rw [dite_eq_right hs]
      by_cases hsub : 3954 ≤ q.val
      · rw [MergedVepCoreSliceClosure.coreBetaOf_at_sub s0 p₁ z q ⟨q.val - 3954, by omega⟩
            (by dsimp; omega),
          MergedVepCoreSliceClosure.coreBetaOf_at_sub s0 p₂ z q ⟨q.val - 3954, by omega⟩
            (by dsimp; omega)]
        exact heq ⟨q.val - 3954, by omega⟩ (by dsimp; omega)
      · by_cases hlt : q.val < SpecsAux.SpecMirror.systemQubits
        · exact (PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 s0 p₁ z ⟨q.val, hlt⟩).trans
            (PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 s0 p₂ z ⟨q.val, hlt⟩).symm
        · exact (PosSlots24SemanticOracleConcrete80.coreBetaOf_mid s0 p₁ z ⟨q.val, q.isLt⟩
            (Nat.le_of_not_lt hlt) (Nat.lt_of_not_ge hsub)).trans
            (PosSlots24SemanticOracleConcrete80.coreBetaOf_mid s0 p₂ z ⟨q.val, q.isLt⟩
              (Nat.le_of_not_lt hlt) (Nat.lt_of_not_ge hsub)).symm
  have hMulP (v : BitAssignment N80) :
      P_scrᴴ.mulVec ((pos24ConjCore80 qft cfg).1.mulVec (P_scr.mulVec (ket80 v))) =
        (pos24ConjCore80 qft cfg).1.mulVec (ket80 v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP_sa, Matrix.mul_assoc, hConjComm,
      ← Matrix.mul_assoc, hP_inv, Matrix.one_mul]
  ext x' x
  rw [sysBlockAtPayloadGen_apply, sysBlockAtPayloadGen_apply,
    hCoreIdx p₁ x', hCoreIdx p₁ x, hCoreIdx p₂ x', hCoreIdx p₂ x]
  refine (MergedVepCoreSliceClosure.msc_entry_eq_dotProduct
    (pos24ConjCore80 qft cfg).1 _ _).trans ((?_ : _ = _).trans
      (MergedVepCoreSliceClosure.msc_entry_eq_dotProduct
        (pos24ConjCore80 qft cfg).1 _ _).symm)
  dsimp only [ket80] at hPermKet hMulP
  rw [← hCoreBetaPerm x', ← hCoreBetaPerm x, ← hPermKet, ← hPermKet,
    ← MergedVepCoreSliceClosure.msc_adj_dotProduct P_scr, hMulP]
end ConfigPosSlots24Semantic80Physics
open scoped Matrix
open PosSlots24SemanticBridge (pos24_6_le_80)
set_option maxRecDepth 2000

def xor16Mat (δ : BitAssignment 16) : Operator (2 ^ 16) :=
  Matrix.of fun a b ↦ if basisBits 16 a = basisBits 16 b + δ then (1 : ℂ) else 0

theorem xor16Mat_mul_self (δ : BitAssignment 16) : xor16Mat δ * xor16Mat δ = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  let mid : Fin (2 ^ 16) := (basisBitsEquiv 16).symm (basisBits 16 c + δ)
  have hmid : basisBits 16 mid = basisBits 16 c + δ :=
    (basisBitsEquiv 16).apply_symm_apply (basisBits 16 c + δ)
  rw [Finset.sum_eq_single mid]
  · simp only [xor16Mat, Matrix.of_apply, hmid, ↓reduceIte, mul_one, Matrix.one_apply]
    have hiff : (basisBits 16 a = basisBits 16 c + δ + δ) ↔ (a = c) :=
      ⟨fun h ↦ (basisBitsEquiv 16).injective (funext fun j ↦ by
        have hj := congrFun h j
        simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero] at hj
        exact hj),
       fun h ↦ by
         subst h
         funext j
         simp⟩
    simp [hiff]
  · intro b _ hb
    have hne : basisBits 16 b ≠ basisBits 16 c + δ := fun heq ↦
      hb ((basisBitsEquiv 16).injective (heq.trans hmid.symm))
    simp [xor16Mat, hne]
  · intro hm
    exact False.elim (hm (Finset.mem_univ _))

theorem xor16Mat_sa (δ : BitAssignment 16) : (xor16Mat δ)ᴴ = xor16Mat δ := by
  ext a b
  simp only [Matrix.conjTranspose_apply, xor16Mat, Matrix.of_apply]
  have hsym {u v : BitAssignment 16} (h : u = v + δ) : v = u + δ := funext fun j ↦ by
    have hj := congrFun h j
    simp only [Pi.add_apply] at hj ⊢
    rw [hj, add_assoc, zmod2_add_self, add_zero]
  split_ifs with h1 h2
  · exact star_one _
  · exact False.elim (h2 (hsym h1))
  · rename_i h2
    exact False.elim (h1 (hsym h2))
  · exact star_zero _

theorem perm_conj_entry {α : Type*} [Fintype α] [DecidableEq α] (P U : Matrix α α ℂ)
    (f : α → α) (hf_inv : ∀ x, f (f x) = x) (hP : ∀ a b, P a b = if a = f b then 1 else 0)
    (i' i : α) : (P * U * P) (f i') (f i) = U i' i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk ↦ by
      simp only [hP k (f i), hf_inv, hk, ↓reduceIte, mul_zero])
      (fun hm ↦ absurd (Finset.mem_univ _) hm),
    Matrix.mul_apply, Finset.sum_eq_single i' (fun k _ hk ↦ by
      have hne : f i' ≠ f k := fun h ↦ hk (by simpa [hf_inv] using (congrArg f h).symm)
      simp only [hP (f i') k, hne, ↓reduceIte, zero_mul])
      (fun hm ↦ absurd (Finset.mem_univ _) hm)]
  simp only [hP (f i') i', hP i (f i), hf_inv, ↓reduceIte, one_mul, mul_one]
end PosSlots24Semantic80Physics
end
end ModPosSlots24Semantic80Physics

end QuantumComputation.Specs.StoppingPowerSolution
