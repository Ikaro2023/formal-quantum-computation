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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.KineticOneWrapUnembed

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
section

open QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
open Operator QProg DynamicCircuit Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectStructuredCB
open PhotochemistrySolution.SelectWalkerDecode
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] pLo13 pHi13 pHiUnx13 pLoUnx12
theorem finBitsVal_eq_sum : ∀ (B : ℕ) (f : Fin B -> ZMod 2), finBitsVal f = ∑ i : Fin B,
    ((f i).val * 2 ^ i.val : ℕ)
  | 0, _ => rfl
  | B + 1, f => by
      rw [show finBitsVal f = (f 0).val + 2 * finBitsVal (fun i => f i.succ) from rfl,
          Fin.sum_univ_succ,
        finBitsVal_eq_sum B, Finset.mul_sum, Fin.val_zero, pow_zero, mul_one]
      exact congrArg ((f 0).val + ·)
          (Finset.sum_congr rfl fun i _ => by rw [Fin.val_succ, pow_succ']; ring)
theorem finBits8_expand (f : Fin 8 ->
    ZMod 2) : finBitsVal f =
    (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val + 16 * (f 4).val + 32 * (f 5).val +
        64 * (f 6).val + 128 * (f 7).val :=
    by erw [show finBitsVal f = (f 0).val + 2 * ((f 1).val + 2 * ((f 2).val + 2 * ((f 3).val +
      2 * ((f 4).val + 2 * ((f 5).val + 2 * ((f 6).val + 2 * ((f 7).val + 2 * 0))))))) from rfl];
          ring
theorem emb25_disj :
    (∀ q : Fin 13, q ≠ 8 -> ∀ v : Fin 13, embLo25 v ≠ embHi25 q) /\
    (∀ u : Fin 13, u ≠ 11 -> ∀ v : Fin 13, embHi25 v ≠ embLo25 u) /\
    (∀ q : Fin 12, q ≠ 11 -> ∀ v : Fin 13, embHiUnx24 v ≠ embLoUnx24 q) /\
    (∀ j : Fin 8, ∀ v : Fin 12, embLoUnx24 v ≠ embHiUnx24 ⟨j.val, by omega⟩) := by
  decide
theorem nibVal_lt (f : Fin 4 -> ZMod 2) : nibVal f < 16 := by
  have ⟨_, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ := ⟨(f 0).val_lt, (f 1).val_lt, (f 2).val_lt, (f 3).val_lt⟩
  unfold nibVal; omega
theorem pAxis25_spec (γ : BitAssignment 25) (hcl : ∀ u : Fin 25, 16 <= u.val -> γ u = 0) :
    let out := pAxis25.fwdBits γ;
    let uBits : Fin 8 -> ZMod 2 := fun k => out ⟨8 + k.val, by omega⟩;
    let cb : ZMod 2 := out ⟨23, by decide⟩;
    (∀ k : Fin 8, out ⟨k.val, by omega⟩ = γ ⟨k.val,
      by omega⟩) /\ ((finBitsVal uBits : ℤ) - 256 * cb.val + 1) =
           twosComplement_frozen (byteOfBits (fun k => γ ⟨k.val, by omega⟩)) -
      twosComplement_frozen (byteOfBits (fun k => γ ⟨8 + k.val, by omega⟩)) /\ out ⟨24, by decide⟩ =
          uBits 0 * uBits 1 /\
    ∀ q : Fin 16, (pAxisUnx24.fwdBits (fun u : Fin 24 => out ⟨u.val, by omega⟩))
        ⟨q.val, by omega⟩ = γ ⟨q.val, by omega⟩ := by
  have ⟨hinjLo, hinjHi, hinjHu, hinjLu⟩ : Function.Injective embLo25 ∧ Function.Injective embHi25 ∧
      Function.Injective embHiUnx24 ∧ Function.Injective embLoUnx24 := by decide
  let fLo : Fin 9 -> ZMod 2 := fun j =>
      if j.val < 4 then γ ⟨j.val, by omega⟩ else if j.val < 8 then γ ⟨4 + j.val, by omega⟩ else 0
  obtain ⟨_, hmLo_eq⟩ := mask9_of_bits fLo
  let mLo : Fin 256 := ⟨(fLo 0).val + 2 * (fLo 1).val + 4 * (fLo 2).val + 8 * (fLo 3).val +
      16 * (fLo 4).val + 32 * (fLo 5).val + 64 * (fLo 6).val + 128 * (fLo 7).val, by
    have ⟨_, _, _, _, _, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ :=
      ⟨(fLo 0).val_lt, (fLo 1).val_lt, (fLo 2).val_lt, (fLo 3).val_lt, (fLo 4).val_lt,
          (fLo 5).val_lt, (fLo 6).val_lt, (fLo 7).val_lt⟩
    omega⟩
  have hmLo_val : mLo.val + 256 * (fLo 8).val = mLo.val := add_zero _
  have pullLo : (fun q : Fin 13 => γ (embLo25 q)) = maskToBits 13 mLo.val := funext fun q => by
    rw [← hmLo_val, hmLo_eq q]
    fin_cases q <;> first | rfl | exact hcl _ (by decide)
  let γ1 := (mapCP embLo25 pLo13).fwdBits γ
  let out := (mapCP embHi25 pHi13).fwdBits γ1
  have hLo := axis_micro_certs.1 mLo
  let oLo := pLo13.fwdBits (maskToBits 13 mLo.val)
  have hγ1_lo (u : Fin 13) : γ1 (embLo25 u) = oLo u :=
    (mapCP_fwd_apply embLo25 hinjLo pLo13 γ u).trans (congrFun (congrArg pLo13.fwdBits pullLo) u)
  let fHi : Fin 9 -> ZMod 2 := fun j =>
    if j.val < 4 then γ ⟨4 + j.val, by omega⟩ else if j.val < 8 then γ ⟨8 + j.val,
        by omega⟩ else oLo ⟨11, by decide⟩
  obtain ⟨hmHi_lt, hmHi_eq⟩ := mask9_of_bits fHi
  let mHi : Fin 512 := ⟨_, hmHi_lt⟩
  have pullHi : (fun q : Fin 13 => γ1 (embHi25 q)) = maskToBits 13 mHi.val := funext fun q =>
      by
    rw [hmHi_eq q]
    rcases eq_or_ne q 8 with rfl | hq8
    · exact hγ1_lo 11
    · exact (mapCP_fwd_outside embLo25 hinjLo pLo13 γ (embHi25 q) (emb25_disj.1 q hq8)).trans
        (by fin_cases q <;> first | contradiction | rfl | exact hcl _ (by decide))
  have hHi := axis_micro_certs.2.1 mHi
  let oHi := pHi13.fwdBits (maskToBits 13 mHi.val)
  have hout_hi (u : Fin 13) : out (embHi25 u) = oHi u :=
    (mapCP_fwd_apply embHi25 hinjHi pHi13 γ1 u).trans (congrFun (congrArg pHi13.fwdBits pullHi) u)
  have hout_lo (u : Fin 13) (hu : u ≠ 11) : out (embLo25 u) = oLo u :=
    (mapCP_fwd_outside embHi25 hinjHi pHi13 γ1 (embLo25 u) (emb25_disj.2.1 u hu)).trans (hγ1_lo u)
  have hgLo (q : Fin 8) : maskToBits 13 mLo.val ⟨q.val, by omega⟩ = fLo ⟨q.val, by omega⟩ :=
    (congrFun (congrArg (maskToBits 13) hmLo_val.symm) _).trans
      (by simpa [show q.val < 9 by omega] using hmLo_eq ⟨q.val, by omega⟩)
  have hgHi (q : Fin 9) : maskToBits 13 mHi.val ⟨q.val, by omega⟩ = fHi q := by
    simpa using hmHi_eq ⟨q.val, by omega⟩
  refine ⟨fun k => ?_, ?_, ?_, fun q => ?_⟩
  · fin_cases k <;> first
      | exact (hout_lo 0 (by decide)).trans ((hLo.1 0).trans (hgLo 0))
      | exact (hout_lo 1 (by decide)).trans ((hLo.1 1).trans (hgLo 1))
      | exact (hout_lo 2 (by decide)).trans ((hLo.1 2).trans (hgLo 2))
      | exact (hout_lo 3 (by decide)).trans ((hLo.1 3).trans (hgLo 3))
      | exact (hout_hi 0).trans ((hHi.1 0).trans (hgHi 0))
      | exact (hout_hi 1).trans ((hHi.1 1).trans (hgHi 1))
      | exact (hout_hi 2).trans ((hHi.1 2).trans (hgHi 2))
      | exact (hout_hi 3).trans ((hHi.1 3).trans (hgHi 3))
  · obtain ⟨h1, h2⟩ := And.intro hLo.2.1 hHi.2.1
    rw [tc_byte_split (fun k => γ ⟨k.val, by omega⟩), tc_byte_split (fun k =>
        γ ⟨8 + k.val, by omega⟩)]
    dsimp only at h1 h2 ⊢
    rw [finBits8_expand]
    change (((out (embLo25 4)).val + 2 * (out (embLo25 5)).val + 4 * (out (embLo25 6)).val + 8 *
        (out (embLo25 7)).val +
      16 * (out (embHi25 4)).val + 32 * (out (embHi25 5)).val + 64 * (out (embHi25 6)).val + 128 *
          (out (embHi25 7)).val : ℕ) : ℤ) -
      256 * (out (embHi25 12)).val + 1 = _
    rw [hout_lo 4 (by decide), hout_lo 5 (by decide), hout_lo 6 (by decide), hout_lo 7 (by decide),
      hout_hi 4, hout_hi 5, hout_hi 6, hout_hi 7, hout_hi 12]
    change ((oLo 4).val + 2 * (oLo 5).val + 4 * (oLo 6).val + 8 * (oLo 7).val) + 16 * (oLo 11).val =
        _ at h1
    change (((oHi 4).val + 2 * (oHi 5).val + 4 * (oHi 6).val + 8 * (oHi 7).val : ℕ) : ℤ) + 16 *
        (1 - (oHi 12).val) =
      15 + tcNib (fun k => maskToBits 13 mHi.val ⟨k.val, by omega⟩) -
        tcNib (fun k => maskToBits 13 mHi.val ⟨4 + k.val, by omega⟩) +
            (maskToBits 13 mHi.val 8).val at h2
    rw [congrArg nibVal (funext fun k => (hgLo ⟨k.val, by omega⟩).trans (show _ =
        γ ⟨k.val, by omega⟩ by fin_cases k <;> rfl)),
      congrArg nibVal (funext fun k => (hgLo ⟨4 + k.val, by omega⟩).trans (show _ =
          γ ⟨8 + k.val, by omega⟩ by fin_cases k <;> rfl))] at h1
    rw [congrArg tcNib (funext fun k => (hgHi ⟨k.val, by omega⟩).trans (show _ =
        γ ⟨4 + k.val, by omega⟩ by fin_cases k <;> rfl)),
      congrArg tcNib (funext fun k =>
        (hgHi ⟨4 + k.val, by omega⟩).trans (show _ = γ ⟨8 + (4 + k.val),
            by omega⟩ by fin_cases k <;> rfl)),
      show (maskToBits 13 mHi.val 8).val = (oLo 11).val from congrArg ZMod.val (hgHi 8)] at h2
    have := nibVal_lt (fun k => γ ⟨8 + k.val, by omega⟩)
    push_cast at h2 ⊢; omega
  · exact (hout_lo 12 (by decide)).trans (hLo.2.2.1.trans (congrArg₂ (· * ·)
        (hout_lo 4 (by decide)).symm (hout_lo 5 (by decide)).symm))
  · let δ0 : BitAssignment 24 := fun u => out ⟨u.val, by omega⟩
    let δ1 := (mapCP embHiUnx24 pHiUnx13).fwdBits δ0
    have hpullH : (fun r : Fin 13 => δ0 (embHiUnx24 r)) = oHi :=
      funext fun r =>
          (show δ0 (embHiUnx24 r) = out (embHi25 r) by fin_cases r <;> rfl).trans (hout_hi r)
    have hδ1_hi (r : Fin 9) : δ1 (embHiUnx24 ⟨r.val, by omega⟩) = fHi r :=
      (mapCP_fwd_apply embHiUnx24 hinjHu pHiUnx13 δ0 _).trans ((congrFun (congrArg pHiUnx13.fwdBits
          hpullH) _).trans
        ((hHi.2.2.2 r).trans (hgHi r)))
    have hpullL : (fun r : Fin 12 => δ1 (embLoUnx24 r)) = fun r => oLo ⟨r.val, by omega⟩ :=
        funext fun r =>
      if hr : r = 11 then hr ▸ hδ1_hi 8
      else (mapCP_fwd_outside embHiUnx24 hinjHu pHiUnx13 δ0 (embLoUnx24 r)
          (emb25_disj.2.2.1 r hr)).trans
        ((show δ0 (embLoUnx24 r) = out (embLo25 ⟨r.val, by omega⟩) by fin_cases r <;> rfl).trans
          (hout_lo ⟨r.val, by omega⟩ fun e => hr (Fin.ext (congrArg (Fin.val : Fin 13 -> ℕ) e))))
    have hLstep (j : Fin 8) : (mapCP embLoUnx24 pLoUnx12).fwdBits δ1 (embLoUnx24 ⟨j.val,
        by omega⟩) = fLo ⟨j.val, by omega⟩ :=
      (mapCP_fwd_apply embLoUnx24 hinjLu pLoUnx12 δ1 _).trans
        ((congrFun (congrArg pLoUnx12.fwdBits hpullL) _).trans ((hLo.2.2.2 j).trans (hgLo j)))
    have hHstep (j : Fin 8) : (mapCP embLoUnx24 pLoUnx12).fwdBits δ1 (embHiUnx24 ⟨j.val,
        by omega⟩) = fHi ⟨j.val, by omega⟩ :=
      (mapCP_fwd_outside embLoUnx24 hinjLu pLoUnx12 δ1 _ (emb25_disj.2.2.2 j)).trans (hδ1_hi ⟨j.val,
          by omega⟩)
    fin_cases q <;> first
      | exact hLstep 0
      | exact hLstep 1
      | exact hLstep 2
      | exact hLstep 3
      | exact hHstep 0
      | exact hHstep 1
      | exact hHstep 2
      | exact hHstep 3
      | exact hLstep 4
      | exact hLstep 5
      | exact hLstep 6
      | exact hLstep 7
      | exact hHstep 4
      | exact hHstep 5
      | exact hHstep 6
      | exact hHstep 7
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
end

set_option exponentiation.threshold 8192

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
def wValNat_xnorA (m w : ℕ) : ℕ :=
    cond (Nat.beq w 58) ((m % 2) * ((m / 2) % 2)) (cond (Nat.beq w 57) ((m / 256) % 2)
    (cond (Nat.ble 24 w && Nat.blt w 32) ((m / Nat.pow 2 (w - 24)) % 2) 0))
def tokBitNat_xnorA (m : ℕ)
    (t : QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor.DToken) : ℕ :=
    (cond t.2.2 1 0 + t.2.1.foldr (fun s acc => wValNat_xnorA m (s % 304) + acc) 0) % 2
def poolSumNat_xnorA (m : ℕ)
    (pool : List QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor.DToken) : ℕ :=
    pool.foldr (fun t acc => tokBitNat_xnorA m t * Nat.pow 2 t.1 + acc) 0
def deltaSqNat_xnorA (uNat cBit : ℕ) : ℕ :=
    cond (Nat.beq cBit 0) ((uNat + 1) * (uNat + 1)) ((255 - uNat) * (255 - uNat))
def mkTok_xnorA (k : ℕ) (ws : List ℕ)
    (b : Bool) : QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor.DToken :=
    Prod.mk k (Prod.mk ws b)
def axTokens0_cert_xnor :
    List QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor.DToken :=
    [mkTok_xnorA 0 [24] true, mkTok_xnorA 2 [58] false,
    mkTok_xnorA 8 [57] true, mkTok_xnorA 2 [26] false,
    mkTok_xnorA 3 [27] false, mkTok_xnorA 4 [28] false,
    mkTok_xnorA 5 [29] false, mkTok_xnorA 6 [30] false,
    mkTok_xnorA 7 [31] false, mkTok_xnorA 8 [24, 57] false,
    mkTok_xnorA 9 [25, 57] false, mkTok_xnorA 10 [26, 57] false,
    mkTok_xnorA 11 [27, 57] false, mkTok_xnorA 12 [28, 57] false,
    mkTok_xnorA 13 [29, 57] false, mkTok_xnorA 14 [30, 57] false,
    mkTok_xnorA 15 [31, 57] false, mkTok_xnorA 2 [24, 26] true,
    mkTok_xnorA 3 [24, 27] true, mkTok_xnorA 4 [24, 28] true,
    mkTok_xnorA 5 [24, 29] true, mkTok_xnorA 6 [24, 30] true,
    mkTok_xnorA 7 [24, 31] true, mkTok_xnorA 3 [25, 26] true,
    mkTok_xnorA 4 [25, 27] true, mkTok_xnorA 5 [25, 28] true,
    mkTok_xnorA 6 [25, 29] true, mkTok_xnorA 7 [25, 30] true,
    mkTok_xnorA 8 [25, 31] true, mkTok_xnorA 5 [26, 27] true,
    mkTok_xnorA 6 [26, 28] true, mkTok_xnorA 7 [26, 29] true,
    mkTok_xnorA 8 [26, 30] true, mkTok_xnorA 9 [26, 31] true,
    mkTok_xnorA 7 [27, 28] true, mkTok_xnorA 8 [27, 29] true,
    mkTok_xnorA 9 [27, 30] true,
  mkTok_xnorA 10 [27, 31] true, mkTok_xnorA 9 [28, 29] true,
      mkTok_xnorA 10 [28, 30] true, mkTok_xnorA 11 [28, 31] true,
      mkTok_xnorA 11 [29, 30] true, mkTok_xnorA 12 [29, 31] true,
      mkTok_xnorA 13 [30, 31] true]
def axCertCheck_xnorA (m : ℕ) : Bool :=
  let uNat := m % 256; let cBit := m / 256; let d2 := deltaSqNat_xnorA uNat cBit
  Nat.beq (poolSumNat_xnorA m axTokens0_cert_xnor) (d2 + 21844)
def checkTree_xnorA (base : ℕ) : ℕ → Bool
  | 0 => axCertCheck_xnorA base
  | d + 1 => checkTree_xnorA base d && checkTree_xnorA (base + Nat.pow 2 d) d
theorem axCert_all_xnorA : checkTree_xnorA 0 9 = true := by decide +kernel
theorem checkTree_mem_xnor : ∀ (d base m : ℕ),
    checkTree_xnorA base d = true → base ≤ m → m < base + Nat.pow 2 d →
      axCertCheck_xnorA m = true := by
  intro d
  induction d with
  | zero => exact fun base m h hlo hhi => Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo ▸ h
  | succ d ih =>
      exact fun base m h hlo hhi =>
        if hmid : m < base + Nat.pow 2 d then ih base m (Bool.and_eq_true_iff.mp h).1 hlo hmid
        else ih (base + Nat.pow 2 d) m (Bool.and_eq_true_iff.mp h).2 (Nat.le_of_not_lt hmid)
          (Nat.lt_of_lt_of_eq hhi (by simp [Nat.pow_succ, Nat.mul_two, Nat.add_assoc]))
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
open Operator QProg DynamicCircuit Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem axMap_facts : (∀ ax : Fin 3, Function.Injective (axMap25 ax)) /\ (∀ ax : Fin 3,
    Function.Injective (axMap24 ax)) /\ (∀ a b : Fin 3, a ≠ b -> ∀ u v : Fin 25, axMap25 a u ≠
        axMap25 b v) /\ (∀ a b : Fin 3,
    a ≠ b -> ∀ u v : Fin 24, axMap24 a u ≠ axMap24 b v) /\ (∀ ax : Fin 3, ∀ u : Fin 24,
    isDaddaOwned (axMap24 ax u).val = false /\ (axMap24 ax u).val ≠ 49) /\ (∀ ax : Fin 3,
        ∀ u : Fin 24, ∀ k : Fin 18,
    axMap24 ax u ≠ d2Wire k) := by decide +kernel
theorem axTokens_shift (ax : Fin 3) (γ : BitAssignment 304) :
    poolSum (axTokens ax.val) γ =
      poolSum (axTokens 0) (fun w =>
        if w.val = 58 then γ (axMap25 ax ⟨24, by omega⟩)
        else if w.val = 57 then γ (axMap25 ax ⟨23, by omega⟩)
        else if h : 24 <= w.val /\ w.val < 32 then γ (axMap25 ax ⟨8 + (w.val - 24), by omega⟩)
        else 0) := by
  fin_cases ax <;> rfl
theorem zmod2_add_val_xnorA (a b : ZMod 2) : (a + b).val = (a.val + b.val) % 2 := by
  fin_cases a <;> fin_cases b <;> decide
theorem zmod2_mul_val_xnorA (a b : ZMod 2) : (a * b).val = a.val * b.val := by
  fin_cases a <;> fin_cases b <;> decide
theorem foldr_zmod2_val_xnorA (m : ℕ) (γ0 : BitAssignment 304)
    (hw : ∀ u : Wire 304, (γ0 u).val = wValNat_xnorA m u.val) :
    ∀ ws : List ℕ,
      (ws.foldr (fun s (acc : ZMod 2) => γ0 (w304 s) + acc) (0 : ZMod 2)).val =
        (ws.foldr (fun s acc => wValNat_xnorA m (s % 304) + acc) 0) % 2
  | [] => rfl
  | s :: ws => by
      dsimp only [List.foldr]
      rw [zmod2_add_val_xnorA,
        foldr_zmod2_val_xnorA m γ0 hw ws, hw (w304 s), show (w304 s).val =
            s % 304 from rfl]
      omega
theorem tokBit_eq_nat_xnorA (m : ℕ) (t : DToken) (γ0 : BitAssignment 304)
    (hw : ∀ u : Wire 304,
    (γ0 u).val = wValNat_xnorA m u.val) :
    (tokBit t γ0).val = tokBitNat_xnorA m t := by
  rw [tokBit, tokBitNat_xnorA, zmod2_add_val_xnorA,
    foldr_zmod2_val_xnorA m γ0 hw t.2.1]
  cases t.2.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, ZMod.val_zero, ZMod.val_one, cond] <;>
      omega
theorem poolSum_eq_nat_xnorA (m : ℕ) (γ0 : BitAssignment 304) (hw : ∀ u : Wire 304,
    (γ0 u).val = wValNat_xnorA m u.val) :
    ∀ pool : List DToken, poolSum pool γ0 = poolSumNat_xnorA m pool
  | [] => rfl
  | t :: pool => by
      dsimp only [poolSum, poolSumNat_xnorA, List.foldr]
      rw [tokBit_eq_nat_xnorA m t γ0 hw]
      exact congrArg (_ + ·) (poolSum_eq_nat_xnorA m γ0 hw pool)
theorem mask9_bits_eq_xnorA (u : Fin 8 -> ZMod 2) (c : ZMod 2) :
    let m := finBitsVal u + 256 * c.val
    m < 512 /\ m % 256 = finBitsVal u /\ m / 256 = c.val /\ m % 2 = (u 0).val /\ (m / 2) % 2 =
        (u 1).val /\ (m / 256) % 2 = c.val /\
      (∀ k : Fin 8, (m / 2 ^ k.val) % 2 = (u k).val) := by
  have ⟨_, _, _, _, _, _, _, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ :=
    ⟨(u 0).val_lt, (u 1).val_lt, (u 2).val_lt, (u 3).val_lt, (u 4).val_lt, (u 5).val_lt,
      (u 6).val_lt, (u 7).val_lt, c.val_lt, finBits8_expand u⟩
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, fun k => ?_⟩
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, 
      Nat.reducePow] <;> omega
theorem deltaSqNat_eq_xnorA (uNat cBit : ℕ) (hu : uNat < 256)
    (hc : cBit < 2) : deltaSqNat_xnorA uNat cBit =
      ((uNat : ℤ) - 256 * (cBit : ℤ) + 1).natAbs ^ 2 := by
  rcases (show cBit = 0 ∨ cBit = 1 by omega) with rfl | rfl
  · exact (pow_two (uNat + 1)).symm.trans (congrArg (· ^ 2) (by omega))
  · exact (pow_two (255 - uNat)).symm.trans (congrArg (· ^ 2) (by omega))
theorem tcMem (a : Fin 256) :
    -128 <= twosComplement_frozen a /\ twosComplement_frozen a <= 127 := by
  revert a; decide +kernel
theorem tcSqLe (a b : Fin 256) : (twosComplement_frozen a -
    twosComplement_frozen b).natAbs ^ 2 <= 65025 := by
  have ⟨_, _⟩ : _ ∧ _ := ⟨tcMem a, tcMem b⟩
  exact Nat.pow_le_pow_left (by omega : _ <= 255) 2
theorem axPool_eval (ax : Fin 3) (γ : BitAssignment 304)
    (hp01 : γ (axMap25 ax ⟨24, by omega⟩) = γ (axMap25 ax ⟨8, by omega⟩) *
        γ (axMap25 ax ⟨9, by omega⟩)) :
    let uBits : Fin 8 -> ZMod 2 := fun k => γ (axMap25 ax ⟨8 + k.val, by omega⟩);
    let delta : ℤ := (finBitsVal uBits : ℤ) - 256 * (γ (axMap25 ax ⟨23, by omega⟩)).val + 1;
    poolSum (axTokens ax.val) γ = delta.natAbs ^ 2 + 21844 := by
  intro uBits _
  let cBit : ZMod 2 := γ (axMap25 ax ⟨23, by omega⟩)
  obtain ⟨hm_lt, hm_mod, hm_div, hm_0, hm_1, hm_c, hm_k⟩ := mask9_bits_eq_xnorA uBits cBit
  have hm := checkTree_mem_xnor 9 0 (finBitsVal uBits + 256 * cBit.val)
    axCert_all_xnorA (Nat.zero_le _) hm_lt
  simp only [axCertCheck_xnorA, Nat.beq_eq] at hm
  rw [hm_mod, hm_div, deltaSqNat_eq_xnorA _ _ (finBitsVal_lt uBits) cBit.val_lt] at hm
  refine (axTokens_shift ax γ).trans ((congrArg (poolSum · _) (by
      simp [axTokens, axTokens0_cert_xnor, mkTok_xnorA, List.range_succ] :
        axTokens 0 = axTokens0_cert_xnor)).trans
    ((poolSum_eq_nat_xnorA _ _ (fun u => ?_) _).trans hm))
  dsimp only [wValNat_xnorA]
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq]
  split_ifs with h58 h57 h24
  · rw [hp01, zmod2_mul_val_xnorA, hm_0, hm_1]
    exact rfl
  · exact hm_c.symm
  · exact (hm_k ⟨u.val - 24, by omega⟩).symm
  · rfl
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
end
end

-- proof on polyFastQft8Bracket blocks
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.FastQft8
-- calculus & pure Bool shift mirrors for 34-AND QFT8
/-- Construct a `7`-bit vector from explicit `Bool` arguments. -/
def vec7 (d0 d1 d2 d3 d4 d5 d6 : Bool) : Fin 7 → Bool
  | 0 => d0 | 1 => d1 | 2 => d2 | 3 => d3 | 4 => d4 | 5 => d5 | 6 => d6
/-- Pure `Bool` single-wire update on `Fin 7`. -/
def updD (d : Fin 7 → Bool) (k : Fin 7) (v : Bool) : Fin 7 → Bool :=
  fun j ↦ if j = k then v else d j
/-- Pure `Bool` single-wire update on `Fin 8`. -/
def updP (p : Fin 8 → Bool) (i : Fin 8) (v : Bool) : Fin 8 → Bool := fun m ↦
    if m = i then v else p m
theorem fun_false_eq_vec7 : (fun _ : Fin 7 ↦ false) =
    vec7 false false false false false false false :=
  funext fun j ↦ by fin_cases j <;> rfl
@[simp] theorem updD_vec7_0 (d0 d1 d2 d3 d4 d5 d6 v : Bool) : updD (vec7 d0 d1 d2 d3 d4 d5 d6) 0 v =
    vec7 v d1 d2 d3 d4 d5 d6 :=
  funext fun j ↦ by fin_cases j <;> rfl
@[simp] theorem updD_vec7_1 (d0 d1 d2 d3 d4 d5 d6 v : Bool) : updD (vec7 d0 d1 d2 d3 d4 d5 d6) 1 v =
    vec7 d0 v d2 d3 d4 d5 d6 :=
  funext fun j ↦ by fin_cases j <;> rfl
@[simp] theorem updD_vec7_2 (d0 d1 d2 d3 d4 d5 d6 v : Bool) : updD (vec7 d0 d1 d2 d3 d4 d5 d6) 2 v =
    vec7 d0 d1 v d3 d4 d5 d6 :=
  funext fun j ↦ by fin_cases j <;> rfl
@[simp] theorem updD_vec7_3 (d0 d1 d2 d3 d4 d5 d6 v : Bool) : updD (vec7 d0 d1 d2 d3 d4 d5 d6) 3 v =
    vec7 d0 d1 d2 v d4 d5 d6 :=
  funext fun j ↦ by fin_cases j <;> rfl
@[simp] theorem updD_vec7_4 (d0 d1 d2 d3 d4 d5 d6 v : Bool) : updD (vec7 d0 d1 d2 d3 d4 d5 d6) 4 v =
    vec7 d0 d1 d2 d3 v d5 d6 :=
  funext fun j ↦ by fin_cases j <;> rfl
@[simp] theorem updD_vec7_5 (d0 d1 d2 d3 d4 d5 d6 v : Bool) : updD (vec7 d0 d1 d2 d3 d4 d5 d6) 5 v =
    vec7 d0 d1 d2 d3 d4 v d6 :=
  funext fun j ↦ by fin_cases j <;> rfl
@[simp] theorem updD_vec7_6 (d0 d1 d2 d3 d4 d5 d6 v : Bool) : updD (vec7 d0 d1 d2 d3 d4 d5 d6) 6 v =
    vec7 d0 d1 d2 d3 d4 d5 v :=
  funext fun j ↦ by fin_cases j <;> rfl
/-- Unsigned integer value of `w` pure `Bool` bits. -/
def regValBool : ∀ (w : ℕ), (Fin w → Bool) → ℕ
  | 0, _ => 0
  | w + 1, b => cond (b 0) 1 0 + 2 * regValBool w (fun i ↦ b i.succ)

open Operator QProg DynamicCircuit Matrix Circuit Qubit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
/-- Boolean witness for `rP` (`8` bits) and `rDelta` (`7` bits) under `γ`. -/
def MatchesPD {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M) (γ : BitAssignment M)
    (p : Fin 8 → Bool) (d : Fin 7 → Bool) : Prop :=
  (∀ i : Fin 8, (γ (rP i)).val = cond (p i) 1 0) ∧
  (∀ j : Fin 7, (γ (rDelta j)).val = cond (d j) 1 0)
/-- Compositional relational Hoare triple for `ClassicalBracketProg.evalBits`. -/
def StepPD {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M) (prog : ClassicalBracketProg M)
    (p₁ : Fin 8 → Bool) (d₁ : Fin 7 → Bool) (p₂ : Fin 8 → Bool) (d₂ : Fin 7 → Bool) : Prop :=
    ∀ γ, MatchesPD rP rDelta γ p₁ d₁ → MatchesPD rP rDelta (prog.evalBits γ) p₂ d₂
theorem StepPD.seq {M : ℕ} {rP : QRegister 8 M} {rDelta : QRegister 7 M}
    {c₁ c₂ : ClassicalBracketProg M} {p₁ p₂ p₃ : Fin 8 → Bool} {d₁ d₂ d₃ : Fin 7 → Bool}
    (h₁ : StepPD rP rDelta c₁ p₁ d₁ p₂ d₂) (h₂ : StepPD rP rDelta c₂ p₂ d₂ p₃ d₃) :
    StepPD rP rDelta (.seq c₁ c₂) p₁ d₁ p₃ d₃ := fun γ h ↦ h₂ (c₁.evalBits γ) (h₁ γ h)
theorem regVal_eq_bool {M : ℕ} :
    ∀ (w : ℕ) (r : QRegister w M) (γ : BitAssignment M) (b : Fin w → Bool),
      (∀ i : Fin w, (γ (r i)).val = cond (b i) 1 0) →
      PhotochemistrySolution.regVal w r γ = regValBool w b
  | 0, _, _, _, _ => rfl
  | w + 1, r, γ, _b, hb =>
        congrArg₂ (· + 2 * ·) (hb 0)
        (regVal_eq_bool w (PhotochemistrySolution.regTail r) γ _ fun i ↦ hb i.succ)
theorem matchesPD_init {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M) (β : BitAssignment M)
    (hD0 : ∀ j : Fin 7, β (rDelta j) = 0) : MatchesPD rP rDelta β (fun i ↦ decide (β (rP i) = 1))
    (fun _ ↦ false) :=
  ⟨fun i ↦ by dsimp only; rcases bit_cases (β (rP i)) with h | h <;> rw [h] <;> rfl, fun j ↦
      (congrArg ZMod.val (hD0 j)).trans rfl⟩
theorem val_not_bit (a : ZMod 2) (pa : Bool) (ha : a.val = cond pa 1 0) : (a + 1).val =
    cond (!pa) 1 0 := by
  fin_cases a <;> cases pa <;> cases ha <;> rfl
theorem val_add_bit (a b : ZMod 2) (pa pb : Bool) (ha : a.val = cond pa 1 0)
    (hb : b.val = cond pb 1 0) : (a + b).val = cond (xor pa pb) 1 0 := by
  fin_cases a <;> fin_cases b <;> cases pa <;> cases pb <;> cases ha <;> cases hb <;> rfl
theorem val_toff_bit (a b c : ZMod 2) (pa pb pc : Bool) (ha : a.val = cond pa 1 0)
    (hb : b.val = cond pb 1 0) (hc : c.val = cond pc 1 0) : (a + b * c).val =
    cond (xor pa (pb && pc)) 1 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> cases pa <;> cases pb <;> cases pc <;>
      cases ha <;> cases hb <;> cases hc <;> rfl
theorem StepPD.xD {M : ℕ} {rP : QRegister 8 M} {rDelta : QRegister 7 M}
    (hPDelta : rP.DisjointWires rDelta) (p : Fin 8 → Bool) (d : Fin 7 → Bool) (k : Fin 7) :
    StepPD rP rDelta (.x (rDelta k)) p d p (updD d k (!d k)) := fun γ h ↦
  ⟨fun i ↦ by simp [ClassicalBracketProg.evalBits, hPDelta.ne i k, h.1 i],
      fun j ↦ by
    by_cases hj : j = k <;>
      simp [ClassicalBracketProg.evalBits, updD, hj,
          rDelta.wires.injective.eq_iff, val_not_bit _ _ (h.2 k), h.2]⟩
theorem StepPD.cnotPD {M : ℕ} {rP : QRegister 8 M} {rDelta : QRegister 7 M}
    (hPDelta : rP.DisjointWires rDelta) (p : Fin 8 → Bool) (d : Fin 7 → Bool)
    (i : Fin 8) (k : Fin 7) :
    StepPD rP rDelta (.cnot (rP i) (rDelta k) (hPDelta.ne i k))
      p d p (updD d k (xor (d k) (p i))) := fun γ h ↦
  ⟨fun m ↦ by simp [ClassicalBracketProg.evalBits, hPDelta.ne m k, h.1 m],
      fun j ↦ by
    by_cases hj : j = k <;>
      simp [ClassicalBracketProg.evalBits, updD, hj,
          rDelta.wires.injective.eq_iff, val_add_bit _ _ _ _ (h.2 k) (h.1 i), h.2]⟩
theorem StepPD.xP {M : ℕ} {rP : QRegister 8 M} {rDelta : QRegister 7 M}
    (hPDelta : rP.DisjointWires rDelta) (p : Fin 8 → Bool) (d : Fin 7 → Bool) (i : Fin 8) :
    StepPD rP rDelta (.x (rP i)) p d (updP p i (!p i)) d := fun γ h ↦
  ⟨fun m ↦ by
    by_cases hm : m = i <;>
      simp [ClassicalBracketProg.evalBits, updP, hm,
          rP.wires.injective.eq_iff, val_not_bit _ _ (h.1 i), h.1],
    fun j ↦
        by simp [ClassicalBracketProg.evalBits, (hPDelta.ne i j).symm,
             h.2 j]⟩
theorem StepPD.pairXC {M : ℕ} {rP : QRegister 8 M} {rDelta : QRegister 7 M}
    (hPDelta : rP.DisjointWires rDelta) (p : Fin 8 → Bool) (d : Fin 7 → Bool)
    (k : Fin 7) (i : Fin 8) :
    StepPD rP rDelta (.seq (.x (rDelta k)) (.cnot (rP i) (rDelta k) (hPDelta.ne i k)))
      p d p (updD d k (xor (!d k) (p i))) := fun γ h ↦
  let ⟨h1, h2⟩ := ((StepPD.xD hPDelta p d k).seq (StepPD.cnotPD hPDelta p _ i k)) γ h
  ⟨h1, fun j ↦ by by_cases hj : j = k <;> simpa [updD, hj] using h2 j⟩
theorem StepPD.tripleXCC {M : ℕ} {rP : QRegister 8 M} {rDelta : QRegister 7 M}
    (hPDelta : rP.DisjointWires rDelta) (p : Fin 8 → Bool) (d : Fin 7 → Bool)
    (k : Fin 7) (i a : Fin 8) :
    StepPD rP rDelta
      (.seq (.x (rDelta k))
        (.seq (.cnot (rP i) (rDelta k) (hPDelta.ne i k))
          (.cnot (rP a) (rDelta k) (hPDelta.ne a k))))
      p d p (updD d k (xor (xor (!d k) (p i)) (p a))) := fun γ h ↦
  let ⟨h1, h2⟩ :=
      ((StepPD.xD hPDelta p d k).seq ((StepPD.cnotPD hPDelta p _ i k).seq (StepPD.cnotPD hPDelta p _
      a k))) γ h
  ⟨h1, fun j ↦ by by_cases hj : j = k <;> simpa [updD, hj] using h2 j⟩
end QuantumComputation.Specs.PhotochemistrySolution.FastQft8

namespace QuantumComputation.Specs.PhotochemistrySolution.FastQft8
-- closed-form coboundary potential phiTail mod 256
/-- Construct an `8`-bit vector from explicit `Bool` arguments. -/
def vec8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Fin 8 → Bool
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | 6 => b6 | 7 => b7
theorem vec8_eta (p : Fin 8 → Bool) : p = vec8 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) :=
  funext fun i ↦ by fin_cases i <;> rfl

open Operator QProg DynamicCircuit Matrix Circuit Qubit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
/-- Extract the `8`-bit `Bool` vector on `rP` from `β`. -/
def pBits {M : ℕ} (rP : QRegister 8 M) (β : BitAssignment M) : Fin 8 → Bool :=
  fun i ↦ decide (β (rP i) = 1)
end QuantumComputation.Specs.PhotochemistrySolution.FastQft8
end

end ScopedLocalHelpers
end
