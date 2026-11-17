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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.KineticQftMidFusionTop

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.WStateStage2LoadUnload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Mux48CtrlSafeOracleBase
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg
    counts_wrapDynOnReg)
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 8192
set_option exponentiation.threshold 8192


namespace QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
theorem eo_pos22 : 0 < 22 := by decide +kernel
end QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70

noncomputable section
set_option exponentiation.threshold 256
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.CoulDom22NoZeroLive232
open PrimitiveGate PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.XMeasChunkQromUnld
  PhotochemistrySolution.CoulombFast
open PhotochemistrySolution.EvenOctB70 PhotochemistrySolution.PotOracleGen
  PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
open PhotochemistrySolution.XMeasLinearCleanStep
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket ket_projector_zero
  matrix_ext_ket writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (ltMask testBit_ltMask
    coordState coordState_spec xorStrict xorStrict_eq evalStrict evalStrict_sound
    natOfZModBits_testBit_lt zmod2_eq_ite_of_beq_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (xorWireUnitary
    xorWireUnitary_mulVec_ket)
-- 3-layer output-assisted 12-TempAND (`48 T`, `0 .TOFF`, `+0 Q`) reversed-output live-cascade
-- `EvenOctBand` unloader `pEvenOctBandLive12Unld` + `46`-TempAND (`184 T`) `pEvenOctBandDomXor46`
-- polymorphic
-- `domSplitPkgNoZeroLive232 : PopBernDomSplitPkg` (`kFloor = 90`, `tDom = 232`).
/-! ### Part 1: Self-Contained 46-TempAND (`184 T`) Forward Normalizer `pEvenOctBandDomXor46` -/

def outWireOfRegRev {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n) (s : ℕ) : Wire n :=
  rOut ⟨B - 1 - (s % B), by omega⟩

def updPrefixRev {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) : ℕ → BitAssignment n
  | 0 => β
  | k + 1 =>
      Function.update (updPrefixRev hB rOut β g k)
        (outWireOfRegRev hB rOut k) (g k)

def updRange {n : ℕ} (outW : ℕ → Wire n) (β : BitAssignment n)
    (g : ℕ → ZMod 2) (ofs : ℕ) : ℕ → BitAssignment n
  | 0 => β
  | m + 1 =>
      Function.update (updRange outW β g ofs m) (outW (ofs + m)) (g (ofs + m))

theorem updRange_eq_updPrefixRev {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) (ofs : ℕ) :
    ∀ m : ℕ,
      updRange (outWireOfRegRev hB rOut) (updPrefixRev hB rOut β g ofs) g ofs m =
        updPrefixRev hB rOut β g (ofs + m)
  | 0 => by simp [updRange]
  | m + 1 => by
      dsimp only [updRange]; rw [updRange_eq_updPrefixRev hB rOut β g ofs m, Nat.add_succ]; rfl
theorem updRange_apply_of_ne {n : ℕ} (outW : ℕ → Wire n) (β : BitAssignment n)
    (g : ℕ → ZMod 2) (ofs : ℕ) {w : Wire n} :
    ∀ (m : ℕ), (∀ t < m, w ≠ outW (ofs + t)) →
      updRange outW β g ofs m w = β w
  | 0, _ => rfl
  | m + 1, hne => by
      dsimp only [updRange]; rw [Function.update_of_ne (hne m (Nat.lt_succ_self m))]
      exact updRange_apply_of_ne outW β g ofs m (fun t ht ↦ hne t (Nat.lt_succ_of_lt ht))

theorem updRange_apply_lt {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) (ofs : ℕ) {t : ℕ} :
    ∀ {m : ℕ}, t < m → ofs + m ≤ B →
      updRange (outWireOfRegRev hB rOut) β g ofs m
        (outWireOfRegRev hB rOut (ofs + t)) = g (ofs + t)
  | 0, ht, _ => absurd ht (Nat.not_lt_zero _)
  | m + 1, ht, hEnd => by
      dsimp only [updRange]
      rcases eq_or_ne t m with rfl | htm
      · exact Function.update_self _ _ _
      · refine (Function.update_of_ne (fun e ↦ ?_) _ _).trans
          (updRange_apply_lt hB rOut β g ofs (by omega) (by omega))
        have hv := congrArg Fin.val (rOut.wires.injective e)
        dsimp [outWireOfRegRev] at hv
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega

theorem updPrefixRev_apply_in {M B n : ℕ} (hB : 0 < B)
    (rIn : QRegister M n) (rOut : QRegister B n)
    (hDisj : rIn.DisjointWires rOut)
    (β : BitAssignment n) (g : ℕ → ZMod 2) (u : Fin M) :
    ∀ k : ℕ, updPrefixRev hB rOut β g k (rIn u) = β (rIn u)
  | 0 => rfl
  | k + 1 =>
      (Function.update_of_ne
        (disj_ne hDisj u ⟨B - 1 - (k % B), by omega⟩) _ _).trans
        (updPrefixRev_apply_in hB rIn rOut hDisj β g u k)

theorem updPrefixRev_apply_lt {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n) (β : BitAssignment n)
    (g : ℕ → ZMod 2) {t : ℕ} : ∀ {k : ℕ}, t < k → k ≤ B →
      updPrefixRev hB rOut β g k (outWireOfRegRev hB rOut t) = g t := fun {k} ht hk ↦ by
  rw [← Nat.zero_add k, ← updRange_eq_updPrefixRev hB rOut β g 0 k]
  simpa only [updPrefixRev, Nat.zero_add] using updRange_apply_lt hB rOut β g 0 ht (by omega)

theorem updPrefixRev_eq_writeReg {B n : ℕ} (hB : 0 < B)
    (rOut : QRegister B n) (β : BitAssignment n) (h : Fin B → ZMod 2) :
    updPrefixRev hB rOut β
        (fun s ↦ h ⟨B - 1 - (s % B), by omega⟩) B =
      writeReg β rOut h := by
  funext w
  by_cases hw : ∃ j : Fin B, rOut j = w
  · obtain ⟨j, rfl⟩ := hw
    have hIdx : B - 1 - (B - 1 - j.val) % B = j.val := by rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [writeReg_apply_reg, show rOut j = outWireOfRegRev hB rOut (B - 1 - j.val) from
        congrArg rOut.wires (Fin.ext hIdx.symm),
            updPrefixRev_apply_lt hB rOut β _ (by omega) le_rfl]
    exact congrArg h (Fin.ext hIdx)
  · simpa only [updPrefixRev, Nat.zero_add, writeReg_apply_of_not_mem _ _ _ _ hw] using
      (congrFun (updRange_eq_updPrefixRev hB rOut β _ 0 B) w).symm.trans
        (updRange_apply_of_ne _ _ _ 0 B fun _ _ e ↦ hw ⟨_, e.symm⟩)

def fAppendRev64 {n : ℕ} (rInScr : QRegister 42 n) (rOut : QRegister 22 n) (u : Fin 64) : Wire n :=
  if hu : u.val < 42 then rInScr ⟨u.val, hu⟩
  else rOut ⟨63 - u.val, by omega⟩

theorem fAppendRev64_injective {n : ℕ} (rInScr : QRegister 42 n) (rOut : QRegister 22 n)
    (hDisj : rInScr.DisjointWires rOut) : Function.Injective (fAppendRev64 rInScr rOut) := by
  intro x y hxy; apply Fin.ext; dsimp only [fAppendRev64] at hxy
  by_cases hx : x.val < 42 <;> by_cases hy : y.val < 42 <;> simp only [hx, hy, ↓reduceDIte] at hxy
  · simpa using congrArg Fin.val (rInScr.wires.injective hxy)
  · exact absurd hxy (disj_ne hDisj _ _)
  · exact absurd hxy.symm (disj_ne hDisj _ _)
  · have hv := congrArg Fin.val (rOut.wires.injective hxy); dsimp at hv; omega

def appendRegRev42_22 {n : ℕ} (rInScr : QRegister 42 n) (rOut : QRegister 22 n)
    (hDisj : rInScr.DisjointWires rOut) : QRegister 64 n :=
    ⟨⟨fAppendRev64 rInScr rOut, fAppendRev64_injective rInScr rOut hDisj⟩⟩
theorem appendRegRev42_22_lo {n : ℕ} (rInScr : QRegister 42 n) (rOut : QRegister 22 n)
    (hDisj : rInScr.DisjointWires rOut) (u : Fin 64)
    (hu : u.val < 42) : appendRegRev42_22 rInScr rOut hDisj u = rInScr ⟨u.val, hu⟩ := by
  change fAppendRev64 rInScr rOut u = _
  dsimp only [fAppendRev64]; exact leg_dif_pos hu

theorem appendRegRev42_22_hi {n : ℕ} (rInScr : QRegister 42 n) (rOut : QRegister 22 n)
    (hDisj : rInScr.DisjointWires rOut) (u : Fin 64) (hu : ¬u.val < 42) :
    appendRegRev42_22 rInScr rOut hDisj u = outWireOfRegRev eo_pos22 rOut (u.val - 42) := by
  change fAppendRev64 rInScr rOut u = _
  dsimp only [fAppendRev64]; rw [leg_dif_neg hu]
  exact congrArg rOut.wires (Fin.ext (by
    dsimp [outWireOfRegRev]
    rw [Nat.mod_eq_of_lt (by omega)]; omega))

theorem outWireOfRegRev_eq_appendRegRev42_22 {n : ℕ}
    (rInScr : QRegister 42 n) (rOut : QRegister 22 n)
    (hDisj : rInScr.DisjointWires rOut) {s : ℕ} (hs : s < 22) :
    outWireOfRegRev eo_pos22 rOut s =
      appendRegRev42_22 rInScr rOut hDisj ⟨42 + s, by omega⟩ := by
  rw [appendRegRev42_22_hi rInScr rOut hDisj ⟨42 + s, by omega⟩ (by dsimp; omega)]
  dsimp only; rw [Nat.add_sub_cancel_left]
def utRowAllLt (bnd a : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | cnt + 1, b, mask =>
      (if Nat.beq (mask % 2) 1 then Nat.blt a bnd && Nat.blt b bnd else true) &&
      utRowAllLt bnd a cnt (b + 1) (mask / 2)

def utPairsAuxAllLt (bnd : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | rem + 1, a, mask =>
      utRowAllLt bnd a rem (a + 1) mask &&
      utPairsAuxAllLt bnd rem (a + 1) (mask >>> rem)

def utPairsAllLt (W bnd mask : ℕ) : Bool := utPairsAuxAllLt bnd W 0 mask
theorem utRowPairs_mem_lt {W n : ℕ} (r : QRegister W n) (bnd a : ℕ) :
    ∀ (cnt b : ℕ) (hbnd : a < b ∧ b + cnt ≤ W) (mask : ℕ),
      utRowAllLt bnd a cnt b mask = true →
      ∀ p ∈ utRowPairs r a cnt b hbnd mask,
        (∃ u : Fin W, u.val < bnd ∧ r u = p.1) ∧
        (∃ u : Fin W, u.val < bnd ∧ r u = p.2.1)
  | 0, _, _, _, _, _, hp => nomatch hp
  | cnt + 1, b, hbnd, mask, hchk, p, hp => by
      obtain ⟨hhd, htl⟩ := Bool.and_eq_true_iff.mp hchk
      dsimp only [utRowPairs] at hp; split_ifs at hhd hp with hbit
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hhd;
            rcases List.mem_cons.mp hp with rfl | hrest
        · exact ⟨⟨⟨a, (ut_row_step1 hbnd).1⟩, hhd.1, rfl⟩, ⟨⟨b, (ut_row_step1 hbnd).2.1⟩, hhd.2,
              rfl⟩⟩
        · exact utRowPairs_mem_lt r bnd a cnt (b + 1) (ut_row_step2 hbnd) (mask / 2) htl p hrest
      · exact utRowPairs_mem_lt r bnd a cnt (b + 1) (ut_row_step2 hbnd) (mask / 2) htl p hp

theorem utPairsAux_mem_lt {W n : ℕ} (r : QRegister W n) (bnd : ℕ) :
    ∀ (rem a : ℕ) (hbnd : a + rem = W) (mask : ℕ),
      utPairsAuxAllLt bnd rem a mask = true →
      ∀ p ∈ utPairsAux r rem a hbnd mask,
        (∃ u : Fin W, u.val < bnd ∧ r u = p.1) ∧
        (∃ u : Fin W, u.val < bnd ∧ r u = p.2.1)
  | 0, _, _, _, _, _, hp => nomatch hp
  | rem + 1, a, hbnd, mask, hchk, p, hp => by
      obtain ⟨hrow, hrest⟩ := Bool.and_eq_true_iff.mp hchk
      rcases List.mem_append.mp hp with hr | ha
      · exact utRowPairs_mem_lt r bnd a rem (a + 1) (ut_aux_step1 hbnd) mask hrow p hr
      · exact utPairsAux_mem_lt r bnd rem (a + 1) (ut_aux_step2 hbnd) (mask >>> rem) hrest p ha

theorem utPairs_mem_lt {W n : ℕ} (r : QRegister W n) (bnd mask : ℕ)
    (hchk : utPairsAllLt W bnd mask = true) : ∀ p ∈ utPairs r mask, (∃ u : Fin W, u.val < bnd ∧
    r u = p.1) ∧ (∃ u : Fin W, u.val < bnd ∧ r u = p.2.1) :=
    utPairsAux_mem_lt r bnd W 0 (Nat.zero_add W) mask hchk
theorem czPairsParity_congr {n : ℕ} (β1 β2 : BitAssignment n) :
    ∀ (ps : List (WirePair n)),
      (∀ p ∈ ps, β1 p.1 = β2 p.1 ∧ β1 p.2.1 = β2 p.2.1) →
      czPairsParity ps β1 = czPairsParity ps β2
  | [], _ => rfl
  | p :: ps, hpEq => by
      obtain ⟨h1, h2⟩ := hpEq p List.mem_cons_self
      simp only [czPairsParity, h1, h2, czPairsParity_congr β1 β2 ps (fun p' hp' ↦
          hpEq p' (List.mem_cons_of_mem p hp'))]

theorem zmod2_eq_of_beq_one {x y : ZMod 2} (h : (x == 1) = (y == 1)) : x = y := by
  fin_cases x <;> fin_cases y <;> cases h <;> rfl

def primGateOutsideXMask (M lo hi xMask c : ℕ) : Option ℕ :=
  let tg := c % 4; let w1 := ((c >>> 2) % 512) % (M + 1); let w2 := ((c >>> 11) % 512) % (M + 1);
  let w3 := ((c >>> 20) % 512) % (M + 1)
  if Nat.beq tg 0 then
    if Nat.ble lo w1 && Nat.blt w1 hi then some xMask
    else some (xMask ^^^ (1 <<< w1))
  else
    let wt := if Nat.beq tg 1 then w2 else w3
    if Nat.ble lo wt && Nat.blt wt hi then some xMask
    else none

def primTreeOutsideXMask (M lo hi : ℕ) : ℕ → PrimTree → Option ℕ
  | xMask, .empty => some xMask
  | xMask, .leaf c => primGateOutsideXMask M lo hi xMask c
  | xMask, .node l r =>
      match primTreeOutsideXMask M lo hi xMask l with
      | none => none
      | some xm1 => primTreeOutsideXMask M lo hi xm1 r

def primTreeTargetsIn (M lo hi : ℕ) (t : PrimTree) : Bool :=
  match primTreeOutsideXMask M lo hi 0 t with
  | some m => Nat.beq m 0
  | none => false

theorem evalPrimGate_testBit_outsideX {M lo hi : ℕ} (xMask xmOut st c j : ℕ)
    (hTgt : primGateOutsideXMask M lo hi xMask c = some xmOut) (hj : ¬(lo ≤ j ∧ j < hi)) :
    ((evalPrimGate M st c).testBit j != xmOut.testBit j) =
      (st.testBit j != xMask.testBit j) := by
  have hGate (wt : ℕ) (cnd : Bool)
      (h : (if (Nat.ble lo wt && Nat.blt wt hi) = true then some xMask else none) = some xmOut) :
      ((if cnd then st ^^^ (1 <<< wt) else st).testBit j != xmOut.testBit j) =
        (st.testBit j != xMask.testBit j) := by
    split_ifs at h with hIn
    injection h with hEq
    subst hEq
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hIn
    split_ifs
    · rw [testBit_xor_shift1, ite_eq_right (by omega)]
    · rfl
  dsimp only [primGateOutsideXMask] at hTgt
  dsimp only [evalPrimGate]
  by_cases h0 : Nat.beq (c % 4) 0 = true
  · simp only [h0, ↓reduceIte] at hTgt ⊢
    split_ifs at hTgt with hIn <;> injection hTgt with hEq <;> subst hEq
    · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hIn
      rw [testBit_xor_shift1, ite_eq_right (by omega)]
    · rw [testBit_xor_shift1, testBit_xor_shift1]
      split_ifs <;> cases st.testBit j <;> cases xMask.testBit j <;> rfl
  · by_cases h1 : Nat.beq (c % 4) 1 = true <;>
      simp only [h0, h1, Bool.false_eq_true, ↓reduceIte] at hTgt ⊢ <;> exact hGate _ _ hTgt

theorem evalPrimTree_testBit_outsideX {M lo hi : ℕ} :
    ∀ (t : PrimTree) (xMask xmOut st j : ℕ),
      primTreeOutsideXMask M lo hi xMask t = some xmOut →
      ¬(lo ≤ j ∧ j < hi) →
      ((evalPrimTree M st t).testBit j != xmOut.testBit j) =
        (st.testBit j != xMask.testBit j)
  | .empty, _, _, _, _, hTgt, _ => by
      simp only [primTreeOutsideXMask, Option.some.injEq] at hTgt
      subst hTgt; rfl
  | .leaf c, xMask, xmOut, st, j, hTgt, hj =>
      evalPrimGate_testBit_outsideX xMask xmOut st c j hTgt hj
  | .node l r, xMask, xmOut, st, j, hTgt, hj => by
      dsimp only [primTreeOutsideXMask] at hTgt
      cases hl : primTreeOutsideXMask M lo hi xMask l with
      | none => simp only [hl] at hTgt; cases hTgt
      | some xm1 =>
          simp only [hl] at hTgt; dsimp only [evalPrimTree];
          exact (evalPrimTree_testBit_outsideX r xm1 xmOut _ j hTgt hj).trans
              (evalPrimTree_testBit_outsideX l xMask xm1 st j hl hj)
theorem evalPrimTree_testBit_outside {M lo hi : ℕ} (t : PrimTree) (st j : ℕ)
    (hTgt : primTreeTargetsIn M lo hi t = true) (hj : ¬(lo ≤ j ∧ j < hi)) :
    (evalPrimTree M st t).testBit j = st.testBit j := by
  dsimp only [primTreeTargetsIn] at hTgt
  rcases h : primTreeOutsideXMask M lo hi 0 t with _ | m
  · simp [h] at hTgt
  · rw [h, Nat.beq_eq] at hTgt
    subst hTgt
    simpa only [Nat.zero_testBit, Bool.bne_false] using
      evalPrimTree_testBit_outsideX t 0 0 st j h hj

def primGateWiresLt (M bnd c : ℕ) : Bool :=
  let tg := c % 4; let w1 := ((c >>> 2) % 512) % (M + 1); let w2 := ((c >>> 11) % 512) % (M + 1);
  let w3 := ((c >>> 20) % 512) % (M + 1)
  Nat.blt w1 bnd &&
    (if Nat.beq tg 0 then true
     else Nat.blt w2 bnd && (if Nat.beq tg 1 then true else Nat.blt w3 bnd))

def primTreeWiresLt (M bnd : ℕ) : PrimTree → Bool
  | .empty => true
  | .leaf c => primGateWiresLt M bnd c
  | .node l r => primTreeWiresLt M bnd l && primTreeWiresLt M bnd r

theorem evalPrimGate_congr_lt {M bnd : ℕ} (st1 st2 c : ℕ) (hW : primGateWiresLt M bnd c = true)
    (hEq : ∀ u < bnd, st1.testBit u = st2.testBit u) : ∀ u < bnd, (evalPrimGate M st1 c).testBit u =
    (evalPrimGate M st2 c).testBit u := by
  intro u hu
  have hXor (b : Bool) (w : ℕ) : (if b then st1 ^^^ (1 <<< w) else st1).testBit u =
      (if b then st2 ^^^ (1 <<< w) else st2).testBit u := by
        split_ifs <;> simp [hEq u hu]
  obtain ⟨hw1, hrest⟩ := (Bool.and_eq_true_iff.mp hW).imp_left Nat.blt_eq.mp
  dsimp only [evalPrimGate]; by_cases h0 : Nat.beq (c % 4) 0 = true
  · simp only [h0, ↓reduceIte, testBit_xor_shift1, hEq u hu]
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hrest ⊢
    obtain ⟨hw2, hrest2⟩ := (Bool.and_eq_true_iff.mp hrest).imp_left Nat.blt_eq.mp
    by_cases h1 : Nat.beq (c % 4) 1 = true <;> simp only [h1, Bool.false_eq_true, ↓reduceIte,
        Nat.blt_eq] at hrest2 ⊢
    · simp only [hEq _ hw1]; exact hXor _ _
    · rw [hEq _ hw1, hEq _ hw2]; exact hXor _ _

theorem evalPrimTree_congr_lt {M bnd : ℕ} :
    ∀ (t : PrimTree) (st1 st2 : ℕ),
      primTreeWiresLt M bnd t = true →
      (∀ u < bnd, st1.testBit u = st2.testBit u) →
      ∀ u < bnd, (evalPrimTree M st1 t).testBit u = (evalPrimTree M st2 t).testBit u
  | .empty, _, _, _, hEq => hEq
  | .leaf c, st1, st2, hW, hEq => evalPrimGate_congr_lt st1 st2 c hW hEq
  | .node l r, st1, st2, hW, hEq => by
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hW
      exact evalPrimTree_congr_lt r _ _ hr (evalPrimTree_congr_lt l st1 st2 hl hEq)
theorem stepCB_decodePrimTree_outside {M lo hi n : ℕ} (r : QRegister (M + 1) n) (t : PrimTree)
    (hTgt : primTreeTargetsIn M lo hi t = true) (γ : BitAssignment n) (u : Fin (M + 1))
    (hu : ¬(lo ≤ u.val ∧ u.val < hi)) : stepCB r (decodePrimTree M t).fwdBits γ (r u) = γ (r u)
    := by
  dsimp only [stepCB]; rw [writeReg_apply_reg]; apply zmod2_eq_of_beq_one
  let β : Fin (M + 1) → ZMod 2 := fun k ↦ γ (r k)
  rw [fwdBits_decodePrimTree_testBit t β (natOfZModBits (M + 1) β)
      (fun i ↦ (natOfZModBits_testBit_lt β i.isLt).symm) u,
    evalPrimTree_testBit_outside t _ u.val hTgt hu]; exact natOfZModBits_testBit_lt β u.isLt
theorem stepCB_decodePrimTree_update_comm {M lo hi bnd n : ℕ} (r : QRegister (M + 1) n)
    (t : PrimTree) (hHi : hi ≤ bnd) (hTgt : primTreeTargetsIn M lo hi t = true)
    (hW : primTreeWiresLt M bnd t = true) (γ : BitAssignment n) (q : Wire n) (val : ZMod 2)
    (hq : ∀ u : Fin (M + 1), u.val < bnd → r u ≠ q) :
    stepCB r (decodePrimTree M t).fwdBits (Function.update γ q val) =
    Function.update (stepCB r (decodePrimTree M t).fwdBits γ) q val := by
  let β1 : Fin (M + 1) → ZMod 2 := fun k ↦ Function.update γ q val (r k)
  let β2 : Fin (M + 1) → ZMod 2 := fun k ↦ γ (r k)
  have hTestEq (k : ℕ) (hk : k < bnd) : (natOfZModBits (M + 1) β1).testBit k =
      (natOfZModBits (M + 1) β2).testBit k := by
    by_cases hkM : k < M + 1
    · rw [natOfZModBits_testBit_lt β1 hkM, natOfZModBits_testBit_lt β2 hkM]
      exact congrArg (· == 1) (Function.update_of_ne (hq ⟨k, hkM⟩ hk) val γ)
    · have hlt (β : Fin (M + 1) → ZMod 2) : (natOfZModBits (M + 1) β).testBit k = false :=
        Nat.testBit_lt_two_pow ((BandEnc12Sync.natOfZModBits_lt (M + 1) β).trans_le
          (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [hlt β1, hlt β2]
  funext w; by_cases hIn : ∃ u : Fin (M + 1), u.val < bnd ∧ r u = w
  · obtain ⟨u, hub, rfl⟩ := hIn
    rw [Function.update_of_ne (hq u hub)]; dsimp only [stepCB]; rw [writeReg_apply_reg,
        writeReg_apply_reg]
    apply zmod2_eq_of_beq_one
    rw [fwdBits_decodePrimTree_testBit t β1 _ (fun i ↦ (natOfZModBits_testBit_lt β1 i.isLt).symm) u,
      fwdBits_decodePrimTree_testBit t β2 _ (fun i ↦ (natOfZModBits_testBit_lt β2 i.isLt).symm) u]
    exact evalPrimTree_congr_lt t _ _ hW hTestEq u.val hub
  · have hOut (δ : BitAssignment n) : stepCB r (decodePrimTree M t).fwdBits δ w = δ w := by
      by_cases hm : ∃ u : Fin (M + 1), r u = w
      · obtain ⟨u, rfl⟩ := hm; exact stepCB_decodePrimTree_outside r t hTgt δ u fun h ↦
            hIn ⟨u, lt_of_lt_of_le h.2 hHi, rfl⟩
      · exact writeReg_apply_of_not_mem _ _ _ _ hm
    rcases eq_or_ne w q with rfl | hwq
    · simp [hOut]
    · simp [hOut, hwq]
theorem stepCB_decodePrimTree_updRange_comm {lo hi bnd n : ℕ}
    (rInScr : QRegister 42 n) (rOut : QRegister 22 n) (hDisj : rInScr.DisjointWires rOut)
    (t : PrimTree) (hHi : hi ≤ bnd)
    (hTgt : primTreeTargetsIn 63 lo hi t = true)
    (hW : primTreeWiresLt 63 bnd t = true)
    (γ : BitAssignment n) (g : ℕ → ZMod 2) (ofs : ℕ) (hOfs : bnd ≤ 42 + ofs) :
    ∀ (m : ℕ), ofs + m ≤ 22 →
      stepCB (appendRegRev42_22 rInScr rOut hDisj) (decodePrimTree 63 t).fwdBits
          (updRange (outWireOfRegRev eo_pos22 rOut) γ g ofs m) =
        updRange (outWireOfRegRev eo_pos22 rOut)
          (stepCB (appendRegRev42_22 rInScr rOut hDisj) (decodePrimTree 63 t).fwdBits γ)
          g ofs m
  | 0, _ => rfl
  | m + 1, hEnd => by
      dsimp only [updRange]
      rw [stepCB_decodePrimTree_update_comm _ t hHi hTgt hW _ _ _ (fun u hu ↦ by
          by_cases hu42 : u.val < 42
          · rw [appendRegRev42_22_lo rInScr rOut hDisj u hu42]; exact disj_ne hDisj _ _
          · rw [appendRegRev42_22_hi rInScr rOut hDisj u hu42]; intro e
            have hv := congrArg Fin.val (rOut.wires.injective e); dsimp [outWireOfRegRev] at hv
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega),
        stepCB_decodePrimTree_updRange_comm rInScr rOut hDisj t hHi hTgt hW γ g ofs hOfs m
            (by omega)]

def setColsAt : List ℕ → ℕ → CT → CT
  | [], _, ct => ct
  | c :: cs, base, ct => setColsAt cs (base + 1) (xorStrict 7 ct base c)

theorem getCT_setColsAt :
    ∀ (cs : List ℕ) (base : ℕ) (ct : CT),
      base + cs.length ≤ 128 →
      (∀ t < cs.length, getCT 7 ct (base + t) = 0) →
      ∀ u < base + cs.length,
        getCT 7 (setColsAt cs base ct) u =
          if u < base then getCT 7 ct u else cs.getD (u - base) 0
  | [], _, _, _, _, _, hu => (ite_eq_left (by dsimp at hu; omega)).symm
  | c :: rest, base, ct, hbnd, hzero, u, hu => by
      dsimp only [setColsAt, List.length] at hbnd hzero hu ⊢
      have hct' (w) (_ : w < 128) : getCT 7 (xorStrict 7 ct base c) w =
          if base = w then getCT 7 ct w ^^^ c else getCT 7 ct w := by
        rw [xorStrict_eq]; exact getCT_xorCT 7 ct w base c (by omega) (by omega)
      rw [getCT_setColsAt rest (base + 1) _ (by omega) (fun t ht ↦ by
        rw [show (base + 1) + t = base + (t + 1) by omega, hct' _ (by omega),
          ite_eq_right (by omega)]
        exact hzero (t + 1) (by omega)) u (by omega)]
      rcases lt_trichotomy u base with hub | rfl | hbu
      · simp [hub, show u < base + 1 by omega, hct' u (by omega), ne_of_gt hub]
      · simp [hct' u (by omega), show getCT 7 ct u = 0 by simpa using hzero 0 (by omega)]
      · simp [show ¬ u < base + 1 by omega, show ¬ u < base by omega, show u - base =
            (u - (base + 1)) + 1 by omega]

def expEvenOctRevCols (nn mx : ℕ) (cs18 : List ℕ) : List ℕ :=
    (List.range 22).map (fun t ↦ (expEvenOctCols nn mx cs18).getD (21 - t) 0)
theorem expEvenOctRevCols_length (nn mx : ℕ)
    (cs18 : List ℕ) : (expEvenOctRevCols nn mx cs18).length = 22 := by simp [expEvenOctRevCols]
theorem expEvenOctRevCols_getD (nn mx : ℕ) (cs18 : List ℕ) {t : ℕ}
    (ht : t < 22) : (expEvenOctRevCols nn mx cs18).getD t 0 = (expEvenOctCols nn mx cs18).getD (21 -
    t) 0 := by simp [expEvenOctRevCols, List.getD_eq_getElem?_getD, ht]
def live12Tree7 : PrimTree :=
  (.node
    (.node
      (.node
        (.node (.leaf 76) (.node (.leaf 80) (.leaf 41033)))
        (.node (.leaf 41029) (.node (.leaf 64) (.leaf 22052946))))
      (.node
        (.node (.leaf 64) (.node (.leaf 60) (.leaf 23099478)))
        (.node (.leaf 60) (.node (.leaf 56) (.leaf 24146010)))))
    (.node
      (.node
        (.node (.leaf 56) (.node (.leaf 52) (.leaf 25192542)))
        (.node (.leaf 52) (.node (.leaf 48) (.leaf 26239074))))
      (.node
        (.node (.leaf 48) (.node (.leaf 44) (.leaf 27285606)))
        (.node
          (.node (.leaf 44) (.leaf 40))
          (.node (.leaf 28332138) (.leaf 40))))))

/--
Layer 2 (`11` leaves, `3` TempANDs = `12 T` ): computes `w28..w31` on `r64` reading `k_2 = r64[43]`
.
-/
def live12Tree3 : PrimTree :=
  (.node
    (.node
      (.node (.leaf 57425) (.leaf 57517))
      (.node (.leaf 32) (.node (.leaf 30425202) (.leaf 32))))
    (.node
      (.node (.leaf 28) (.node (.leaf 31471734) (.leaf 28)))
      (.node (.leaf 24) (.node (.leaf 32518266) (.leaf 24)))))

/--
Layer 3 (`9` leaves, `2` TempANDs = `8 T` ): computes `w32..w34` on `r64` reading
`k_2 = r64[43], k_1 = r64[44]` .
-/
def live12Tree2 : PrimTree :=
  (.node
    (.node
      (.node (.leaf 65633) (.leaf 65709))
      (.node (.leaf 65713) (.leaf 16)))
    (.node
      (.node (.leaf 34611330) (.leaf 16))
      (.node (.leaf 0) (.node (.leaf 35651718) (.leaf 0)))))

/-- Combined 3-layer forward tree (`12` TempANDs = `48 T`) on `r64`. -/
def live12FullTree : PrimTree :=
  .node (.node live12Tree7 live12Tree3) live12Tree2

/--
`22` upper-triangular `64` -wire `CZ` masks (`388` `CZ` pairs, identical to `quadUnldLive14Mask` ).
-/
def live12QuadMask : ℕ → ℕ
  | 0 => 0x200000000001 <<< 936
  | 1 =>
        ((0x7000000000020000000000 <<< 256) ||| (0x4000000000004000000000002000000 <<< 128) |||
        0x80000000000010000000000001) <<< 548
  | 2 =>
        ((0x1c00000000008 <<< 512) ||| (0x1000000000001000000000 <<< 384) ||| (0x2000000000 <<<
        128) ||| 0x8000000000000100000000000001) <<< 330
  | 3 =>
        ((0x70000000000200000000000 <<< 768) ||| (0x20000000 <<< 640) |||
        (0x800000000000000000000000000 <<< 512) ||| (0x80000000000002000000 <<< 384) |||
        (0x20000000000000100000000000000 <<< 128) ||| 0x1) <<< 32
  | 4 =>
        ((0x1000000000000040000000000017000 <<< 384) ||| (0x60000000000000c00000000 <<< 256) |||
        (0xc00000000000006000000000000 <<< 128) ||| 0x1800000000000003000000000000003) <<< 88
  | 5 =>
        ((0x100000000000002000 <<< 384) ||| (0x5c000000000000c00000000 <<< 256) |||
        (0xc00000000000006000000000000 <<< 128) ||| 0x1800000000000003000000000000003) <<< 87
  | 6 =>
        ((0x8000 <<< 384) ||| (0x8000000000000b80000000 <<< 256) |||
        (0xc00000000000006000000000000 <<< 128) ||| 0x1800000000000003000000000000003) <<< 86
  | 7 =>
        ((0x20000000000000100000000 <<< 256) ||| (0xb80000000000006000000000000 <<< 128) |||
        0x1800000000000003000000000000003) <<< 85
  | 8 => 0x40000000000000100000000000005c0000000000001800000000000003000000000000003 <<< 84
  | 9 => 0x40000000000000080000000000001700000000000003000000000000003 <<< 83
  | 10 => 0x200000000000000200000000000002e00000000000003 <<< 82
  | 11 => 0x4000000000000002000000000000017 <<< 78
  | 12 => 0x4000000000000001 <<< 78
  | 13 => 1 <<< 79
  | 14 =>
        ((0x20000000000000 <<< 896) ||| (0x70000000000000000000000 <<< 768) |||
        (0x40000000000000000000000020000000 <<< 640) ||| (0x100000000000000 <<< 512) |||
        (0x80000000000000000000 <<< 384) ||| (0x4000000000000000000000000 <<< 256) |||
        (0x20000000000000000000000000080 <<< 128) ||| 0x5553800000000000000000000000001) <<< 32
  | 15 =>
        ((0x40000000000 <<< 768) ||| (0xb8000000000180000000000180000000 <<< 640) |||
        (0xc000000000003000000000000600 <<< 512) ||| (0x6000000000000300000000 <<< 384) |||
        (0xc00000000000018000000000000 <<< 256) ||| (0x180000000000000c0000000000000300 <<< 128) |||
        0x2005554e00000800002fff5) <<< 78
  | 16 =>
        ((0x80000000000 <<< 768) ||| (0x80000000000b80000000000c0000000 <<< 640) |||
        (0x6000000000001800000000000300 <<< 512) ||| (0x3000000000000180000000 <<< 384) |||
        (0x60000000000000c000000000000 <<< 256) ||| (0xc000000000000060000000000000180 <<< 128) |||
        0x3000000000001002aaa7) <<< 78
  | 17 =>
        ((0x200000000000100000000000b800 <<< 640) ||| (0x600000000000180000000000 <<< 512) |||
        (0x3000000000000300000000000018000 <<< 384) ||| (0x60000000000000c00000000 <<< 256) |||
        (0xc00000000000006000000000000 <<< 128) ||| 0x1800000000000003000000000000003) <<< 93
  | 18 =>
        ((0x4000000000001000 <<< 640) ||| (0x5c0000000000180000000000 <<< 512) |||
        (0x3000000000000300000000000018000 <<< 384) ||| (0x60000000000000c00000000 <<< 256) |||
        (0xc00000000000006000000000000 <<< 128) ||| 0x1800000000000003000000000000003) <<< 92
  | 19 =>
        ((0x4000 <<< 640) ||| (0x80000000000170000000000 <<< 512) |||
        (0x3000000000000300000000000018000 <<< 384) ||| (0x60000000000000c00000000 <<< 256) |||
        (0xc00000000000006000000000000 <<< 128) ||| 0x1800000000000003000000000000003) <<< 91
  | 20 =>
        ((0x200000000000020000000000 <<< 512) ||| (0x2e00000000000300000000000018000 <<< 384) |||
        (0x60000000000000c00000000 <<< 256) ||| (0xc00000000000006000000000000 <<< 128) |||
        0x1800000000000003000000000000003) <<< 90
  | 21 =>
        ((0x80000000000 <<< 512) ||| (0x4000000000002e0000000000018000 <<< 384) |||
        (0x60000000000000c00000000 <<< 256) ||| (0xc00000000000006000000000000 <<< 128) |||
        0x1800000000000003000000000000003) <<< 89
  | _ => 0

theorem live12FullTree_targets : primTreeTargetsIn 63 19 35 live12FullTree = true := by
  decide +kernel
theorem live12Quad_lt_chk : ((List.range 22).all (fun s => utPairsAllLt 64 (42 + s)
    (live12QuadMask s))) = true := by decide +kernel
theorem live12Quad_lt_of_lt22 {s : ℕ} (hs : s < 22) : utPairsAllLt 64 (42 + s) (live12QuadMask s) =
    true := List.all_eq_true.mp live12Quad_lt_chk s (List.mem_range.mpr hs)
theorem utPairsAllLt_zero : utPairsAllLt 64 0 0 = true := by decide +kernel
theorem live12QuadMask_of_ge22 {s : ℕ} (hs : 22 ≤ s) : live12QuadMask s = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm 22 k]
  rfl
theorem live12Quad_lt_of_ge22 {s : ℕ} (hs : 22 ≤ s) : utPairsAllLt 64 0 (live12QuadMask s) =
    true := by
  rw [live12QuadMask_of_ge22 hs]
  exact utPairsAllLt_zero

theorem live12Quad_all64_chk : ((List.range 22).all (fun s =>
    utPairsAllLt 64 64 (live12QuadMask s))) = true := by decide +kernel
theorem live12Quad_lt64 (s : ℕ) : utPairsAllLt 64 64 (live12QuadMask s) = true := by
  rcases lt_or_ge s 22 with hs | hs
  · exact List.all_eq_true.mp live12Quad_all64_chk s (List.mem_range.mpr hs)
  · rw [live12QuadMask_of_ge22 hs]
    decide +kernel

def initRev64CT (nn : ℕ) : CT :=
    setColsAt (expEvenOctRevCols nn (coordState 18).2.1 (coordState 18).2.2) 42 (initDomCT nn)
def fullLive12CT (nn : ℕ) : CT := evalStrict 63 (coordState 18).2.1 (initRev64CT nn) live12FullTree
theorem initDomCT_hi0_chk (nn : ℕ) (hnn : nn = 0 ∨ nn = 1) : ∀ t < 22, getCT 7 (initDomCT nn)
    (42 + t) = 0 := by
  obtain ⟨hc0, hc1⟩ := Bool.and_eq_true_iff.mp (by decide +kernel :
    (((List.range 22).all fun t => Nat.beq (getCT 7 (initDomCT 0) (42 + t)) 0) &&
     ((List.range 22).all fun t => Nat.beq (getCT 7 (initDomCT 1) (42 + t)) 0)) = true)
  rcases hnn with rfl | rfl <;> intro t ht
  · exact Nat.beq_eq.mp (List.all_eq_true.mp hc0 t (List.mem_range.mpr ht))
  · exact Nat.beq_eq.mp (List.all_eq_true.mp hc1 t (List.mem_range.mpr ht))

theorem live12Quad_chk0 :
    checkQuadMasks 64 22 (fullLive12CT 0) live12QuadMask (expEvenOctRevCols 0 (coordState 18).2.1
    (coordState 18).2.2) (ltMask 196608) = true := by decide +kernel
theorem live12Quad_chk1 :
    checkQuadMasks 64 22 (fullLive12CT 1) live12QuadMask (expEvenOctRevCols 1 (coordState 18).2.1
    (coordState 18).2.2) (ltMask 196608) = true := by decide +kernel
def eoBitFn (p : ℕ × ℕ × ℕ) (j : Fin 22) : ZMod 2 :=
    if (if j.val < 8 then p.1.testBit j.val else if j.val < 18 then p.2.1.testBit (j.val -
    8) else p.2.2.testBit (j.val - 18)) then 1 else 0
theorem live12Full_parity_eq {n : ℕ} (rInScr : QRegister 42 n)
    (rOut : QRegister 22 n) (hDisj : rInScr.DisjointWires rOut)
    (γ : BitAssignment n)
    (hd2 : natOfZModBits 18 (fun b ↦ γ (rInScr ⟨1 + b.val, by omega⟩)) < 196608)
    (hZero : ∀ u : Fin 42, 19 ≤ u.val → γ (rInScr u) = 0)
    (s : Fin 22) :
    let p := evenOctIdxT10K (γ (rInScr ⟨0, by omega⟩) == 1)
      (natOfZModBits 18 (fun b ↦ γ (rInScr ⟨1 + b.val, by omega⟩)))
    let r64 := appendRegRev42_22 rInScr rOut hDisj
    czPairsParity (utPairs r64 (live12QuadMask s.val)) (stepCB r64
      (decodePrimTree 63 live12FullTree).fwdBits (updPrefixRev eo_pos22 rOut γ (fun t ↦ eoBitFn p
        ⟨21 - (t % 22), by omega⟩) 22)) =
      eoBitFn p ⟨21 - s.val, by omega⟩ := by
  dsimp only
  set d2 := natOfZModBits 18 (fun b ↦ γ (rInScr ⟨1 + b.val, by omega⟩))
  have hd2_262 : d2 < 2 ^ 18 := by norm_num; omega
  let nn := if γ (rInScr ⟨0, by omega⟩) == 1 then 1 else 0
  have hnn : nn = 0 ∨ nn = 1 := by dsimp only [nn]; split_ifs <;> decide
  let p := evenOctIdxT10K (γ (rInScr ⟨0, by omega⟩) == 1) d2
  let r64 := appendRegRev42_22 rInScr rOut hDisj
  let γ22 := updPrefixRev eo_pos22 rOut γ (fun t ↦ eoBitFn p ⟨21 - (t % 22), by omega⟩) 22
  let β0 : Fin 64 → ZMod 2 := fun u ↦ γ22 (r64 u)
  let stFull := stepCB r64 (decodePrimTree 63 live12FullTree).fwdBits γ22
  have hInitBit (u) (hu : u < 64) : (getCT 7 (initRev64CT nn) u).testBit d2 =
      (natOfZModBits 64 β0).testBit u := by
    have hlen := expEvenOctRevCols_length nn (coordState 18).2.1 (coordState 18).2.2
    rw [show getCT 7 (initRev64CT nn) u = _ from getCT_setColsAt _ 42 _ (by omega)
        (fun t _ ↦ initDomCT_hi0_chk nn hnn t (by omega)) u (by omega),
            natOfZModBits_testBit_lt β0 hu]
    dsimp only [β0, γ22]; by_cases hu42 : u < 42
    · rw [ite_eq_left hu42, appendRegRev42_22_lo rInScr rOut hDisj ⟨u, hu⟩ hu42,
        updPrefixRev_apply_in eo_pos22 rInScr rOut hDisj,
            getCT_initDomCT nn d2 u hd2_262 (by omega)]
      rcases eq_or_ne u 0 with rfl | hu0
      · simp only [↓reduceIte, nn]; cases γ (rInScr ⟨0, by omega⟩) == 1 <;> rfl
      · by_cases hu19 : u < 19
        · simpa only [hu0, hu19, ↓reduceIte, show (⟨u, hu42⟩ : Fin 42) = ⟨1 + (u - 1), by omega⟩
            from Fin.ext (by dsimp; omega)] using
              natOfZModBits_testBit_lt (fun i : Fin 18 ↦ γ (rInScr ⟨1 + i.val, by omega⟩))
                  (by omega : u - 1 < 18)
        · simp only [hu0, hu19, ↓reduceIte, hZero ⟨u, hu42⟩ (by dsimp; omega)]; rfl
    · have ht : u - 42 < 22 := by omega
      rw [ite_eq_right hu42, appendRegRev42_22_hi rInScr rOut hDisj ⟨u, hu⟩ hu42,
        updPrefixRev_apply_lt eo_pos22 rOut _ _ ht le_rfl, expEvenOctRevCols_getD _ _ _ ht,
        show eoBitFn p ⟨21 - ((u - 42) % 22), by omega⟩ = eoBitFn p ⟨21 - (u - 42), by omega⟩ from
          congrArg (eoBitFn p) (Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt ht])), eoBitFn,
        show ∀ b : Bool, ((if b then (1 : ZMod 2) else 0) == 1) = b from fun b ↦ by cases b <;> rfl]
      dsimp only [nn, p]; cases γ (rInScr ⟨0, by omega⟩) == 1 <;> simp only [Bool.false_eq_true,
          ↓reduceIte]
      · exact expEvenOctCols_testBit 0 (by omega) hd2_262 (21 - (u - 42)) (by omega)
      · exact expEvenOctCols_testBit 1 (by omega) hd2_262 (21 - (u - 42)) (by omega)
  obtain ⟨_, hC18, _, _, _⟩ := coordState_spec 18
  have hPost64 (u : Fin 64) : (stFull (r64 u) == 1) =
      (getCT 7 (fullLive12CT nn) u.val).testBit d2 := by
    dsimp only [stFull, stepCB]; rw [writeReg_apply_reg]
    exact (fwdBits_decodePrimTree_testBit live12FullTree β0 _ (fun i ↦
        (natOfZModBits_testBit_lt β0 i.isLt).symm) u).trans
      (evalStrict_sound (by omega : 63 < 128) live12FullTree (initRev64CT nn) _ d2
        (by rw [hC18, Nat.testBit_two_pow_sub_one];
              exact decide_eq_true (hd2_262.trans_le (by norm_num)))
        hInitBit u.val u.isLt).symm
  refine zmod2_eq_ite_of_beq_one (czPairsParity (utPairs r64 (live12QuadMask s.val)) stFull)
    (if 21 - s.val < 8 then p.1.testBit (21 - s.val) else if 21 - s.val < 18 then
      p.2.1.testBit (21 - s.val - 8) else p.2.2.testBit (21 - s.val - 18)) ?_
  rw [utPairs_parity_eq_col r64 (fullLive12CT nn) stFull d2 (live12QuadMask s.val) hPost64]
  have hQuad (b : ℕ) (hb : b < 2) (hchk : checkQuadMasks 64 22 (fullLive12CT b) live12QuadMask
      (expEvenOctRevCols b (coordState 18).2.1 (coordState 18).2.2) (ltMask 196608) = true) :=
    (checkQuadMasks_sound _ live12QuadMask _ (ltMask 196608) d2 hchk
      (by rw [testBit_ltMask]; exact decide_eq_true hd2) s.val s.isLt).trans
      ((congrArg (·.testBit d2) (expEvenOctRevCols_getD b _ _ s.isLt)).trans
        (expEvenOctCols_testBit b hb hd2_262 (21 - s.val) (by omega)))
  dsimp only [fullLive12CT, initRev64CT, nn, p]
  rcases (γ (rInScr ⟨0, by omega⟩) == 1) with _ | _ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact hQuad 0 (by omega) live12Quad_chk0
  · exact hQuad 1 (by omega) live12Quad_chk1

/-- Parametric sub-range `.XMEAS + CZ` unloader over `s ∈ [ofs, ofs + cnt)`. -/
def pUnloadLive12Range {Var : Type} {n : ℕ} (v : Var) (rInScr : QRegister 42 n)
    (rOut : QRegister 22 n) (hDisj : rInScr.DisjointWires rOut)
    (ofs cnt : ℕ) : DynamicCircuit Var n :=
  let r64 := appendRegRev42_22 rInScr rOut hDisj
  xUnloadChunkCzPairsSeqDyn v (outWireOfRegRev eo_pos22 rOut) ofs
    (fun i ↦ utPairs r64 (live12QuadMask (ofs + i)))
    (.circuit .identity) cnt

attribute [local semireducible] remeasureIf projBit chunkXorOp in
theorem subspaceStep_pUnloadLive12Range {Var : Type} [Fintype Var] [DecidableEq Var] {Wk n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister Wk n) (rInScr : QRegister 42 n)
    (rOut : QRegister 22 n) (hDisj : rInScr.DisjointWires rOut) (ofs cnt bnd : ℕ)
    (hEnd : ofs + cnt ≤ 22) (hMaskBnd : ∀ i < cnt, utPairsAllLt 64 bnd (live12QuadMask (ofs + i)) =
    true) (stBase stRef : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (gRev : BitAssignment n → ℕ → ZMod 2) (hOut0 : ∀ i < cnt, ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) →
    stBase δ (outWireOfRegRev eo_pos22 rOut (ofs + i)) = 0)
    (hAgreeLo : ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) → ∀ u : Fin 64, u.val < bnd → u.val < 42 +
    ofs → stBase δ (appendRegRev42_22 rInScr rOut hDisj u) =
    stRef δ (appendRegRev42_22 rInScr rOut hDisj u))
    (hRefUpd : ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) → ∀ t < cnt,
    stRef δ (outWireOfRegRev eo_pos22 rOut (ofs + t)) = gRev δ (ofs + t))
    (hParityRef : ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) → ∀ i < cnt,
    czPairsParity (utPairs (appendRegRev42_22 rInScr rOut hDisj) (live12QuadMask (ofs + i)))
    (stRef δ) = gRev δ (ofs + i)) : SubspaceStep (mkKetOpW rWork (fun δ ↦
    updRange (outWireOfRegRev eo_pos22 rOut) (stBase δ) (gRev δ) ofs cnt) ph)
    (mkKetOpW rWork stBase ph) (pUnloadLive12Range v rInScr rOut hDisj ofs cnt) ∧
    (pUnloadLive12Range v rInScr rOut hDisj ofs cnt).count .T = 0 ∧
    (pUnloadLive12Range v rInScr rOut hDisj ofs cnt).count .TOFF = 0 ∧ (∀ S : Wire n → Prop,
    (∀ u, S (rInScr u)) → (∀ j, S (rOut j)) →
    DynWires S (pUnloadLive12Range v rInScr rOut hDisj ofs cnt)) := by
  let r64 := appendRegRev42_22 rInScr rOut hDisj
  let outW := outWireOfRegRev eo_pos22 rOut
  let pairsFn := fun i ↦ utPairs r64 (live12QuadMask (ofs + i))
  let bitFn := fun i ↦ czPairsParity (pairsFn i)
  have hout_inj {a b : ℕ} (ha : a < 22) (hb : b < 22) (e : outW a = outW b) : a = b := by
    have hv := congrArg Fin.val (rOut.wires.injective e)
    simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv; omega
  have hWireNe {i : ℕ} {u : Fin 64} (hi22 : ofs + i < 22) (hub : u.val < 42 + (ofs + i)) : r64 u ≠
      outW (ofs + i) :=
    if hu42 : u.val < 42 then appendRegRev42_22_lo rInScr rOut hDisj u hu42 ▸ disj_ne hDisj ⟨u.val,
        hu42⟩ _
    else appendRegRev42_22_hi rInScr rOut hDisj u hu42 ▸ fun e ↦
        absurd (hout_inj (by omega) hi22 e) (by omega)
  have hf (i) : ∀ β a, bitFn i (Function.update β (outW (ofs + i)) a) = bitFn i β :=
    czPairsParity_indep (outW (ofs + i)) (pairsFn i) fun p hp ↦ by
      by_cases hi22 : ofs + i < 22
      · obtain ⟨⟨u1, hu1, eq1⟩, ⟨u2, hu2, eq2⟩⟩ :=
            utPairs_mem_lt r64 (42 + (ofs + i)) _ (live12Quad_lt_of_lt22 hi22) p hp
        exact ⟨eq1 ▸ hWireNe hi22 hu1, eq2 ▸ hWireNe hi22 hu2⟩
      · obtain ⟨⟨_, hu1, _⟩, _⟩ := utPairs_mem_lt r64 0 _ (live12Quad_lt_of_ge22 (by omega)) p hp
        exact (Nat.not_lt_zero _ hu1).elim
  have hChunkEq (m) (hm : m ≤ cnt) : chunkXorOp outW ofs bitFn hf m * mkKetOpW rWork stBase ph =
      mkKetOpW rWork (fun δ ↦ updRange outW (stBase δ) (gRev δ) ofs m) ph := by
    induction m with
    | zero => exact Matrix.one_mul _
    | succ i ih =>
        change ((xorWireUnitary (outW (ofs + i)) (bitFn i) (hf i)).1 *
            chunkXorOp outW ofs bitFn hf i) * mkKetOpW rWork stBase ph = _
        rw [Matrix.mul_assoc, ih (by omega), show (xorWireUnitary (outW (ofs + i)) (bitFn i)
            (hf i)).1 *
            mkKetOpW rWork (fun δ ↦ updRange outW (stBase δ) (gRev δ) ofs i) ph =
            mkKetOpW rWork (fun δ ↦ Function.update (updRange outW (stBase δ) (gRev δ) ofs i)
                (outW (ofs + i))
              (updRange outW (stBase δ) (gRev δ) ofs i (outW (ofs + i)) +
                  bitFn i (updRange outW (stBase δ) (gRev δ) ofs i))) ph from
          matrix_ext_ket fun δ ↦ by
            rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
            split_ifs
            · rw [Matrix.mulVec_smul, xorWireUnitary_mulVec_ket]
            · exact Matrix.mulVec_zero _]
        refine mkKetOpW_congr rWork (fun δ hz ↦ ?_) (fun _ _ ↦ rfl)
        have hiCnt : i < cnt := by omega
        have hAgree (u : Fin 64) (huBnd : u.val < bnd) (huCaus : u.val < 42 + (ofs + i)) :
            updRange outW (stBase δ) (gRev δ) ofs i (r64 u) = stRef δ (r64 u) := by
          by_cases huOfs : u.val < 42 + ofs
          · exact (updRange_apply_of_ne outW (stBase δ) (gRev δ) ofs i fun _ _ ↦
              hWireNe (by omega) (by omega)).trans (hAgreeLo δ hz u huBnd huOfs)
          · rw [appendRegRev42_22_hi rInScr rOut hDisj u (by omega), show u.val - 42 = ofs +
                (u.val - 42 - ofs) by omega,
              updRange_apply_lt eo_pos22 rOut (stBase δ) (gRev δ) ofs (by omega) (by omega)]
            exact (hRefUpd δ hz (u.val - 42 - ofs) (by omega)).symm
        dsimp only [updRange]
        rw [(updRange_apply_of_ne outW (stBase δ) (gRev δ) ofs i fun _ _ e ↦
            absurd (hout_inj (by omega) (by omega) e) (by omega)).trans (hOut0 i hiCnt δ hz),
                zero_add]
        exact congrArg (Function.update _ _) ((czPairsParity_congr _ (stRef δ)
            (pairsFn i) fun p hp ↦ by
          obtain ⟨⟨u1, hu1C, eq1⟩, ⟨u2, hu2C, eq2⟩⟩ :=
              utPairs_mem_lt r64 (42 + (ofs + i)) _ (live12Quad_lt_of_lt22 (by omega)) p hp
          obtain ⟨⟨u1', hu1B, eq1'⟩, ⟨u2', hu2B, eq2'⟩⟩ :=
              utPairs_mem_lt r64 bnd _ (hMaskBnd i hiCnt) p hp
          exact ⟨eq1 ▸ hAgree u1 (r64.wires.injective (eq1'.trans eq1.symm) ▸ hu1B) hu1C,
            eq2 ▸ hAgree u2 (r64.wires.injective (eq2'.trans eq2.symm) ▸ hu2B) hu2C⟩).trans
                (hParityRef δ hz i hiCnt))
  obtain ⟨htC, hfC⟩ := count_xUnloadChunkCzPairsSeqDyn v outW ofs pairsFn (.circuit .identity) cnt
  refine ⟨?_, htC, hfC, fun S hrIn hrOut ↦ dynWires_xUnloadChunk v outW ofs pairsFn (fun _ ↦
      hrOut _) (fun j p hp ↦ by
      have hr64 (u : Fin 64) : S (r64 u) :=
        if hu42 : u.val < 42 then appendRegRev42_22_lo rInScr rOut hDisj u hu42 ▸ hrIn _
        else appendRegRev42_22_hi rInScr rOut hDisj u hu42 ▸ hrOut _
      obtain ⟨⟨u1, _, eq1⟩, ⟨u2, _, eq2⟩⟩ :=
          utPairs_mem_lt r64 64 _ (live12Quad_lt64 (ofs + j)) p hp
      exact ⟨eq1 ▸ hr64 u1, eq2 ▸ hr64 u2⟩) cnt⟩
  rw [← show outW = outWireOfRegRev eo_pos22 rOut from rfl, ← hChunkEq cnt le_rfl]
  exact subspaceStep_xUnloadChunkCzPairsSeqDyn v outW ofs pairsFn bitFn hf (fun _ _ ↦ rfl)
      (.circuit .identity)
    (mkKetOpW rWork stBase ph) (mkKetOpW rWork stBase ph) (fun M0 ↦ ⟨M0, by simp, rfl⟩) cnt
    (fun a _ b _ hab e ↦ hab (by have := hout_inj (by omega) (by omega) e; omega))
    (fun i hi ↦ projBit_zero_mkKetOpW rWork _ stBase ph (hOut0 i hi))
end QuantumComputation.Specs.PhotochemistrySolution.CoulDom22NoZeroLive232

namespace QuantumComputation.Specs.PhotochemistrySolution.MidOW58U10
open DynamicCircuit PhotochemistrySolution.InPlaceModAdd PhotochemistrySolution.Stage4FineFast
  PhotochemistrySolution.MidOWCore PhotochemistrySolution.Poly28Sub254 CtrlSafeOracleBase.MidOW60
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PrimitiveGate (T TOFF)
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP
theorem topPre_lt0 (k : ℕ) : 0 < 3 * k + 2 := by omega
theorem topPre_lt1 (k : ℕ) : 1 < 3 * k + 2 := by omega
theorem topPre_ltZ (k : ℕ) (i : Fin (k + 1)) : 1 + i.val < 3 * k + 2 := by have := i.isLt; omega
theorem topPre_ltB (k : ℕ) (i : Fin k) : k + 2 + i.val < 3 * k + 2 := by have := i.isLt; omega
theorem topPre_ltB0 (k : ℕ) : k + 3 < 3 * (k + 1) + 2 := by omega

theorem topPre_ne01 {n : ℕ} (k : ℕ) (r : QRegister (3 * k + 2) n) : r ⟨0, topPre_lt0 k⟩ ≠
    r ⟨1, topPre_lt1 k⟩ := fun e ↦ nomatch r.wires.injective e
theorem topPre_neB0Z0 {n : ℕ} (k : ℕ) (r : QRegister (3 * (k + 1) + 2) n) :
    r ⟨k + 3, topPre_ltB0 k⟩ ≠ r ⟨1, topPre_lt1 (k + 1)⟩ :=
  fun e ↦ by have hv : k + 3 = 1 := congrArg Fin.val (r.wires.injective e); omega

/-- Subregister index map for the carry-majority `cpMaj4` block of `pUngatedAddCarryKickTopPre`. -/
def idxTopMaj (k : ℕ) (u : Fin 4) : ℕ :=
    if u.val = 0 then 1 else if u.val = 1 then k + 3 else if u.val = 2 then 0 else 2 * k + 4
theorem idxTopMaj_lt (k : ℕ) (u : Fin 4) : idxTopMaj k u < 3 * (k + 1) + 2 := by
  dsimp only [idxTopMaj]; split_ifs <;> omega
/-- `Fin`-typed wire map for the carry-majority `cpMaj4` block of `pUngatedAddCarryKickTopPre`. -/
def fTopMaj (k : ℕ) : Fin 4 → Fin (3 * (k + 1) + 2) := fun u ↦ ⟨idxTopMaj k u, idxTopMaj_lt k u⟩
theorem fTopMaj_inj (k : ℕ) : Function.Injective (fTopMaj k) := fun a b e ↦ by
  have hv : idxTopMaj k a = idxTopMaj k b := congrArg Fin.val e
  have _ := a.isLt; have _ := b.isLt
  dsimp only [idxTopMaj] at hv; split_ifs at hv <;> exact Fin.ext (by omega)

/-- Subregister index map for the recursive inner call of `pUngatedAddCarryKickTopPre`. -/
def idxTopSub (k : ℕ) (u : Fin (3 * k + 2)) : ℕ :=
    if u.val = 0 then 2 * k + 4 else if u.val < k + 2 then 1 + u.val else if u.val < 2 * k +
    2 then 2 + u.val else 3 + u.val
theorem idxTopSub_lt (k : ℕ) (u : Fin (3 * k + 2)) : idxTopSub k u < 3 * (k + 1) + 2 := by
  have _ := u.isLt; dsimp only [idxTopSub]; split_ifs <;> omega
/-- `Fin`-typed wire map for the recursive inner call of `pUngatedAddCarryKickTopPre`. -/
def fTopSub (k : ℕ) : Fin (3 * k + 2) → Fin (3 * (k + 1) + 2) := fun u ↦
    ⟨idxTopSub k u, idxTopSub_lt k u⟩
theorem fTopSub_inj (k : ℕ) : Function.Injective (fTopSub k) := fun a b e ↦ by
  have hv : idxTopSub k a = idxTopSub k b := congrArg Fin.val e
  have _ := a.isLt; have _ := b.isLt
  dsimp only [idxTopSub] at hv; split_ifs at hv <;> exact Fin.ext (by omega)

/--
Ungated `(k + 1)`-bit Z-slice + `k`-bit B-slice in-place adder + carry-out phase kick on
`3 * k + 2` wires (`r[0] = cin`, `r[1..k+1] = Z[0..k]`, `r[k+2..2*k+1] = B[0..k-1]`,
`r[2*k+2..3*k+1] = cln[0..k-1]`): `4 * k` `T` gates, `0` `.TOFF`, where `Z[k]` has already
absorbed the top addend bit before entering.
-/
def pUngatedAddCarryKickTopPre : (k : ℕ) → {Var : Type} → {n : ℕ} → Var → QRegister (3 * k + 2) n →
    DynamicCircuit Var n
  | 0, _, _, v, r =>
      let w0 := r ⟨0, topPre_lt0 0⟩; let w1 := r ⟨1, topPre_lt1 0⟩
      .seq (cz2 w0 w1 (topPre_ne01 0 r)) (cnot1 v w0 w1 (topPre_ne01 0 r))
  | k + 1, _, _, v, r =>
      .seq
        (wrapDynOnReg v (r.compose ⟨fTopMaj k, fTopMaj_inj k⟩) cpMaj4
          (pUngatedAddCarryKickTopPre k v (r.compose ⟨fTopSub k, fTopSub_inj k⟩)))
        (.seq
          (cnot1 v (r ⟨k + 3, topPre_ltB0 k⟩) (r ⟨1, topPre_lt1 (k + 1)⟩) (topPre_neB0Z0 k r))
          (cnot1 v (r ⟨0, topPre_lt0 (k + 1)⟩) (r ⟨1, topPre_lt1 (k + 1)⟩) (topPre_ne01 (k + 1) r)))

theorem pUngatedAddCarryKickTopPre_counts : ∀ (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (r : QRegister (3 * k + 2) n),
    (pUngatedAddCarryKickTopPre k v r).count PrimitiveGate.T = 4 * k ∧
    (pUngatedAddCarryKickTopPre k v r).count PrimitiveGate.TOFF = 0
  | 0, Var, _, v, r => by
      obtain ⟨t1, f1⟩ := cz2_counts (Var := Var) _ _ (topPre_ne01 0 r)
      obtain ⟨t2, f2⟩ := cnot1_counts (Var := Var) v _ _ (topPre_ne01 0 r)
      dsimp only [pUngatedAddCarryKickTopPre, DynamicCircuit.count]; rw [t1, f1, t2, f2];
          exact ⟨rfl, rfl⟩
  | k + 1, Var, _, v, r => by
      obtain ⟨ihT, ihF⟩ :=
          pUngatedAddCarryKickTopPre_counts k v (r.compose ⟨fTopSub k, fTopSub_inj k⟩)
      obtain ⟨wT, wF⟩ := counts_wrapDynOnReg v (r.compose ⟨fTopMaj k, fTopMaj_inj k⟩) cpMaj4
        (pUngatedAddCarryKickTopPre k v (r.compose ⟨fTopSub k, fTopSub_inj k⟩))
      obtain ⟨c1T, c1F⟩ := cnot1_counts (Var := Var) v _ _ (topPre_neB0Z0 k r)
      obtain ⟨c2T, c2F⟩ := cnot1_counts (Var := Var) v _ _ (topPre_ne01 (k + 1) r)
      dsimp only [pUngatedAddCarryKickTopPre, DynamicCircuit.count]; rw [wT, wF, cpMaj4_numAnd,
          ihT, ihF, c1T, c1F, c2T, c2F]
      exact ⟨by omega, rfl⟩

theorem pUngatedAddCarryKickTopPre_dynWires : ∀ (k : ℕ) {Var : Type} {n : ℕ} (P : Wire n → Prop)
    (v : Var) (r : QRegister (3 * k + 2) n),
    (∀ i : Fin (3 * k + 2), P (r i)) → DynWires P (pUngatedAddCarryKickTopPre k v r)
  | 0, _, _, P, v, r, hP =>
      ⟨cz2_dynWires P _ _ (topPre_ne01 0 r) (hP _) (hP _), cnot1_dynWires P v _ _ (topPre_ne01 0 r)
          (hP _) (hP _)⟩
  | k + 1, _, _, P, v, r, hP =>
      ⟨dynWires_wrapDynOnReg v (r.compose ⟨fTopMaj k, fTopMaj_inj k⟩)
          (fun u ↦ hP (fTopMaj k u)) cpMaj4
        (pUngatedAddCarryKickTopPre_dynWires k P v (r.compose ⟨fTopSub k, fTopSub_inj k⟩)
            (fun u ↦ hP (fTopSub k u))),
       cnot1_dynWires P v _ _ (topPre_neB0Z0 k r) (hP _)
           (hP _), cnot1_dynWires P v _ _ (topPre_ne01 (k + 1) r) (hP _) (hP _)⟩

theorem zmod2_add_carry_id (a b : ZMod 2) : a.val + b.val = (a + b).val + 2 * (a * b).val := by
  fin_cases a <;> fin_cases b <;> decide

theorem topPre_finBitsVal_fin0 (f : Fin 0 → ZMod 2) : finBitsVal f = 0 :=
    Nat.lt_one_iff.mp (finBitsVal_lt f)

/-- `MidOWHi16U10TopPreK58` (`416 T`, `0 .TOFF`, `kMid = 58`) package marker. -/
def midOWHi16U10TopPreK58Pkg_104 : MidOWU10Pkg true 14 58 416 := ⟨⟩
end QuantumComputation.Specs.PhotochemistrySolution.MidOW58U10
end


namespace QuantumComputation.Specs.PhotochemistrySolution.EvenOctTightWalk

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  WithLp ComplexConjugate PhotochemistrySolution PhotochemistrySolution.GQSP
  PhotochemistrySolution.OvBidir PhotochemistrySolution.QubitizationCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectCompactRot34
open PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectCsa64GqspWalk
  PhotochemistrySolution.SelectLcu70Rot32
attribute [local irreducible] SpecDefs.systemQubits_frozen ancWOfScr
lemma complex_sub_norm_sq_phaseGradA (a b : ℂ) : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 *
    (star b *
    a).re := by simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
                  Complex.sub_im, Complex.star_def, Complex.mul_re, Complex.conj_re,
                  Complex.conj_im]; ring
lemma complex_re_sum_phaseGradA {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) : (∑ x ∈ s, f x).re = ∑ x ∈ s, (f x).re := by
  classical
  induction s using Finset.induction_on <;> simp [*]
lemma pgL2Norm_sub_sq_unit_phaseGradA {ι : Type*} [Fintype ι] (u v : ι → ℂ) (hu : pgL2Norm u = 1)
    (hv : pgL2Norm v = 1) : pgL2Norm (u - v) ^ 2 = 2 - 2 * (∑ x : ι, star (v x) * u x).re := by
  classical
  rw [pgL2Norm_sq, complex_re_sum_phaseGradA, Finset.mul_sum]
  simp_rw [Pi.sub_apply, complex_sub_norm_sq_phaseGradA]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← pgL2Norm_sq, hu, hv, one_pow];
      ring
lemma align_unit_factor_phaseGradA (u v : ZMod 2 → ℂ) {ε α : ℝ} (_hε : 0 ≤ ε)
    (hu : pgL2Norm u = 1) (hv : pgL2Norm v = 1)
    (h : pgL2Norm (u - Complex.exp (α * Complex.I) • v) ≤ ε) : ∃ (θ c : ℝ), (0 ≤ c ∧ c ≤ 1) ∧ 1 -
    c ≤ ε ^ 2 / 2 ∧ ∑ x : ZMod 2, star ((Complex.exp (θ * Complex.I) • v) x) * u x = (c : ℂ) := by
  let v' : ZMod 2 → ℂ := Complex.exp (α * Complex.I) • v
  let ip : ℂ := ∑ x : ZMod 2, star (v' x) * u x
  have hsq :=
      pgL2Norm_sub_sq_unit_phaseGradA u v' hu (by rw [pgL2Norm_exp_ofReal_mul_I_smul, hv]) ▸
    pow_le_pow_left₀ (pgL2Norm_nonneg _) h 2
  let θ : ℝ := α + ip.arg
  let w : ZMod 2 → ℂ := Complex.exp (θ * Complex.I) • v
  have hip_align : ∑ x : ZMod 2, star (w x) * u x = (‖ip‖ : ℂ) := by
    refine (show ∑ x : ZMod 2, star (w x) * u x = star (Complex.exp ((ip.arg : ℂ) * Complex.I)) *
        ip by
      dsimp only [ip, w, v', θ, Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, star_mul, star_mul, star_mul];
          ring).trans
      ((congrArg _ (Complex.norm_mul_exp_arg_mul_I ip).symm).trans ?_)
    rw [← mul_assoc, mul_comm _ (‖ip‖ : ℂ), mul_assoc, show star (Complex.exp ((ip.arg : ℂ) *
        Complex.I)) *
      Complex.exp ((ip.arg : ℂ) * Complex.I) =
          1 by rw [Complex.star_def, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow, Complex.ofReal_one],
            mul_one]
  have hw_sq :=
      (pgL2Norm_sub_sq_unit_phaseGradA u w hu (by rw [pgL2Norm_exp_ofReal_mul_I_smul, hv])).trans
    (by rw [hip_align, Complex.ofReal_re]) ▸ sq_nonneg (pgL2Norm (u - w))
  exact ⟨θ, ‖ip‖, ⟨norm_nonneg ip, by linarith⟩, by linarith [Complex.re_le_norm ip], hip_align⟩
lemma one_sub_prod_and_le_one_phaseGradA {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc0 : ∀ i ∈ s, 0 ≤ c i) (hc1 : ∀ i ∈ s, c i ≤ 1) : (1 - ∏ i ∈ s, c i ≤ ∑ i ∈ s, (1 - c i)) ∧
    (∏ i ∈ s, c i ≤ 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hs0 := Finset.prod_nonneg fun i hi ↦ hc0 i (Finset.mem_insert_of_mem hi)
      obtain ⟨_, _⟩ :=
          ih (fun i hi ↦ hc0 i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hc1 i (Finset.mem_insert_of_mem hi))
      exact ⟨by nlinarith [hc0 a (Finset.mem_insert_self a s), hc1 a (Finset.mem_insert_self a s)],
        by nlinarith [hc0 a (Finset.mem_insert_self a s), hc1 a (Finset.mem_insert_self a s)]⟩
end

end QuantumComputation.Specs.PhotochemistrySolution.EvenOctTightWalk

end
