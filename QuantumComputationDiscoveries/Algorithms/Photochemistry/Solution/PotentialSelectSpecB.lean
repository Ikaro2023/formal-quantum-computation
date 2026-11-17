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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.PotentialSelectSpecA

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section
-- monotone workspace widening
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution
  PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.QubitizationWalkSem
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.XMeasChunkQromUnldA
open PhotochemistrySolution.XMeasChunkQromUnld PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Stage4Kin14Scb
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open scoped Matrix Circuit.Notation BigOperators
attribute [local irreducible] systemQubits_frozen ancWOfScr PgBase.phaseGradientState
    phaseFlipUnitary abpKin14Usel abpKin14Csel bSpeciesSwap50

/--
Dependency-inverted Stage-4 `Zero-NErem` potential oracle on `QRegister (146 + Wp) n`
(`Wp <= 169 + wIn` clean workspace wires: `Wp <= 351` at `wIn = 182`, `Q = 6,314`).
-/
structure Stage4ZeroNEremPotOracle (Wp : ℕ) (potExpect : PotExpectFn) where
  tPot : ℕ
  phaseBit : Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment 41 → ZMod 2
  pCsel : ∀ {Var : Type} {n : ℕ}, Var → QRegister (146 + Wp) n → DynamicCircuit Var n
  pUsel : ∀ {Var : Type} {n : ℕ}, Var → QRegister (146 + Wp) n → DynamicCircuit Var n
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (r : QRegister (146 + Wp) n),
    let uC :=
        phaseFlipUnitary (fun δ : BitAssignment n ↦ δ (wPotLocQ r) * δ (wPotIsPot r) *
        potOracleBitEval phaseBit r δ)
    let uU :=
        phaseFlipUnitary (fun δ : BitAssignment n ↦ δ (wPotIsPot r) * potOracleBitEval phaseBit r δ)
    CleanWorkStep (rPotWork r) uC (pCsel v r) ∧
    CleanWorkStep (rPotWork r) uU (pUsel v r) ∧
    (pCsel v r).count .T = tPot ∧
    (pUsel v r).count .T = tPot ∧
    (pCsel v r).count .TOFF = 0 ∧
    (pUsel v r).count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var)
    (r : QRegister (146 + Wp) n),
    (∀ i : Fin (146 + Wp), S (r i)) → DynWires S (pCsel v r) ∧ DynWires S (pUsel v r)
  avg_coin41 : ∀ (isScreen isNN : Bool) (sp1 sp2 : Fin 4)
      (nA nB eA eB : Fin 3 → Fin 256),
    (2 ^ 41 : ℂ)⁻¹ *
      (∑ z : BitAssignment 41, bitSign (phaseBit isScreen isNN sp1 sp2 nA nB eA eB z)) =
      (potExpect isScreen isNN sp1 sp2 nA nB eA eB : ℂ)

theorem pot0_le_690 : 0 ≤ 690 := Nat.zero_le 690
theorem fin22_lt_521_pot : 22 < 521 := by omega
theorem writeReg_self {k n : ℕ} (r : QRegister k n) (β : BitAssignment n) : writeReg β r (fun i ↦
    β (r i)) = β :=
  funext fun w ↦
    if h : ∃ i : Fin k, r i = w then h.elim fun i hi ↦ hi ▸ writeReg_apply_reg β r _ i
    else writeReg_apply_of_not_mem β r _ w h
/-- Canonical `146`-wire zero-workspace Stage-4 potential register on `dLayout`. -/
def rPot0Layout : QRegister (146 + 0) dLayout := rPotZeroNErem 0 pot0_le_690

/-- Bit vector encoding `zeroNEremOutMask s` on `rOut40Layout`. -/
def outMaskBits40 (s : ZeroNEremSector) : BitAssignment 40 :=
  fun j ↦ if (zeroNEremOutMask s).testBit j.val then 1 else 0
/-- Input ket bit assignment with `(c, z)` written onto `rLcu82Layout`. -/
def routedStage0 (β : BitAssignment dLayout) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    BitAssignment dLayout :=
  DynCircExt.writeReg β rLcu82Layout (pack82 c z)
/-- Post-Stage-1 ket bit assignment with `outMaskBits40 (decodeCoin c)` on `rOut40Layout`. -/
def routedStage1 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (β : BitAssignment dLayout)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) : BitAssignment dLayout :=
  DynCircExt.writeReg (routedStage0 β c z) rOut40Layout (outMaskBits40 (decodeCoin c))
/-- Post-nuclear-router ket bit assignment `routerSwapBits rNucLayout (routedStage1 ...)`. -/
def routedStage2 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (β : BitAssignment dLayout)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) : BitAssignment dLayout :=
  routerSwapBits rNucLayout (routedStage1 decodeCoin β c z)
/-- Full post-`wNoHad` ket bit assignment on clean scratch. -/
def routedKet (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (β : BitAssignment dLayout)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) : BitAssignment dLayout :=
    routerSwapBits rElecLayout (routedStage2 decodeCoin β c z)

theorem rNuc_header_eq_out40 : rHas1 rNucLayout = wHasN1 ∧ rRawHas2 rNucLayout = wRawHasN2 ∧
    (∀ d : Fin 6, rIdx1 rNucLayout d = rOut40Layout ⟨2 + d.val, by omega⟩) ∧
    (∀ d : Fin 6, rIdx2 rNucLayout d = rOut40Layout ⟨8 + d.val, by omega⟩) := by
  have hn {k : ℕ} (hk : k < 14) : rNucLayout ⟨k, hNW1394.symm ▸ by omega⟩ = rOut40Layout ⟨k,
      by omega⟩ :=
    Fin.ext (by
      erw [val_nucRouterWireFn, val_rOut40Layout]
      dsimp
      split_ifs
      omega)
  exact ⟨hn (by omega), hn (by omega), fun _ ↦ hn (by omega), fun _ ↦ hn (by omega)⟩

theorem rElec_header_eq_out40 : rHas1 rElecLayout = wHasE1 ∧ rRawHas2 rElecLayout = wRawHasE2 ∧
    (∀ d : Fin 8, rIdx1 rElecLayout d = rOut40Layout ⟨16 + d.val, by omega⟩) ∧
    (∀ d : Fin 8, rIdx2 rElecLayout d = rOut40Layout ⟨24 + d.val, by omega⟩) := by
  have he {k j : ℕ} (hk : k < 18) (hj : j = 14 + k) :
      rElecLayout ⟨k, hEW5056.symm ▸ by omega⟩ = rOut40Layout ⟨j, by omega⟩ :=
    Fin.ext (by
      erw [val_elecRouterWireFn, val_rOut40Layout]
      dsimp
      split_ifs
      omega)
  exact ⟨he (by omega) rfl, he (by omega) rfl, fun _ ↦ he (by omega)
      (by omega), fun _ ↦ he (by omega) (by omega)⟩

theorem rPot0_flags_eq_out40 :
    wPotIsScreen rPot0Layout = rOut40Layout ⟨32, by omega⟩ ∧ wPotIsPot rPot0Layout =
        rOut40Layout ⟨33, by omega⟩ ∧
    wPotIsKin rPot0Layout = rOut40Layout ⟨34, by omega⟩ ∧ wPotIsNN rPot0Layout = rOut40Layout ⟨35,
        by omega⟩ ∧
    wPotSp1B0 rPot0Layout = rOut40Layout ⟨36, by omega⟩ ∧ wPotSp1B1 rPot0Layout = rOut40Layout ⟨37,
        by omega⟩ ∧
    wPotSp2B0 rPot0Layout = rOut40Layout ⟨38, by omega⟩ ∧ wPotSp2B1 rPot0Layout = rOut40Layout ⟨39,
        by omega⟩ := by
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_,
      Fin.ext ?_⟩
  all_goals erw [val_potZeroNEremWireFn pot0_le_690]

theorem bool_ite_eq {b₁ b₂ : Bool} (h : b₁ = b₂) :
    (if b₁ then (1 : ZMod 2) else 0) = (if b₂ then 1 else 0) :=
  congrArg (fun b : Bool ↦ if b then (1 : ZMod 2) else 0) h

theorem packOut40ZeroNErem_fields (hasN1 hasN2 : Bool) (n1 n2 : ℕ) (hasE1 hasE2 : Bool)
    (e1 e2 : ℕ)
    (isScreen isPot isKin isNN : Bool) (sp1 aux2 : ℕ) (hn1 : n1 < 64) (hn2 : n2 < 64)
        (he1 : e1 < 256) (he2 : e2 < 256)
    (δ : BitAssignment dLayout)
    (hOut : ∀ j : Fin 40, δ (rOut40Layout j) =
      if (packOut40ZeroNErem hasN1 hasN2 n1 n2 hasE1 hasE2 e1 e2 isScreen isPot isKin isNN sp1
          aux2).testBit j.val then 1 else 0) :
    δ (rHas1 rNucLayout) = (if hasN1 then 1 else 0) ∧ δ (rRawHas2 rNucLayout) =
        (if hasN2 then 1 else 0) ∧
    idxValD (rIdx1 rNucLayout) δ = n1 ∧ idxValD (rIdx2 rNucLayout) δ = n2 ∧
    δ (rHas1 rElecLayout) = (if hasE1 then 1 else 0) ∧ δ (rRawHas2 rElecLayout) =
        (if hasE2 then 1 else 0) ∧
    idxValD (rIdx1 rElecLayout) δ = e1 ∧ idxValD (rIdx2 rElecLayout) δ = e2 ∧
    δ (wPotIsScreen rPot0Layout) = (if isScreen then 1 else 0) ∧ δ wIsFine =
        (if isPot then 1 else 0) ∧
    δ wIsKin = (if isKin then 1 else 0) ∧ δ (wPotIsNN rPot0Layout) = (if isNN then 1 else 0) ∧
    δ (wPotSp1B0 rPot0Layout) = (if sp1.testBit 0 then 1 else 0) ∧
    δ (wPotSp1B1 rPot0Layout) = (if sp1.testBit 1 then 1 else 0) ∧
    δ wAxis0 = (if aux2.testBit 0 then 1 else 0) ∧ δ wAxis1 = (if aux2.testBit 1 then 1 else 0)
        := by
  let M := packOut40ZeroNErem hasN1 hasN2 n1 n2 hasE1 hasE2 e1 e2 isScreen isPot isKin isNN sp1 aux2
  have hb (b : Bool) (k : ℕ) (hk : k ≠ 0) : (if b then (1 : ℕ) else 0).testBit k = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (by cases b <;> decide) (Nat.pow_le_pow_right (by decide)
        (Nat.pos_of_ne_zero hk)))
  have hb0 (b : Bool) : (if b then (1 : ℕ) else 0).testBit 0 = b := by cases b <;> rfl
  have flag_eq {w : Wire dLayout} {b : Bool} (k : Fin 40) (hw : w = rOut40Layout k)
      (hb_eq : M.testBit k.val = b := by
        simp [M, packOut40ZeroNErem, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, hb0,
            hb,
          Nat.testBit_two_pow_sub_one 2, Nat.testBit_two_pow_sub_one 6,
              Nat.testBit_two_pow_sub_one 8]) :
      δ w = if b then 1 else 0 := (congrArg δ hw).trans ((hOut k).trans (bool_ite_eq hb_eq))
  have idx_eq {D : ℕ} (rI : Fin D → Wire dLayout) (x off : ℕ) (hx : x < 2 ^ D) (ho : off + D ≤ 40)
      (hWire : ∀ d : Fin D, rI d = rOut40Layout ⟨off + d.val, by omega⟩)
      (hBit : ∀ j, j < D → M.testBit (off + j) = x.testBit j := by
        intro j hj
        interval_cases j <;> simp [M, packOut40ZeroNErem, Nat.testBit_or, Nat.testBit_shiftLeft,
            Nat.testBit_and, hb,
          Nat.testBit_two_pow_sub_one 6, Nat.testBit_two_pow_sub_one 8]) :
      idxValD rI δ = x := Nat.eq_of_testBit_eq fun j ↦ by
    rw [testBit_idxValD]
    by_cases hj : j < D
    · rw [dite_eq_left hj, hWire ⟨j, hj⟩, hOut ⟨off + j, by omega⟩]
      dsimp only
      rw [hBit j hj]
      cases x.testBit j <;> simp
    · exact (dite_eq_right hj).trans
        (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
            (Nat.le_of_not_lt hj)))).symm
  have ⟨PF, NH, EH⟩ : _ ∧ _ ∧ _ :=
      ⟨rPot0_flags_eq_out40, rNuc_header_eq_out40, rElec_header_eq_out40⟩
  exact ⟨flag_eq ⟨0, by omega⟩ NH.1 (by cases hasN1 <;> simp [M, packOut40ZeroNErem]),
      flag_eq ⟨1, by omega⟩ NH.2.1,
    idx_eq _ n1 2 hn1 (by omega) NH.2.2.1, idx_eq _ n2 8 hn2 (by omega) NH.2.2.2,
    flag_eq ⟨14, by omega⟩ EH.1, flag_eq ⟨15, by omega⟩ EH.2.1,
    idx_eq _ e1 16 he1 (by omega) EH.2.2.1, idx_eq _ e2 24 he2 (by omega) EH.2.2.2,
    flag_eq ⟨32, by omega⟩ PF.1, flag_eq ⟨33, by omega⟩ rfl, flag_eq ⟨34, by omega⟩ rfl,
        flag_eq ⟨35, by omega⟩ PF.2.2.2.1,
    flag_eq ⟨36, by omega⟩ PF.2.2.2.2.1, flag_eq ⟨37, by omega⟩ PF.2.2.2.2.2.1,
    flag_eq ⟨38, by omega⟩ rfl, flag_eq ⟨39, by omega⟩ rfl⟩

theorem stage1_outside_eq (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (β : BitAssignment dLayout)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) {w : Wire dLayout}
    (hwOut : ¬ (5715 ≤ w.val ∧ w.val < 5755)) (hwLcu : w.val < 7215 ∨ 7297 ≤ w.val) :
    routedStage1 decodeCoin β c z w = β w := by
  have n1 : w ∉ Set.range rOut40Layout.wires :=
    fun ⟨j, e⟩ ↦ absurd ((val_rOut40Layout j).symm.trans (congrArg Fin.val e)) (by omega)
  have n0 : w ∉ Set.range rLcu82Layout.wires :=
    fun ⟨i, e⟩ ↦
        absurd ((val_rLcu82Layout i).symm.trans (congrArg Fin.val e)) (by
          dsimp [mLayout]
          omega)
  exact (DynCircExt.writeReg_apply_of_not_mem _ _ _ _ n1).trans
    (DynCircExt.writeReg_apply_of_not_mem _ _ _ _ n0)

theorem stage1_scr_zero {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {β : BitAssignment dLayout}
    (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41) {w : Wire dLayout}
    (hw : (5650 ≤ w.val ∧ w.val < 5715) ∨ (5755 ≤ w.val ∧ w.val < 7215)) :
    routedStage1 decodeCoin β c z w = 0 := by
  have heq : w = rScrLayout ⟨w.val - 5650, by
    dsimp [scrLLayout]
    omega⟩ :=
    Fin.ext (by
      rw [val_rScrLayout]
      dsimp
      omega)
  exact (stage1_outside_eq decodeCoin β c z (by omega) (.inl (by omega))).trans (heq ▸ hScr _)

theorem zeroNEremOutMask_router_valid (s : ZeroNEremSector) (δ : BitAssignment dLayout)
    (hOut : ∀ j : Fin 40, δ (rOut40Layout j) = outMaskBits40 s j) :
    (δ (rRawHas2 rNucLayout) = 1 → δ (rHas1 rNucLayout) = 1) ∧
    (δ (rHas1 rNucLayout) = 1 → idxValD (rIdx1 rNucLayout) δ < 47) ∧
    (δ (rRawHas2 rNucLayout) = 1 → idxValD (rIdx2 rNucLayout) δ < 47) ∧
    (δ (rRawHas2 rElecLayout) = 1 → δ (rHas1 rElecLayout) = 1) ∧
    (δ (rHas1 rElecLayout) = 1 → idxValD (rIdx1 rElecLayout) δ < 187) ∧
    (δ (rRawHas2 rElecLayout) = 1 → idxValD (rIdx2 rElecLayout) δ < 187) := by
  have imp1 {a b : Bool} (hab : a = true → b = true) (h : (if a then (1 : ZMod 2) else 0) = 1) :
      (if b then (1 : ZMod 2) else 0) = 1 := match a, h with
    | false, h => absurd h zero_ne_one
    | true, _ => ite_eq_left (hab rfl)
  have checkPack {hN1 hN2 : Bool} {n1 n2 : ℕ} {hE1 hE2 : Bool} {e1 e2 : ℕ}
      {isScreen isPot isKin isNN : Bool} {sp1 aux2 : ℕ}
      (heq : zeroNEremOutMask s =
          packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2)
      (impN : hN2 = true → hN1 = true := by
        decide) (lN1 : n1 < 47 := by omega) (lN2 : n2 < 47 := by omega)
      (impE : hE2 = true → hE1 = true := by
        decide) (lE1 : e1 < 187 := by omega) (lE2 : e2 < 187 := by omega) :=
    let F :=
        packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2
      (by omega) (by omega) (by omega) (by omega) δ fun j ↦
          (hOut j).trans (by
            dsimp [outMaskBits40]
            rw [heq])
    And.intro (fun h : δ (rRawHas2 rNucLayout) = 1 ↦ F.1.trans (imp1 impN (F.2.1.symm.trans h))) <|
    And.intro (fun _ : δ (rHas1 rNucLayout) = 1 ↦ F.2.2.1.trans_lt lN1) <|
    And.intro (fun _ : δ (rRawHas2 rNucLayout) = 1 ↦ F.2.2.2.1.trans_lt lN2) <|
    And.intro (fun h : δ (rRawHas2 rElecLayout) = 1 ↦
        F.2.2.2.2.1.trans (imp1 impE (F.2.2.2.2.2.1.symm.trans h))) <|
    And.intro (fun _ : δ (rHas1 rElecLayout) = 1 ↦ F.2.2.2.2.2.2.1.trans_lt lE1)
      (fun _ : δ (rRawHas2 rElecLayout) = 1 ↦ F.2.2.2.2.2.2.2.1.trans_lt lE2)
  cases s with
  | idle =>
      exact checkPack (show _ =
        packOut40ZeroNErem false false 0 0 false false 0 0 false false false false 0 0 from rfl)
  | ee n1 e1 e2 =>
      exact checkPack (by rw [zeroNEremOutMask]) (lN1 := n1.isLt) (lE1 := e1.isLt)
        (lE2 := e2.isLt)
  | nn n1 n2 e1 =>
      exact checkPack (by rw [zeroNEremOutMask]) (lN1 := n1.isLt) (lN2 := n2.isLt)
        (lE1 := e1.isLt)
  | en n1 e1 => exact checkPack (by rw [zeroNEremOutMask]) (lN1 := n1.isLt) (lE1 := e1.isLt)
  | kin i ax =>
      have _ := i.isLt
      exact if hi : i.val < 47 then checkPack (by rw [zeroNEremOutMask, ite_eq_left hi])
        else checkPack (by rw [zeroNEremOutMask, ite_eq_right hi])

theorem routerSwapBits_outside_mod {M D n : ℕ} (r : RouterReg M D n) {β : BitAssignment n}
    (hβ : ValidRouterInput r β)
    {w : Wire n} (hLo : ∀ b : Fin 24, w ≠ rBufLo r b) (hHi : ∀ b : Fin 24, w ≠ rBufHi r b)
    (hSys : ∀ (p : Fin M) (b : Fin 24), w ≠ rSys r p b) : routerSwapBits r β w = β w :=
  (routerSwapBits_spec r hβ).2.2.2 w hLo hHi fun p b e ↦ absurd e (hSys p b)

theorem validRouter_stage1 {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout}
    (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    ValidRouterInput rNucLayout (routedStage1 decodeCoin β c z) ∧
    (∀ j : Fin (routerWidth 187 8), routedStage2 decodeCoin β c z (rElecLayout j) =
        routedStage1 decodeCoin β c z (rElecLayout j)) ∧
    ValidRouterInput rElecLayout (routedStage2 decodeCoin β c z) ∧
    (∀ w : Wire dLayout, (5650 ≤ w.val ∧ w.val < 5755) ∨ (5803 ≤ w.val ∧ w.val < 5851) ∨
        (5899 ≤ w.val ∧ w.val < 7298) →
      routedKet decodeCoin β c z w = routedStage1 decodeCoin β c z w) ∧
    (∀ b : Fin 24, routedKet decodeCoin β c z (rBufLo rNucLayout b) =
        routedStage2 decodeCoin β c z (rBufLo rNucLayout b)) ∧
    (∀ b : Fin 24, routedKet decodeCoin β c z (rBufHi rNucLayout b) =
        routedStage2 decodeCoin β c z (rBufHi rNucLayout b)) := by
  let δ₁ := routedStage1 decodeCoin β c z
  let δ₂ := routedStage2 decodeCoin β c z
  have hHdr := zeroNEremOutMask_router_valid (decodeCoin c) δ₁ fun j ↦
      DynCircExt.writeReg_apply_reg _ rOut40Layout _ j
  have zNuc {k : ℕ} (hlt : k < routerWidth 47 6) (hk : 14 ≤ k ∧ (k < 110 ∨ 1238 ≤ k) := by
    dsimp <;> omega) :
      δ₁ (rNucLayout ⟨k, hlt⟩) = 0 := stage1_scr_zero hScr c z (.inr (by
    have _ : k < 1394 := hNW1394 ▸ hlt
    erw [val_nucRouterWireFn ⟨k, hlt⟩]
    dsimp
    split_ifs <;> omega))
  have hVN : ValidRouterInput rNucLayout δ₁ :=
    ⟨hHdr.1, hHdr.2.1, hHdr.2.2.1, fun _ ↦ ⟨zNuc _, zNuc _, zNuc _, zNuc _⟩, fun w hw ↦ by
      rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
      have hge : basePub 47 6 ≤ i.val := (Finset.mem_filter.mp hi).2
      exact zNuc i.isLt (by
        unfold basePub at hge
        omega)⟩
  have nucModBnd {k : ℕ} (hk : (14 ≤ k ∧ k < 62) ∨ (110 ≤ k ∧ k < 1238)) :
      let v := (rNucLayout ⟨k, hNW1394.symm ▸ by omega⟩).val
      v < 1128 ∨ (5755 ≤ v ∧ v < 5803) := by
    dsimp only
    erw [val_nucRouterWireFn ⟨k, _⟩]
    dsimp
    split_ifs <;> omega
  have hNucMod (w : Wire dLayout) (hw : ¬ (w.val < 1128 ∨ (5755 ≤ w.val ∧ w.val < 5803))) : δ₂ w =
      δ₁ w :=
    routerSwapBits_outside_mod rNucLayout hVN
      (fun b e ↦ hw (e ▸ nucModBnd (.inl ⟨by omega, (fun _ ↦ by omega) b.isLt⟩)))
      (fun b e ↦ hw (e ▸ nucModBnd (.inl ⟨by omega, (fun _ ↦ by omega) b.isLt⟩)))
      (fun p b e ↦ hw (e ▸ nucModBnd (.inr ⟨by omega, (fun _ _ ↦ by omega) p.isLt b.isLt⟩)))
  have hKeepE (j : Fin (routerWidth 187 8)) : δ₂ (rElecLayout j) = δ₁ (rElecLayout j) :=
    hNucMod (rElecLayout j) ((fun _ ↦ by omega) (val_rElec_bounds j))
  have idx_keep (rI : Fin 8 → Wire dLayout) (hr : ∀ d : Fin 8, δ₂ (rI d) = δ₁ (rI d)) :
      idxValD rI δ₂ = idxValD rI δ₁ :=
    Nat.eq_of_testBit_eq fun j ↦ by
      rw [testBit_idxValD, testBit_idxValD]
      by_cases hj : j < 8 <;> simp [hj, hr]
  have zE2 {k : ℕ} (hlt : k < routerWidth 187 8) (hk : 18 ≤ k ∧ (k < 114 ∨ 4602 ≤ k) := by
    dsimp <;> omega) :
      δ₂ (rElecLayout ⟨k, hlt⟩) = 0 :=
          (hKeepE ⟨k, hlt⟩).trans <| stage1_scr_zero hScr c z (.inr (by
    have _ : k < 5056 := hEW5056 ▸ hlt
    erw [val_elecRouterWireFn ⟨k, hlt⟩]
    dsimp
    split_ifs <;> omega))
  have hVE : ValidRouterInput rElecLayout δ₂ :=
    ⟨fun h ↦ (hKeepE _).trans (hHdr.2.2.2.1 ((hKeepE _).symm.trans h)),
     fun h ↦ (idx_keep _ fun _ ↦ hKeepE _).trans_lt (hHdr.2.2.2.2.1 ((hKeepE _).symm.trans h)),
     fun h ↦ (idx_keep _ fun _ ↦ hKeepE _).trans_lt (hHdr.2.2.2.2.2 ((hKeepE _).symm.trans h)),
     fun _ ↦ ⟨zE2 _, zE2 _, zE2 _, zE2 _⟩,
     fun w hw ↦ by
       rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
       have hge : basePub 187 8 ≤ i.val := (Finset.mem_filter.mp hi).2
       exact zE2 i.isLt (by
         unfold basePub at hge
         omega)⟩
  have elecModBnd {k : ℕ} (hk : (18 ≤ k ∧ k < 66) ∨ (114 ≤ k ∧ k < 4602)) :
      let v := (rElecLayout ⟨k, hEW5056.symm ▸ by omega⟩).val
      (1128 ≤ v ∧ v < 5616) ∨ (5851 ≤ v ∧ v < 5899) := by
    dsimp only
    erw [val_elecRouterWireFn ⟨k, _⟩]
    dsimp
    split_ifs <;> omega
  have hElecMod (w : Wire dLayout)
      (hw : ¬ ((1128 ≤ w.val ∧ w.val < 5616) ∨ (5851 ≤ w.val ∧ w.val < 5899))) :
      routedKet decodeCoin β c z w = δ₂ w :=
    routerSwapBits_outside_mod rElecLayout hVE
      (fun b e ↦ hw (e ▸ elecModBnd (.inl ⟨by omega, (fun _ ↦ by omega) b.isLt⟩)))
      (fun b e ↦ hw (e ▸ elecModBnd (.inl ⟨by omega, (fun _ ↦ by omega) b.isLt⟩)))
      (fun p b e ↦ hw (e ▸ elecModBnd (.inr ⟨by omega, (fun _ _ ↦ by omega) p.isLt b.isLt⟩)))
  have hElecNuc (w : Wire dLayout) (h : w.val < 1128 ∨ (5755 ≤ w.val ∧ w.val < 5803)) :
      routedKet decodeCoin β c z w = δ₂ w := hElecMod w (by omega)
  exact ⟨hVN, hKeepE, hVE, fun w hw ↦ (hElecMod w (by omega)).trans (hNucMod w (by omega)),
    fun b ↦
        hElecNuc (rBufLo rNucLayout b) (nucModBnd (k := 14 + b.val)
        (.inl ⟨by omega, (fun _ ↦ by omega) b.isLt⟩)),
    fun b ↦
        hElecNuc (rBufHi rNucLayout b) (nucModBnd (k := 38 + b.val)
        (.inl ⟨by omega, (fun _ ↦ by omega) b.isLt⟩))⟩

end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end
end
