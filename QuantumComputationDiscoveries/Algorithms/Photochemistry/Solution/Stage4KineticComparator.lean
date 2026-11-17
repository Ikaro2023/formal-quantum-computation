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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.FineDistSqQromBridge
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SplitRouterSupportedOn
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

section Stage4KinClosed
set_option allowUnsafeReducibility true
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SelectKinThreshCore
  QuantumComputation.Specs.PhotochemistrySolution.TargetBScr
set_option exponentiation.threshold 256

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb
open Operator QProg DynamicCircuit Matrix Circuit Qubit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
def avoids226 (m : ℕ) : ComputeProg 226 → Bool
  | .id => true
  | .x u => !m.testBit u.val
  | .cnot cw tw _ => !m.testBit cw.val && !m.testBit tw.val
  | .andGate c₁ c₂ a _ _ _ => !m.testBit c₁.val && !m.testBit c₂.val && !m.testBit a.val
  | .seq p₁ p₂ => avoids226 m p₁ && avoids226 m p₂
theorem fwdBits_avoids (m : ℕ) (p : ComputeProg 226) (h : avoids226 m p = true) :
    (∀ (β₁ β₂ : BitAssignment 226), (∀ w : Wire 226, m.testBit w.val = false → β₁ w = β₂ w) →
    ∀ w : Wire 226, m.testBit w.val = false → p.fwdBits β₁ w = p.fwdBits β₂ w) ∧
    (∀ (β : BitAssignment 226) (w : Wire 226), m.testBit w.val = true → p.fwdBits β w = β w) := by
  have hne {u w : Wire 226} (hu : m.testBit u.val = false) (hw : m.testBit w.val = true) : w ≠ u :=
    fun e ↦ Bool.noConfusion ((e ▸ hw).symm.trans hu)
  induction p <;> simp only [avoids226, Bool.and_eq_true, Bool.not_eq_true'] at h
  case id => exact ⟨fun _ _ hβ _ hw ↦ hβ _ hw, fun _ _ _ ↦ rfl⟩
  case x u =>
    exact ⟨fun _ _ hβ w hw ↦
        by simp only [ComputeProg.fwdBits, Function.update_apply, hβ u h, hβ w hw],
      fun _ _ hw ↦ Function.update_of_ne (hne h hw) _ _⟩
  case cnot cw tw _ =>
    exact ⟨fun _ _ hβ w hw ↦
        by simp only [ComputeProg.fwdBits, Function.update_apply, hβ cw h.1, hβ tw h.2, hβ w hw],
      fun _ _ hw ↦ Function.update_of_ne (hne h.2 hw) _ _⟩
  case andGate c₁ c₂ a _ _ _ =>
    exact ⟨fun _ _ hβ w hw ↦ by
        simp only [ComputeProg.fwdBits, Function.update_apply, hβ c₁ h.1.1, hβ c₂ h.1.2, hβ a h.2,
            hβ w hw],
      fun _ _ hw ↦ Function.update_of_ne (hne h.2 hw) _ _⟩
  case seq ih₁ ih₂ =>
    exact ⟨fun _ _ hβ ↦ (ih₂ h.2).1 _ _ ((ih₁ h.1).1 _ _ hβ),
      fun _ w hw ↦ ((ih₂ h.2).2 _ w hw).trans ((ih₁ h.1).2 _ w hw)⟩
abbrev wKin (i : ℕ) : Wire 226 := finMod 225 i
abbrev wIsKin226 : Wire 226 := finMod 225 22
abbrev wLocQ226 : Wire 226 := finMod 225 23
abbrev wOutKin226 : Wire 226 := finMod 225 24
abbrev wFlip226 : Wire 226 := finMod 225 225
theorem hq226_ne_out : wLocQ226 ≠ wOutKin226 := by decide
def mKeep : ℕ := (1 <<< 22) ||| (1 <<< 23) ||| (1 <<< 24)
def codeToCP226 (op : ℕ) : ComputeProg 226 :=
  let w1 := wKin ((op / 4) % 256); let w2 := wKin ((op / 1024) % 256);
  let w3 := wKin ((op / 262144) % 256)
  if op % 4 = 0 then safeCnotCP w1 w2 else safeAndGateCP w1 w2 w3
def sBitList15 : List ℕ := [61, 63, 69, 75, 85, 95, 109, 123, 137, 147, 157, 163, 169, 171, 170]
def sBitIdx15 (b : Fin 15) : Wire 226 := wKin (sBitList15.getD b.val 61)
def sqCodes226 : List ℕ :=
    [25600, 25628, 26628, 26652, 27656, 27676, 28684, 28700, 29712, 29724, 30740, 30748, 31768,
    31772, 8415333, 8678501, 8941669, 9204837, 9468005, 9731173, 9989225, 10252393, 10515561,
    10778729, 11041897, 11300973, 11564141, 11827309, 12090477, 12350577, 12613745, 12876913,
    13138037, 13401205, 13663353, 13919261, 14182429, 14445597, 14708765, 14971933, 15235101,
    15498269, 15754269, 62492, 62564, 16307441, 64752, 64724, 65640, 65784, 66664, 66776, 17368321,
    67688, 68856, 68824, 68712, 17858829, 70924, 70784, 71900, 71952, 72924, 72968, 18947353, 73948,
    75024, 75016, 74972, 19432741, 77092, 76932, 78048, 78120, 79072, 79136, 20526385, 80096, 81192,
    81184, 81120, 82072, 82236, 83096, 83052, 21579073, 84120, 85308, 85100, 85144, 22055245, 87372,
    87176, 88376, 88400, 89400, 89416, 23158105, 90424, 91472, 91464, 91448, 92316, 92516, 93340,
    93412, 24210793, 94364, 95588, 95460, 95388, 24677749, 97652, 97420, 98656, 98680, 99680, 99696,
    25789825, 100704, 101752, 101744, 101728, 102512, 102796, 103536, 103656, 26842513, 104560,
    105868, 105704, 105584, 106656, 106908, 107680, 107692, 27895201, 108704, 109980, 109740,
    109728, 28348845, 112044, 111760, 113048, 113072, 114072, 114088, 29474233, 115096, 116144,
    116136, 116120, 116972, 117188, 117996, 118152, 30526921, 119020, 120260, 120200, 120044,
    120996, 121300, 122020, 122032, 31579609, 123044, 124372, 124080, 124068, 32019941, 126436,
    126100, 127440, 127464, 128464, 128480, 33158641, 129488, 130536, 130528, 130512, 131188,
    131580, 132212, 132544, 34211329, 133236, 134652, 134592, 134260, 135348, 135692, 136372,
    136380, 35264017, 137396, 138764, 138428, 138420, 35695133, 140828, 140456, 141832, 141856,
    142856, 142872, 36843049, 143880, 144928, 144920, 144904, 145600, 145972, 146624, 146936,
    37895737, 147648, 149044, 148984, 148672, 38320709, 151108, 150712, 152112, 152136, 153136,
    153152, 39474769, 154160, 155208, 155200, 155184, 155848, 156252, 156872, 156792, 40527457,
    157896, 159324, 158840, 158920, 40945261, 161388, 160964, 162392, 162416, 163416, 163432,
    42106489, 164440, 165488, 165480, 165464, 42520197, 167556, 167116, 168060, 168584, 169084,
    169600, 43685521, 170108, 171656, 171648, 171132, 44094109, 173724, 173264, 44735137, 175776,
    175768]
def pSq15CP : ComputeProg 226 := cpOfList (sqCodes226.map codeToCP226)
def prefixSum (f : ℕ → ZMod 2) : ℕ → ℕ | 0 => 0 | n + 1 => prefixSum f n + (f n).val * 2 ^ n
theorem prefixSum_lt (f : ℕ → ZMod 2) (n : ℕ) : prefixSum f n < 2 ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
      rcases (by have := (f n).val_lt; omega : (f n).val = 0 ∨ (f n).val = 1) with h | h <;>
        simp only [prefixSum, h, pow_succ] <;> omega
theorem testBit_eq_of_mod_two_pow {a b n i : ℕ} (hi : i < n) (hm : a % 2 ^ n = b % 2 ^ n) :
    a.testBit i = b.testBit i := by
  simpa [Nat.testBit_mod_two_pow, hi] using congrArg (·.testBit i) hm

abbrev w21 (i : ℕ) : Wire 21 := finMod 20 i
def pNib4 : ComputeProg 21 :=
  cpOfList ([0, 1, 2, 3].map fun j ↦
    let cP : Wire 21 := if j = 0 then w21 8 else w21 (11 + 3 * (j - 1))
    let t1 : Wire 21 := w21 (9 + 3 * j); let t2 : Wire 21 := w21 (10 + 3 * j)
    let cO : Wire 21 := w21 (11 + 3 * j)
    cpOfList [safeCnotCP cP t1, safeCnotCP (w21 j) t1, safeCnotCP cP t2,
        safeCnotCP (w21 (4 + j)) t2, safeAndGateCP t1 t2 cO, safeCnotCP cP cO])
def map21 (m : Fin 21 → Wire 226) : ComputeProg 21 → ComputeProg 226
  | .id => .id
  | .x u => .x (m u)
  | .cnot c t _ => safeCnotCP (m c) (m t)
  | .andGate c₁ c₂ a _ _ _ => safeAndGateCP (m c₁) (m c₂) (m a)
  | .seq p₁ p₂ => .seq (map21 m p₁) (map21 m p₂)
def uPad (b : ℕ) : Wire 226 :=
    if b = 0 then wKin 173 else if b = 1 then wKin 174 else wKin (8 + (b - 2))
def sPad (b : ℕ) : Wire 226 :=
    if b = 0 then wKin 175 else if b = 1 then wKin 176 else sBitIdx15 (finMod 14 (b - 2))
def nibMap (g : Fin 4) (q : Fin 21) : Wire 226 :=
    if q.val < 4 then uPad (4 * g.val + q.val) else if q.val < 8 then sPad (4 * g.val +
    (q.val - 4)) else if q.val = 8 then (if g.val = 0 then wKin 172 else wKin (188 + 12 *
    (g.val - 1))) else wKin (177 + 12 * g.val + (q.val - 9))
def pCarry16CP : ComputeProg 226 :=
    cpOfList ([0, 1, 2, 3].map fun g ↦ map21 (nibMap (finMod 3 g)) pNib4)
def kOfBits8 (β : BitAssignment 226) : Fin 256 := finMod 255 (prefixSum (fun j ↦ β (wKin j)) 8)
theorem kOfBits8_val (β : BitAssignment 226) : (kOfBits8 β).val = prefixSum (fun j ↦
    β (wKin j)) 8 := by
  have := prefixSum_lt (fun j ↦ β (wKin j)) 8; dsimp [kOfBits8, finMod]; omega

def pFlipCP : ComputeProg 226 :=
    cpOfList [.x wFlip226, safeCnotCP (sBitIdx15 (finMod 14 14)) wFlip226,
    safeCnotCP (wKin 224) wFlip226]
def pKinMidPreCP : ComputeProg 226 := .seq pSq15CP (.seq pCarry16CP pFlipCP)
def pKinPre80CP : ComputeProg 226 := .seq pKinMidPreCP (safeAndGateCP wIsKin226 wFlip226 wOutKin226)
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb
end

noncomputable section
set_option exponentiation.threshold 1024
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb

open Operator QProg DynamicCircuit Matrix Circuit Qubit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open PhotochemistrySolution.QubitizationWalkSem
def abpKin14Usel : AndBracketProg 226 := pKinPre80CP.wrap (.prim (zGateCirc wOutKin226))
def abpKin14Csel : AndBracketProg 226 :=
    pKinPre80CP.wrap (.prim (czCircuit wLocQ226 wOutKin226 hq226_ne_out))
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb
attribute [irreducible] QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb.abpKin14Usel
    QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb.abpKin14Csel
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull

open Operator QProg DynamicCircuit Matrix Circuit Qubit QFT
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.Stage4Kin14Scb
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (czCircuit bitSign)
open PhotochemistrySolution.SelectStructKinComp
/- ## Section 1: 16-AND (`64 T`, `0 TOFF`) 3-Axis Coordinate Mux `bAxisMux27` -/

abbrev wMux (i : ℕ) : Wire 27 := finMod 26 i
def sMaskMux1 : ℕ := 1 <<< 26
/--
In-place 1-AND Fredkin swap on `(a, b)` controlled by `s` using clean ancilla `anc` (`β anc = 0`).
-/
def cswapMux27 (s a b anc : Wire 27) : StructuredCB 27 :=
  scbOfList [.cnot b a, .tempAndCnot s a anc b, .cnot b a]
/-- 8-bit controlled byte swapper on `wMux (2..9)` and `wMux (off..off+7)`. -/
def byteSwapMux27 (s : Wire 27) (off : ℕ) : StructuredCB 27 :=
  scbOfList ((List.range 8).map fun j ↦ cswapMux27 s (wMux (2 + j)) (wMux (off + j)) (wMux 26))
/--
16-AND (`64 T`) 3-axis coordinate swapper:
`wMux 0 = sy` , `wMux 1 = sz` , `wMux (2..9) = x` , `wMux (10..17) = y` , `wMux (18..25) = z` ,
`wMux 26 = anc` .
-/
def bAxisMux27 : StructuredCB 27 := .seq (byteSwapMux27 (wMux 0) 10) (byteSwapMux27 (wMux 1) 18)
theorem bAxisMux27_props : bAxisMux27.numTempAnd = 16 ∧ bAxisMux27.modMask = (((1 <<< 24) - 1) <<<
    2) ∧ bAxisMux27.validCleanMask sMaskMux1 = true :=
  of_checkKinSCBFast rfl
/-- Reduced single-bit model `(sy, sz, x_j, y_j, z_j)` when `anc = 0`. -/
def mux1Bit6 (sy sz x y z : ZMod 2) : ZMod 2 × ZMod 2 × ZMod 2 :=
  let a1 := x + y; let b1 := y + sy * a1; let a2 := a1 + b1; let a3 := a2 + z;
  let c1 := z + sz * a3; let a4 := a3 + c1
  (a4, b1, c1)
theorem mux1Bit6_axes : (∀ x y z : ZMod 2, mux1Bit6 0 0 x y z = (x, y, z)) ∧ (∀ x y z : ZMod 2,
    mux1Bit6 1 0 x y z = (y, x, z)) ∧ (∀ x y z : ZMod 2, mux1Bit6 0 1 x y z = (z, y, x)) :=
  ⟨by decide, by decide, by decide⟩
theorem cswapMux27_evalS (s a b anc : Wire 27)
    (hs_ne_a : s ≠ a) (hs_ne_anc : s ≠ anc) (ha_ne_anc : a ≠ anc)
    (hanc_ne_b : anc ≠ b) (hb_ne_a : b ≠ a) (_hs_ne_b : s ≠ b)
    (β : BitAssignment 27) (hanc : β anc = 0) :
    (cswapMux27 s a b anc).evalS β =
      let a1 := β a + β b; let b1 := β b + β s * a1
      Function.update (Function.update β b b1) a (a1 + b1) := by
  funext w
  dsimp only [cswapMux27, scbOfList, List.foldr, StructuredCB.evalS]
  rw [ite_eq_right hb_ne_a, ite_eq_right hb_ne_a, ite_eq_right hs_ne_a, ite_eq_right hs_ne_anc,
    ite_eq_right ha_ne_anc, ite_eq_right hanc_ne_b, Function.update_self,
    Function.update_of_ne ha_ne_anc.symm _ β, hanc, Function.update_of_ne hs_ne_a _ β,
    Function.update_of_ne hb_ne_a _ β, zero_add]
  by_cases hwa : w = a <;> by_cases hwb : w = b <;> simp [hwa, hwb, hb_ne_a, hb_ne_a.symm]
theorem byteSwapMux27_step_kinFull (s : Wire 27) (off other : ℕ)
    (hs : s.val < 2) (hoff : (off = 10 ∧ other = 18) ∨ (off = 18 ∧ other = 10)) :
    ∀ (k : ℕ) (γ : BitAssignment 27), k ≤ 8 → γ (wMux 26) = 0 →
      let η :=
          (scbOfList ((List.range k).map fun j ↦ cswapMux27 s (wMux (2 + j)) (wMux (off + j))
          (wMux 26))).evalS γ
      η (wMux 0) = γ (wMux 0) ∧ η (wMux 1) = γ (wMux 1) ∧ η (wMux 26) = 0 ∧
      (∀ i : Fin 8, η (wMux (other + i.val)) = γ (wMux (other + i.val))) ∧
      (∀ i : Fin 8, i.val < k →
        let a1 := γ (wMux (2 + i.val)) + γ (wMux (off + i.val));
        let b1 := γ (wMux (off + i.val)) + γ s * a1
        η (wMux (2 + i.val)) = a1 + b1 ∧ η (wMux (off + i.val)) = b1) ∧
      (∀ i : Fin 8, k ≤ i.val →
        η (wMux (2 + i.val)) = γ (wMux (2 + i.val)) ∧ η (wMux (off + i.val)) =
            γ (wMux (off + i.val))) := by
  intro k
  induction k with
  | zero =>
      exact fun _ _ hanc ↦ ⟨rfl, rfl, hanc, fun _ ↦ rfl,
        fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ ↦ ⟨rfl, rfl⟩⟩
  | succ k ih =>
      intro γ hk hanc
      have hseq (l : List (StructuredCB 27)) (x : StructuredCB 27) :
          ∀ δ, (scbOfList (l ++ [x])).evalS δ = x.evalS ((scbOfList l).evalS δ) := by
        induction l with
          | nil => exact fun _ ↦ rfl
          | cons hd _ ihl => exact fun δ ↦ ihl (hd.evalS δ)
      dsimp only
      rw [List.range_succ, List.map_append, List.map_singleton, hseq]
      obtain ⟨h0, h1, h26, hoth, hlt, hge⟩ := ih γ (Nat.le_of_succ_le hk) hanc
      obtain ⟨hk2, hkoff⟩ := hge ⟨k, hk⟩ le_rfl
      have h_s_eq : (scbOfList ((List.range k).map fun j ↦
          cswapMux27 s (wMux (2 + j)) (wMux (off + j)) (wMux 26))).evalS γ s = γ s := by
        rcases (by omega : s.val = 0 ∨ s.val = 1) with h | h
        · simpa [show s = wMux 0 from Fin.ext h] using h0
        · simpa [show s = wMux 1 from Fin.ext h] using h1
      have nw {a b : Wire 27} (h : a.val ≠ b.val := by
          rcases hoff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp [wMux, finMod] <;> omega) : a ≠ b :=
        Fin.ne_of_val_ne h
      rw [cswapMux27_evalS s (wMux (2 + k)) (wMux (off + k)) (wMux 26) nw nw nw nw nw nw _ h26]
      dsimp only
      have u2 {η : BitAssignment 27} {v1 v2 w v} (hw1 : w ≠ wMux (2 + k)) (hw2 : w ≠ wMux (off + k))
          (he : η w = v) : Function.update (Function.update η (wMux (off + k)) v1)
            (wMux (2 + k)) v2 w = v := by
        rw [Function.update_of_ne hw1, Function.update_of_ne hw2, he]
      refine ⟨u2 nw nw h0, u2 nw nw h1, u2 nw nw h26, fun i ↦ u2 nw nw (hoth i), fun i hi ↦ ?_,
        fun i hi ↦
            ⟨u2 nw nw (hge i (Nat.le_of_succ_le hi)).1, u2 nw nw (hge i (Nat.le_of_succ_le hi)).2⟩⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | rfl
      · exact ⟨u2 nw nw (hlt i hik).1, u2 nw nw (hlt i hik).2⟩
      · dsimp at hk2 hkoff
        exact ⟨by rw [Function.update_self, hk2, hkoff, h_s_eq],
          by rw [Function.update_of_ne nw, Function.update_self, hk2, hkoff, h_s_eq]⟩
theorem bAxisMux27_evalS (β : BitAssignment 27) (hanc : β (wMux 26) = 0) :
    bAxisMux27.evalS β (wMux 0) = β (wMux 0) ∧
    bAxisMux27.evalS β (wMux 1) = β (wMux 1) ∧
    bAxisMux27.evalS β (wMux 26) = 0 ∧
    ∀ j : Fin 8,
      let (o0, o1, o2) :=
          mux1Bit6 (β (wMux 0)) (β (wMux 1)) (β (wMux (2 + j.val))) (β (wMux (10 + j.val)))
          (β (wMux (18 + j.val)))
      bAxisMux27.evalS β (wMux (2 + j.val)) = o0 ∧
      bAxisMux27.evalS β (wMux (10 + j.val)) = o1 ∧
      bAxisMux27.evalS β (wMux (18 + j.val)) = o2 := by
  obtain ⟨y0, y1, y26, yz, ylt, _⟩ :=
      byteSwapMux27_step_kinFull (wMux 0) 10 18 (by decide) (.inl ⟨rfl, rfl⟩) 8 β le_rfl hanc
  obtain ⟨z0, z1, z26, zy, zlt, _⟩ :=
      byteSwapMux27_step_kinFull (wMux 1) 18 10 (by decide) (.inr ⟨rfl, rfl⟩) 8 _ le_rfl y26
  refine ⟨z0.trans y0, z1.trans y1, z26, fun j ↦ ?_⟩
  obtain ⟨⟨ey2, ey10⟩, ez2, ez18⟩ := And.intro (ylt j j.isLt) (zlt j j.isLt)
  dsimp only [mux1Bit6, bAxisMux27, byteSwapMux27, StructuredCB.evalS]
  exact ⟨by rw [ez2, ey2, yz j, y1], by rw [zy j, ey10], by rw [ez18, ey2, yz j, y1]⟩
/-- 8-bit `basisBits 8 k` matches `kOfBits8` identically on all `k : Fin 256`. -/
theorem kOfBits8_of_basisBits8 (k : Fin 256) (β : BitAssignment 226)
    (hβ : ∀ b : Fin 8, β (wKin b.val) = basisBits 8 k b) : kOfBits8 β = k := by
  let P (x : Fin 256) := finMod 255 (prefixSum (fun j ↦ basisBits 8 x (finMod 7 j)) 8) = x
  have h16 : ∀ a b : Fin 16, P ⟨16 * a.1 + b.1, by omega⟩ := by decide
  have hpre : ∀ n ≤ 8, prefixSum (fun j ↦ β (wKin j)) n = prefixSum (fun j ↦
      basisBits 8 k (finMod 7 j)) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [prefixSum, prefixSum, ih (Nat.le_of_succ_le hn), hβ ⟨n, hn⟩,
          show finMod 7 n = ⟨n, hn⟩ from Fin.ext (by dsimp [finMod]; omega)]
  exact (congrArg (finMod 255) (hpre 8 le_rfl)).trans
    ((Fin.ext (Nat.div_add_mod k.1 16) : (⟨16 * (k.1 / 16) + k.1 % 16, by omega⟩ : Fin 256) = k) ▸
      h16 ⟨k.1 / 16, by omega⟩ ⟨k.1 % 16, by omega⟩)
/--
Single-axis kinetic operator matrix on `Fin (2 ^ 8)` after `2^30`-coin averaging:
`Fᴴ * diag(fun k ↦ ((twosComplement k : ℝ)^2 - 8192) / 8192) * F`.
-/
noncomputable def kinAxisShiftedOp : Operator (2 ^ 8) :=
    (QFT.qftMatrix 8)ᴴ * Matrix.diagonal (fun k : Fin 256 ↦
    ((((twosComplement_frozen k : ℝ) ^ 2 - 8192) / 8192 : ℝ) : ℂ)) * QFT.qftMatrix 8
end QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull
attribute [irreducible] QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull.bAxisMux27
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution
namespace QuantumComputation.Specs.PhotochemistrySolution.KineticFast
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb (wKin)
/-- Compact Pauli-X gate on wire `w` of `Wire 226`. -/
def gx226 (w : ℕ) : ComputeProg 226 := .x (wKin w)
/-- Compact CNOT gate on wires `(c, t)` of `Wire 226`. -/
def gc226 (c t : ℕ) : ComputeProg 226 := safeCnotCP (wKin c) (wKin t)
/-- Compact temporary-AND gate on wires `(c₁, c₂, a)` of `Wire 226`. -/
def ga226 (c₁ c₂ a : ℕ) : ComputeProg 226 := safeAndGateCP (wKin c₁) (wKin c₂) (wKin a)
/-- Balanced binary `.seq` tree for `ComputeProg 226` keeping kernel stack depth logarithmic. -/
def seqCP226 : List (ComputeProg 226) → ComputeProg 226
  | [] => .id
  | [p] => p
  | p₁ :: p₂ :: rest =>
      let k := (p₁ :: p₂ :: rest).length / 2
      .seq (seqCP226 ((p₁ :: p₂ :: rest).take k)) (seqCP226 ((p₁ :: p₂ :: rest).drop k))
termination_by ps => ps.length
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_take, List.length_drop]; omega
end QuantumComputation.Specs.PhotochemistrySolution.KineticFast

namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit
  PhotochemistrySolution.Stage4Kin14Scb PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (kinAxisShiftedOp
    kOfBits8_of_basisBits8)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB (finMod)
theorem prefixSum_eq_sum_pow (f : ℕ → ZMod 2) :
    ∀ n : ℕ, prefixSum f n = ∑ b : Fin n, if f b.val = 1 then 2 ^ b.val else 0
  | 0 => rfl
  | n + 1 => by
      rcases DynCircExt.bit_cases (f n) with h | h <;>
        simp [Fin.sum_univ_castSucc, prefixSum, prefixSum_eq_sum_pow f n, h, ZMod.val_one]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

section
set_option exponentiation.threshold 8192
open Operator QProg DynamicCircuit Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
namespace QuantumComputation.Specs.PhotochemistrySolution.KineticFast
attribute [local semireducible] StructuredCB.validProgMask StructuredCB.finalCleanMask
-- Kinetic phase compute programs with bit-parallel verification.
def pKinMidPre8CP : ComputeProg 226 :=
    seqCP226 [gx226 25, gc226 7 25, gc226 25 26, gc226 0 26, gc226 8 27, gc226 25 26, gc226 25 27,
    ga226 26 27 28, gc226 25 28, gc226 25 29, gc226 1 29, gc226 9 30, gc226 28 29, gc226 28 30,
    ga226 29 30 31, gc226 28 31, gc226 25 32, gc226 2 32, gc226 10 33, gc226 31 32, gc226 31 33,
    ga226 32 33 34, gc226 31 34, gc226 25 35, gc226 3 35, gc226 11 36, gc226 34 35, gc226 34 36,
    ga226 35 36 37, gc226 34 37, gc226 25 38, gc226 4 38, gc226 12 39, gc226 37 38, gc226 37 39,
    ga226 38 39 40, gc226 37 40, gc226 25 41, gc226 5 41, gc226 13 42, gc226 40 41, gc226 40 42,
    ga226 41 42 43, gc226 40 43, gc226 25 44, gc226 6 44, gc226 14 45, gc226 43 44, gc226 43 45,
    ga226 44 45 46, gc226 43 46]
inductive LTreeW0 : Type
  | leaf : ℕ → LTreeW0
  | node : LTreeW0 → LTreeW0 → LTreeW0
/-- All-zero `LTreeW0` of depth `d`. -/
def ltreeZeroW0 : ℕ → LTreeW0
  | 0 => .leaf 0
  | d + 1 =>
      let c := ltreeZeroW0 d
      .node c c
/-- Read wire `i` lane bitmask at depth `d`. -/
def LTreeW0.get : ℕ → LTreeW0 → ℕ → ℕ
  | 0, .leaf v, _ => v
  | d + 1, .node l hi, i => if i.testBit d then hi.get d i else l.get d i
  | _, _, _ => 0
/-- Write wire `i` lane bitmask at depth `d`. -/
def LTreeW0.set : ℕ → LTreeW0 → ℕ → ℕ → LTreeW0
  | 0, _, _, v => .leaf v
  | d + 1, .node l hi, i, v =>
      if i.testBit d then .node l (hi.set d i v) else .node (l.set d i v) hi
  | d + 1, .leaf _, i, v =>
      let z := ltreeZeroW0 d
      if i.testBit d then .node z (z.set d i v) else .node (z.set d i v) z
/-- Single-pass GMP bit-parallel evaluator over all lanes simultaneously. -/
def evalLanesW0 (allOnes : ℕ) : ComputeProg 226 → LTreeW0 → LTreeW0
  | .id, t => t
  | .x u, t => t.set 8 u.val (allOnes ^^^ t.get 8 u.val)
  | .cnot cw tw _, t => t.set 8 tw.val (t.get 8 tw.val ^^^ t.get 8 cw.val)
  | .andGate c₁ c₂ a _ _ _, t =>
      t.set 8 a.val (t.get 8 a.val ^^^ (t.get 8 c₁.val &&& t.get 8 c₂.val))
  | .seq p₁ p₂, t => evalLanesW0 allOnes p₂ (evalLanesW0 allOnes p₁ t)
/-- Duplicate a `2^d`-bit lane pattern into a `2^(d+1)`-bit lane pattern. -/
def dupMaskW0 (d m : ℕ) : ℕ := m ||| (m <<< (1 <<< d))
/-- `2^(k + 1 + r)`-bit Walsh mask whose bit `lane` equals `lane.testBit k`. -/
def walshMaskW0 (k : ℕ) : ℕ → ℕ
  | 0 => ((1 <<< (1 <<< k)) - 1) <<< (1 <<< k)
  | r + 1 => dupMaskW0 (k + 1 + r) (walshMaskW0 k r)
/-- Contiguous `[lo, hi)` bitmask `(1 <<< hi) - (1 <<< lo)`. -/
def rangeMaskW0 (hi lo : ℕ) : ℕ := (1 <<< hi) - (1 <<< lo)
/-- Balanced depth-`d` bitwise OR over `[base .. base + 2^d)`. -/
def orTreeW0 (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, base => f base
  | d + 1, base => orTreeW0 f d base ||| orTreeW0 f d (base + (1 <<< d))
/-- Pure `Nat` magnitude `|twosComplement k|` for `k < 256`. -/
def tcAbs8W0 (k : ℕ) : ℕ := if Nat.ble k 127 then k else 256 - k
/-- Expected `32,768`-bit truth table (`lane = q + 128 * k`) for `tcAbs8W0 k ≤ q`. -/
def expectedCmpMaskW0 : ℕ :=
    orTreeW0 (fun k ↦ if Nat.ble (tcAbs8W0 k) 127 then rangeMaskW0 (128 * k + 128)
    (128 * k + tcAbs8W0 k) else 0) 8 0
end QuantumComputation.Specs.PhotochemistrySolution.KineticFast

namespace QuantumComputation.Specs.PhotochemistrySolution.KineticFast
-- lane evaluation for pKinPre8CP (32 T) and pKinPreW0CP (164 T)
theorem ltreeZeroW0_get : ∀ d i, (ltreeZeroW0 d).get d i = 0
  | 0, _ => rfl
  | d + 1, i => by dsimp only [ltreeZeroW0, LTreeW0.get]; split_ifs <;> exact ltreeZeroW0_get d i
theorem ltree_set_self : ∀ d (t : LTreeW0) i v, (t.set d i v).get d i = v
  | 0, _, _, _ => rfl
  | d + 1, t, i, v => by
      cases t <;> cases hbi : i.testBit d <;> simp [LTreeW0.set, LTreeW0.get, hbi,
          ltree_set_self d _ i v]
theorem ltree_set_other :
    ∀ d (t : LTreeW0) i j v,
      (∃ k < d, i.testBit k ≠ j.testBit k) → (t.set d i v).get d j = t.get d j
  | 0, _, _, _, _, ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero k)
  | d + 1, t, i, j, v, ⟨k, hk, hne⟩ => by
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
      · cases t <;> cases hbi : i.testBit d <;> cases hbj : j.testBit d <;>
          simp [LTreeW0.set, LTreeW0.get, hbi, hbj, fun s ↦ ltree_set_other d s i j v ⟨k, hlt, hne⟩,
              ltreeZeroW0_get]
      · cases t <;> cases hbi : i.testBit k <;> cases hbj : j.testBit k <;> simp_all [LTreeW0.set,
            LTreeW0.get, ltreeZeroW0_get]
theorem ltree_set8_ne {t : LTreeW0} {u v : ℕ} (hu : u < 256) (hv : v < 256) (hne : u ≠ v)
    (x : ℕ) : (t.set 8 u x).get 8 v = t.get 8 v :=
  ltree_set_other 8 t u v x <| Classical.byContradiction fun hAll ↦ hne <|
    Nat.eq_of_testBit_eq fun k ↦ if hk : k < 8 then Classical.byContradiction fun h1 ↦
        hAll ⟨k, hk, h1⟩ else by
      have hpow : 256 ≤ 2 ^ k :=
          le_trans (by decide : 256 ≤ 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu hpow),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv hpow)]
theorem zmod2_one_add : ∀ a : ZMod 2, ((a + 1 == 1)) = Bool.not (a == 1) := by decide
theorem zmod2_xor : ∀ a b : ZMod 2, ((a + b == 1)) = xor (a == 1) (b == 1) := by decide
theorem zmod2_and : ∀ a b : ZMod 2, ((a * b == 1)) = ((a == 1) && (b == 1)) := by decide
theorem rangeMaskW0_testBit (hi lo i : ℕ) (h : lo ≤ hi) : (rangeMaskW0 hi lo).testBit i =
    decide (lo ≤ i ∧ i < hi) := by
  rw [show rangeMaskW0 hi lo = (2 ^ (hi - lo) - 1) <<< lo by
    unfold rangeMaskW0; simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.sub_mul, ← Nat.pow_add,
        Nat.sub_add_cancel h],
    Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h1 : lo ≤ i <;> by_cases h2 : i < hi <;> simp [h1, h2] <;> omega
theorem evalLanesW0_testBit {N lane : ℕ} (hl : lane < N) (p : ComputeProg 226) : ∀ (t : LTreeW0)
    (β : BitAssignment 226), (∀ w : Wire 226, (t.get 8 w.val).testBit lane = (β w == 1)) → ∀ w :
    Wire 226, ((evalLanesW0 ((1 <<< N) - 1) p t).get 8 w.val).testBit lane = (p.fwdBits β w == 1)
    := by
  have hAll : ((1 <<< N) - 1).testBit lane = true := by
    simpa [rangeMaskW0, hl] using rangeMaskW0_testBit N 0 lane (Nat.zero_le N)
  have step (a : Wire 226) (m : ℕ) (b : ZMod 2) (t : LTreeW0) (β : BitAssignment 226)
      (h : ∀ w : Wire 226, (t.get 8 w.val).testBit lane = (β w == 1))
      (hm : m.testBit lane = (b == 1)) (w : Wire 226) :
      ((t.set 8 a.val m).get 8 w.val).testBit lane = (Function.update β a b w == 1) := by
    rcases eq_or_ne a w with rfl | e
    · rw [ltree_set_self, Function.update_self, hm]
    · rw [ltree_set8_ne (lt_trans a.isLt (by decide)) (lt_trans w.isLt (by decide))
          (Fin.val_ne_of_ne e),
        Function.update_of_ne e.symm, h w]
  induction p with
  | id => exact fun _ _ h ↦ h
  | seq _ _ ih₁ ih₂ => exact fun t β h ↦ ih₂ _ _ (ih₁ t β h)
  | x u => exact fun t β h ↦ step u _ _ t β h (by simp [Nat.testBit_xor, hAll, h u, zmod2_one_add])
  | cnot cw tw _ =>
      exact fun t β h ↦
          step tw _ _ t β h (by simp [Nat.testBit_xor, h tw, h cw, zmod2_xor])
  | andGate c₁ c₂ a _ _ _ =>
      exact fun t β h ↦ step a _ _ t β h
        (by simp [Nat.testBit_xor, Nat.testBit_and, h a, h c₁, h c₂, zmod2_xor, zmod2_and])
theorem orTreeW0_testBit (f : ℕ → ℕ) :
    ∀ d base i, ((orTreeW0 f d base).testBit i = true) ↔
      ∃ k < 2 ^ d, (f (base + k)).testBit i = true
  | 0, base, i =>
      ⟨fun h ↦ ⟨0, Nat.zero_lt_one, by simpa [orTreeW0] using h⟩,
       fun ⟨k, hk, h⟩ ↦ by simpa [orTreeW0, show k = 0 by omega] using h⟩
  | d + 1, base, i => by
      dsimp only [orTreeW0]
      rw [Nat.testBit_or, Bool.or_eq_true, orTreeW0_testBit f d base i,
        orTreeW0_testBit f d (base + (1 <<< d)) i, Nat.one_shiftLeft, Nat.pow_succ]
      exact ⟨fun h ↦ h.elim (fun ⟨k, hk, h⟩ ↦ ⟨k, by omega, h⟩)
          (fun ⟨k, hk, h⟩ ↦ ⟨2 ^ d + k, by omega, by simpa [Nat.add_assoc] using h⟩),
        fun ⟨k, hk, h⟩ ↦ if hlo : k < 2 ^ d then .inl ⟨k, hlo, h⟩ else
          .inr ⟨k - 2 ^ d, by omega,
              by simpa [show base + 2 ^ d + (k - 2 ^ d) = base + k by omega] using h⟩⟩
theorem walshMaskW0_high (k : ℕ) :
    ∀ r i, 2 ^ (k + 1 + r) ≤ i → (walshMaskW0 k r).testBit i = false
  | 0, i, hi => by
      have h2 : 2 * 2 ^ k ≤ i := by simpa [Nat.pow_succ, Nat.mul_comm] using hi
      simp [walshMaskW0, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, show ¬(i - 2 ^ k <
          2 ^ k) by omega]
  | r + 1, i, hi => by
      have h2 : 2 ^ (k + 1 + r) * 2 ≤ i := by simpa [← Nat.add_assoc, Nat.pow_succ] using hi
      simp [walshMaskW0, dupMaskW0, Nat.one_shiftLeft, walshMaskW0_high k r i (by omega),
        walshMaskW0_high k r (i - 2 ^ (k + 1 + r)) (by omega)]
theorem walshMaskW0_low (k : ℕ) :
    ∀ r i, i < 2 ^ (k + 1 + r) → (walshMaskW0 k r).testBit i = i.testBit k
  | 0, i, hi => by
      have h2 : i < 2 * 2 ^ k := by simpa [Nat.pow_succ, Nat.mul_comm] using hi
      dsimp only [walshMaskW0]
      rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
        Nat.testBit, Nat.shiftRight_eq_div_pow]
      by_cases hlo : 2 ^ k ≤ i
      · rw [show i / 2 ^ k = 1 by
          rw [show i = (i - 2 ^ k) + 1 * 2 ^ k by omega,
            Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt (by omega)]]
        simp [hlo, show i - 2 ^ k < 2 ^ k by omega]
      · simp [hlo, Nat.div_eq_of_lt (show i < 2 ^ k by omega)]
  | r + 1, i, hi => by
      have h2 : i < 2 ^ (k + 1 + r) * 2 := by simpa [← Nat.add_assoc, Nat.pow_succ] using hi
      dsimp only [walshMaskW0, dupMaskW0]
      rw [Nat.one_shiftLeft, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hlo : 2 ^ (k + 1 + r) ≤ i
      · rw [walshMaskW0_high k r i hlo, Bool.false_or, decide_eq_true hlo, Bool.true_and,
          walshMaskW0_low k r (i - 2 ^ (k + 1 + r)) (by omega)]
        refine testBit_eq_of_mod_two_pow (Nat.lt_succ_self k) ?_
        have _ : 2 ^ (k + 1 + r) = 2 ^ r * 2 ^ (k + 1) := by rw [← Nat.pow_add, Nat.add_comm]
        conv_rhs =>
            rw [show i = (i - 2 ^ (k + 1 + r)) + 2 ^ r * 2 ^ (k + 1) by omega,
            Nat.add_mul_mod_self_right]
      · simp [hlo, walshMaskW0_low k r i (by omega)]
theorem prefixSum_testBit_lt :
    ∀ (n : ℕ) (f : ℕ → ZMod 2) (i : ℕ), i < n →
      (prefixSum f n).testBit i = (f i == 1)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, f, i, hi =>
      if e : i = n then by
        subst e
        rw [prefixSum, Nat.testBit, Nat.shiftRight_eq_div_pow,
            Nat.add_mul_div_right _ _ (Nat.two_pow_pos i),
          Nat.div_eq_of_lt (prefixSum_lt f i), Nat.zero_add]
        rcases DynCircExt.bit_cases (f i) with hf | hf <;> rw [hf] <;> decide
      else by
        rw [prefixSum, testBit_eq_of_mod_two_pow (show i < n by omega)
            (Nat.add_mul_mod_self_right _ _ _)]
        exact prefixSum_testBit_lt n f i (by omega)
theorem tcAbs8W0_eq (x : Fin 256) : (twosComplement_frozen x).natAbs = tcAbs8W0 x.val := by
  have _ := x.isLt
  change ((x.val : ℤ).bmod 256).natAbs = tcAbs8W0 x.val
  unfold tcAbs8W0 Int.bmod; simp only [Nat.ble_eq]; split_ifs <;> omega
theorem expectedCmpMaskW0_testBit {q k : ℕ} (hq : q < 128)
    (hk : k < 256) : expectedCmpMaskW0.testBit (q + 128 * k) = decide (tcAbs8W0 k ≤ q) := by
  unfold expectedCmpMaskW0
  by_cases hle : tcAbs8W0 k ≤ q
  · rw [decide_eq_true hle]
    exact (orTreeW0_testBit _ 8 0 _).mpr ⟨k, hk, by
      rw [Nat.zero_add, ite_eq_left (Nat.ble_eq.mpr (by omega)),
          rangeMaskW0_testBit _ _ _ (by omega)]
      exact decide_eq_true (by omega)⟩
  · rw [decide_eq_false hle, Bool.eq_false_iff]
    rintro htrue
    obtain ⟨k', _, hbit⟩ := (orTreeW0_testBit _ 8 0 _).mp htrue
    by_cases hb : Nat.ble (tcAbs8W0 k') 127 = true
    · have _ := Nat.ble_eq.mp hb
      rw [Nat.zero_add, ite_eq_left hb, rangeMaskW0_testBit _ _ _ (by omega),
          decide_eq_true_iff] at hbit
      obtain rfl : k' = k := by omega
      omega
    · simp [hb] at hbit

-- pKinMidPre8CP and pKinMidPreW0CP
theorem lane_q_k_testBit {q k : ℕ} (hq : q < 128) : (∀ i < 7, (q + 128 * k).testBit i =
    q.testBit i) ∧ (∀ i, (q + 128 * k).testBit (7 + i) = k.testBit i) := by
  refine ⟨fun i hi ↦ testBit_eq_of_mod_two_pow hi (Nat.add_mul_mod_self_left q 128 k), fun i ↦ ?_⟩
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_add,
      Nat.shiftRight_eq_div_pow _ 7, show 2 ^ 7 = 128 by rfl,
      Nat.add_mul_div_left _ _ (by omega : 0 < 128), Nat.div_eq_of_lt hq, Nat.zero_add]
theorem wKin_val_eq {x : ℕ} (hx : x < 226) : (wKin x).val = x := by dsimp [wKin, finMod]; omega
end QuantumComputation.Specs.PhotochemistrySolution.KineticFast
end

namespace QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.ZeroNEremAxisSq18
  PhotochemistrySolution.ZeroNEremCsa36Kick PhotochemistrySolution.ShortBin7
  PhotochemistrySolution.ShortBin7XagOpt
/-- `64`-bit mask (`0x5555fff7ffffffff`) of the `55` reachable `6`-bit pre-priority codes `p6`. -/
def validPre6Mask64 : ℕ := 6149102306861252607
/-- Exact closed-form Boolean predicate characterizing the `9` unreachable `6`-bit codes. -/
def badPre6Bool (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  (b0 && b4 && b5) || (b0 && b1 && Bool.not b2 && Bool.not b3 && Bool.not b4 && b5)
theorem validPre6Mask64_eq : ∀ p6 : Fin 64, validPre6Mask64.testBit p6.val =
    Bool.not (badPre6Bool (p6.val.testBit 0) (p6.val.testBit 1) (p6.val.testBit 2)
    (p6.val.testBit 3) (p6.val.testBit 4) (p6.val.testBit 5)) := by decide +kernel
/-- Bitwise `5`-AND priority decoder mapping `(w_act, r15, r16, r17, r18, r19)` to `oh6[j]`. -/
def pre6OhBool (j : ℕ) (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  let oh5 := b0 && b5; let rem4 := Bool.xor b0 oh5; let oh4 := rem4 && b4;
  let rem3 := Bool.xor rem4 oh4; let oh3 := rem3 && b3; let rem2 := Bool.xor rem3 oh3;
  let oh2 := rem2 && b2; let rem1 := Bool.xor rem2 oh2; let oh1 := rem1 && b1;
  let oh0 := Bool.xor rem1 oh1
  if j = 0 then oh0
  else if j = 1 then oh1
  else if j = 2 then oh2
  else if j = 3 then oh3
  else if j = 4 then oh4
  else if j = 5 then oh5
  else false
/-- `32,768`-bit column-parallel priority decoder matching `pre6OhBool` at every bit `q`. -/
def pre6OhCol (j : ℕ) (c0 c1 c2 c3 c4 c5 : ℕ) : ℕ :=
  let oh5 := c0 &&& c5; let rem4 := c0 ^^^ oh5; let oh4 := rem4 &&& c4; let rem3 := rem4 ^^^ oh4;
  let oh3 := rem3 &&& c3; let rem2 := rem3 ^^^ oh3; let oh2 := rem2 &&& c2;
  let rem1 := rem2 ^^^ oh2; let oh1 := rem1 &&& c1; let oh0 := rem1 ^^^ oh1
  if j = 0 then oh0
  else if j = 1 then oh1
  else if j = 2 then oh2
  else if j = 3 then oh3
  else if j = 4 then oh4
  else if j = 5 then oh5
  else 0
theorem pre6OhCol_testBit (j : ℕ) (hj : j < 6) (c0 c1 c2 c3 c4 c5 q : ℕ) :
    (pre6OhCol j c0 c1 c2 c3 c4 c5).testBit q = pre6OhBool j (c0.testBit q) (c1.testBit q)
    (c2.testBit q) (c3.testBit q) (c4.testBit q) (c5.testBit q) := by
  unfold pre6OhCol pre6OhBool
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Nat.testBit_and, Nat.testBit_xor]
/-- `32,768`-bit column-parallel unreachable-code detector matching `badPre6Bool` for `q < 2^15`. -/
def badPre6Col (m15 c0 c1 c2 c3 c4 c5 : ℕ) : ℕ :=
  (c0 &&& c4 &&& c5) |||
    (c0 &&& c1 &&& (m15 ^^^ c2) &&& (m15 ^^^ c3) &&& (m15 ^^^ c4) &&& c5)
theorem badPre6Col_testBit (c0 c1 c2 c3 c4 c5 q : ℕ)
    (hq : q < 2 ^ 15) : (badPre6Col (repMask 15) c0 c1 c2 c3 c4 c5).testBit q =
    badPre6Bool (c0.testBit q) (c1.testBit q) (c2.testBit q) (c3.testBit q) (c4.testBit q)
    (c5.testBit q) := by
  unfold badPre6Col badPre6Bool
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, repMask_testBit, decide_eq_true hq]
  cases c2.testBit q <;> cases c3.testBit q <;> cases c4.testBit q <;> rfl
/-- `6`-bit one-hot value decoded from `6`-bit pre-priority code `p6`. -/
def oneHot6OfPre6 (p6 : ℕ) : ℕ := packBits 6 fun j ↦
    pre6OhBool j (p6.testBit 0) (p6.testBit 1) (p6.testBit 2) (p6.testBit 3) (p6.testBit 4)
    (p6.testBit 5)
theorem oneHot6OfPre6_lt (p6 : ℕ) : oneHot6OfPre6 p6 < 64 :=
  lt_of_lt_of_eq (packBits_lt 6 _) (by decide)
theorem oneHot6OfPre6_testBit (p6 : ℕ) (j : Fin 6) : (oneHot6OfPre6 p6).testBit j.val =
    pre6OhBool j.val (p6.testBit 0) (p6.testBit 1) (p6.testBit 2) (p6.testBit 3) (p6.testBit 4)
    (p6.testBit 5) := by
  simp [oneHot6OfPre6, packBits_testBit, j.isLt]
/--
`14` -TempAND (`M = 29`) 3D pre-priority combiner emitting `(w_act, r15..r19)` on wires `15..20` .
-/
def treeCombPre14 : PrimTree :=
    .node (.node (.node (.node (.node (.node (.node (.leaf 44) (.leaf 19945498)) (.node (.leaf 44)
    (.leaf 21))) (.node (.node (.leaf 25) (.leaf 0)) (.node (.leaf 10281) (.node (.leaf 10285)
    (.leaf 20))))) (.node (.node (.node (.leaf 16787458) (.leaf 20)) (.node (.leaf 10281)
    (.node (.leaf 10285) (.leaf 0)))) (.node (.node (.leaf 21) (.leaf 25)) (.node (.leaf 12365)
    (.node (.leaf 20545) (.leaf 40)))))) (.node (.node (.node (.node (.leaf 22040602) (.leaf 40))
    (.node (.leaf 20545) (.node (.leaf 12365) (.leaf 41)))) (.node (.node (.leaf 45) (.leaf 10265))
    (.node (.leaf 10281) (.node (.leaf 10325) (.leaf 18884610)))))
    (.node (.node (.node (.leaf 10265) (.leaf 10281)) (.node (.leaf 10325) (.node (.leaf 41)
    (.leaf 45)))) (.node (.node (.leaf 2073) (.leaf 2093)) (.node (.leaf 4) (.node (.leaf 10265)
    (.leaf 10317))))))) (.node (.node (.node (.node (.node (.leaf 10305) (.leaf 10313))
    (.node (.leaf 23078918) (.leaf 10265))) (.node (.node (.leaf 10317) (.leaf 10305))
    (.node (.leaf 10313) (.node (.leaf 4) (.leaf 2073)))))
    (.node (.node (.node (.leaf 2093) (.leaf 5)) (.node (.leaf 45) (.node (.leaf 77)
    (.leaf 43097)))) (.node (.node (.leaf 24160258) (.leaf 43097)) (.node (.leaf 5)
    (.node (.leaf 45) (.leaf 77)))))) (.node (.node (.node (.node (.leaf 4145) (.leaf 14385))
    (.node (.leaf 20985866) (.node (.leaf 14385) (.leaf 4145))))
    (.node (.node (.leaf 4125) (.leaf 4145)) (.node (.leaf 12365) (.node (.leaf 12373)
    (.leaf 12381))))) (.node (.node (.node (.leaf 25178122) (.leaf 12365)) (.node (.leaf 12373)
    (.node (.leaf 12381) (.leaf 4125)))) (.node (.node (.leaf 4145) (.leaf 6177))
    (.node (.leaf 16437) (.node (.leaf 32) (.leaf 26230798))))))))
    (.node (.node (.node (.node (.node (.node (.leaf 32) (.leaf 16437)) (.node (.leaf 6177)
    (.leaf 6177))) (.node (.node (.leaf 6193) (.leaf 6197)) (.node (.leaf 6225) (.node (.leaf 4121)
    (.leaf 4125))))) (.node (.node (.node (.leaf 4173) (.leaf 4181)) (.node (.leaf 4189)
    (.node (.leaf 4177) (.leaf 4193)))) (.node (.node (.leaf 8) (.leaf 27267086)) (.node (.leaf 8)
    (.node (.leaf 4121) (.leaf 4125)))))) (.node (.node (.node (.node (.leaf 4173) (.leaf 4181))
    (.node (.leaf 4189) (.node (.leaf 4177) (.leaf 4193)))) (.node (.node (.leaf 6177) (.leaf 6193))
    (.node (.leaf 6197) (.node (.leaf 6225) (.leaf 6177)))))
    (.node (.node (.node (.leaf 6197) (.leaf 6249)) (.node (.leaf 16437) (.node (.leaf 16485)
    (.leaf 16489))))
  (.node (.node (.leaf 28327950) (.leaf 16437)) (.node (.leaf 16485) (.node (.leaf 16489)
      (.leaf 6177))))))) (.node (.node (.node (.node (.node (.leaf 6197) (.leaf 6249))
      (.node (.leaf 16) (.leaf 36))) (.node (.node (.leaf 56) (.leaf 29378578))
      (.node (.leaf 30437490) (.node (.leaf 16) (.leaf 36)))))
      (.node (.node (.node (.leaf 56) (.leaf 6245)) (.node (.leaf 6253) (.node (.leaf 12)
      (.leaf 15734902)))) (.node (.node (.leaf 12) (.leaf 6245)) (.node (.leaf 6253)
      (.node (.leaf 36869) (.leaf 36885))))))
      (.node (.node (.node (.node (.leaf 36929) (.leaf 36953)) (.node (.leaf 32769)
      (.node (.leaf 32789) (.leaf 32809)))) (.node (.node (.leaf 64) (.leaf 34821))
      (.node (.leaf 34841) (.node (.leaf 34861) (.leaf 38921)))))
      (.node (.node (.node (.leaf 38937) (.leaf 38941)) (.node (.leaf 38961) (.node (.leaf 38997)
      (.leaf 39005)))) (.node (.node (.leaf 40973) (.leaf 40993)) (.node (.leaf 41009)
      (.node (.leaf 41013) (.leaf 41057))))))))
def outCombPre14_32K : CT := evalCTWStrict (repMask 15) 29 initComb32K treeCombPre14
def outPre6Col (k : ℕ) : ℕ := getCT 7 outCombPre14_32K (15 + k)
theorem checkCombPre14Lo_true : allBelow 15 (fun w ↦ Nat.beq (getCT 7 outCombPre14_32K w)
    (getCT 7 initComb32K w)) = true := by decide +kernel
theorem checkCombPre14Hi_true : allBelow 6 (fun j ↦ Nat.beq (pre6OhCol j (outPre6Col 0)
    (outPre6Col 1) (outPre6Col 2) (outPre6Col 3) (outPre6Col 4) (outPre6Col 5) &&& validCombMask32K)
    (specColComb32K j &&& validCombMask32K)) = true := by
  decide +kernel
theorem checkCombPre14Valid_true : Nat.beq (badPre6Col (repMask 15) (outPre6Col 0) (outPre6Col 1)
    (outPre6Col 2) (outPre6Col 3) (outPre6Col 4) (outPre6Col 5) &&& validCombMask32K) 0 =
    true := by decide +kernel
theorem evalPrimTree_combPre14_bits (sx sy sz : ℕ)
    (hsx : sx < 32) (hsy : sy < 32) (hsz : sz < 32)
    (hvx : validSq5Mask32.testBit sx = true)
    (hvy : validSq5Mask32.testBit sy = true)
    (hvz : validSq5Mask32.testBit sz = true) :
    let q := sx ||| (sy <<< 5) ||| (sz <<< 10)
    let st := evalPrimTree 29 q treeCombPre14
    let p6 : Fin 64 := ⟨packBits 6 fun k ↦ st.testBit (15 + k),
      lt_of_lt_of_eq (packBits_lt 6 _) (by decide)⟩
    (∀ w < 15, st.testBit w = q.testBit w) ∧ validPre6Mask64.testBit p6.val = true ∧
    (∀ j : Fin 6, (oneHot6OfPre6 p6.val).testBit j.val =
      (fin8OneHotNat (sq5Val sx + sq5Val sy + sq5Val sz)).testBit j.val) := by
  intro q st p6
  rcases triple5_div_mod hsx hsy hsz with ⟨hqlt, hqmod, hyzAnd, hyzShr⟩
  have hSnd := evalCTW_sound (W := 15) (M := 29) (by omega) treeCombPre14 initComb32K q q (by omega)
    fun u _ ↦ initComb32K_spec hqlt u (by omega)
  have hvq := validCombMask32K_testBit hsx hsy hsz hvx hvy hvz
  have hpBit (k : ℕ) (hk : k < 6 := by omega) : p6.val.testBit k = (outPre6Col k).testBit q := by
    change (packBits 6 fun i ↦ st.testBit (15 + i)).testBit k = (getCT 7 outCombPre14_32K (15 +
        k)).testBit q
    rw [packBits_testBit, decide_eq_true hk, Bool.true_and,
      show st.testBit (15 + k) = _ from (hSnd (15 + k) (by omega)).symm, ← evalCTWStrict_eq]; rfl
  refine ⟨fun w hw ↦ by
      rw [show st.testBit w = _ from (hSnd w (by omega)).symm, ← evalCTWStrict_eq,
        show getCT 7 (evalCTWStrict (repMask 15) 29 initComb32K treeCombPre14) w = _ from
          Nat.beq_eq.mp ((allBelow_true_iff 15 _).mp checkCombPre14Lo_true w hw),
        initComb32K_spec hqlt w (by omega)], ?_, fun j ↦ ?_⟩
  · rw [validPre6Mask64_eq p6, hpBit 0, hpBit 1, hpBit 2, hpBit 3, hpBit 4, hpBit 5,
      ← badPre6Col_testBit _ _ _ _ _ _ q (by omega)]
    have hbad0 := congrArg (·.testBit q) (Nat.beq_eq.mp checkCombPre14Valid_true)
    rw [Nat.testBit_and, hvq, Bool.and_true, Nat.zero_testBit] at hbad0
    exact congrArg Bool.not hbad0
  · rw [oneHot6OfPre6_testBit p6 j, hpBit 0, hpBit 1, hpBit 2, hpBit 3, hpBit 4, hpBit 5,
      ← pre6OhCol_testBit j.val j.isLt _ _ _ _ _ _ q]
    have h1 := congrArg (·.testBit q)
      (Nat.beq_eq.mp ((allBelow_true_iff 6 _).mp checkCombPre14Hi_true j.val j.isLt))
    rw [Nat.testBit_and, Nat.testBit_and, hvq, Bool.and_true, Bool.and_true] at h1
    rw [h1, specColComb32K, forceNat_eq, forceNat_eq, ShortBin7.packPowTree_testBit 5 10 0 _ q,
      show (2 ^ (5 + 10) : ℕ) = 32768 by decide, show (2 ^ 5 : ℕ) = 32 by decide, zero_add]
    dsimp only [q]; simp only [hqmod, hqlt, decide_true, Bool.true_and, hyzAnd, hyzShr]
    change (oh5Tab2048 j.val >>> ((if Nat.ble 48 (getSq5Fast sy + getSq5Fast sz) then 48
      else getSq5Fast sy + getSq5Fast sz) <<< 5)).testBit sx = _
    rw [getSq5Fast_eq ⟨sy, hsy⟩, getSq5Fast_eq ⟨sz, hsz⟩]
    cases h48 : Nat.ble 48 (sq5Val sy + sq5Val sz)
    · have _ := mt Nat.ble_eq.mpr (Bool.eq_false_iff.mp h48)
      simp only [Bool.false_eq_true, ↓reduceIte];
          rw [oh5Tab2048_row_testBit j.val sx _ hsx (by omega), ← Nat.add_assoc]
    · have _ := Nat.ble_eq.mp h48
      simp only [↓reduceIte]; rw [oh5Tab2048_row_testBit j.val sx 48 hsx (by omega)]
      unfold fin8OneHotNat; rw [itePos (Nat.ble_eq.mpr (by omega)),
          itePos (Nat.ble_eq.mpr (by omega))]
end QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
end
end Stage4KinClosed
end
