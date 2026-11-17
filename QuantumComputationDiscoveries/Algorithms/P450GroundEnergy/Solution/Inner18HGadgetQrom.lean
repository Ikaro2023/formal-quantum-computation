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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HGadgetAux

/-!
# Low-Scratch (`25` Scratch, `(88 + 2 * R + 2 * G)` `T`) H-Gadget Symplectic `14`-Plane QROM Loader

Implements a `{Var : Type}`-computable `25`-scratch (`25 ≤ sScr`), `(88 + 2 * R + 2 * G)`-`T`,
`0`-`TOFF` grouped Hadamard-gadget symplectic `14`-plane QROM loader from a `128`-wire one-hot
register (`418 T` on the Keep-9 `optSymp14Plan` witness with `R = 147, G = 18`).

## Mechanism
- **Vanishing top column ANF coefficients**: Every `30`-column parity-extended mask satisfies
  `colMaskAnf col 30 = 0` and `colMaskAnf col 31 = 0`, so every `rcColAff` and Lempel schedule step
  only references the first `29` non-constant `5`-bit ANF monomials (`1 .. 29`).
- **`80-T` `29`-monomial encoder (`24` scratch + `wG`)**: Prepares all `29` degree-`≤ 4` `5`-bit
  monomials across the `5` index wires and `24` scratch wires using `28 T` deterministic W-state
  one-hot expansion on `x₀..x₃`, a `0-T` Mobius CNOT butterfly, and `13` clean AND gates (`52 T`),
  uncomputed in `0 T` via measurement-based uncomputation (`revUncomputeDyn`).
- **`8-T` top-monomial carry-phase fixup**: Evaluates the `m = 30` (`x₁x₂x₃x₄`) and `m = 31`
  (`x₀x₁x₂x₃x₄`) terms of `totPhi P` via two `4-T` temporary AND sandwiches onto `wG`.

## References
- A. Lempel, "Matrix factorization over GF(2) and trace-orthogonal bases of GF(2^n),"
  *SIAM J. Comput.* **4**(2), 175-186 (1975), DOI: 10.1137/0204014.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity,"
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: 10.22331/q-2018-06-18-74.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, "Trading T gates for dirty qubits in state
  preparation and unitary synthesis," *Quantum* **8**, 1375 (2024),
  DOI: 10.22331/q-2024-06-17-1375.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
    QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
    CoherentAlias AliasPrep
  Mobius126OneHot MidReflCtxRetain StepBound148Borrow
  Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 StepAnfAndCoin14Core StepKeep9Symp14Data
  HGadgetSympQrom OptKeep9Symp14Data Inner18Symp14Walk Inner18Load Inner18HadWSuperLegsA
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GroupUnary (
  RevCompute predProj predProj_conjTranspose
  predProj_idem restrictPred restrictPred_coe)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepOuter8Pi145Outer (
  predProj_mulVec_ket TransRealizes
  EquivRev WSplitValid InvWSplitDet splitRevLoop dWExpandDet1 dWExpandDet1_count_toff
  dWExpandDet1_count_t)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2Folded184Select (
  revComputeDyn revUncomputeDyn
  count_revComputeDyn_toff count_revComputeDyn_t count_revUncomputeDyn_toff count_revUncomputeDyn_t)
open _root_.Function (update update_of_ne update_self update_idem update_eq_self)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit (
  xorWireUnitary xorWireUnitary_mulVec_ket phaseFlipUnitary
  phaseFlipUnitary_mulVec_ket xMeasUnloadWireDyn count_xMeasUnloadWireDyn_toff
  count_xMeasUnloadWireDyn_t wp_xMeasUnloadWireDyn_update_self cleanFinsetProj
  restrictAssertionToCleanFinset restrictAssertionToCleanFinset_coe
  restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM (
  zeroProjOn zeroProjOn_mulVec_ket
  zeroProjOn_conjTranspose bitSign bitSign_add bit_cases basisBits_symm czMaskCircuit
  count_czMaskCircuit_toff count_czMaskCircuit_t ket_czMaskCircuit monoEval monoEval_zero anfCoeffs
  disjoint_image_of_disjointWires)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance instNeZeroTwoPowHg25B (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

namespace Inner18Bound322HGadgetQrom

/-! ## Section 3: `80-T` `29`-Monomial Encoder/Decoder & `25`-Scratch QROM Loader -/

/-- Lift a local `RevCompute m` AST onto `r : QRegister m N`. -/
def mapRev {m N : ℕ} (r : QRegister m N) : RevCompute m → RevCompute N
  | .id => .id
  | .x q => .x (r q)
  | .cnot c t h => .cnot (r c) (r t) (r.wires.injective.ne h)
  | .andGate c₁ c₂ a h₁₂ h₁a h₂a =>
      .andGate (r c₁) (r c₂) (r a) (r.wires.injective.ne h₁₂)
        (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
  | .seq p₁ p₂ => .seq (mapRev r p₁) (mapRev r p₂)
@[simp] theorem numAnd_mapRev {m N : ℕ} (r : QRegister m N) :
    ∀ p : RevCompute m, (mapRev r p).numAnd = p.numAnd
  | .id => rfl
  | .x _ => rfl
  | .cnot _ _ _ => rfl
  | .andGate _ _ _ _ _ _ => rfl
  | .seq p₁ p₂ => by simp [mapRev, RevCompute.numAnd, numAnd_mapRev r p₁, numAnd_mapRev r p₂]
theorem mapRev_spec {m N : ℕ} (r : QRegister m N) (p : RevCompute m) (β : BitAssignment N) :
    (mapRev r p).validOn β = p.validOn (fun i ↦ β (r i)) ∧
      (∀ i : Fin m, (mapRev r p).fwdBits β (r i) = p.fwdBits (fun j ↦ β (r j)) i) ∧
      (∀ w : Wire N, w ∉ Set.range r.wires → (mapRev r p).fwdBits β w = β w) := by
  induction p generalizing β with
  | id => exact ⟨rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩
  | x q =>
      refine ⟨rfl, fun i ↦ ?_, fun w hw ↦ update_of_ne (fun he ↦ hw ⟨q, he.symm⟩) _ _⟩
      by_cases hi : i = q
      · subst hi
        simp [mapRev, RevCompute.fwdBits]
      · simp [mapRev, RevCompute.fwdBits, update_of_ne (r.wires.injective.ne hi), update_of_ne hi]
  | cnot c t _ =>
      refine ⟨rfl, fun i ↦ ?_, fun w hw ↦ update_of_ne (fun he ↦ hw ⟨t, he.symm⟩) _ _⟩
      by_cases hi : i = t
      · subst hi
        simp [mapRev, RevCompute.fwdBits]
      · simp [mapRev, RevCompute.fwdBits, update_of_ne (r.wires.injective.ne hi), update_of_ne hi]
  | andGate c₁ c₂ a _ _ _ =>
      refine ⟨rfl, fun i ↦ ?_, fun w hw ↦ update_of_ne (fun he ↦ hw ⟨a, he.symm⟩) _ _⟩
      by_cases hi : i = a
      · subst hi
        simp [mapRev, RevCompute.fwdBits]
      · simp [mapRev, RevCompute.fwdBits, update_of_ne (r.wires.injective.ne hi), update_of_ne hi]
  | seq p₁ p₂ ih₁ ih₂ =>
      obtain ⟨hv1, hf1, ho1⟩ := ih₁ β
      obtain ⟨hv2, hf2, ho2⟩ := ih₂ ((mapRev r p₁).fwdBits β)
      have hEq1 : (fun i ↦ (mapRev r p₁).fwdBits β (r i)) = p₁.fwdBits (fun j ↦ β (r j)) :=
        funext hf1
      rw [hEq1] at hv2 hf2
      exact ⟨by simp [mapRev, RevCompute.validOn, hv1, hv2], hf2,
        fun w hw ↦ (ho2 w hw).trans (ho1 w hw)⟩
theorem mapRev_splitRevLoop {N : ℕ} (r29 : QRegister 29 N) (ctrl : Wire 29) :
    ∀ (R : ℕ) (w0 w1 : Fin R → Wire 29) (hd : StepOuter8Pi145Outer.WPairDisj R ctrl w0 w1)
      (hd' : StepOuter8Pi145Outer.WPairDisj R (r29 ctrl) (fun i ↦ r29 (w0 i))
        (fun i ↦ r29 (w1 i))),
      mapRev r29 (splitRevLoop ctrl R w0 w1 hd) =
        splitRevLoop (r29 ctrl) R (fun i ↦ r29 (w0 i)) (fun i ↦ r29 (w1 i)) hd'
  | 0, _, _, _, _ => rfl
  | R + 1, w0, w1, _, _ => by
      dsimp only [splitRevLoop, mapRev]
      rw [mapRev_splitRevLoop r29 ctrl R (fun i ↦ w0 i.succ) (fun i ↦ w1 i.succ) _ _]

/-- `1`-AND (`4 T`) local `2 → 4` one-hot decoder on wires `0, 1 → 5..8`. -/
def init4LocalRev : RevCompute 29 :=
  .seq (.andGate 0 1 8 (by decide) (by decide) (by decide))
    (.seq (.cnot 1 7 (by decide))
      (.seq (.cnot 8 7 (by decide))
        (.seq (.cnot 0 6 (by decide))
          (.seq (.cnot 8 6 (by decide))
            (.seq (.x 5)
              (.seq (.cnot 0 5 (by decide)) (.cnot 7 5 (by decide))))))))
theorem wSplitLocalPairDisj (R : ℕ) (ctrl : Wire 29) (hctrl : ctrl.val < 5)
    (h2R : 5 + 2 * R ≤ 21) :
    StepOuter8Pi145Outer.WPairDisj R ctrl
      (fun i : Fin R ↦ ⟨5 + i.val, by omega⟩)
      (fun i : Fin R ↦ ⟨5 + R + i.val, by omega⟩) where
  w0_inj _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  w1_inj _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  w01_ne _ _ h := by
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega
  ctrl_w0 _ h := by
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega
  ctrl_w1 _ h := by
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega

/-- Local `4`-pair (`2 → 4 → 8`) reversible W-splitting model on wires `5..8 → 9..12`. -/
def split4LocalRev : RevCompute 29 :=
  splitRevLoop 2 4 (fun i ↦ ⟨5 + i.val, by omega⟩) (fun i ↦ ⟨5 + 4 + i.val, by omega⟩)
    (wSplitLocalPairDisj 4 2 (by decide) (by decide))

/-- Local `8`-pair (`8 → 16`) reversible W-splitting model on wires `5..12 → 13..20`. -/
def split8LocalRev : RevCompute 29 :=
  splitRevLoop 3 8 (fun i ↦ ⟨5 + i.val, by omega⟩) (fun i ↦ ⟨5 + 8 + i.val, by omega⟩)
    (wSplitLocalPairDisj 8 3 (by decide) (by decide))

/-- Low-monomial (`1 .. 15`) wire locations inside `Fin 29`. -/
def loSrc29 : Fin 15 → Wire 29 :=
  ![0, 1, 8, 2, 10, 11, 12, 3, 14, 15, 16, 17, 18, 19, 20]

/-- High-monomial (`17 .. 29`) clean target wire locations inside `Fin 29`. -/
def hiTgt29 : Fin 13 → Wire 29 :=
  ![5, 6, 7, 9, 13, 21, 22, 23, 24, 25, 26, 27, 28]
theorem hiAnd_disj (k : Fin 13) :
    (4 : Wire 29) ≠ loSrc29 ⟨k.val, by omega⟩ ∧
      (4 : Wire 29) ≠ hiTgt29 k ∧ loSrc29 ⟨k.val, by omega⟩ ≠ hiTgt29 k := by
  revert k
  decide

/-- Single stage (`st = 2^b`) of the `4`-bit upward-controlled Mobius CNOT butterfly. -/
def mobiusPhaseRev (st : ℕ) (hst : st ≤ 8) : (m : ℕ) → m ≤ 16 → RevCompute 29
  | 0, _ => .id
  | m + 1, hm =>
      .seq (mobiusPhaseRev st hst m (Nat.le_of_succ_le hm))
        (if h : m &&& st = 0 ∧ m + st < 16 ∧ 0 < st then
          have hne : (⟨5 + m + st, by omega⟩ : Wire 29) ≠ ⟨5 + m, by omega⟩ := by
            intro heq
            have hv := congrArg Fin.val heq
            dsimp only at hv
            omega
          .cnot ⟨5 + m + st, by omega⟩ ⟨5 + m, by omega⟩ hne
        else .id)

/-- `13`-AND loop computing `x₄ * mono_k` (`k = 1 .. 13`) into `hiTgt29`. -/
def hiAndLoopRev : (n : ℕ) → n ≤ 13 → RevCompute 29
  | 0, _ => .id
  | n + 1, hn =>
      let d := hiAnd_disj ⟨n, hn⟩
      .seq (hiAndLoopRev n (Nat.le_of_succ_le hn))
        (.andGate 4 (loSrc29 ⟨n, by omega⟩) (hiTgt29 ⟨n, hn⟩) d.1 d.2.1 d.2.2)

/-- `13`-AND (`52 T`) post-one-hot Mobius + root-clear + high-monomial local circuit. -/
def post29LocalRev : RevCompute 29 :=
  .seq
    (.seq
      (.seq
        (.seq
          (.seq (mobiusPhaseRev 1 (by decide) 16 le_rfl)
            (mobiusPhaseRev 2 (by decide) 16 le_rfl))
          (mobiusPhaseRev 4 (by decide) 16 le_rfl))
        (mobiusPhaseRev 8 (by decide) 16 le_rfl))
      (.seq (.x 5)
        (.seq (.cnot 0 6 (by decide))
          (.seq (.cnot 1 7 (by decide))
            (.seq (.cnot 2 9 (by decide)) (.cnot 3 13 (by decide)))))))
    (hiAndLoopRev 13 le_rfl)
theorem numAnd_init4LocalRev : init4LocalRev.numAnd = 1 := by decide
theorem numAnd_post29LocalRev : post29LocalRev.numAnd = 13 := by decide

/-- Full `29`-wire local reversible model (`init4`, `split4`, `split8`, `post29`). -/
def enc29LocalRev : RevCompute 29 :=
  .seq (.seq (.seq init4LocalRev split4LocalRev) split8LocalRev) post29LocalRev

/-- Ordered local wire index for monomial `u + 1` (`u : Fin 29`). -/
def mono29LocalWire (u : Fin 29) : Wire 29 :=
  if h15 : u.val < 15 then loSrc29 ⟨u.val, h15⟩
  else if u.val = 15 then 4
  else hiTgt29 ⟨u.val - 16, by omega⟩
theorem mono29LocalWire_injective : Function.Injective mono29LocalWire := fun i j hij ↦ by
  revert i j hij
  decide

/-- Ordered `29`-wire local register holding `monoEval 5 x 1 .. monoEval 5 x 29`. -/
def mono29LocalReg : QRegister 29 29 :=
  ⟨⟨mono29LocalWire, mono29LocalWire_injective⟩⟩

/-- Canonical clean-scratch local `29`-bit input for `x : Fin (2 ^ 5)`. -/
def in29 (x : Fin (2 ^ 5)) : BitAssignment 29 :=
  fun i ↦ if h : i.val < 5 then basisBits 5 x ⟨i.val, h⟩ else 0
theorem enc29_init4_valid (x : Fin (2 ^ 5)) : init4LocalRev.validOn (in29 x) = true := by
  revert x
  decide +kernel
theorem enc29_split4_inv (x : Fin (2 ^ 5)) (i : Fin 4) :
    let s0 := init4LocalRev.fwdBits (in29 x)
    s0 ⟨5 + 4 + i.val, by omega⟩ = 0 ∧
      s0 ⟨5 + i.val, by omega⟩ = (if i.val = x.val % 4 then 1 else 0) := by
  revert x i
  decide +kernel
theorem enc29_split8_inv (x : Fin (2 ^ 5)) (i : Fin 8) :
    let s1 := split4LocalRev.fwdBits (init4LocalRev.fwdBits (in29 x))
    s1 ⟨5 + 8 + i.val, by omega⟩ = 0 ∧
      s1 ⟨5 + i.val, by omega⟩ = (if i.val = x.val % 8 then 1 else 0) := by
  revert x i
  decide +kernel
theorem enc29_post_valid (x : Fin (2 ^ 5)) :
    post29LocalRev.validOn
      (split8LocalRev.fwdBits (split4LocalRev.fwdBits (init4LocalRev.fwdBits (in29 x)))) =
      true := by
  revert x
  decide +kernel
theorem enc29_mono_fwd (x : Fin (2 ^ 5)) (u : Fin 29) :
    enc29LocalRev.fwdBits (in29 x) (mono29LocalReg u) =
      monoEval 5 (basisBits 5 x) ⟨u.val + 1, by omega⟩ := by
  revert x u
  decide +kernel
theorem monoEval5_30_31 (x : Fin (2 ^ 5)) :
    monoEval 5 (basisBits 5 x) ⟨16, by decide⟩ * monoEval 5 (basisBits 5 x) ⟨14, by decide⟩ =
      monoEval 5 (basisBits 5 x) ⟨30, by decide⟩ ∧
    monoEval 5 (basisBits 5 x) ⟨16, by decide⟩ * monoEval 5 (basisBits 5 x) ⟨15, by decide⟩ =
      monoEval 5 (basisBits 5 x) ⟨31, by decide⟩ := by
  revert x
  decide
/-- `29`-wire working register `(rQrom 0..4) ++ (rScr 0..23)`. -/
def mkReg29 {N sScr : ℕ} (rQrom : QRegister (aliasQromBits 5 128 9 0) N)
    (rScr : QRegister sScr N) (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) :
    QRegister 29 N :=
  (rQrom.slice 0 5 (by decide)).concat (rScr.slice 0 24 (by omega))
    ((hdisj.compose_left _).compose_right _)
theorem mkReg29_lt5 {N sScr : ℕ} (rQrom : QRegister (aliasQromBits 5 128 9 0) N)
    (rScr : QRegister sScr N) (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    (j : Fin 29) (hj : j.val < 5) :
    mkReg29 rQrom rScr hScr hdisj j = (rQrom.slice 0 5 (by decide)) ⟨j.val, hj⟩ := by
  let k : Fin 5 := ⟨j.val, hj⟩
  have hEq : j = Fin.castAdd 24 k := Fin.ext rfl
  exact (congrArg (fun x ↦ mkReg29 rQrom rScr hScr hdisj x) hEq).trans
    (QRegister.concat_apply_left (rQrom.slice 0 5 (by decide)) (rScr.slice 0 24 (by omega)) _ k)
theorem mkReg29_ge5 {N sScr : ℕ} (rQrom : QRegister (aliasQromBits 5 128 9 0) N)
    (rScr : QRegister sScr N) (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    (j : Fin 29) (hj : ¬ j.val < 5) :
    mkReg29 rQrom rScr hScr hdisj j =
      (rScr.slice 0 24 (by omega)) ⟨j.val - 5, by omega⟩ := by
  have hjlt := j.isLt
  let k : Fin 24 := ⟨j.val - 5, by omega⟩
  have hEq : j = Fin.natAdd 5 k := Fin.ext (by
    dsimp only [k, Fin.val_natAdd]
    omega)
  exact (congrArg (fun x ↦ mkReg29 rQrom rScr hScr hdisj x) hEq).trans
    (QRegister.concat_apply_right (rQrom.slice 0 5 (by decide)) (rScr.slice 0 24 (by omega)) _ k)
theorem reg29_ne_wG {N sScr : ℕ} (rQrom : QRegister (aliasQromBits 5 128 9 0) N)
    (rScr : QRegister sScr N) (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    (j : Fin 29) : mkReg29 rQrom rScr hScr hdisj j ≠ rScr ⟨24, by omega⟩ := by
  by_cases hj : j.val < 5
  · rw [mkReg29_lt5 rQrom rScr hScr hdisj j hj]
    exact (hdisj.compose_left _).ne ⟨j.val, hj⟩ ⟨24, by omega⟩
  · rw [mkReg29_ge5 rQrom rScr hScr hdisj j hj]
    intro hEq
    have hv := congrArg Fin.val (rScr.wires.injective hEq)
    dsimp only [QRegister.slice, QRegister.compose_apply, QRegister.block_apply_val] at hv
    omega
theorem wSplitReg29Valid {N : ℕ} (r29 : QRegister 29 N) (wG : Wire N)
    (hwG : ∀ j : Fin 29, r29 j ≠ wG) (R : ℕ) (ctrl : Wire 29)
    (hctrl : ctrl.val < 5) (h2R : 5 + 2 * R ≤ 21) :
    WSplitValid R (r29 ctrl)
      (fun i : Fin R ↦ r29 ⟨5 + i.val, by omega⟩)
      (fun i : Fin R ↦ r29 ⟨5 + R + i.val, by omega⟩) wG where
  w0_inj _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val (r29.wires.injective h)))
  w1_inj _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val (r29.wires.injective h)))
  w01_ne i j h := (wSplitLocalPairDisj R ctrl hctrl h2R).w01_ne i j (r29.wires.injective h)
  ctrl_w0 i h := (wSplitLocalPairDisj R ctrl hctrl h2R).ctrl_w0 i (r29.wires.injective h)
  ctrl_w1 i h := (wSplitLocalPairDisj R ctrl hctrl h2R).ctrl_w1 i (r29.wires.injective h)
  q_ctrl := (hwG ctrl).symm
  q_w0 _ := (hwG _).symm
  q_w1 _ := (hwG _).symm

/-- `80-T`, `0-TOFF` `29`-monomial encoder on `mkReg29` using `rScr 24` as `wG`. -/
def enc29Dyn {Var : Type} {N sScr : ℕ} (v : Var)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) : DynamicCircuit Var N :=
  let r29 := mkReg29 rQrom rScr hScr hdisj
  let wG := rScr ⟨24, by omega⟩
  let hwG := reg29_ne_wG rQrom rScr hScr hdisj
  .seq
    (.seq
      (.seq (revComputeDyn (mapRev r29 init4LocalRev))
        (dWExpandDet1 v 4 (r29 2) _ _ wG (wSplitReg29Valid r29 wG hwG 4 2 (by decide) (by decide))))
      (dWExpandDet1 v 8 (r29 3) _ _ wG (wSplitReg29Valid r29 wG hwG 8 3 (by decide) (by decide))))
    (revComputeDyn (mapRev r29 post29LocalRev))

/-- `80-T` `29`-monomial sandwich (`enc29Dyn`, `mid`, `revUncomputeDyn`). -/
def withMono29Dyn {Var : Type} {N sScr : ℕ} (v : Var)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    (mid : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (enc29Dyn v rQrom rScr hScr hdisj)
    (.seq mid (revUncomputeDyn v (mapRev (mkReg29 rQrom rScr hScr hdisj) enc29LocalRev)))
@[simp] theorem count_withMono29Dyn_toff {Var : Type} {N sScr : ℕ} (v : Var)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    {mid : DynamicCircuit Var N} (hm : mid.count .TOFF = 0) :
    (withMono29Dyn v rQrom rScr hScr hdisj mid).count .TOFF = 0 := by
  simp [withMono29Dyn, enc29Dyn, DynamicCircuit.count, count_revComputeDyn_toff,
    count_revUncomputeDyn_toff, hm]
@[simp] theorem count_withMono29Dyn_t {Var : Type} {N sScr : ℕ} (v : Var)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    (mid : DynamicCircuit Var N) :
    (withMono29Dyn v rQrom rScr hScr hdisj mid).count .T = 80 + mid.count .T := by
  simp only [withMono29Dyn, enc29Dyn, DynamicCircuit.count, count_revComputeDyn_t,
    count_revUncomputeDyn_t, dWExpandDet1_count_t, numAnd_mapRev, numAnd_init4LocalRev,
    numAnd_post29LocalRev]
  omega
theorem wpZeroSet_withMono29Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {N sScr : ℕ}
    (v : Var) (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    {φ : BitAssignment N → ZMod 2} {mid : DynamicCircuit Var N}
    (hMid : WpZeroSet v (rScr.image \ (rScr.slice 0 24 (by omega)).image)
      (diagKetUnitary φ) mid) :
    WpZeroSet v rScr.image
      (diagKetUnitary fun β ↦
        φ ((mapRev (mkReg29 rQrom rScr hScr hdisj) enc29LocalRev).fwdBits β))
      (withMono29Dyn v rQrom rScr hScr hdisj mid) := by
  let rIdx := rQrom.slice 0 5 (by decide)
  let rScr24 := rScr.slice 0 24 (by omega)
  let rScr25 := rScr.slice 0 25 (by omega)
  let r29 := mkReg29 rQrom rScr hScr hdisj
  let wG := rScr ⟨24, by omega⟩
  let hwG := reg29_ne_wG rQrom rScr hScr hdisj
  let S_tail := rScr.image \ rScr24.image
  let S_enc : BitAssignment N → Bool := fun β ↦ decide (∀ j : Fin 25, β (rScr25 j) = 0)
  have hQromScr := disjoint_image_of_disjointWires hdisj
  have hSub : rScr25.image ⊆ rScr.image := rScr.image_compose_subset _
  have hNot29 {w : Wire N} (hw : w ∈ S_tail) : w ∉ Set.range r29.wires := by
    rintro ⟨j, rfl⟩
    obtain ⟨hwScr, hwNot24⟩ := Finset.mem_sdiff.mp hw
    by_cases hj : j.val < 5
    · have hjQ : r29 j ∈ rQrom.image := by
        dsimp only [r29]
        rw [mkReg29_lt5 rQrom rScr hScr hdisj j hj]
        exact rQrom.image_compose_subset _ ((rIdx.mem_image _).mpr ⟨⟨j.val, hj⟩, rfl⟩)
      exact Finset.disjoint_left.mp hQromScr hjQ hwScr
    · apply hwNot24
      dsimp only [r29]
      rw [mkReg29_ge5 rQrom rScr hScr hdisj j hj]
      exact (rScr24.mem_image _).mpr ⟨⟨j.val - 5, by omega⟩, rfl⟩
  have hClean (β : BitAssignment N) (h0 : ∀ w ∈ rScr.image, β w = 0)
      (w : Wire N) (hw : w ∈ S_tail) :
      (mapRev r29 enc29LocalRev).fwdBits β w = 0 :=
    ((mapRev_spec r29 enc29LocalRev β).2.2 w (hNot29 hw)).trans (h0 w (Finset.mem_sdiff.mp hw).1)
  have hwGNot29 : wG ∉ Set.range r29.wires := fun ⟨j, hj⟩ ↦ hwG j hj
  let p0 := mapRev r29 init4LocalRev
  let p1 := mapRev r29 split4LocalRev
  let p2 := mapRev r29 split8LocalRev
  let p3 := mapRev r29 post29LocalRev
  let q1 := p0.seq p1
  let q2 := q1.seq p2
  have hChain (β : BitAssignment N) (hS : S_enc β = true) :
      p0.validOn β = true ∧
      InvWSplitDet 4 (fun i : Fin 4 ↦ r29 ⟨5 + i.val, by omega⟩)
        (fun i : Fin 4 ↦ r29 ⟨5 + 4 + i.val, by omega⟩) wG (p0.fwdBits β) ∧
      InvWSplitDet 8 (fun i : Fin 8 ↦ r29 ⟨5 + i.val, by omega⟩)
        (fun i : Fin 8 ↦ r29 ⟨5 + 8 + i.val, by omega⟩) wG (q1.fwdBits β) ∧
      p3.validOn (q2.fwdBits β) = true := by
    have h25 := of_decide_eq_true hS
    let x := CircuitModular.UnsignedGivens.localIdx rIdx β
    have hIn : (fun i : Fin 29 ↦ β (r29 i)) = in29 x := by
      funext i
      dsimp only [in29, r29]
      by_cases hi : i.val < 5
      · simp only [hi, ↓reduceDIte]
        rw [mkReg29_lt5 rQrom rScr hScr hdisj i hi]
        exact (congrFun (basisBits_symm (fun k ↦ β (rIdx k))) ⟨i.val, hi⟩).symm
      · simp only [hi, ↓reduceDIte]
        rw [mkReg29_ge5 rQrom rScr hScr hdisj i hi]
        have hrw : rScr24 ⟨i.val - 5, by omega⟩ = rScr25 ⟨i.val - 5, by omega⟩ := rfl
        rw [hrw]
        exact h25 _
    have hwG0 : β wG = 0 := h25 ⟨24, by decide⟩
    obtain ⟨hv0, hf0, ho0⟩ := mapRev_spec r29 init4LocalRev β
    rw [hIn] at hv0 hf0
    obtain ⟨_, hf01, ho01⟩ := mapRev_spec r29 (init4LocalRev.seq split4LocalRev) β
    rw [hIn] at hf01
    obtain ⟨_, hf012, _⟩ :=
      mapRev_spec r29 ((init4LocalRev.seq split4LocalRev).seq split8LocalRev) β
    rw [hIn] at hf012
    have hq2Eq : (fun i ↦ q2.fwdBits β (r29 i)) =
        split8LocalRev.fwdBits (split4LocalRev.fwdBits (init4LocalRev.fwdBits (in29 x))) :=
      funext hf012
    have hv3 : p3.validOn (q2.fwdBits β) = true := by
      rw [(mapRev_spec r29 post29LocalRev (q2.fwdBits β)).1, hq2Eq]
      exact enc29_post_valid x
    have hi4 : InvWSplitDet 4 (fun i : Fin 4 ↦ r29 ⟨5 + i.val, by omega⟩)
        (fun i : Fin 4 ↦ r29 ⟨5 + 4 + i.val, by omega⟩) wG (p0.fwdBits β) := by
      refine ⟨(ho0 wG hwGNot29).trans hwG0,
        fun i ↦ (hf0 _).trans (enc29_split4_inv x i).1,
        ⟨x.val % 4, Nat.mod_lt _ (by decide)⟩,
        (hf0 _).trans ((enc29_split4_inv x _).2.trans (ite_eq_left rfl)),
        fun i hne ↦ (hf0 _).trans ((enc29_split4_inv x i).2.trans
          (ite_eq_right (Fin.val_ne_of_ne hne)))⟩
    have hi8 : InvWSplitDet 8 (fun i : Fin 8 ↦ r29 ⟨5 + i.val, by omega⟩)
        (fun i : Fin 8 ↦ r29 ⟨5 + 8 + i.val, by omega⟩) wG (q1.fwdBits β) := by
      refine ⟨(ho01 wG hwGNot29).trans hwG0,
        fun i ↦ (hf01 _).trans (enc29_split8_inv x i).1,
        ⟨x.val % 8, Nat.mod_lt _ (by decide)⟩,
        (hf01 _).trans ((enc29_split8_inv x _).2.trans (ite_eq_left rfl)),
        fun i hne ↦ (hf01 _).trans ((enc29_split8_inv x i).2.trans
          (ite_eq_right (Fin.val_ne_of_ne hne)))⟩
    exact ⟨hv0.trans (enc29_init4_valid x), hi4, hi8, hv3⟩
  have e0 : EquivRev v S_enc p0 (revComputeDyn p0) :=
    EquivRev.ofRevCompute v S_enc p0 fun β hS ↦ (hChain β hS).1
  let hv4 := wSplitReg29Valid r29 wG hwG 4 2 (by decide) (by decide)
  have hp1Eq : p1 = splitRevLoop (r29 2) 4 _ _ hv4.toWPairDisj :=
    mapRev_splitRevLoop r29 2 4 _ _ _ _
  have e1 : EquivRev v S_enc q1
      (.seq (revComputeDyn p0) (dWExpandDet1 v 4 (r29 2) _ _ wG hv4)) := by
    dsimp only [q1]
    rw [hp1Eq]
    refine e0.seq (EquivRev.ofDWExpandDet1 v 4 (r29 2) _ _ wG hv4 _ fun γ hγ ↦ ?_)
    rw [← p0.fwdBits_invBits γ]
    exact (hChain _ hγ).2.1
  let hv8 := wSplitReg29Valid r29 wG hwG 8 3 (by decide) (by decide)
  have hp2Eq : p2 = splitRevLoop (r29 3) 8 _ _ hv8.toWPairDisj :=
    mapRev_splitRevLoop r29 3 8 _ _ _ _
  have e2 : EquivRev v S_enc q2
      (.seq (.seq (revComputeDyn p0) (dWExpandDet1 v 4 (r29 2) _ _ wG hv4))
        (dWExpandDet1 v 8 (r29 3) _ _ wG hv8)) := by
    dsimp only [q2]
    rw [hp2Eq]
    refine e1.seq (EquivRev.ofDWExpandDet1 v 8 (r29 3) _ _ wG hv8 _ fun γ hγ ↦ ?_)
    rw [← q1.fwdBits_invBits γ]
    exact (hChain _ hγ).2.2.1
  have e3 : EquivRev v S_enc (q2.seq p3) (enc29Dyn v rQrom rScr hScr hdisj) := by
    refine e2.seq (EquivRev.ofRevCompute v _ p3 fun γ hγ ↦ ?_)
    rw [← q2.fwdBits_invBits γ]
    exact (hChain _ hγ).2.2.2
  exact wpZeroSet_equivRev_diag v rScr25 rScr.image S_tail hSub
    (mapRev r29 enc29LocalRev) (enc29Dyn v rQrom rScr hScr hdisj) e3 hClean hMid
attribute [irreducible] enc29Dyn withMono29Dyn

/-! ## Section 4: `25`-Scratch `(88 + 2 * R + 2 * G)`-`T` Loader & Keep-9 `418-T` Packages -/
theorem reg29_ne_qrom_ge5 {N sScr : ℕ} (rQrom : QRegister (aliasQromBits 5 128 9 0) N)
    (rScr : QRegister sScr N) (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr)
    (j : Fin 29) (m : Fin (aliasQromBits 5 128 9 0)) (hm : 5 ≤ m.val) :
    mkReg29 rQrom rScr hScr hdisj j ≠ rQrom m := by
  by_cases hj : j.val < 5
  · rw [mkReg29_lt5 rQrom rScr hScr hdisj j hj]
    intro hEq
    have hv := congrArg Fin.val (rQrom.wires.injective hEq)
    dsimp only [QRegister.slice, QRegister.compose_apply, QRegister.block_apply_val] at hv
    omega
  · rw [mkReg29_ge5 rQrom rScr hScr hdisj j hj]
    exact ((hdisj.compose_right _).ne m ⟨j.val - 5, by omega⟩).symm

/-- Build `Mid29Layout N` from `(rQrom, rScr)` using `mkReg29.compose mono29LocalReg`
and `rScr 24` as `wG`. -/
def mkMid29 {N sScr : ℕ} (rQrom : QRegister (aliasQromBits 5 128 9 0) N)
    (rScr : QRegister sScr N) (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) :
    Mid29Layout N where
  rHot := rQrom.slice 5 128 (by decide)
  rMono := (mkReg29 rQrom rScr hScr hdisj).compose mono29LocalReg
  wG := rScr ⟨24, by omega⟩
  rOut := rQrom.slice 133 14 (by decide)
  hHotMono c u := (reg29_ne_qrom_ge5 rQrom rScr hScr hdisj (mono29LocalReg u)
    (QRegister.block 5 128 (by decide) c) (by
      rw [QRegister.block_apply_val]
      omega)).symm
  hHotG c := (hdisj.compose_left _).ne c ⟨24, by omega⟩
  hMonoG u := reg29_ne_wG rQrom rScr hScr hdisj (mono29LocalReg u)
  hGOut k := ((hdisj.compose_left _).ne k ⟨24, by omega⟩).symm
  hHotOut c k :=
    (rQrom.slice_disjoint_of_le 5 128 133 14 (by decide) (by decide) (by omega)).ne c k
  hMonoOut u k := reg29_ne_qrom_ge5 rQrom rScr hScr hdisj (mono29LocalReg u)
    (QRegister.block 133 14 (by decide) k) (by
      rw [QRegister.block_apply_val]
      omega)

/-- Parametric `(88 + 2 * R + 2 * G)`-`T`, `25`-scratch (`0 TOFF`) H-gadget QROM loader. -/
def qromHGadgetSymp14Low25FromHot128LoadDyn {Var : Type} {R G N sScr : ℕ}
    (v : Var) (P : HGadgetSymp14Plan R G)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) : DynamicCircuit Var N :=
  let M := mkMid29 rQrom rScr hScr hdisj
  .seq (.circuit (hPreC M.rOut 14 le_rfl))
    (.seq (withMono29Dyn v rQrom rScr hScr hdisj (mid29Dyn v P M))
      (.circuit (hRevC M.rOut 14 le_rfl)))
@[simp] theorem count_qromHGadgetSymp14Low25FromHot128LoadDyn_toff
    {Var : Type} {R G N sScr : ℕ} (v : Var) (P : HGadgetSymp14Plan R G)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) :
    (qromHGadgetSymp14Low25FromHot128LoadDyn v P rQrom rScr hScr hdisj).count .TOFF = 0 := by
  simp [qromHGadgetSymp14Low25FromHot128LoadDyn, DynamicCircuit.count]
@[simp] theorem count_qromHGadgetSymp14Low25FromHot128LoadDyn_t
    {Var : Type} {R G N sScr : ℕ} (v : Var) (P : HGadgetSymp14Plan R G)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) :
    (qromHGadgetSymp14Low25FromHot128LoadDyn v P rQrom rScr hScr hdisj).count .T =
      88 + 2 * R + 2 * G := by
  simp only [qromHGadgetSymp14Low25FromHot128LoadDyn, DynamicCircuit.count, count_hRevCirc_t,
    count_hPreCirc_t, count_withMono29Dyn_t, count_mid29Dyn_t]
  omega
theorem cleanPredRealizes_qromHGadgetSymp14Low25FromHot128LoadDyn
    {Var : Type} [Fintype Var] [DecidableEq Var] {R G N sScr : ℕ}
    (v : Var) (P : HGadgetSymp14Plan R G)
    (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N)
    (hScr : 25 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) :
    CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj rScr.image
        (oneHotPred (rQrom.slice 5 128 (by decide))))
      (rQrom.embedUnitary
        (aliasTableXorUnitary (5 + 128) 14 (hotLinearTargetFn 5 128 14 P.targetBoolTable)))
      (qromHGadgetSymp14Low25FromHot128LoadDyn v P rQrom rScr hScr hdisj) := by
  let rIdx := rQrom.slice 0 5 (by decide)
  let rScr24 := rScr.slice 0 24 (by omega)
  let r29 := mkReg29 rQrom rScr hScr hdisj
  let pEnc := mapRev r29 enc29LocalRev
  let M := mkMid29 rQrom rScr hScr hdisj
  let S_tail : Finset (Wire N) := rScr.image \ rScr24.image
  have hQromScr := disjoint_image_of_disjointWires hdisj
  have hwS : M.wG ∈ S_tail := by
    refine Finset.mem_sdiff.mpr ⟨(rScr.mem_image M.wG).mpr ⟨⟨24, by omega⟩, rfl⟩, fun hm ↦ ?_⟩
    obtain ⟨k, hk⟩ := (rScr24.mem_image M.wG).mp hm
    have hv := congrArg Fin.val (rScr.wires.injective hk)
    dsimp only [rScr24, QRegister.slice, QRegister.compose_apply, QRegister.block_apply_val] at hv
    have := k.isLt
    omega
  have hDisjOutScr : Disjoint M.rOut.image rScr.image :=
    Disjoint.mono_left (rQrom.image_compose_subset _) hQromScr
  have hMonoWp := wpZeroSet_withMono29Dyn v rQrom rScr hScr hdisj
    (wpZeroSet_mid29Dyn v P M S_tail hwS)
  set D := diagKetUnitary (fun β ↦ rMid29P P M (pEnc.fwdBits β))
  have hSeq1 := WpZeroSet.seq_diag_left hMonoWp
    (WpZeroSet.of_circuit v rScr.image (hRevC M.rOut 14 le_rfl) (by simp))
  have hFullWp := wpZero_seq_circ (hPreC M.rOut 14 le_rfl) (by simp)
    (zProj_comm_hPre M.rOut hDisjOutScr 14 le_rfl) hSeq1
  set G_full : Unitary (2 ^ N) :=
    (hRevC M.rOut 14 le_rfl).eval * D * (hPreC M.rOut 14 le_rfl).eval
  have hOutNot29 (j : Fin 14) : M.rOut j ∉ Set.range r29.wires := by
    rintro ⟨i, hi⟩
    exact reg29_ne_qrom_ge5 rQrom rScr hScr hdisj i (QRegister.block 133 14 (by decide) j)
      (by
        rw [QRegister.block_apply_val]
        omega) hi
  have hEncUpdOut (j : Fin 14) (β : BitAssignment N) (b : ZMod 2) :
      pEnc.fwdBits (update β (M.rOut j) b) = update (pEnc.fwdBits β) (M.rOut j) b := by
    have hInEq : (fun k ↦ update β (M.rOut j) b (r29 k)) = fun k ↦ β (r29 k) :=
      funext fun k ↦ update_of_ne (fun h ↦ hOutNot29 j ⟨k, h⟩) b β
    funext w
    by_cases hw : w ∈ Set.range r29.wires
    · obtain ⟨i, rfl⟩ := hw
      have hne : r29 i ≠ M.rOut j := fun h ↦ hOutNot29 j ⟨i, h⟩
      rw [(mapRev_spec r29 enc29LocalRev _).2.1 i, hInEq, update_of_ne hne,
        (mapRev_spec r29 enc29LocalRev β).2.1 i]
    · rw [(mapRev_spec r29 enc29LocalRev _).2.2 w hw]
      by_cases hwo : w = M.rOut j
      · subst hwo
        simp [update_self]
      · rw [update_of_ne hwo, update_of_ne hwo, (mapRev_spec r29 enc29LocalRev β).2.2 w hw]
  let wordFull (β : BitAssignment N) : Fin 14 → Bool := rMid29W P M (pEnc.fwdBits β)
  let φFull (β : BitAssignment N) : ZMod 2 := rDel29S2 P M (pEnc.fwdBits β)
  have hWordOut (j : Fin 14) (β : BitAssignment N) (b : ZMod 2) :
      rMid29W P M (update β (M.rOut j) b) = rMid29W P M β :=
    rawMid29Word_upd P M (fun c ↦ M.hHotOut c j) (fun u ↦ M.hMonoOut u j) β b
  have hPhiOut (j : Fin 14) (β : BitAssignment N) (b : ZMod 2) :
      rDel29S2 P M (update β (M.rOut j) b) = rDel29S2 P M β := by
    unfold rDel29S2
    refine congrArg₂ (· + ·) ?_ ?_
    · suffices ∀ n hn, rCarry29P P M (update β (M.rOut j) b) n hn =
          rCarry29P P M β n hn from this G le_rfl
      intro n hn
      induction n with
      | zero => rfl
      | succ _ ihm =>
          simp only [rCarry29P, ihm (Nat.le_of_succ_le hn), rgCarry29,
            v29_upd M (fun c ↦ M.hHotOut c j) (fun u ↦ M.hMonoOut u j)]
    · simp only [rFix29P, update_of_ne (M.hHotOut _ j), update_of_ne (M.hMonoOut _ j)]
  have hDK (δ : BitAssignment N) : D.1.mulVec (XMeasCircuit.ket δ) =
      bitSign (φFull δ + ∑ k : Fin 14, δ (M.rOut k) * b2z (wordFull δ k)) • XMeasCircuit.ket δ := by
    dsimp only [D]
    rw [ket_sdk_eq δ, diagKetUnitary_mulVec_ket, ← ket_sdk_eq δ]
    refine congrArg (· • XMeasCircuit.ket δ) (congrArg bitSign ?_)
    dsimp only [rMid29P, φFull, wordFull]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun k _ ↦ ?_)
    rw [(mapRev_spec r29 enc29LocalRev δ).2.2 (M.rOut k) (hOutNot29 k)]
  have hGK (β : BitAssignment N) : G_full.1.mulVec (XMeasCircuit.ket β) =
      bitSign (φFull β) •
        XMeasCircuit.ket (writeReg β M.rOut (fun k ↦ β (M.rOut k) + b2z (wordFull β k))) := by
    have hK := ket_hSand_diag M.rOut D wordFull φFull
      (fun j δ b ↦ (congrArg (rMid29W P M) (hEncUpdOut j δ b)).trans (hWordOut j _ b))
      (fun j δ b ↦ (congrArg (rDel29S2 P M) (hEncUpdOut j δ b)).trans (hPhiOut j _ b))
      hDK 14 le_rfl β
    rwa [remPhase_14, xorPrefAssign_14] at hK
  let F_lin := hotLinearTargetFn 5 128 14 P.targetBoolTable
  let U_q := rQrom.embedUnitary (aliasTableXorUnitary (5 + 128) 14 F_lin)
  let Q := Mobius126OneHot.cleanPredProj rScr.image (oneHotPred M.rHot)
  have hPresU : PreservesWires U_q.1 (rScr.image ∪ M.rHot.image) := by
    intro i j ⟨w, hw, hne⟩
    have hketU : U_q.1 i j = (U_q.1 *ᵥ CoherentAlias.ket (basisBits N j)) i := by
      simp [CoherentAlias.ket, basisState]
    rw [hketU]
    dsimp only [U_q]
    rw [aliasTableXorUnitary, embedUnitary_bitPermUnitary_mulVec_ket]
    dsimp only [Equiv.coe_fn_mk]
    have hSame : writeReg (basisBits N j) rQrom (aliasTableXorBits (5 + 128) 14 F_lin
        (fun m ↦ basisBits N j (rQrom m))) w = basisBits N j w := by
      rcases Finset.mem_union.mp hw with hwS0 | hwH
      · obtain ⟨s, rfl⟩ := (rScr.mem_image w).mp hwS0
        exact writeReg_apply_of_not_mem _ _ _ _ fun ⟨m, hm⟩ ↦ hdisj.ne m s hm
      · obtain ⟨c, rfl⟩ := (M.rHot.mem_image w).mp hwH
        have hcEq : M.rHot c = rQrom ⟨5 + c.val,
            Nat.lt_of_lt_of_le (Nat.add_lt_add_left c.isLt 5) (by decide)⟩ := rfl
        rw [hcEq, writeReg_apply_reg]
        simp [aliasTableXorBits, show ¬(5 + 128 ≤ 5 + c.val) by omega]
    simp only [CoherentAlias.ket, basisState, Pi.single_apply]
    refine ite_eq_right fun heq ↦ hne ?_
    rw [heq, basisBits_symm]
    exact hSame
  have hCommS : zeroProjOn rScr.image * U_q.1ᴴ = U_q.1ᴴ * zeroProjOn rScr.image := by
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using
      congrArg (·ᴴ) (preservesWires_comm_zeroProjOn hPresU Finset.subset_union_left)
  have hCommP : predProj (oneHotPred M.rHot) * U_q.1ᴴ = U_q.1ᴴ * predProj (oneHotPred M.rHot) := by
    have hc := preservesWires_comm_predProj hPresU (P := oneHotPred M.rHot) fun α β h ↦ by
      have hH (c : Fin 128) := h _ (Finset.mem_union_right _ ((M.rHot.mem_image _).mpr ⟨c, rfl⟩))
      unfold oneHotPred
      exact decide_eq_decide.mpr
        ⟨fun ⟨rc, hrc⟩ ↦ ⟨rc, fun c ↦ (hH c).symm.trans (hrc c)⟩,
         fun ⟨rc, hrc⟩ ↦ ⟨rc, fun c ↦ (hH c).trans (hrc c)⟩⟩
    simpa only [conjTranspose_mul, predProj_conjTranspose] using congrArg (·ᴴ) hc
  have hCommQ : Q * U_q.1ᴴ = U_q.1ᴴ * Q := by
    dsimp only [Q, Mobius126OneHot.cleanPredProj]
    rw [Matrix.mul_assoc, hCommP, ← Matrix.mul_assoc, hCommS, Matrix.mul_assoc]
  have hMat : G_full.1 * Q = U_q.1 * Q := by
    refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
    dsimp only [Q, Mobius126OneHot.cleanPredProj]
    rw [ket_sdk_eq β]
    simp only [← mulVec_mulVec, predProj_mulVec_ket]
    by_cases hOh : oneHotPred M.rHot β = true
    · simp only [hOh, ↓reduceIte, zeroProjOn_mulVec_ket]
      rw [← ket_sdk_eq β]
      by_cases hS0 : ∀ w ∈ rScr.image, β w = 0
      · rw [ite_eq_left hS0]
        unfold oneHotPred at hOh
        obtain ⟨rc, hrc⟩ := of_decide_eq_true hOh
        let x : Fin (2 ^ 5) := (basisBits 5).symm (fun i ↦ β (rIdx i))
        have hxBits : basisBits 5 x = fun i ↦ β (rIdx i) := basisBits_symm _
        have hIn29 : (fun i : Fin 29 ↦ β (r29 i)) = in29 x := by
          funext i
          dsimp only [in29, r29]
          by_cases hi : i.val < 5
          · simp only [hi, ↓reduceDIte]
            rw [mkReg29_lt5 rQrom rScr hScr hdisj i hi]
            exact (congrFun hxBits ⟨i.val, hi⟩).symm
          · simp only [hi, ↓reduceDIte]
            rw [mkReg29_ge5 rQrom rScr hScr hdisj i hi]
            exact hS0 _ (rScr.image_compose_subset _
              ((rScr24.mem_image _).mpr ⟨⟨i.val - 5, by omega⟩, rfl⟩))
        set γ := pEnc.fwdBits β
        have hγHot (c : Fin 128) : γ (M.rHot c) = if c = rc then 1 else 0 := by
          have hn : M.rHot c ∉ Set.range r29.wires := fun ⟨i, hi⟩ ↦
            reg29_ne_qrom_ge5 rQrom rScr hScr hdisj i (QRegister.block 5 128 (by decide) c)
              (by
                rw [QRegister.block_apply_val]
                omega) hi
          change pEnc.fwdBits β (M.rHot c) = _
          rw [(mapRev_spec r29 enc29LocalRev β).2.2 (M.rHot c) hn, hrc c]
        have hγMono (u : Fin 29) :
            γ (M.rMono u) = monoEval 5 (basisBits 5 x) ⟨u.val + 1, by omega⟩ := by
          change pEnc.fwdBits β (r29 (mono29LocalReg u)) = _
          rw [(mapRev_spec r29 enc29LocalRev β).2.1 (mono29LocalReg u), hIn29, enc29_mono_fwd]
        have hEnvNoHi {y : Var157} (hy : NoHi29 y) : vEnv29 M γ y = idEnv rc x y := by
          rcases y with j | u
          · dsimp only [vEnv29, vWire29, idEnv]
            rw [hγHot ⟨j.val, by omega⟩]
            by_cases hj : j.val = rc.val
            · simp [hj, z2b]
            · simp [hj, show (⟨j.val, by omega⟩ : Fin 128) ≠ rc from
                fun h ↦ hj (congrArg Fin.val h), z2b]
          · have hu29 : u.val < 29 := hy
            dsimp only [vEnv29, vWire29, idEnv]
            simp only [hu29, ↓reduceDIte]
            rw [hγMono ⟨u.val, hu29⟩]
        have hCarryEq : rCarry29P P M γ G le_rfl = totPhi P rc x := by
          have hEqG (g : Fin G) : rgCarry29 P g M γ = idCarry P g rc x := by
            dsimp only [rgCarry29, idCarry]
            have hl := noHi29_lempelSch P g
            rw [evalHGad_eq_of_mem (fun st hst y hy ↦ hEnvNoHi (hl.1 st hst y hy))
              (fun st hst y hy ↦ hEnvNoHi (hl.2.1 st hst y hy))
              (fun y hy ↦ hEnvNoHi (hl.2.2 y hy))]
          suffices ∀ n hn, rCarry29P P M γ n hn =
              ∑ i : Fin n, b2z (idCarry P ⟨i.val, i.isLt.trans_le hn⟩ rc x) from this G le_rfl
          intro n hn
          induction n with
          | zero => rfl
          | succ n ihm =>
              rw [rCarry29P, ihm (Nat.le_of_succ_le hn), hEqG ⟨n, hn⟩, Fin.sum_univ_castSucc]
              rfl
        have hFixEq : rFix29P M (totPhi P) γ = totPhi P rc x := by
          dsimp only [rFix29P]
          rw [Finset.sum_eq_single rc (fun c _ hc ↦ by simp [hγHot c, hc])
              (fun h ↦ False.elim (h (Finset.mem_univ rc))),
            Finset.sum_eq_single rc (fun c _ hc ↦ by simp [hγHot c, hc])
              (fun h ↦ False.elim (h (Finset.mem_univ rc))),
            Finset.sum_eq_single rc (fun c _ hc ↦ by simp [hγHot c, hc])
              (fun h ↦ False.elim (h (Finset.mem_univ rc)))]
          rw [hγHot rc, ite_eq_left rfl, one_mul, mul_one, mul_one]
          simp_rw [hγMono]
          rw [(monoEval5_30_31 x).1, (monoEval5_30_31 x).2]
          have hDecomp := anf5_decomp (totPhi P rc) x
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hDecomp
          dsimp only [Fin.val_castSucc, Fin.val_last] at hDecomp
          linear_combination hDecomp
        have hPhiZero : φFull β = 0 := by
          change rCarry29P P M γ G le_rfl + rFix29P M (totPhi P) γ = 0
          rw [hCarryEq, hFixEq, CharTwo.add_self_eq_zero]
        have hWordEq : wordFull β = P.targetBoolTable rc x := by
          funext k
          change xor (rGrps29P P k M γ G le_rfl) (rDiag29B P k M γ) = P.targetBoolTable rc x k
          dsimp only [HGadgetSymp14Plan.targetBoolTable]
          have hGPref : ∀ n hn, rGrps29P P k M γ n hn = P.prefBool k rc x n hn := by
            intro n hn
            induction n with
            | zero => rfl
            | succ n ihm =>
                have hp := noHi29_affPairs P ⟨n, hn⟩
                have hBit : rgBit29 P ⟨n, hn⟩ M γ = P.grpBit ⟨n, hn⟩ rc x :=
                  xorPairs_eq_of_mem fun p hmem ↦
                    ⟨fun y hy ↦ hEnvNoHi ((hp p hmem).1 y hy),
                     fun y hy ↦ hEnvNoHi ((hp p hmem).2 y hy)⟩
                simp only [rGrps29P, HGadgetSymp14Plan.prefBool, ihm (Nat.le_of_succ_le hn), hBit]
          have hDiag : rDiag29B P k M γ = xor
              (if h : rc.val < 126 then P.rowDiag k ⟨rc.val, h⟩ else false)
              (extCol24Bool (P.colDiag k) x) := by
            dsimp only [rDiag29B]
            rw [evStep_eq_of_mem (fun y hy ↦ hEnvNoHi (noHi29_rcColAff _ _ hy)), evalStep_rcColAff]
          rw [hGPref G le_rfl, hDiag]
        rw [hGK β, hPhiZero, bitSign_zero2, one_smul]
        have hketC (δ : BitAssignment N) : XMeasCircuit.ket δ = CoherentAlias.ket δ := rfl
        dsimp only [U_q]
        rw [hketC β, aliasTableXorUnitary, embedUnitary_bitPermUnitary_mulVec_ket, ← hketC]
        dsimp only [Equiv.coe_fn_mk]
        let cHot : Fin (2 ^ 128) := (basisBits 128).symm (fun c ↦ β (M.rHot c))
        have hcHot (c : Fin 128) : basisBits 128 cHot c = if c = rc then 1 else 0 := by
          rw [congrFun (basisBits_symm _) c, hrc c]
        have hAddrEq : (basisBits (5 + 128)).symm
            (fun i : Fin (5 + 128) ↦ β (rQrom ⟨i.val, i.isLt.trans_le (by decide)⟩)) =
            combineAddr x cHot := by
          dsimp only [combineAddr]
          apply congrArg (basisBits (5 + 128)).symm
          funext i
          by_cases hi5 : i.val < 5
          · simp only [hi5, ↓reduceDIte]
            rw [congrFun hxBits ⟨i.val, hi5⟩]
            exact congrArg β (congrArg rQrom.wires (Fin.ext (Nat.zero_add i.val).symm))
          · simp only [hi5, ↓reduceDIte]
            rw [congrFun (basisBits_symm (fun c ↦ β (M.rHot c))) _]
            exact congrArg β (congrArg rQrom.wires
              (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hi5)).symm))
        have hFn := hotLinearTargetFn_combineAddr_oneHot P.targetBoolTable x rc cHot hcHot
        apply congrArg XMeasCircuit.ket
        funext w
        by_cases hwQ : w ∈ Set.range rQrom.wires
        · obtain ⟨m, rfl⟩ := hwQ
          rw [writeReg_apply_reg]
          change _ = aliasTableXorBits (5 + 128) 14 F_lin (fun q ↦ β (rQrom q)) m
          dsimp only [aliasTableXorBits]
          by_cases hm : 5 + 128 ≤ m.val
          · have hk14 : m.val - 133 < 14 := by
              have := m.isLt
              dsimp [aliasQromBits, aliasOutBits] at this
              omega
            let k : Fin 14 := ⟨m.val - 133, hk14⟩
            have hmOut : rQrom m = M.rOut k :=
              congrArg rQrom.wires (Fin.ext (Nat.add_sub_of_le hm).symm)
            have hkEq : (⟨m.val - (5 + 128), by omega⟩ : Fin 14) = k := Fin.ext rfl
            simp only [hm, ↓reduceDIte, F_lin]
            rw [hmOut, writeReg_apply_reg, hWordEq, hAddrEq, hFn, hkEq]
            rfl
          · have hnotOut : rQrom m ∉ Set.range M.rOut.wires := by
              rintro ⟨k, hk'⟩
              change rQrom (QRegister.block 133 14 (by decide) k) = rQrom m at hk'
              have hv := congrArg Fin.val (rQrom.wires.injective hk')
              rw [QRegister.block_apply_val] at hv
              omega
            rw [writeReg_apply_of_not_mem _ M.rOut _ _ hnotOut]
            simp [hm]
        · have hnotOut : w ∉ Set.range M.rOut.wires :=
            fun ⟨k, hk'⟩ ↦ hwQ ⟨QRegister.block 133 14 (by decide) k, hk'⟩
          rw [writeReg_apply_of_not_mem _ M.rOut _ _ hnotOut,
            writeReg_apply_of_not_mem _ rQrom _ _ hwQ]
      · rw [ite_eq_right hS0, mulVec_zero, mulVec_zero]
    · simp [hOh]
  dsimp only [qromHGadgetSymp14Low25FromHot128LoadDyn]
  refine ⟨hFullWp.1, hCommQ, hFullWp.2.1, fun Θ hΘ σ ↦ ?_⟩
  have hQH : Qᴴ = Q := cleanPredProj_conjTranspose rScr.image (oneHotPred M.rHot)
  have hQMat : Q * G_full.1ᴴ = Q * U_q.1ᴴ := by
    simpa only [conjTranspose_mul, hQH] using congrArg (·ᴴ) hMat
  have hWpS := congrArg (fun A : Store Var → Observable (Fin (2 ^ N)) ↦
    (A σ).1.conj (predProj (oneHotPred M.rHot))) (hFullWp.2.2 Θ hΘ)
  rw [SelectSwapQROM.restrictZeroSet_coe, SelectSwapQROM.restrictZeroSet_coe, conj_conj,
    conj_conj, predProj_mul_zeroProjOn_eq_cleanPredProj] at hWpS
  change ((wp _ Θ σ).1).conj Q = ((qcWpQAssign G_full Θ σ).1).conj Q at hWpS
  refine hWpS.trans ?_
  change ((qcWpQAssign G_full Θ σ).1).conj Q = ((qcWpQAssign U_q Θ σ).1).conj Q
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    star_eq_conjTranspose, conj_conj, hQMat]
attribute [irreducible] qromHGadgetSymp14Low25FromHot128LoadDyn

end Inner18Bound322HGadgetQrom

section DotNotationBridges
open Inner18Bound322HGadgetQrom

/-- Build `{Var : Type}`-computable `OneHot14LoadCirc2` (`88 + 2 * R + 2 * G` `T`, `25` scratch)
from any `HGadgetSymp14Plan R G`. -/
def Inner18HadWSuperLegsA.OneHot14LoadCirc2.ofHGadgetPlanLow25
    (Var : Type) {R G : ℕ} (P : HGadgetSymp14Plan R G) :
    OneHot14LoadCirc2 Var 25 (88 + 2 * R + 2 * G) where
  loadDyn v rQrom rScr hs hdisj := qromHGadgetSymp14Low25FromHot128LoadDyn v P rQrom rScr hs hdisj
  count_toff v rQrom rScr hs h :=
    count_qromHGadgetSymp14Low25FromHot128LoadDyn_toff v P rQrom rScr hs h
  count_t v rQrom rScr hs h :=
    count_qromHGadgetSymp14Low25FromHot128LoadDyn_t v P rQrom rScr hs h

/-- Build certified `OneHot14LoadBundle_3` (`88 + 2 * R + 2 * G` `T`, `25` scratch) from any
`HGadgetSymp14Plan` whose `targetBoolTable` equals `boolTbl`. -/
def Inner18HadWSuperLegsA.OneHot14LoadBundle_3.ofHGadgetPlanLow25
    (Var : Type) [Fintype Var] [DecidableEq Var] {R G : ℕ} (P : HGadgetSymp14Plan R G)
    (boolTbl : Fin 128 → Fin (2 ^ 5) → Fin 14 → Bool) (hTbl : P.targetBoolTable = boolTbl) :
    OneHot14LoadBundle_3 Var 25 (88 + 2 * R + 2 * G) boolTbl where
  toOneHot14LoadCirc2 := OneHot14LoadCirc2.ofHGadgetPlanLow25 Var P
  clean2 v rQrom rScr hs hdisj := by
    rw [← hTbl]
    exact cleanPredRealizes_qromHGadgetSymp14Low25FromHot128LoadDyn v P rQrom rScr hs hdisj

/-- Build `{Var : Type}`-computable `OneHot14LoadCirc` (`88 + 2 * R + 2 * G` `T`, `25` scratch)
from any `HGadgetSymp14Plan R G`. -/
def Inner18Load.OneHot14LoadCirc.ofHGadgetPlanLow25
    (Var : Type) {R G : ℕ} (P : HGadgetSymp14Plan R G) :
    OneHot14LoadCirc Var 25 (88 + 2 * R + 2 * G) where
  loadDyn v rQrom rScr hs hdisj := qromHGadgetSymp14Low25FromHot128LoadDyn v P rQrom rScr hs hdisj
  count_toff v rQrom rScr hs h :=
    count_qromHGadgetSymp14Low25FromHot128LoadDyn_toff v P rQrom rScr hs h
  count_t v rQrom rScr hs h :=
    count_qromHGadgetSymp14Low25FromHot128LoadDyn_t v P rQrom rScr hs h

/-- Build certified `OneHot14LoadBundle2` (`88 + 2 * R + 2 * G` `T`, `25` scratch) from any
`HGadgetSymp14Plan` whose `targetBoolTable` equals `boolTbl`. -/
noncomputable def
    Inner18Load.OneHot14LoadBundle2.ofHGadgetPlanLow25
    (Var : Type) {R G : ℕ} (P : HGadgetSymp14Plan R G)
    (boolTbl : Fin 128 → Fin (2 ^ 5) → Fin 14 → Bool) (hTbl : P.targetBoolTable = boolTbl) :
    OneHot14LoadBundle2 Var 25 (88 + 2 * R + 2 * G) (hotLinearTargetFn 5 128 14 boolTbl)
      (fun rc x k ↦ if boolTbl rc x k then 1 else 0) :=
  OneHot14LoadBundle2.ofLinearClean (OneHot14LoadCirc.ofHGadgetPlanLow25 Var P) boolTbl
    fun v rQrom rScr hs hdisj ↦ by
      rw [← hTbl]
      exact cleanPredRealizes_qromHGadgetSymp14Low25FromHot128LoadDyn v P rQrom rScr hs hdisj

namespace Inner18Bound322HGadgetQrom

/-- Concrete `{Var : Type}`-computable `418-T` (`25` scratch, `R = 147`, `G = 18`) Keep-9
`OneHot14LoadCirc` backed by `optSymp14Plan`. -/
def keep9HGadgetLow25LoadCirc (Var : Type) : OneHot14LoadCirc Var 25 418 :=
  OneHot14LoadCirc.ofHGadgetPlanLow25 Var optSymp14Plan

/-- Concrete certified `418-T` (`25` scratch) Keep-9 `OneHot14LoadBundle2`. -/
noncomputable def keep9HGadgetLow25LoadBundle (Var : Type) :
    OneHot14LoadBundle2 Var 25 418 (hotLinearTargetFn 5 128 14 keep9Hot24BoolTable)
      keep9SliceTargetFn14 :=
  OneHot14LoadBundle2.ofKeep9LinearClean (keep9HGadgetLow25LoadCirc Var)
    fun v rQrom rScr hs hdisj ↦ by
      rw [← optSymp14Plan_targetBoolTable_eq]
      exact cleanPredRealizes_qromHGadgetSymp14Low25FromHot128LoadDyn
        v optSymp14Plan rQrom rScr hs hdisj

end Inner18Bound322HGadgetQrom

/-- Dot-notation `OneHot14LoadCirc.hgLow25` (`25` scratch, `418 T`). -/
def Inner18Load.OneHot14LoadCirc.hgLow25 (Var : Type) :
    OneHot14LoadCirc Var 25 418 :=
  keep9HGadgetLow25LoadCirc Var

/-- Dot-notation `OneHot14LoadBundle2.hgLow25` (`25` scratch, `418 T`). -/
noncomputable def Inner18Load.OneHot14LoadBundle2.hgLow25
    (Var : Type) : OneHot14LoadBundle2 Var 25 418
      (hotLinearTargetFn 5 128 14 keep9Hot24BoolTable) keep9SliceTargetFn14 :=
  keep9HGadgetLow25LoadBundle Var

/-- Dot-notation `OneHot14LoadCirc2.hgLow25` (`25` scratch, `418 T`). -/
def Inner18HadWSuperLegsA.OneHot14LoadCirc2.hgLow25
    (Var : Type) : OneHot14LoadCirc2 Var 25 418 :=
  OneHot14LoadCirc2.ofHGadgetPlanLow25 Var optSymp14Plan

/-- Dot-notation `OneHot14LoadBundle_3.hgLow25` (`25` scratch, `418 T`). -/
def Inner18HadWSuperLegsA.OneHot14LoadBundle_3.hgLow25
    (Var : Type) [Fintype Var] [DecidableEq Var] :
    OneHot14LoadBundle_3 Var 25 418 keep9Hot24BoolTable :=
  OneHot14LoadBundle_3.ofHGadgetPlanLow25 Var optSymp14Plan keep9Hot24BoolTable
    optSymp14Plan_targetBoolTable_eq

end DotNotationBridges

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
