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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HGadgetPrepOutCore

@[expose] public section

/-! # Hadamard-Gadget `wOuter = 8` `PREP_out` (`hGadgetPreSwap103Dyn`, `hGadgetLeaf94Dyn` & Outer)
`192-T` (`87`-scratch) pre-swap `hGadgetPreSwap103Dyn`, `152-T` (`82`-scratch) X-measurement
phase leaf `hGadgetLeaf94Dyn`, word-parametric `wOuter = 8` `PREP_out` (`268 + 3 * wordCountT`
forward / `228 + 3 * wordCountT` backward), and `wInner2`-polymorphic outer comb wrappers (Babbush
et
al., *Phys. Rev. X* **8**, 041015, 2018; Gidney, *Quantum* **2**, 74, 2018; Low, Kliuchnikov, and
Schaeffer, *Quantum* **8**, 1375, 2024, DOI: `10.22331/q-2024-06-17-1375`). -/
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetPrepOutOuter8
open QuantumComputation.Specs QuantumComputation.Specs.P450
section PrepOutOuter8Impl
open Operator QProg Matrix Circuit Real HermitianMat
open QuantumComputation QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
  Solution.BlockEncodingCore
open Solution.CoherentAlias hiding ket localIdx matrix_ext_ket
open Solution.MidReflCtxRetain (hotCtxPhaseLoop)
open Solution.StepAnfAndCoin14Core (count_hotCtxPhaseLoop_toff2
  count_hotCtxPhaseLoop_t2 ket_hotCtxPhaseLoop)
open Solution.HGadgetSympQrom Solution.OuterWeights.GroverUniform
open Solution.Comparators hiding ket bit_cases matrix_ext_ket zeroProjOn
  zeroProjOn_mulVec_ket zeroProjOn_conjTranspose ket_Z
open Solution.SelectSwapQROM Solution.StepOuter8Pi145L1
  Solution.ReordOuter13Bridge
  Solution.Pi145Fast2RotCore
  Solution.OptFactoredMag30AndCoin9
  Solution.Phase2MidSandwich
  Solution.MobiusOptSubcube163Walk
  Solution.CompactZeroCmp20OuterParam
  Solution.CompactStepZeroCmp20OuterParam
  Solution.Outer8Pi145Compact2RotOuter
open Solution.StepOuter8Pi145Outer hiding b2z
open Solution.Outer8Pi145Compact2RotDyn hiding b2z_xor b2z_and
open _root_.Function (update update_of_ne update_self update_idem update_eq_self)
open Solution.XMeasCircuit (xorWireUnitary xorWireUnitary_mulVec_ket phaseFlipUnitary
  phaseFlipUnitary_mulVec_ket xMeasUnloadWireDyn count_xMeasUnloadWireDyn_toff
  count_xMeasUnloadWireDyn_t)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowPrep12 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
theorem count_seq2 {Var : Type} {N a : ℕ} (p₁ p₂ : DynamicCircuit Var N)
    (g : PrimitiveGate a) : (p₁.seq p₂).count g = p₁.count g + p₂.count g := rfl
theorem localIdx_block_congr {N off w : ℕ} (h1 h2 : off + w ≤ N) {β₁ β₂ : BitAssignment N}
    (h : ∀ j : Fin w, β₁ ⟨off + j.val, by omega⟩ = β₂ ⟨off + j.val, by omega⟩) :
    localIdx (QRegister.block off w h1) β₁ = localIdx (QRegister.block off w h2) β₂ :=
  congrArg (basisBits w).symm (funext h)
theorem rFib_eq_cSlot {N cOff : ℕ} (h10 : cOff + 10 ≤ N) (h16 : cOff + 16 ≤ N)
    (f : Fin 10) : QRegister.block cOff 10 h10 f = cSlot cOff h16 ⟨f.val, by omega⟩ :=
  Fin.ext (by rw [qreg_block_apply])
theorem env56_eq_idEnv56 {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (γ : BitAssignment N) (g : Fin 46) (optF : Option (Fin 10))
    (hHot : ∀ i : Fin 46, γ (rHot i) = if i = g then 1 else 0)
    (hFib : ∀ f : Fin 10, γ (rFib f) = b2z (optF == some f)) :
    env56 rHot rFib γ = idEnv56 g optF := by
  funext u
  rcases u with i | f
  · dsimp only [env56, idEnv56]
    rw [hHot i]
    by_cases h : i = g
    · rw [ite_eq_left h, decide_eq_true h]
      decide
    · rw [ite_eq_right h, decide_eq_false h]
      decide
  · dsimp only [env56, idEnv56]
    rw [hFib f, z2b_b2z]
theorem quad5Bit_eq_of_env {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (M : Fin 46 → Fin 10 → Bool) (γ : BitAssignment N) (g : Fin 46) (optF : Option (Fin 10))
    (hEnv : env56 rHot rFib γ = idEnv56 g optF) :
    quad5Bit rHot rFib M γ = b2z (optF.elim false (M g)) := by
  dsimp only [quad5Bit]
  rw [hEnv, xorPairs_quad5_idEnv56]
  cases optF <;> rfl
theorem bit01_pair_lt4 (x0 x1 : ZMod 2) : bit01Nat x0 + 2 * bit01Nat x1 < 4 := by
  rcases bit_cases x0 with rfl | rfl <;> rcases bit_cases x1 with rfl | rfl <;> decide
theorem y_anf_lt184 (g : Fin 46) (x0 x1 : ZMod 2) :
    4 * g.val + (bit01Nat x0 + 2 * bit01Nat x1) < 184 := by
  have hg := g.isLt
  have hr := bit01_pair_lt4 x0 x1
  omega
theorem anf2_xor4_eval (R : Fin 4 → Bool) (x0 x1 : ZMod 2) :
    b2z (R 0) + x0 * b2z (xor (R 0) (R 1)) + x1 * b2z (xor (R 0) (R 2)) +
        (x0 * x1) * b2z (xor (xor (R 0) (R 1)) (xor (R 2) (R 3))) =
      b2z (R ⟨bit01Nat x0 + 2 * bit01Nat x1, bit01_pair_lt4 x0 x1⟩) := by
  refine Eq.trans (b := b2z (R 0) + x0 * (b2z (R 0) + b2z (R 1)) + x1 * (b2z (R 0) + b2z (R 2)) +
      (x0 * x1) * (b2z (R 0) + b2z (R 1) + b2z (R 2) + b2z (R 3))) (by
    simp only [b2z_xor]
    ring) (anf2_eval_zmod2 (fun r ↦ b2z (R r)) x0 x1)
theorem block_ne_of_ge {N off len : ℕ} (h : off + len ≤ N) (w : Wire N) (hw : off + len ≤ w.val)
    (i : Fin len) : QRegister.block off len h i ≠ w := fun e ↦ by
  have hv := congrArg Fin.val e
  rw [qreg_block_apply] at hv
  dsimp only at hv
  omega
theorem block_ne_block {N o1 l1 o2 l2 : ℕ} (h1 : o1 + l1 ≤ N) (h2 : o2 + l2 ≤ N)
    (hd : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (i : Fin l1) (j : Fin l2) :
    QRegister.block o1 l1 h1 i ≠ QRegister.block o2 l2 h2 j := fun e ↦ by
  have hv := congrArg Fin.val e
  rw [qreg_block_apply, qreg_block_apply] at hv
  dsimp only at hv
  omega
theorem not_mem_block {N off len : ℕ} (h : off + len ≤ N) (w : Wire N)
    (hw : w.val < off ∨ off + len ≤ w.val) : w ∉ (QRegister.block off len h).image := fun hm ↦ by
  obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
  have hv := congrArg Fin.val hj
  rw [qreg_block_apply] at hv
  dsimp only at hv
  omega
theorem hotFibRouter_spec {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (off cOff s46 sScr : ℕ) (hcOff : off + 50 = cOff) (hs46 : off + 46 = s46)
    (h12 : 12 ≤ off) (hs : 77 ≤ sScr) (hScrN : off + sScr ≤ N) (hN : off + sScr = N)
    (v : Var) (pRt : GroupUnary.RevCompute N)
    (hpRt : pRt = (wHot46Rev off h12 (by omega)).seq (cFib11Rev cOff (by omega) (by omega)))
    (S0 : BitAssignment N → Bool)
    (hScr0 : ∀ β, S0 β = true → ∀ j : Fin sScr, β (QRegister.block off sScr hScrN j) = 0) :
    let S1 : BitAssignment N → Bool := fun γ ↦ S0 (pRt.invBits γ)
    let rHot : QRegister 46 N := QRegister.block off 46 (by omega)
    let rFib : QRegister 10 N := QRegister.block cOff 10 (by omega)
    TransRealizes v S0 S1 pRt.toCircuit.eval (.seq (wHot46FwdDyn v off h12 (by omega))
        (cFib11FwdDyn v cOff (by omega) (by omega))) ∧
    TransRealizes v S1 S0 pRt.toCircuit.eval⁻¹ (Lac2Folded184Select.revUncomputeDyn v pRt) ∧
    (∀ γ1 : BitAssignment N, S1 γ1 = true → ∀ k : ℕ, off + 66 ≤ k → (hk : k < N) → γ1 ⟨k, hk⟩ = 0) ∧
    ∀ β : BitAssignment N, S0 β = true →
      let γ1 := pRt.fwdBits β
      let g := DyadicXMeasPrepOut13.effGroup
        ((localIdx (QRegister.block 0 8 (by omega)) β).val / 4)
      let c := localIdx (QRegister.block 8 4 (by omega)) β
      (∀ w : Wire N, w.val < off → γ1 w = β w) ∧
      γ1 ⟨s46, by omega⟩ = β ⟨0, by omega⟩ * β ⟨1, by omega⟩ ∧
      (∀ i : Fin 46, γ1 (rHot i) = if i = g then 1 else 0) ∧
      (∀ f : Fin 10, γ1 (rFib f) = b2z (coinOptFib c == some f)) ∧
      env56 rHot rFib γ1 = idEnv56 g (coinOptFib c) := by
  subst hcOff
  subst hs46
  cases hpRt
  let pHot := wHot46Rev (N := N) off h12 (by omega)
  let pFib := cFib11Rev (N := N) (off + 50) (by omega) (by omega)
  let pRt0 := pHot.seq pFib
  let rHot : QRegister 46 N := QRegister.block off 46 (by omega)
  let rFib : QRegister 10 N := QRegister.block (off + 50) 10 (by omega)
  obtain ⟨eHot, hHotSpec⟩ := wHot46_equiv_and_spec v off h12 (by omega) S0 fun β hS j ↦ by
    have hj : (⟨off + j.val, by omega⟩ : Wire N) =
        QRegister.block off sScr hScrN ⟨j.val, by omega⟩ := Fin.ext (by rw [qreg_block_apply])
    exact hj ▸ hScr0 β hS ⟨j.val, by omega⟩
  have hFibClean (γ : BitAssignment N) (hγ : S0 (pHot.invBits γ) = true) (s : Fin 16) :
      γ (cSlot (off + 50) (by omega) s) = 0 := by
    have h1 := (hHotSpec (pHot.invBits γ) hγ).1 (cSlot (off + 50) (by omega) s) (Or.inr (by
      dsimp only [cSlot]
      omega))
    rw [pHot.fwdBits_invBits] at h1
    have hw : cSlot (off + 50) (by omega) s =
        QRegister.block off sScr hScrN ⟨50 + s.val, by omega⟩ := Fin.ext (by
      rw [qreg_block_apply]
      dsimp only [cSlot]
      omega)
    exact h1.trans (hw ▸ hScr0 (pHot.invBits γ) hγ ⟨50 + s.val, by omega⟩)
  obtain ⟨eFib, hFibSpec⟩ := cFib11_equiv_and_spec v (off + 50) (by omega) (by omega)
    (fun γ ↦ S0 (pHot.invBits γ)) hFibClean
  obtain ⟨hvRt, _, htrRtB, hfwdRt⟩ := eHot.seq eFib
  have hCl (γ1 : BitAssignment N) (h1 : S0 (pRt0.invBits γ1) = true) (k : ℕ)
      (hk1 : off + 66 ≤ k) (hk2 : k < N) : γ1 ⟨k, hk2⟩ = 0 := by
    let β := pRt0.invBits γ1
    have hFibS : S0 (pHot.invBits (pHot.fwdBits β)) = true := by rwa [pHot.invBits_fwdBits]
    have hγ1 : γ1 = pFib.fwdBits (pHot.fwdBits β) := (pRt0.fwdBits_invBits γ1).symm
    have hw : (⟨k, hk2⟩ : Wire N) = QRegister.block off sScr hScrN ⟨k - off, by omega⟩ :=
      Fin.ext (by
        rw [qreg_block_apply]
        dsimp only
        omega)
    rw [hγ1,
      (hFibSpec (pHot.fwdBits β) hFibS).1 ⟨k, hk2⟩ (Or.inr (show (off + 50) + 16 ≤ k by omega)),
      (hHotSpec β h1).1 ⟨k, hk2⟩ (Or.inr (show off + 50 ≤ k by omega)), hw]
    exact hScr0 β h1 ⟨k - off, by omega⟩
  refine ⟨htrRtB.to_transRealizes_revCompute pRt0 hfwdRt,
    TransRealizes.uncomputeDyn v pRt0 S0 hvRt, hCl, fun β hS0 ↦ ?_⟩
  have hFibS : S0 (pHot.invBits (pHot.fwdBits β)) = true := by rwa [pHot.invBits_fwdBits]
  let g := DyadicXMeasPrepOut13.effGroup ((localIdx (QRegister.block 0 8 (by omega)) β).val / 4)
  let c := localIdx (QRegister.block 8 4 (by omega)) β
  have hOut (w : Wire N) (hw : w.val < off) : pRt0.fwdBits β w = β w :=
    ((hFibSpec (pHot.fwdBits β) hFibS).1 w (Or.inl (by omega))).trans
      ((hHotSpec β hS0).1 w (Or.inl hw))
  have h46 : pRt0.fwdBits β ⟨off + 46, by omega⟩ = β ⟨0, by omega⟩ * β ⟨1, by omega⟩ :=
    ((hFibSpec (pHot.fwdBits β) hFibS).1 ⟨off + 46, by omega⟩
      (Or.inl (show off + 46 < off + 50 by omega))).trans (hHotSpec β hS0).2.1
  have hrHot (i : Fin 46) : rHot i = ⟨off + i.val, by omega⟩ := Fin.ext (by
    dsimp only [rHot]
    rw [qreg_block_apply])
  have hHot1 (i : Fin 46) : pRt0.fwdBits β (rHot i) = if i = g then 1 else 0 := by
    rw [hrHot i]
    exact ((hFibSpec (pHot.fwdBits β) hFibS).1 ⟨off + i.val, by omega⟩
      (Or.inl (show off + i.val < off + 50 by omega))).trans ((hHotSpec β hS0).2.2 i)
  have hFib1 (f : Fin 10) : pRt0.fwdBits β (rFib f) = b2z (coinOptFib c == some f) := by
    dsimp only [rFib]
    rw [show pRt0.fwdBits β = pFib.fwdBits (pHot.fwdBits β) from rfl,
      rFib_eq_cSlot (by omega) (by omega) f, (hFibSpec (pHot.fwdBits β) hFibS).2 f,
      localIdx_block_congr _ (by omega) fun j ↦
        (hHotSpec β hS0).1 ⟨8 + j.val, by omega⟩ (Or.inl (show 8 + j.val < off by omega))]
  exact ⟨hOut, h46, hHot1, hFib1, env56_eq_idEnv56 rHot rFib _ g (coinOptFib c) hHot1 hFib1⟩
/-! ### `192-T` (`87`-Scratch) Forward `PREP_out` Pre-Swap (`hGadgetPreSwap103Dyn`) -/
/-- ANF polynomial planes `0..3` over `(x₀, x₁)` of `keepRawBool`. -/
def keepPolyBool (r : Fin 4) (g : Fin 46) (f : Fin 10) : Bool :=
  match r.val with
  | 0 => keepRawBool 0 g f
  | 1 => xor (keepRawBool 0 g f) (keepRawBool 1 g f)
  | 2 => xor (keepRawBool 0 g f) (keepRawBool 2 g f)
  | _ => xor (xor (keepRawBool 0 g f) (keepRawBool 1 g f))
      (xor (keepRawBool 2 g f) (keepRawBool 3 g f))
/-- Sum of the `4` Hadamard-gadget carry phases of `keepPolyBool 0..3` on `(g, optF)`. -/
def keepPhi (g : Fin 46) (optF : Option (Fin 10)) : Bool :=
  xor (xor (quad5CarryBool (idEnv56 g optF) (keepPolyBool 0))
        (quad5CarryBool (idEnv56 g optF) (keepPolyBool 1)))
    (xor (quad5CarryBool (idEnv56 g optF) (keepPolyBool 2))
      (quad5CarryBool (idEnv56 g optF) (keepPolyBool 3)))
/-- `46`-wire one-hot group register `16..61` on `N = 103`. -/
abbrev rHot103 : QRegister 46 103 := QRegister.block 16 46 (by decide)
/-- `10`-wire coin-fiber register `66..75` on `N = 103`. -/
abbrev rFib103 : QRegister 10 103 := QRegister.block 66 10 (by decide)
theorem rHot103_ne (w : Wire 103) (hw : 62 ≤ w.val) (i : Fin 46) : rHot103 i ≠ w :=
  block_ne_of_ge (by decide) w hw i
theorem rFib103_ne (w : Wire 103) (hw : 76 ≤ w.val) (j : Fin 10) : rFib103 j ≠ w :=
  block_ne_of_ge (by decide) w hw j
theorem rHotFib103_ne (i : Fin 46) (j : Fin 10) : rHot103 i ≠ rFib103 j :=
  block_ne_block (by decide) (by decide) (Or.inl (by decide)) i j
/-- `48-T` (`0 TOFF`) 4-plane `keep` ANF loader onto wires `82..85` with carry cancellation. -/
def kLoad4C : Circuit 103 :=
  let g (w : Wire 103) (hw : 76 ≤ w.val) (r : Fin 4) :=
    quad5GadC w rHot103 rFib103 (rHot103_ne w (by omega)) (rFib103_ne w hw) (keepPolyBool r)
  g ⟨82, by decide⟩ (by decide) 0 ;;ᶜ g ⟨83, by decide⟩ (by decide) 1 ;;ᶜ
    g ⟨84, by decide⟩ (by decide) 2 ;;ᶜ g ⟨85, by decide⟩ (by decide) 3 ;;ᶜ
    fix46x10C rHot103 rFib103 rHotFib103_ne keepPhi
/-- `0-T` (`0 TOFF`) X-measurement unloader of wires `85..82`. -/
def kUnload4Dyn {Var : Type} (v : Var) : DynamicCircuit Var 103 :=
  let u (w : Wire 103) (hw : 76 ≤ w.val) (r : Fin 4) := xMeasUnloadWireDyn v w (.circuit
    (quad5FixC w rHot103 rFib103 (rHot103_ne w (by omega)) (rFib103_ne w hw) (keepPolyBool r)))
  .seq (u ⟨85, by decide⟩ (by decide) 3) (.seq (u ⟨84, by decide⟩ (by decide) 2)
    (.seq (u ⟨83, by decide⟩ (by decide) 1) (u ⟨82, by decide⟩ (by decide) 0)))
/-- Classical involutive bit-XOR on `82..85` matching `kLoad4C` on `(rHot103, rFib103)` sectors. -/
def kLoad4Bits (γ : BitAssignment 103) : BitAssignment 103 := update (update (update (update γ
    ⟨82, by decide⟩ (γ ⟨82, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 0) γ))
    ⟨83, by decide⟩ (γ ⟨83, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 1) γ))
    ⟨84, by decide⟩ (γ ⟨84, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 2) γ))
    ⟨85, by decide⟩ (γ ⟨85, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 3) γ)
/-- `3`-AND (`12-T`) ANF combiner writing `k₀ + x₀ * k₁ + x₁ * k₂ + s₀₁ * k₃` onto wire `92`. -/
def mkComb3Rev : GroupUnary.RevCompute 103 :=
  .seq (.cnot ⟨82, by decide⟩ ⟨92, by decide⟩ (by decide)) (.seq
    (.andGate ⟨0, by decide⟩ ⟨83, by decide⟩ ⟨86, by decide⟩ (by decide) (by decide) (by decide))
    (.seq (.cnot ⟨86, by decide⟩ ⟨92, by decide⟩ (by decide)) (.seq
      (.andGate ⟨1, by decide⟩ ⟨84, by decide⟩ ⟨87, by decide⟩ (by decide) (by decide) (by decide))
      (.seq (.cnot ⟨87, by decide⟩ ⟨92, by decide⟩ (by decide)) (.seq (.andGate ⟨62, by decide⟩
        ⟨85, by decide⟩ ⟨88, by decide⟩ (by decide) (by decide) (by decide))
        (.cnot ⟨88, by decide⟩ ⟨92, by decide⟩ (by decide)))))))
/-- Combined router `wHot46Rev 16 ;; cFib11Rev 66` on `N = 103`. -/
def pPreRt : GroupUnary.RevCompute 103 :=
  (wHot46Rev 16 (by decide) (by decide)).seq (cFib11Rev 66 (by decide) (by decide))
/-- `7`-AND (`28-T`) reversible tail `mkComb3Rev ;; pCompactAlt23 ;; affTop2Rev ;; mkOr2`. -/
def pPreTail : GroupUnary.RevCompute 103 :=
  mkComb3Rev.seq (pCompactAlt23.seq (affTop2Rev.seq mkOr2))
theorem count_kLoad4C_toff : kLoad4C.count .TOFF = 0 := by
  simp only [kLoad4C, Circuit.count_seq, count_quad5GadC_toff, count_fix46x10C_toff]
theorem count_kLoad4C_t : kLoad4C.count .T = 48 := by
  simp only [kLoad4C, Circuit.count_seq, count_quad5GadC_t, count_fix46x10C_t]
theorem count_kUnload4Dyn_toff {Var : Type} (v : Var) : (kUnload4Dyn v).count .TOFF = 0 := by
  simp only [kUnload4Dyn, DynamicCircuit.count, count_xMeasUnloadWireDyn_toff, count_quad5FixC_toff]
theorem count_kUnload4Dyn_t {Var : Type} (v : Var) : (kUnload4Dyn v).count .T = 0 := by
  simp only [kUnload4Dyn, DynamicCircuit.count, count_xMeasUnloadWireDyn_t, count_quad5FixC_t]
@[simp] theorem numAnd_mkComb3Rev : mkComb3Rev.numAnd = 3 := rfl
@[simp] theorem numAnd_pPreTail : pPreTail.numAnd = 7 := by
  simp only [pPreTail, GroupUnary.RevCompute.numAnd, numAnd_mkComb3Rev,
    numAnd_pCompactAlt23, numAndAffTop2Rev, numAndMkOr2]
/-- `192-T` (`0 TOFF`, `87`-scratch) Hadamard-gadget pre-swap loader for `alt4BoolTable`. -/
def hGadgetPreSwap103Dyn {Var : Type} (v : Var) : DynamicCircuit Var 103 :=
  .seq (.seq (.seq (.seq (.seq
    (.seq (wHot46FwdDyn v 16 (by decide) (by decide)) (cFib11FwdDyn v 66 (by decide) (by decide)))
    (.circuit kLoad4C)) (Lac2Folded184Select.revComputeDyn pPreTail))
    (Lac2Folded184Select.revComputeDyn alt4CopyRev))
    (Lac2Folded184Select.revUncomputeDyn v pPreTail))
    (.seq (kUnload4Dyn v) (Lac2Folded184Select.revUncomputeDyn v pPreRt))
attribute [irreducible] hGadgetPreSwap103Dyn
@[simp] theorem countHGadgetPreSwap103Dyn_toff {Var : Type} (v : Var) :
    (hGadgetPreSwap103Dyn v).count .TOFF = 0 := by
  unfold hGadgetPreSwap103Dyn
  simp [DynamicCircuit.count, count_kLoad4C_toff, count_kUnload4Dyn_toff]
@[simp] theorem countHGadgetPreSwap103Dyn_t {Var : Type} (v : Var) :
    (hGadgetPreSwap103Dyn v).count .T = 192 := by
  unfold hGadgetPreSwap103Dyn
  simp [DynamicCircuit.count, count_kLoad4C_t, count_kUnload4Dyn_t]
theorem mkComb3Rev_spec (γ : BitAssignment 103) (h86 : γ ⟨86, by decide⟩ = 0)
    (h87 : γ ⟨87, by decide⟩ = 0) (h88 : γ ⟨88, by decide⟩ = 0) (h92 : γ ⟨92, by decide⟩ = 0) :
    mkComb3Rev.validOn γ = true ∧
    (∀ u : Wire 103, (u.val < 86 ∨ 93 ≤ u.val) → mkComb3Rev.fwdBits γ u = γ u) ∧
    mkComb3Rev.fwdBits γ ⟨92, by decide⟩ =
      γ ⟨82, by decide⟩ + γ ⟨0, by decide⟩ * γ ⟨83, by decide⟩ +
        γ ⟨1, by decide⟩ * γ ⟨84, by decide⟩ + γ ⟨62, by decide⟩ * γ ⟨85, by decide⟩ := by
  have wne (a b : ℕ) (h : a ≠ b) (ha : a < 103 := by decide) (hb : b < 103 := by decide) :
      (⟨a, ha⟩ : Wire 103) ≠ ⟨b, hb⟩ := fun e ↦ h (congrArg Fin.val e)
  set g1 := update γ ⟨92, by decide⟩ (γ ⟨92, by decide⟩ + γ ⟨82, by decide⟩)
  set g2 := update g1 ⟨86, by decide⟩ (g1 ⟨86, by decide⟩ + g1 ⟨0, by decide⟩ * g1 ⟨83, by decide⟩)
  set g3 := update g2 ⟨92, by decide⟩ (g2 ⟨92, by decide⟩ + g2 ⟨86, by decide⟩)
  set g4 := update g3 ⟨87, by decide⟩ (g3 ⟨87, by decide⟩ + g3 ⟨1, by decide⟩ * g3 ⟨84, by decide⟩)
  set g5 := update g4 ⟨92, by decide⟩ (g4 ⟨92, by decide⟩ + g4 ⟨87, by decide⟩)
  set g6 := update g5 ⟨88, by decide⟩ (g5 ⟨88, by decide⟩ + g5 ⟨62, by decide⟩ * g5 ⟨85, by decide⟩)
  set g7 := update g6 ⟨92, by decide⟩ (g6 ⟨92, by decide⟩ + g6 ⟨88, by decide⟩)
  have hg_eq : mkComb3Rev.fwdBits γ = g7 := rfl
  have hg1 : g1 = update γ ⟨92, by decide⟩ (γ ⟨82, by decide⟩) := by simp only [g1, h92, zero_add]
  have hv86 : g1 ⟨86, by decide⟩ = 0 := by
    rw [hg1, update_of_ne (by decide)]
    exact h86
  have hg2 : g2 = update g1 ⟨86, by decide⟩ (γ ⟨0, by decide⟩ * γ ⟨83, by decide⟩) :=
    congrArg (update g1 ⟨86, by decide⟩) (by
      rw [hv86, zero_add]
      simp only [hg1, update_of_ne (wne 0 92 (by decide)), update_of_ne (wne 83 92 (by decide))])
  have hg3 : g3 = update g2 ⟨92, by decide⟩
      (γ ⟨82, by decide⟩ + γ ⟨0, by decide⟩ * γ ⟨83, by decide⟩) := by
    simp only [g3, hg2, hg1, update_self, update_of_ne (wne 92 86 (by decide))]
  have hv87 : g3 ⟨87, by decide⟩ = 0 := by
    rw [hg3, update_of_ne (by decide), hg2, update_of_ne (by decide), hg1, update_of_ne (by decide)]
    exact h87
  have hg4 : g4 = update g3 ⟨87, by decide⟩ (γ ⟨1, by decide⟩ * γ ⟨84, by decide⟩) :=
    congrArg (update g3 ⟨87, by decide⟩) (by
      rw [hv87, zero_add]
      simp only [hg3, hg2, hg1, update_of_ne (wne 1 92 (by decide)),
        update_of_ne (wne 84 92 (by decide)), update_of_ne (wne 1 86 (by decide)),
        update_of_ne (wne 84 86 (by decide))])
  have hg5 : g5 = update g4 ⟨92, by decide⟩ (γ ⟨82, by decide⟩ +
      γ ⟨0, by decide⟩ * γ ⟨83, by decide⟩ + γ ⟨1, by decide⟩ * γ ⟨84, by decide⟩) := by
    simp only [g5, hg4, hg3, update_self, update_of_ne (wne 92 87 (by decide))]
  have hv88 : g5 ⟨88, by decide⟩ = 0 := by
    rw [hg5, update_of_ne (by decide), hg4, update_of_ne (by decide), hg3, update_of_ne (by decide),
      hg2, update_of_ne (by decide), hg1, update_of_ne (by decide)]
    exact h88
  have hg6 : g6 = update g5 ⟨88, by decide⟩ (γ ⟨62, by decide⟩ * γ ⟨85, by decide⟩) :=
    congrArg (update g5 ⟨88, by decide⟩) (by
      rw [hv88, zero_add]
      simp only [hg5, hg4, hg3, hg2, hg1, update_of_ne (wne 62 92 (by decide)),
        update_of_ne (wne 85 92 (by decide)), update_of_ne (wne 62 87 (by decide)),
        update_of_ne (wne 85 87 (by decide)), update_of_ne (wne 62 86 (by decide)),
        update_of_ne (wne 85 86 (by decide))])
  have hg7 : g7 = update g6 ⟨92, by decide⟩
      (γ ⟨82, by decide⟩ + γ ⟨0, by decide⟩ * γ ⟨83, by decide⟩ +
        γ ⟨1, by decide⟩ * γ ⟨84, by decide⟩ + γ ⟨62, by decide⟩ * γ ⟨85, by decide⟩) := by
    simp only [g7, hg6, hg5, update_self, update_of_ne (wne 92 88 (by decide))]
  have hvalid : mkComb3Rev.validOn γ = true := by
    change (true && ((g1 ⟨86, by decide⟩ == 0) && (true && ((g3 ⟨87, by decide⟩ == 0) &&
      (true && ((g5 ⟨88, by decide⟩ == 0) && true)))))) = true
    rw [hv86, hv87, hv88]
    decide
  refine ⟨hvalid, fun u hu ↦ ?_, by rw [hg_eq, hg7, update_self]⟩
  have hne (k : ℕ) (hk : 86 ≤ k ∧ k < 93) (hN : k < 103) : u ≠ ⟨k, hN⟩ := fun e ↦ by
    have hv : u.val = k := congrArg Fin.val e
    omega
  have h92' := hne 92 ⟨by decide, by decide⟩ (by decide)
  rw [hg_eq, hg7, update_of_ne h92', hg6, update_of_ne (hne 88 ⟨by decide, by decide⟩ (by decide)),
    hg5, update_of_ne h92', hg4, update_of_ne (hne 87 ⟨by decide, by decide⟩ (by decide)),
    hg3, update_of_ne h92', hg2, update_of_ne (hne 86 ⟨by decide, by decide⟩ (by decide)),
    hg1, update_of_ne h92']
theorem hne83_82 : (⟨83, by decide⟩ : Wire 103) ≠ ⟨82, by decide⟩ := by decide
theorem hne84_82 : (⟨84, by decide⟩ : Wire 103) ≠ ⟨82, by decide⟩ := by decide
theorem hne84_83 : (⟨84, by decide⟩ : Wire 103) ≠ ⟨83, by decide⟩ := by decide
theorem hne85_82 : (⟨85, by decide⟩ : Wire 103) ≠ ⟨82, by decide⟩ := by decide
theorem hne85_83 : (⟨85, by decide⟩ : Wire 103) ≠ ⟨83, by decide⟩ := by decide
theorem hne85_84 : (⟨85, by decide⟩ : Wire 103) ≠ ⟨84, by decide⟩ := by decide
theorem kLoad4Bits_82 (γ : BitAssignment 103) : kLoad4Bits γ ⟨82, by decide⟩ =
    γ ⟨82, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 0) γ := by
  simp only [kLoad4Bits, update_of_ne hne85_82.symm, update_of_ne hne84_82.symm,
    update_of_ne hne83_82.symm, update_self]
theorem kLoad4Bits_83 (γ : BitAssignment 103) : kLoad4Bits γ ⟨83, by decide⟩ =
    γ ⟨83, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 1) γ := by
  simp only [kLoad4Bits, update_of_ne hne85_83.symm, update_of_ne hne84_83.symm, update_self]
theorem kLoad4Bits_84 (γ : BitAssignment 103) : kLoad4Bits γ ⟨84, by decide⟩ =
    γ ⟨84, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 2) γ := by
  simp only [kLoad4Bits, update_of_ne hne85_84.symm, update_self]
theorem kLoad4Bits_85 (γ : BitAssignment 103) : kLoad4Bits γ ⟨85, by decide⟩ =
    γ ⟨85, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 3) γ := by
  simp only [kLoad4Bits, update_self]
theorem kLoad4Bits_other (γ : BitAssignment 103) (w : Wire 103)
    (h : w.val < 82 ∨ 86 ≤ w.val) : kLoad4Bits γ w = γ w := by
  have hne (k : ℕ) (hk : 82 ≤ k ∧ k < 86) (hN : k < 103) : w ≠ ⟨k, hN⟩ := fun e ↦ by
    have hv : w.val = k := congrArg Fin.val e
    omega
  simp only [kLoad4Bits, update_of_ne (hne 85 ⟨by decide, by decide⟩ (by decide)),
    update_of_ne (hne 84 ⟨by decide, by decide⟩ (by decide)),
    update_of_ne (hne 83 ⟨by decide, by decide⟩ (by decide)),
    update_of_ne (hne 82 ⟨by decide, by decide⟩ (by decide))]
theorem kLoad4Bits_invol (γ : BitAssignment 103) : kLoad4Bits (kLoad4Bits γ) = γ := by
  have he (γ' : BitAssignment 103) (w : Wire 103) (hw : 76 ≤ w.val) (val : ZMod 2) :
      env56 rHot103 rFib103 (update γ' w val) = env56 rHot103 rFib103 γ' :=
    env56_upd rHot103 rFib103 (rHot103_ne w (by omega)) (rFib103_ne w hw) γ' val
  have hq (r : Fin 4) : quad5Bit rHot103 rFib103 (keepPolyBool r) (kLoad4Bits γ) =
      quad5Bit rHot103 rFib103 (keepPolyBool r) γ := by
    dsimp only [quad5Bit, kLoad4Bits]
    rw [he _ ⟨85, by decide⟩ (by decide), he _ ⟨84, by decide⟩ (by decide),
      he _ ⟨83, by decide⟩ (by decide), he _ ⟨82, by decide⟩ (by decide)]
  funext w
  by_cases h0 : w = ⟨82, by decide⟩
  · rw [h0, kLoad4Bits_82, kLoad4Bits_82, hq 0, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · by_cases h1 : w = ⟨83, by decide⟩
    · rw [h1, kLoad4Bits_83, kLoad4Bits_83, hq 1, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · by_cases h2 : w = ⟨84, by decide⟩
      · rw [h2, kLoad4Bits_84, kLoad4Bits_84, hq 2, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · by_cases h3 : w = ⟨85, by decide⟩
        · rw [h3, kLoad4Bits_85, kLoad4Bits_85, hq 3, add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · simp only [kLoad4Bits, update_of_ne h3, update_of_ne h2, update_of_ne h1, update_of_ne h0]
theorem kLoad4Bits_reverse_eq (γ : BitAssignment 103) : update (update (update (update γ
      ⟨85, by decide⟩ (γ ⟨85, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 3) γ))
      ⟨84, by decide⟩ (γ ⟨84, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 2) γ))
      ⟨83, by decide⟩ (γ ⟨83, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 1) γ))
      ⟨82, by decide⟩ (γ ⟨82, by decide⟩ + quad5Bit rHot103 rFib103 (keepPolyBool 0) γ) =
      kLoad4Bits γ := by
  funext w
  by_cases h0 : w = ⟨82, by decide⟩
  · rw [h0, kLoad4Bits_82, update_self]
  · by_cases h1 : w = ⟨83, by decide⟩
    · rw [h1, kLoad4Bits_83, update_of_ne hne83_82, update_self]
    · by_cases h2 : w = ⟨84, by decide⟩
      · rw [h2, kLoad4Bits_84, update_of_ne hne84_82, update_of_ne hne84_83, update_self]
      · by_cases h3 : w = ⟨85, by decide⟩
        · rw [h3, kLoad4Bits_85, update_of_ne hne85_82, update_of_ne hne85_83,
            update_of_ne hne85_84, update_self]
        · simp only [kLoad4Bits, update_of_ne h3, update_of_ne h2, update_of_ne h1, update_of_ne h0]
theorem kLoad4Bits_agreeOut12_16 {α β : BitAssignment 103}
    (h : ∀ w : Wire 103, (w.val < 12 ∨ 16 ≤ w.val) → α w = β w) :
    ∀ w : Wire 103, (w.val < 12 ∨ 16 ≤ w.val) → kLoad4Bits α w = kLoad4Bits β w := by
  have he : env56 rHot103 rFib103 α = env56 rHot103 rFib103 β := by
    funext v
    rcases v with i | j
    · exact congrArg z2b (h (rHot103 i) (Or.inr (by simp [rHot103])))
    · exact congrArg z2b (h (rFib103 j) (Or.inr (by
        have hv : (rFib103 j).val = 66 + j.val := rfl
        omega)))
  have hq (r : Fin 4) : quad5Bit rHot103 rFib103 (keepPolyBool r) α =
      quad5Bit rHot103 rFib103 (keepPolyBool r) β := by simp [quad5Bit, he]
  intro w hw
  by_cases h0 : w = ⟨82, by decide⟩
  · rw [h0, kLoad4Bits_82, kLoad4Bits_82, hq 0, h _ (Or.inr (by decide))]
  · by_cases h1 : w = ⟨83, by decide⟩
    · rw [h1, kLoad4Bits_83, kLoad4Bits_83, hq 1, h _ (Or.inr (by decide))]
    · by_cases h2 : w = ⟨84, by decide⟩
      · rw [h2, kLoad4Bits_84, kLoad4Bits_84, hq 2, h _ (Or.inr (by decide))]
      · by_cases h3 : w = ⟨85, by decide⟩
        · rw [h3, kLoad4Bits_85, kLoad4Bits_85, hq 3, h _ (Or.inr (by decide))]
        · simp only [kLoad4Bits, update_of_ne h3, update_of_ne h2, update_of_ne h1,
            update_of_ne h0, h w hw]
theorem revDisjRange_pPreRt : RevDisjRange 12 16 pPreRt :=
  ⟨revDisjRangePreSwapComputeRev2.1, revDisjRange_cFib11Rev 66 (by decide) (by decide)⟩
theorem revDisjRange_pPreTail : RevDisjRange 12 16 pPreTail := ⟨by
    dsimp [mkComb3Rev, RevDisjRange]
    decide, revDisjRangePreSwapComputeRev2.2.2⟩
theorem pPreRt_eq : pPreRt =
    (wHot46Rev 16 (by decide) (by decide)).seq (cFib11Rev 66 (by decide) (by decide)) := rfl
attribute [irreducible] mkComb3Rev pPreRt
theorem cleanRealizesHGadgetPreSwap103Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) : Solution.CleanDyn.CleanRealizes v (QRegister.block 0 16 (by decide) :
      QRegister 16 103)
      (QRegister.block 16 87 (by decide) : QRegister 87 103)
      (xorLoadUnitary 12 4 4096 alt4BoolTable) (hGadgetPreSwap103Dyn v) := by
  let rAct16 : QRegister 16 103 := QRegister.block 0 16 (by decide)
  let rScr87 : QRegister 87 103 := QRegister.block 16 87 (by decide)
  let U_tgt := rAct16.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable)
  have hDec {p : Prop} {inst : Decidable p} : @decide p inst = true ↔ p :=
    @decide_eq_true_iff p inst
  suffices hMain : ∀ (S0 : BitAssignment 103 → Bool),
      (∀ β, S0 β = true ↔ ∀ j : Fin 87, β (rScr87 j) = 0) →
      TransRealizes v S0 S0 U_tgt (hGadgetPreSwap103Dyn v) by
    exact cleanRealizes_of_transRealizes rAct16 rScr87 (by decide) (hMain _ fun _ ↦ hDec)
  intro S0 hS0_iff
  unfold hGadgetPreSwap103Dyn
  let S1 : BitAssignment 103 → Bool := fun γ ↦ S0 (pPreRt.invBits γ)
  obtain ⟨htrRt, htrUnRt, hS1_clean, hRtSpec⟩ :=
    hotFibRouter_spec (N := 103) 16 66 62 87 rfl rfl (by decide) (by decide) (by decide)
      (by decide) v pPreRt pPreRt_eq S0 fun β hS j ↦ (hS0_iff β).mp hS j
  let fK (r : Fin 4) := quad5Bit rHot103 rFib103 (keepPolyBool r)
  have hFK (r : Fin 4) (w : Wire 103) (hw : 76 ≤ w.val) (ξ : BitAssignment 103) (val : ZMod 2) :
      fK r (update ξ w val) = fK r ξ :=
    quad5Bit_upd _ _ (rHot103_ne w (by omega)) (rFib103_ne w hw) (keepPolyBool r) ξ val
  have hFK82 (r : Fin 4) := hFK r ⟨82, by decide⟩ (by decide)
  have hFK83 (r : Fin 4) := hFK r ⟨83, by decide⟩ (by decide)
  have hFK84 (r : Fin 4) := hFK r ⟨84, by decide⟩ (by decide)
  have hFK85 (r : Fin 4) := hFK r ⟨85, by decide⟩ (by decide)
  let U82 := xorWireUnitary ⟨82, by decide⟩ (fK 0) (hFK82 0)
  let U83 := xorWireUnitary ⟨83, by decide⟩ (fK 1) (hFK83 1)
  let U84 := xorWireUnitary ⟨84, by decide⟩ (fK 2) (hFK84 2)
  let U85 := xorWireUnitary ⟨85, by decide⟩ (fK 3) (hFK85 3)
  let U_k4 := U85 * (U84 * (U83 * U82))
  have hUk4_ket (ξ : BitAssignment 103) :
      U_k4.1.mulVec (Solution.XMeasCircuit.ket ξ) = Solution.XMeasCircuit.ket (kLoad4Bits ξ) := by
    dsimp only [U_k4, U82, U83, U84, U85]
    simp only [Submonoid.coe_mul, ← mulVec_mulVec, xorWireUnitary_mulVec_ket, hFK82, hFK83, hFK84,
      update_of_ne hne83_82, update_of_ne hne84_83, update_of_ne hne84_82, update_of_ne hne85_84,
      update_of_ne hne85_83, update_of_ne hne85_82]
    dsimp only [kLoad4Bits, fK]
  have hUk4_sq : U_k4 * U_k4 = 1 := Subtype.ext <| Solution.XMeasCircuit.matrix_ext_ket fun ξ ↦ by
    change (U_k4.1 * U_k4.1).mulVec _ = (1 : Operator _).mulVec _
    rw [← mulVec_mulVec, hUk4_ket, hUk4_ket, kLoad4Bits_invol, one_mulVec]
  let S2 : BitAssignment 103 → Bool := fun δ ↦ S1 (kLoad4Bits δ)
  have hUk4_map : U_k4.1 * GroupUnary.predProj S1 = GroupUnary.predProj S2 * U_k4.1 :=
    ketPerm_mul_predProj U_k4 kLoad4Bits
      (fun ξ ↦ by rw [← ket_sdk_eq, hUk4_ket, ket_sdk_eq]) S1 S2
      fun ξ ↦ (congrArg S1 (kLoad4Bits_invol ξ)).symm
  have htrLoad : TransRealizes v S1 S2 U_k4 (.circuit kLoad4C) := by
    refine TransRealizes.of_circuit_invUnitary v kLoad4C U_k4 count_kLoad4C_toff
      hUk4_sq hUk4_map <| Solution.XMeasCircuit.matrix_ext_ket fun γ1 ↦ ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, ket_sdk_eq γ1, predProj_mulVec_ket]
    cases h1 : S1 γ1
    · simp only [Bool.false_eq_true, ↓reduceIte, mulVec_zero]
    · simp only [↓reduceIte]
      rw [← ket_sdk_eq γ1, hUk4_ket]
      let β := pPreRt.invBits γ1
      obtain ⟨_, _, hHot0, hFib0, hEnv0⟩ := hRtSpec β h1
      have hγ1 : pPreRt.fwdBits β = γ1 := pPreRt.fwdBits_invBits γ1
      let g := DyadicXMeasPrepOut13.effGroup
        ((localIdx (QRegister.block 0 8 (by decide)) β).val / 4)
      let c := localIdx (QRegister.block 8 4 (by decide)) β
      have hHot1 (i : Fin 46) : γ1 (rHot103 i) = if i = g then 1 else 0 :=
        (congrFun hγ1 (rHot103 i)).symm.trans (hHot0 i)
      have hFib1 (f : Fin 10) : γ1 (rFib103 f) = b2z (coinOptFib c == some f) :=
        (congrFun hγ1 (rFib103 f)).symm.trans (hFib0 f)
      have hEnv1 : env56 rHot103 rFib103 γ1 = idEnv56 g (coinOptFib c) :=
        (congrArg (env56 rHot103 rFib103) hγ1.symm).trans hEnv0
      have he (w : Wire 103) (hw : 76 ≤ w.val) (ξ : BitAssignment 103) (val : ZMod 2) :
          env56 rHot103 rFib103 (update ξ w val) = env56 rHot103 rFib103 ξ :=
        env56_upd rHot103 rFib103 (rHot103_ne w (by omega)) (rFib103_ne w hw) ξ val
      dsimp only [kLoad4C]
      rw [eval_seq_mv, ket_quad5GadC_zero _ _ _ _ _ _ γ1 (hS1_clean γ1 h1 82 (by decide) _),
        mulVec_smul, eval_seq_mv, ket_quad5GadC_zero _ _ _ _ _ _ _ (by
          rw [update_of_ne hne83_82]
          exact hS1_clean γ1 h1 83 (by decide) _),
        mulVec_smul, eval_seq_mv, ket_quad5GadC_zero _ _ _ _ _ _ _ (by
          rw [update_of_ne hne84_83, update_of_ne hne84_82]
          exact hS1_clean γ1 h1 84 (by decide) _),
        mulVec_smul, eval_seq_mv, ket_quad5GadC_zero _ _ _ _ _ _ _ (by
          rw [update_of_ne hne85_84, update_of_ne hne85_83, update_of_ne hne85_82]
          exact hS1_clean γ1 h1 85 (by decide) _),
        mulVec_smul, ket_fix46x10C_sector _ _ _ _ _ g (coinOptFib c) (fun i ↦ by
            rw [update_of_ne (rHot103_ne ⟨85, by decide⟩ (by decide) i),
              update_of_ne (rHot103_ne ⟨84, by decide⟩ (by decide) i),
              update_of_ne (rHot103_ne ⟨83, by decide⟩ (by decide) i),
              update_of_ne (rHot103_ne ⟨82, by decide⟩ (by decide) i), hHot1 i]) (fun f ↦ by
            rw [update_of_ne (rFib103_ne ⟨85, by decide⟩ (by decide) f),
              update_of_ne (rFib103_ne ⟨84, by decide⟩ (by decide) f),
              update_of_ne (rFib103_ne ⟨83, by decide⟩ (by decide) f),
              update_of_ne (rFib103_ne ⟨82, by decide⟩ (by decide) f), hFib1 f])]
      simp only [smul_smul, ← bitSign_add, he ⟨82, by decide⟩ (by decide),
        he ⟨83, by decide⟩ (by decide), he ⟨84, by decide⟩ (by decide)]
      have hz4 (a b d e : ZMod 2) : a + (b + (d + (e + (a + b + (d + e))))) = 0 := by
        ring_nf
        simp [show (2 : ZMod 2) = 0 from rfl]
      have hPhi0 : b2z (quad5CarryBool (env56 rHot103 rFib103 γ1) (keepPolyBool 0)) +
          (b2z (quad5CarryBool (env56 rHot103 rFib103 γ1) (keepPolyBool 1)) +
            (b2z (quad5CarryBool (env56 rHot103 rFib103 γ1) (keepPolyBool 2)) +
              (b2z (quad5CarryBool (env56 rHot103 rFib103 γ1) (keepPolyBool 3)) +
                b2z (keepPhi g (coinOptFib c))))) = 0 := by
        rw [hEnv1]
        simp only [keepPhi, b2z_xor]
        exact hz4 _ _ _ _
      rw [hPhi0, bitSign_zero2, one_smul]
      refine congrArg Solution.XMeasCircuit.ket ?_
      simp only [kLoad4Bits, quad5Bit, he ⟨84, by decide⟩ (by decide),
        he ⟨83, by decide⟩ (by decide), he ⟨82, by decide⟩ (by decide),
        hS1_clean γ1 h1 82 (by decide) _, hS1_clean γ1 h1 83 (by decide) _,
        hS1_clean γ1 h1 84 (by decide) _, hS1_clean γ1 h1 85 (by decide) _, zero_add]
  let S1_1 (ξ : BitAssignment 103) := S1 (update ξ ⟨82, by decide⟩ (ξ ⟨82, by decide⟩ + fK 0 ξ))
  let S1_2 (ξ : BitAssignment 103) := S1_1 (update ξ ⟨83, by decide⟩ (ξ ⟨83, by decide⟩ + fK 1 ξ))
  let S1_3 (ξ : BitAssignment 103) := S1_2 (update ξ ⟨84, by decide⟩ (ξ ⟨84, by decide⟩ + fK 2 ξ))
  let S1_4 (ξ : BitAssignment 103) := S1_3 (update ξ ⟨85, by decide⟩ (ξ ⟨85, by decide⟩ + fK 3 ξ))
  have hS1_4_eq : S1_4 = S2 := funext fun ξ ↦ congrArg S1 (by
    simp only [hFK85, hFK84, hFK83, update_of_ne hne85_84.symm, update_of_ne hne84_83.symm,
      update_of_ne hne85_83.symm, update_of_ne hne83_82.symm, update_of_ne hne84_82.symm,
      update_of_ne hne85_82.symm]
    exact kLoad4Bits_reverse_eq ξ)
  have huStep (q : Wire 103) (hq76 : 76 ≤ q.val) (r : Fin 4) (S : BitAssignment 103 → Bool)
      (hClean : ∀ ξ, S ξ = true → ξ q = 0) :=
    TransRealizes.xMeasUnloadWire v q (fK r) (hFK r q hq76) S hClean (quad5FixC q rHot103 rFib103
      (rHot103_ne q (by omega)) (rFib103_ne q hq76) (keepPolyBool r))
      (count_quad5FixC_toff ..) (ket_quad5FixC_zero _ _ _ _ _ _)
  have hu82 := huStep ⟨82, by decide⟩ (by decide) 0 S1 fun ξ hξ ↦
    hS1_clean ξ hξ 82 (by decide) (by decide)
  have hu83 := huStep ⟨83, by decide⟩ (by decide) 1 S1_1 fun ξ hξ ↦ by
    have h0 := hS1_clean _ hξ 83 (by decide) (by decide)
    rwa [update_of_ne hne83_82] at h0
  have hu84 := huStep ⟨84, by decide⟩ (by decide) 2 S1_2 fun ξ hξ ↦ by
    have h0 := hS1_clean _ hξ 84 (by decide) (by decide)
    rwa [update_of_ne hne84_82, update_of_ne hne84_83] at h0
  have hu85 := huStep ⟨85, by decide⟩ (by decide) 3 S1_3 fun ξ hξ ↦ by
    have h0 := hS1_clean _ hξ 85 (by decide) (by decide)
    rwa [update_of_ne hne85_82, update_of_ne hne85_83, update_of_ne hne85_84] at h0
  have hUu_eq : U82 * U83 * U84 * U85 = U_k4 :=
      Subtype.ext <| Solution.XMeasCircuit.matrix_ext_ket fun ξ ↦ by
    rw [hUk4_ket]
    dsimp only [U82, U83, U84, U85]
    simp only [Submonoid.coe_mul, ← mulVec_mulVec, xorWireUnitary_mulVec_ket, hFK85, hFK84, hFK83,
      update_of_ne hne85_84.symm, update_of_ne hne84_83.symm, update_of_ne hne85_83.symm,
      update_of_ne hne83_82.symm, update_of_ne hne84_82.symm, update_of_ne hne85_82.symm]
    exact congrArg Solution.XMeasCircuit.ket (kLoad4Bits_reverse_eq ξ)
  have htrUnload : TransRealizes v S2 S1 U_k4 (kUnload4Dyn v) :=
    hUu_eq ▸ (hu85.seq (hu84.seq (hu83.seq hu82))).congr_pred hS1_4_eq rfl
  obtain ⟨hrt_pres, hrt_inv_ext⟩ := revDisjRange_inv_fwd_preserve revDisjRange_pPreRt
  obtain ⟨htl_pres, htl_inv_ext⟩ := revDisjRange_inv_fwd_preserve revDisjRange_pPreTail
  have hTailSpec (γ2 : BitAssignment 103) (h2 : S2 γ2 = true) :
      pPreTail.validOn γ2 = true ∧ alt4CopyRev.validOn (pPreTail.fwdBits γ2) = true ∧
      pPreRt.invBits (kLoad4Bits (pPreTail.invBits (alt4CopyRev.fwdBits (pPreTail.fwdBits γ2)))) =
        xorRegBits (pPreRt.invBits (kLoad4Bits γ2)) (QRegister.block 12 4 (by decide))
          (alt4BoolTable (localIdx (QRegister.block 0 12 (by decide))
            (pPreRt.invBits (kLoad4Bits γ2))).val) := by
    let γ1 := kLoad4Bits γ2
    let β := pPreRt.invBits γ1
    have h1 : S1 γ1 = true := h2
    obtain ⟨hOut0, h62_0, hHot0, _, hEnv0⟩ := hRtSpec β h1
    have hγ2_eq : γ2 = kLoad4Bits γ1 := (kLoad4Bits_invol γ2).symm
    have hγ1_eq : γ1 = pPreRt.fwdBits β := (pPreRt.fwdBits_invBits γ1).symm
    have hOutRt (w : Wire 103) (hw : w.val < 16) : γ2 w = β w := by
      rw [hγ2_eq, kLoad4Bits_other γ1 w (Or.inl (by omega)), hγ1_eq, hOut0 w hw]
    have hClean86 (k : ℕ) (hk1 : 86 ≤ k) (hk2 : k < 103) : γ2 ⟨k, hk2⟩ = 0 := by
      rw [hγ2_eq, kLoad4Bits_other γ1 ⟨k, hk2⟩ (Or.inr (show 86 ≤ k by omega))]
      exact hS1_clean γ1 h1 k (by omega) hk2
    let x := (localIdx (QRegister.block 0 8 (by decide)) β).val
    let g := DyadicXMeasPrepOut13.effGroup (x / 4)
    let c := localIdx (QRegister.block 8 4 (by decide)) β
    have hHot2 (i : Fin 46) : γ2 ⟨16 + i.val, by omega⟩ = if i = g then 1 else 0 := by
      have hi : (⟨16 + i.val, by omega⟩ : Wire 103) = rHot103 i :=
        Fin.ext (by rw [qreg_block_apply])
      rw [hγ2_eq, kLoad4Bits_other γ1 ⟨16 + i.val, by omega⟩
        (Or.inl (show 16 + i.val < 82 by omega)), hγ1_eq, hi]
      exact hHot0 i
    have hS01_2 : γ2 ⟨62, by decide⟩ = γ2 ⟨0, by decide⟩ * γ2 ⟨1, by decide⟩ := by
      rw [hOutRt ⟨0, by decide⟩ (by decide), hOutRt ⟨1, by decide⟩ (by decide), hγ2_eq,
        kLoad4Bits_other γ1 ⟨62, by decide⟩ (Or.inl (by decide)), hγ1_eq]
      exact h62_0
    have hEnv1 : env56 rHot103 rFib103 γ1 = idEnv56 g (coinOptFib c) :=
      (congrArg (env56 rHot103 rFib103) hγ1_eq).trans hEnv0
    have hkVal (r : Fin 4) : quad5Bit rHot103 rFib103 (keepPolyBool r) γ1 =
        b2z ((coinOptFib c).elim false (keepPolyBool r g)) :=
      quad5Bit_eq_of_env rHot103 rFib103 (keepPolyBool r) γ1 g (coinOptFib c) hEnv1
    obtain ⟨hv_mc, hout_mc, h92_mc⟩ := mkComb3Rev_spec γ2 (hClean86 86 (by decide) _)
      (hClean86 87 (by decide) _) (hClean86 88 (by decide) _) (hClean86 92 (by decide) _)
    let γ2m := mkComb3Rev.fwdBits γ2
    have hHot_m (i : Fin 46) : γ2m ⟨16 + i.val, by omega⟩ = if i = g then 1 else 0 :=
      (hout_mc _ (Or.inl (show 16 + i.val < 86 by omega))).trans (hHot2 i)
    have h0_m : γ2m ⟨0, by decide⟩ = β ⟨0, by decide⟩ :=
      (hout_mc ⟨0, by decide⟩ (Or.inl (by decide))).trans (hOutRt ⟨0, by decide⟩ (by decide))
    have h1_m : γ2m ⟨1, by decide⟩ = β ⟨1, by decide⟩ :=
      (hout_mc ⟨1, by decide⟩ (Or.inl (by decide))).trans (hOutRt ⟨1, by decide⟩ (by decide))
    have hS01_m : γ2m ⟨62, by decide⟩ = γ2m ⟨0, by decide⟩ * γ2m ⟨1, by decide⟩ := by
      rw [h0_m, h1_m, ← hOutRt ⟨0, by decide⟩ (by decide), ← hOutRt ⟨1, by decide⟩ (by decide)]
      exact (hout_mc ⟨62, by decide⟩ (Or.inl (by decide))).trans hS01_2
    have hCl_m (k : ℕ) (hk1 : 93 ≤ k) (hk2 : k < 103) : γ2m ⟨k, hk2⟩ = 0 :=
      (hout_mc _ (Or.inr (show 93 ≤ k by omega))).trans (hClean86 k (by omega) hk2)
    obtain ⟨hv_lac, hout_lac, hb2_2, hb3_2⟩ := pCompactAlt23_spec γ2m g hHot_m hS01_m
      (hCl_m 93 (by decide) _) (hCl_m 94 (by decide) _)
      (hCl_m 95 (by decide) _) (hCl_m 96 (by decide) _)
    let γ3 := pCompactAlt23.fwdBits γ2m
    have hCl_3 (k : ℕ) (hk1 : 98 ≤ k) (hk2 : k < 103) : γ3 ⟨k, hk2⟩ = 0 :=
      (hout_lac ⟨k, hk2⟩ (Or.inr (show 97 ≤ k by omega))).trans (hCl_m k (by omega) hk2)
    obtain ⟨hv_aff, hout_aff, hb6_aff, hb7_aff⟩ := affTop2Rev_spec γ3 g
      (fun i ↦ (hout_lac _ (Or.inl (show 16 + i.val < 93 by omega))).trans (hHot_m i))
      (hCl_3 98 (by decide) _) (hCl_3 99 (by decide) _) (hCl_3 100 (by decide) _)
    let γ4 := affTop2Rev.fwdBits γ3
    obtain ⟨hv_or, hout_or, hor101, hor102⟩ := mkOr2_spec γ4
      ((hout_aff _ (Or.inr (by decide))).trans (hCl_3 101 (by decide) _))
      ((hout_aff _ (Or.inr (by decide))).trans (hCl_3 102 (by decide) _))
    let γ5 := mkOr2.fwdBits γ4
    obtain ⟨hv_cp, hout_cp_f, _, hc12, hc13, hc14, hc15⟩ := alt4CopyRev_spec γ5
    refine ⟨Bool.and_eq_true_iff.mpr ⟨hv_mc, Bool.and_eq_true_iff.mpr ⟨hv_lac,
      Bool.and_eq_true_iff.mpr ⟨hv_aff, hv_or⟩⟩⟩, hv_cp, ?_⟩
    have hsp12 := localIdx12_split_of_ge (by decide) β
    have h12_mod := hsp12.2.1
    have h12_div := hsp12.2.2.1
    have hx_mod4 := hsp12.2.2.2.1
    let y : Fin 184 := ⟨4 * g.val + x % 4, by omega⟩
    let mk := pktKeepSel10
      (basisBits 10 ⟨(pi145CompactTable y).keep % 1024, Nat.mod_lt _ (by decide)⟩) (basisBits 4 c)
    have h92_4 : γ4 ⟨92, by decide⟩ = γ2 ⟨82, by decide⟩ + γ2 ⟨0, by decide⟩ * γ2 ⟨83, by decide⟩ +
        γ2 ⟨1, by decide⟩ * γ2 ⟨84, by decide⟩ + γ2 ⟨62, by decide⟩ * γ2 ⟨85, by decide⟩ :=
      ((hout_aff ⟨92, by decide⟩ (Or.inl (by decide))).trans
        (hout_lac ⟨92, by decide⟩ (Or.inl (by decide)))).trans h92_mc
    have hmk_4 : γ4 ⟨92, by decide⟩ = mk := by
      rw [h92_4, hS01_2, hOutRt ⟨0, by decide⟩ (by decide), hOutRt ⟨1, by decide⟩ (by decide),
        hγ2_eq, kLoad4Bits_82, kLoad4Bits_83, kLoad4Bits_84, kLoad4Bits_85,
        hS1_clean γ1 h1 82 (by decide) _, hS1_clean γ1 h1 83 (by decide) _,
        hS1_clean γ1 h1 84 (by decide) _, hS1_clean γ1 h1 85 (by decide) _,
        zero_add, zero_add, zero_add, zero_add, hkVal 0, hkVal 1, hkVal 2, hkVal 3]
      dsimp only [mk]
      rw [pktKeepSel10_eq_optFib]
      rcases coinOptFib c with _ | f
      · simp [b2z]
      · change b2z (keepRawBool 0 g f) +
            β ⟨0, by decide⟩ * b2z (xor (keepRawBool 0 g f) (keepRawBool 1 g f)) +
            β ⟨1, by decide⟩ * b2z (xor (keepRawBool 0 g f) (keepRawBool 2 g f)) +
            (β ⟨0, by decide⟩ * β ⟨1, by decide⟩) *
              b2z (xor (xor (keepRawBool 0 g f) (keepRawBool 1 g f))
                (xor (keepRawBool 2 g f) (keepRawBool 3 g f))) = _
        rw [anf2_xor4_eval (fun r ↦ keepRawBool r g f) (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)]
        dsimp only [keepRawBool]
        rw [b2z_z2b]
        exact congrArg (fun u : Fin 184 ↦
          basisBits 10 ⟨(pi145CompactTable u).keep % 1024, Nat.mod_lt _ (by decide)⟩ f)
          (Fin.ext (congrArg (4 * g.val + ·) hx_mod4.symm))
    have hanf := alt_basisBits_eq g (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
    have hy_top : (⟨4 * g.val + (bit01Nat (β ⟨0, by decide⟩) + 2 * bit01Nat (β ⟨1, by decide⟩)),
        y_anf_lt184 g (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)⟩ : Fin 184) = y :=
      Fin.ext (congrArg (4 * g.val + ·) hx_mod4.symm)
    dsimp only at hanf
    rw [hy_top] at hanf
    rcases hanf with ⟨ha7, ha6, ha3, ha2⟩
    have hb2_3 : γ3 ⟨93, by decide⟩ = basisBits 8 (altFin256_2 y) 2 := hb2_2.trans (by
      rw [h0_m, h1_m]
      exact ha2.symm)
    have hb3_3 : γ3 ⟨94, by decide⟩ = basisBits 8 (altFin256_2 y) 3 := hb3_2.trans ha3.symm
    have h1_3 : γ3 ⟨1, by decide⟩ = β ⟨1, by decide⟩ :=
      (hout_lac ⟨1, by decide⟩ (Or.inl (by decide))).trans h1_m
    have hb6_4 : γ4 ⟨99, by decide⟩ = basisBits 8 (altFin256_2 y) 6 := hb6_aff.trans (by
      rw [h1_3]
      exact ha6.symm)
    have hb7_4 : γ4 ⟨100, by decide⟩ = basisBits 8 (altFin256_2 y) 7 := hb7_aff.trans ha7.symm
    have hTbl (j : Fin 4) : (if alt4BoolTable (localIdx (QRegister.block 0 12 (by decide)) β).val
        j then (1 : ZMod 2) else 0) = loadedAlt4Bits y mk j := by
      rw [show alt4BoolTable (localIdx (QRegister.block 0 12 (by decide)) β).val j =
          (loadedAlt4Bits y mk j == 1) by
        unfold alt4BoolTable
        simp only [h12_mod, h12_div]
        rfl]
      rcases bit_cases (loadedAlt4Bits y mk j) with hv | hv <;> rw [hv] <;> decide
    let rAlt : QRegister 4 103 := QRegister.block 12 4 (by decide)
    change pPreRt.invBits (kLoad4Bits (pPreTail.invBits (alt4CopyRev.fwdBits γ5))) =
      xorRegBits β rAlt (alt4BoolTable (localIdx (QRegister.block 0 12 (by decide)) β).val)
    funext w
    by_cases hw12 : 12 ≤ w.val ∧ w.val < 16
    · obtain ⟨j, rfl⟩ : ∃ j : Fin 4, w = rAlt j := ⟨⟨w.val - 12, by omega⟩, Fin.ext (by
        dsimp only [rAlt]
        rw [qreg_block_apply]
        dsimp only
        omega)⟩
      have hj16 : (rAlt j).val < 16 := by
        dsimp only [rAlt]
        rw [qreg_block_apply]
        dsimp only
        omega
      have hkPres (ξ : BitAssignment 103) : kLoad4Bits ξ (rAlt j) = ξ (rAlt j) :=
        kLoad4Bits_other ξ _ (Or.inl (Nat.lt_of_lt_of_le hj16 (by decide)))
      have hβ_w : β (rAlt j) = γ5 (rAlt j) := ((htl_pres γ2 _ hw12).1.trans (hOutRt _ hj16)).symm
      rw [(hrt_pres _ _ hw12).2, hkPres, (htl_pres _ _ hw12).2,
        SelectSwapQROM.xorRegBits_apply_reg, hTbl j, hβ_w]
      have h92_5 : γ5 ⟨92, by decide⟩ = mk := (hout_or _ (by decide)).trans hmk_4
      have h93_5 : γ5 ⟨93, by decide⟩ = basisBits 8 (altFin256_2 y) 2 :=
        (hout_or _ (by decide)).trans ((hout_aff _ (Or.inl (by decide))).trans hb2_3)
      have h94_5 : γ5 ⟨94, by decide⟩ = basisBits 8 (altFin256_2 y) 3 :=
        (hout_or _ (by decide)).trans ((hout_aff _ (Or.inl (by decide))).trans hb3_3)
      have h101_5 : γ5 ⟨101, by decide⟩ = (1 + mk) * basisBits 8 (altFin256_2 y) 6 :=
        hor101.trans (by rw [hmk_4, hb6_4])
      have h102_5 : γ5 ⟨102, by decide⟩ = (1 + mk) * basisBits 8 (altFin256_2 y) 7 :=
        hor102.trans (by rw [hmk_4, hb7_4])
      let sL := loadedAlt4Bits y mk
      clear hw12 hj16 hkPres hβ_w
      fin_cases j
      · change alt4CopyRev.fwdBits γ5 ⟨12, by decide⟩ = γ5 ⟨12, by decide⟩ + sL 0
        rw [hc12, h93_5]
        simp [sL, loadedAlt4Bits, ret4Idx]
      · change alt4CopyRev.fwdBits γ5 ⟨13, by decide⟩ = γ5 ⟨13, by decide⟩ + sL 1
        rw [hc13, h94_5]
        simp [sL, loadedAlt4Bits, ret4Idx]
      · change alt4CopyRev.fwdBits γ5 ⟨14, by decide⟩ = γ5 ⟨14, by decide⟩ + sL 2
        rw [hc14, h92_5, h101_5, add_assoc]
        simp [sL, loadedAlt4Bits, ret4Idx]
      · change alt4CopyRev.fwdBits γ5 ⟨15, by decide⟩ = γ5 ⟨15, by decide⟩ + sL 3
        rw [hc15, h92_5, h102_5, add_assoc]
        simp [sL, loadedAlt4Bits, ret4Idx]
    · have hw_out : w.val < 12 ∨ 16 ≤ w.val := by omega
      rw [SelectSwapQROM.xorRegBits_apply_of_not_mem _ _ _ _
        (not_mem_block (by decide) w hw_out), hrt_inv_ext _ _ (kLoad4Bits_agreeOut12_16
          (htl_inv_ext (alt4CopyRev.fwdBits γ5) γ5 hout_cp_f)) w hw_out]
      exact congrFun (congrArg (fun u ↦ pPreRt.invBits (kLoad4Bits u))
        (pPreTail.invBits_fwdBits γ2)) w
  let S3 : BitAssignment 103 → Bool := fun ε ↦ S2 (pPreTail.invBits ε)
  have htrTail : TransRealizes v S2 S3 pPreTail.toCircuit.eval
      (Lac2Folded184Select.revComputeDyn pPreTail) :=
    TransRealizes.computeDyn v pPreTail S2 fun γ2 h2 ↦ (hTailSpec γ2 h2).1
  have hS3_eq : (fun δ ↦ S3 (alt4CopyRev.invBits δ)) = S3 := by
    funext δ
    dsimp only [S3, S2, S1]
    have h3_ext := hrt_inv_ext _ _ (kLoad4Bits_agreeOut12_16
      (htl_inv_ext (alt4CopyRev.invBits δ) δ (alt4CopyRev_spec δ).2.2.1))
    rw [Bool.eq_iff_iff, hS0_iff, hS0_iff]
    exact ⟨fun h j ↦ (h3_ext (rScr87 j) (Or.inr (by simp [rScr87]))).symm.trans (h j),
      fun h j ↦ (h3_ext (rScr87 j) (Or.inr (by simp [rScr87]))).trans (h j)⟩
  have htrCopy : TransRealizes v S3 S3 alt4CopyRev.toCircuit.eval
      (Lac2Folded184Select.revComputeDyn alt4CopyRev) :=
    (TransRealizes.computeDyn v alt4CopyRev S3 fun ε hε ↦ by
      have h := (hTailSpec (pPreTail.invBits ε) hε).2.1
      rwa [pPreTail.fwdBits_invBits] at h).congr_pred rfl hS3_eq
  have htrUnTail : TransRealizes v S3 S2 pPreTail.toCircuit.eval⁻¹
      (Lac2Folded184Select.revUncomputeDyn v pPreTail) :=
    TransRealizes.uncomputeDyn v pPreTail S2 fun γ2 h2 ↦ (hTailSpec γ2 h2).1
  have htrAll := (((((htrRt.seq htrLoad).seq htrTail).seq htrCopy).seq htrUnTail).seq
    (htrUnload.seq htrUnRt))
  have hTgtKet (ξ : BitAssignment 103) :
      U_tgt.1.mulVec (ket ξ) = ket (xorRegBits ξ (QRegister.block 12 4 (by decide))
        (alt4BoolTable (localIdx (QRegister.block 0 12 (by decide)) ξ).val)) := by
    let idx := localIdx (QRegister.block 0 12 (by decide)) ξ
    have hr16 : rAct16 = (QRegister.block 0 12 (by decide)).concat
        (QRegister.block 12 4 (by decide)) (by decide) :=
      CoherentAlias.qreg_ext fun k ↦ by fin_cases k <;> decide
    dsimp only [U_tgt]
    rw [hr16, embed_xorLoadUnitary_mulVec_ket]
    congr 2
    funext j
    change decide (idx.val < 4096 ∧ alt4BoolTable idx.val j = true) = alt4BoolTable idx.val j
    simp
  have hMapTgt : U_tgt.1 * GroupUnary.predProj S0 = GroupUnary.predProj S0 * U_tgt.1 := by
    refine ketPerm_mul_predProj U_tgt (fun ξ ↦ xorRegBits ξ (QRegister.block 12 4 (by decide))
        (alt4BoolTable (localIdx (QRegister.block 0 12 (by decide)) ξ).val))
      hTgtKet S0 S0 fun β ↦ ?_
    rw [Bool.eq_iff_iff, hS0_iff, hS0_iff]
    have hnot (j : Fin 87) :
        rScr87 j ∉ (QRegister.block 12 4 (by decide) : QRegister 4 103).image :=
      not_mem_block (by decide) (rScr87 j) (Or.inr (by
        dsimp only [rScr87]
        rw [qreg_block_apply]
        dsimp only
        omega))
    exact ⟨fun h j ↦ (xorRegBits_apply_of_not_mem _ _ _ _ (hnot j)).trans (h j),
      fun h j ↦ (xorRegBits_apply_of_not_mem _ _ _ _ (hnot j)).symm.trans (h j)⟩
  refine htrAll.congr_unitary hMapTgt <| SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, predProj_mulVec_ket]
  cases hS : S0 β
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mulVec_zero]
  · simp only [↓reduceIte]
    have hket : ket = GroupUnary.ket (N := 103) := rfl
    have hket_sdk : ket = Solution.XMeasCircuit.ket (n := 103) := rfl
    have h2 : S2 (kLoad4Bits (pPreRt.fwdBits β)) = true := by
      dsimp only [S2, S1]
      rwa [kLoad4Bits_invol, pPreRt.invBits_fwdBits]
    have hSpec := (hTailSpec (kLoad4Bits (pPreRt.fwdBits β)) h2).2.2
    rw [kLoad4Bits_invol, pPreRt.invBits_fwdBits] at hSpec
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [hket, pPreRt.toCircuit_mulVec_ket, ← hket, hket_sdk, hUk4_ket, ← hket_sdk,
      hket, pPreTail.toCircuit_mulVec_ket, alt4CopyRev.toCircuit_mulVec_ket,
      revCompute_eval_inv_mulVec_ket, ← hket, hket_sdk, hUk4_ket, ← hket_sdk,
      hket, revCompute_eval_inv_mulVec_ket, ← hket, hSpec, hTgtKet β]
attribute [irreducible] keepPolyBool keepPhi kLoad4C kUnload4Dyn kLoad4Bits pPreTail

/-! ### `152-T` (`82`-Scratch) X-Measurement Phase Leaf (`hGadgetLeaf94Dyn`) -/
theorem b2z_eq (b : Bool) : StepOuter8Pi145Outer.b2z b = b2z b := rfl
theorem b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by cases a <;> rfl
theorem b2z_beq_one (u : ZMod 2) : b2z (u == 1) = u := by
  rcases bit_cases u with rfl | rfl <;> decide
/-- `46`-wire one-hot group register `12..57` on `N = 94`. -/
abbrev rHot94 : QRegister 46 94 := QRegister.block 12 46 (by decide)
/-- `10`-wire coin-fiber register `62..71` on `N = 94`. -/
abbrev rFib94 : QRegister 10 94 := QRegister.block 62 10 (by decide)
theorem rHot94_ne (w : Wire 94) (hw : 58 ≤ w.val) (i : Fin 46) : rHot94 i ≠ w :=
  block_ne_of_ge (by decide) w hw i
theorem rFib94_ne (w : Wire 94) (hw : 72 ≤ w.val) (j : Fin 10) : rFib94 j ≠ w :=
  block_ne_of_ge (by decide) w hw j
theorem rHotFib94_ne (i : Fin 46) (j : Fin 10) : rHot94 i ≠ rFib94 j :=
  block_ne_block (by decide) (by decide) (Or.inl (by decide)) i j
theorem rHotCtx94_ne (i : Fin 46) (u : Fin 2) :
    rHot94 i ≠ (QRegister.block 0 2 (by decide) : QRegister 2 94) u :=
  block_ne_block (by decide) (by decide) (Or.inr (by decide)) i u
/-- Raw `(1 + alt_6 / alt_7) * keep` product at `y = 4 * g + r` for outcome `m`. -/
def leafQRaw (m : Fin (2 ^ 4)) (r : Fin 4) (g : Fin 46) (f : Fin 10) : Bool :=
  let y : Fin 184 := ⟨4 * g.val + r.val, by omega⟩
  (xor ((basisBits 4 m 2 == 1) && !(basisBits 8 (altFin256_2 y) 6 == 1))
    ((basisBits 4 m 3 == 1) && !(basisBits 8 (altFin256_2 y) 7 == 1))) && keepRawBool r g f
/-- ANF polynomial planes `0..3` over `(x₀, x₁)` of `leafQRaw m`. -/
def leafQPoly (m : Fin (2 ^ 4)) (r : Fin 4) (g : Fin 46) (f : Fin 10) : Bool :=
  match r.val with
  | 0 => leafQRaw m 0 g f
  | 1 => xor (leafQRaw m 0 g f) (leafQRaw m 1 g f)
  | 2 => xor (leafQRaw m 0 g f) (leafQRaw m 2 g f)
  | _ => xor (xor (leafQRaw m 0 g f) (leafQRaw m 1 g f))
      (xor (leafQRaw m 2 g f) (leafQRaw m 3 g f))
/-- Combined `(g, optF)` carry-cancellation and `r = 0` constant plane for `hGadgetLeaf94Dyn`. -/
def leafPhi (m : Fin (2 ^ 4)) (g : Fin 46) (optF : Option (Fin 10)) : Bool :=
  xor (xor (quad5CarryBool (idEnv56 g optF) (leafQPoly m 1))
        (quad5CarryBool (idEnv56 g optF) (leafQPoly m 2)))
    (xor (quad5CarryBool (idEnv56 g optF) (leafQPoly m 3)) (optF.elim false (leafQPoly m 0 g)))
/-- `0-T` `(Z, CZ)` phase sweep applying `p₀(y)` over `(rHot94, (x₀, x₁))`. -/
def p0PhaseC (m : Fin (2 ^ 4)) : Circuit 94 :=
  hotCtxPhaseLoop 2 46 rHot94 (QRegister.block 0 2 (by decide)) rHotCtx94_ne
    (fun g ↦ b2z (leafP0B0 m g))
    (fun g u ↦ if u.val = 0 then b2z (leafP0B1 m g) else b2z (leafP0B2 m g)) 46 le_rfl
@[simp] theorem count_p0PhaseC_toff (m : Fin (2 ^ 4)) : (p0PhaseC m).count .TOFF = 0 :=
  count_hotCtxPhaseLoop_toff2 _ _ _ _ _ 46 le_rfl
@[simp] theorem count_p0PhaseC_t (m : Fin (2 ^ 4)) : (p0PhaseC m).count .T = 0 :=
  count_hotCtxPhaseLoop_t2 _ _ _ _ _ 46 le_rfl
/-- `0-T` combined `(rHot94, rFib94)` and `(rHot94, (x₀, x₁))` phase fixup on `N = 94`. -/
def leafMidPhaseC (m : Fin (2 ^ 4)) : Circuit 94 :=
  fix46x10C rHot94 rFib94 rHotFib94_ne (leafPhi m) ;;ᶜ p0PhaseC m
@[simp] theorem count_leafMidPhaseC_toff (m : Fin (2 ^ 4)) : (leafMidPhaseC m).count .TOFF = 0 := by
  simp [leafMidPhaseC]
@[simp] theorem count_leafMidPhaseC_t (m : Fin (2 ^ 4)) : (leafMidPhaseC m).count .T = 0 := by
  simp [leafMidPhaseC]
/-- `12-T` (`0 TOFF`) Hadamard-gadget load + `CZ` + X-measurement unload on wire `78`. -/
def quad5StepDyn {Var : Type} (v : Var) (M : Fin 46 → Fin 10 → Bool)
    (ctrl : Wire 94) (hctrl : ctrl ≠ ⟨78, by decide⟩) : DynamicCircuit Var 94 :=
  .seq (.circuit (quad5GadC ⟨78, by decide⟩ rHot94 rFib94 (rHot94_ne _ (by decide))
      (rFib94_ne _ (by decide)) M ;;ᶜ SelectSwapQROM.czCircuit ctrl ⟨78, by decide⟩ hctrl))
    (xMeasUnloadWireDyn v ⟨78, by decide⟩ (.circuit (quad5FixC ⟨78, by decide⟩ rHot94 rFib94
      (rHot94_ne _ (by decide)) (rFib94_ne _ (by decide)) M)))
@[simp] theorem count_quad5StepDyn_toff {Var : Type} (v : Var) (M : Fin 46 → Fin 10 → Bool)
    (ctrl : Wire 94) (hctrl : ctrl ≠ ⟨78, by decide⟩) :
    (quad5StepDyn v M ctrl hctrl).count .TOFF = 0 := by
  simp [quad5StepDyn, DynamicCircuit.count, count_xMeasUnloadWireDyn_toff,
    SelectSwapQROM.count_czCircuit_toff]
@[simp] theorem count_quad5StepDyn_t {Var : Type} (v : Var) (M : Fin 46 → Fin 10 → Bool)
    (ctrl : Wire 94) (hctrl : ctrl ≠ ⟨78, by decide⟩) :
    (quad5StepDyn v M ctrl hctrl).count .T = 12 := by
  simp [quad5StepDyn, DynamicCircuit.count, count_xMeasUnloadWireDyn_t,
    SelectSwapQROM.count_czCircuit_t]
theorem quad5StepDyn_transRealizes {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var)
    (M : Fin 46 → Fin 10 → Bool) (ctrl : Wire 94) (hctrl : ctrl ≠ ⟨78, by decide⟩)
    (S1 : BitAssignment 94 → Bool) (h78 : ∀ γ, S1 γ = true → γ ⟨78, by decide⟩ = 0) :
    TransRealizes v S1 S1 (phaseFlipUnitary fun γ ↦
      b2z (quad5CarryBool (env56 rHot94 rFib94 γ) M) + γ ctrl * quad5Bit rHot94 rFib94 M γ)
      (quad5StepDyn v M ctrl hctrl) := by
  let q78 : Wire 94 := ⟨78, by decide⟩
  let fM := quad5Bit rHot94 rFib94 M
  have hfM (ξ : BitAssignment 94) (val : ZMod 2) : fM (update ξ q78 val) = fM ξ :=
    quad5Bit_upd rHot94 rFib94 (rHot94_ne q78 (by decide)) (rFib94_ne q78 (by decide)) M ξ val
  let φM (γ : BitAssignment 94) : ZMod 2 :=
    b2z (quad5CarryBool (env56 rHot94 rFib94 γ) M) + γ ctrl * fM γ
  have hφM (ξ : BitAssignment 94) (val : ZMod 2) : φM (update ξ q78 val) = φM ξ := by
    dsimp only [φM]
    rw [env56_upd rHot94 rFib94 (rHot94_ne q78 (by decide)) (rFib94_ne q78 (by decide)) ξ val,
      update_of_ne hctrl, hfM]
  let U_x := xorWireUnitary q78 fM hfM
  let U_pre := U_x * phaseFlipUnitary φM
  have hUpre_ket (ξ : BitAssignment 94) : U_pre.1.mulVec (Solution.XMeasCircuit.ket ξ) =
      bitSign (φM ξ) • Solution.XMeasCircuit.ket (update ξ q78 (ξ q78 + fM ξ)) := by
    dsimp only [U_pre, U_x]
    rw [Submonoid.coe_mul, ← mulVec_mulVec, phaseFlipUnitary_mulVec_ket, bitSign_sdk_eq,
      mulVec_smul, xorWireUnitary_mulVec_ket]
  have hUx_sq : U_x * U_x = 1 := Subtype.ext <| Solution.XMeasCircuit.matrix_ext_ket fun ξ ↦ by
    change (U_x.1 * U_x.1).mulVec _ = (1 : Operator _).mulVec _
    rw [← mulVec_mulVec, xorWireUnitary_mulVec_ket, xorWireUnitary_mulVec_ket, one_mulVec,
      update_self, hfM, update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, update_eq_self]
  have hUpre_sq : U_pre * U_pre = 1 := Subtype.ext <| Solution.XMeasCircuit.matrix_ext_ket fun ξ ↦
      by
    change (U_pre.1 * U_pre.1).mulVec _ = (1 : Operator _).mulVec _
    rw [← mulVec_mulVec, hUpre_ket, mulVec_smul, hUpre_ket, smul_smul, ← bitSign_add, hφM,
      CharTwo.add_self_eq_zero, bitSign_zero2, one_smul, update_self, hfM, update_idem,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, update_eq_self, one_mulVec]
  let S_post : BitAssignment 94 → Bool := fun δ ↦ S1 (update δ q78 (δ q78 + fM δ))
  have hUpre_map : U_pre.1 * GroupUnary.predProj S1 = GroupUnary.predProj S_post * U_pre.1 :=
    SelectSwapQROM.matrix_ext_ket fun ξ ↦ by
      have hSp_eq : S_post (update ξ q78 (ξ q78 + fM ξ)) = S1 ξ := by
        dsimp only [S_post]
        rw [update_self, hfM, update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero,
          update_eq_self]
      rw [← mulVec_mulVec, ← mulVec_mulVec, predProj_mulVec_ket, ← ket_sdk_eq, hUpre_ket,
        ket_sdk_eq, mulVec_smul, predProj_mulVec_ket, hSp_eq]
      by_cases hS : S1 ξ = true
      · rw [ite_eq_left hS, ite_eq_left hS, ← ket_sdk_eq, hUpre_ket, ket_sdk_eq]
      · rw [ite_eq_right hS, ite_eq_right hS, mulVec_zero, smul_zero]
  have htrPre : TransRealizes v S1 S_post U_pre
      (.circuit (quad5GadC q78 rHot94 rFib94 (rHot94_ne _ (by decide)) (rFib94_ne _ (by decide))
        M ;;ᶜ SelectSwapQROM.czCircuit ctrl q78 hctrl)) := by
    refine TransRealizes.of_circuit_invUnitary v _ U_pre (by
        simp only [Circuit.count_seq, count_quad5GadC_toff, SelectSwapQROM.count_czCircuit_toff])
      hUpre_sq hUpre_map <| Solution.XMeasCircuit.matrix_ext_ket fun γ ↦ ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, ket_sdk_eq γ, predProj_mulVec_ket]
    by_cases hS : S1 γ = true
    · rw [ite_eq_left hS, ← ket_sdk_eq γ, hUpre_ket, eval_seq_mv,
        ket_quad5GadC_zero _ _ _ _ _ _ γ (h78 γ hS), mulVec_smul, ket_sdk_eq _,
        SelectSwapQROM.ket_czCircuit, ← ket_sdk_eq _, smul_smul, ← bitSign_add,
        update_of_ne hctrl, update_self, h78 γ hS]
      dsimp only [φM, fM]
      rw [zero_add]
    · rw [ite_eq_right hS, mulVec_zero, mulVec_zero]
  have htrUn := TransRealizes.xMeasUnloadWire v q78 fM hfM S1 h78
    (quad5FixC q78 rHot94 rFib94 (rHot94_ne _ (by decide)) (rFib94_ne _ (by decide)) M)
    (count_quad5FixC_toff ..) (ket_quad5FixC_zero _ _ _ _ _ _)
  have hSeq := htrPre.seq htrUn
  have hMul : U_x * U_pre = phaseFlipUnitary φM := by
    dsimp only [U_pre]
    rw [← mul_assoc, hUx_sq, one_mul]
  rwa [hMul] at hSeq
/-- Combined router `wHot46Rev 12 ;; cFib11Rev 62` on `N = 94`. -/
def pLeafRt : GroupUnary.RevCompute 94 :=
  (wHot46Rev 12 (by decide) (by decide)).seq (cFib11Rev 62 (by decide) (by decide))
/-- `152-T` (`0 TOFF`, `82`-scratch) Hadamard-gadget X-measurement phase leaf for
`alt4BoolTable`. -/
def hGadgetLeaf94Dyn {Var : Type} (v : Var) (m : Fin (2 ^ 4)) : DynamicCircuit Var 94 :=
  .seq (.seq (.seq (.seq (.seq
    (.seq (wHot46FwdDyn v 12 (by decide) (by decide)) (cFib11FwdDyn v 62 (by decide) (by decide)))
    (quad5StepDyn v (leafQPoly m 1) ⟨0, by decide⟩ (by decide)))
    (quad5StepDyn v (leafQPoly m 2) ⟨1, by decide⟩ (by decide)))
    (quad5StepDyn v (leafQPoly m 3) ⟨58, by decide⟩ (by decide))) (.circuit (leafMidPhaseC m)))
    (Lac2Folded184Select.revUncomputeDyn v pLeafRt)
attribute [irreducible] hGadgetLeaf94Dyn
@[simp] theorem countHGadgetLeaf94Dyn_toff {Var : Type} (v : Var) (m : Fin (2 ^ 4)) :
    (hGadgetLeaf94Dyn v m).count .TOFF = 0 := by
  unfold hGadgetLeaf94Dyn
  simp [DynamicCircuit.count]
@[simp] theorem countHGadgetLeaf94Dyn_t {Var : Type} (v : Var) (m : Fin (2 ^ 4)) :
    (hGadgetLeaf94Dyn v m).count .T = 152 := by
  unfold hGadgetLeaf94Dyn
  simp [DynamicCircuit.count]
theorem pLeafRt_eq : pLeafRt =
    (wHot46Rev 12 (by decide) (by decide)).seq (cFib11Rev 62 (by decide) (by decide)) := rfl
attribute [irreducible] pLeafRt
theorem cleanRealizesHGadgetLeaf94Dyn {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var)
    (m : Fin (2 ^ 4)) : Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 12 (by decide) : QRegister 12 94)
      (QRegister.block 12 82 (by decide) : QRegister 82 94)
      (diagPhaseUnitary 12 4096 (parityPhaseTable 4 alt4BoolTable m))
      (hGadgetLeaf94Dyn v m) := by
  let rAct12 : QRegister 12 94 := QRegister.block 0 12 (by decide)
  let rScr82 : QRegister 82 94 := QRegister.block 12 82 (by decide)
  let U_tgt := rAct12.embedUnitary (diagPhaseUnitary 12 4096 (parityPhaseTable 4 alt4BoolTable m))
  have hDec {p : Prop} {inst : Decidable p} : @decide p inst = true ↔ p :=
    @decide_eq_true_iff p inst
  suffices hMain : ∀ (S0 : BitAssignment 94 → Bool),
      (∀ β, S0 β = true ↔ ∀ j : Fin 82, β (rScr82 j) = 0) →
      TransRealizes v S0 S0 U_tgt (hGadgetLeaf94Dyn v m) by
    exact cleanRealizes_of_transRealizes rAct12 rScr82 (by decide) (hMain _ fun _ ↦ hDec)
  intro S0 hS0_iff
  unfold hGadgetLeaf94Dyn
  let S1 : BitAssignment 94 → Bool := fun γ ↦ S0 (pLeafRt.invBits γ)
  obtain ⟨htrRt, htrUnRt, hCl94, hLeafSpec⟩ :=
    hotFibRouter_spec (N := 94) 12 62 58 82 rfl rfl (by decide) (by decide) (by decide)
      (by decide) v pLeafRt pLeafRt_eq S0 fun β hS j ↦ (hS0_iff β).mp hS j
  have h78 (γ1 : BitAssignment 94) (h1 : S1 γ1 = true) : γ1 ⟨78, by decide⟩ = 0 :=
    hCl94 γ1 h1 78 (by decide) (by decide)
  have htrQ1 := quad5StepDyn_transRealizes v (leafQPoly m 1) ⟨0, by decide⟩ (by decide) S1 h78
  have htrQ2 := quad5StepDyn_transRealizes v (leafQPoly m 2) ⟨1, by decide⟩ (by decide) S1 h78
  have htrQ3 := quad5StepDyn_transRealizes v (leafQPoly m 3) ⟨58, by decide⟩ (by decide) S1 h78
  have htrMid : TransRealizes v S1 S1 (leafMidPhaseC m).eval (.circuit (leafMidPhaseC m)) :=
    TransRealizes.of_circuit v (leafMidPhaseC m) (count_leafMidPhaseC_toff m)
      (diagScalar_mul_predProj (leafMidPhaseC m).eval _ (fun γ ↦ by
        rw [leafMidPhaseC, SelectSwapQROM.eval_seq_mulVec, fix46x10C_def, p0PhaseC,
          ket_hotCtxPhaseLoop, mulVec_smul, ket_hotCtxPhaseLoop, smul_smul]) S1)
  have htrAll := (((((htrRt.seq htrQ1).seq htrQ2).seq htrQ3).seq htrMid).seq htrUnRt)
  have hMapTgt : U_tgt.1 * GroupUnary.predProj S0 = GroupUnary.predProj S0 * U_tgt.1 :=
    diagScalar_mul_predProj U_tgt _ (fun γ ↦ embed_diagPhaseUnitary_mulVec_ket rAct12 _ γ) S0
  refine htrAll.congr_unitary hMapTgt <| SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, predProj_mulVec_ket]
  cases hS : S0 β
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mulVec_zero]
  · simp only [↓reduceIte]
    let γ1 := pLeafRt.fwdBits β
    obtain ⟨_, hmod256, hdiv256, hxrem, _⟩ := localIdx12_split_of_ge (by decide) β
    let idx12 := (localIdx rAct12 β).val
    let x := (localIdx (QRegister.block 0 8 (by decide)) β).val
    let g := DyadicXMeasPrepOut13.effGroup (x / 4)
    let c := localIdx (QRegister.block 8 4 (by decide)) β
    obtain ⟨hOut1, h58_0, hHot0, hFib0, hEnv0⟩ := hLeafSpec β hS
    have h0_1 : γ1 ⟨0, by decide⟩ = β ⟨0, by decide⟩ := hOut1 ⟨0, by decide⟩ (by decide)
    have h1_1 : γ1 ⟨1, by decide⟩ = β ⟨1, by decide⟩ := hOut1 ⟨1, by decide⟩ (by decide)
    have h58_1 : γ1 ⟨58, by decide⟩ = β ⟨0, by decide⟩ * β ⟨1, by decide⟩ := h58_0
    have hHot1 (i : Fin 46) : γ1 (rHot94 i) = if i = g then 1 else 0 := hHot0 i
    have hFib1 (f : Fin 10) : γ1 (rFib94 f) = b2z (coinOptFib c == some f) := hFib0 f
    have hEnv1 : env56 rHot94 rFib94 γ1 = idEnv56 g (coinOptFib c) := hEnv0
    have hqBit (r : Fin 4) : quad5Bit rHot94 rFib94 (leafQPoly m r) γ1 =
        b2z ((coinOptFib c).elim false (leafQPoly m r g)) :=
      quad5Bit_eq_of_env rHot94 rFib94 (leafQPoly m r) γ1 g (coinOptFib c) hEnv1
    let y : Fin 184 := ⟨4 * g.val + x % 4, by omega⟩
    let kv : Fin 1024 := ⟨(pi145CompactTable y).keep % 1024, Nat.mod_lt _ (by decide)⟩
    let mk : ZMod 2 := pktKeepSel10 (basisBits 10 kv) (basisBits 4 c)
    have hanf := alt_basisBits_eq g (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
    have hy_top : (⟨4 * g.val + (bit01Nat (β ⟨0, by decide⟩) + 2 * bit01Nat (β ⟨1, by decide⟩)),
        y_anf_lt184 g (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)⟩ : Fin 184) = y :=
      Fin.ext (congrArg (4 * g.val + ·) hxrem.symm)
    dsimp only at hanf
    rw [hy_top] at hanf
    simp only [b2z_eq] at hanf
    rcases hanf with ⟨ha7, ha6, ha3, ha2⟩
    have hsum4 (f : Fin 4 → ZMod 2) : ∑ j : Fin 4, f j = f 0 + f 1 + f 2 + f 3 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change f 0 + (f 1 + (f 2 + f 3)) = _
      ring
    have hp0_ket : (p0PhaseC m).eval.1.mulVec (ket γ1) =
        bitSign (∑ j : Fin 4, basisBits 4 m j * basisBits 8 (altFin256_2 y) (ret4Idx j)) •
          ket γ1 := by
      rw [p0PhaseC, ket_hotCtxPhaseLoop]
      refine congrArg (· • ket γ1) (congrArg bitSign ?_)
      rw [Finset.sum_eq_single g]
      · dsimp only
        rw [Fin.eta, hHot1 g, ite_eq_left rfl, one_mul, Fin.sum_univ_two]
        simp only [Fin.val_zero, Fin.val_one, ↓reduceIte]
        change b2z (leafP0B0 m g) + (b2z (leafP0B1 m g) * γ1 ⟨0, by decide⟩ +
          b2z (leafP0B2 m g) * γ1 ⟨1, by decide⟩) = _
        rw [h0_1, h1_1, hsum4]
        simp only [leafP0B0, leafP0B1, leafP0B2, b2z_xor, b2z_and, b2z_beq_one,
          ret4Idx, ha2, ha3, ha6, ha7]
        ring
      · intro i _ hi
        dsimp only
        rw [Fin.eta, hHot1 i, ite_eq_right hi, zero_mul]
      · exact fun h ↦ False.elim (h (Finset.mem_univ g))
    have hq_sum : (b2z (quad5CarryBool (idEnv56 g (coinOptFib c)) (leafQPoly m 1)) +
          β ⟨0, by decide⟩ * b2z ((coinOptFib c).elim false (leafQPoly m 1 g))) +
        (b2z (quad5CarryBool (idEnv56 g (coinOptFib c)) (leafQPoly m 2)) +
          β ⟨1, by decide⟩ * b2z ((coinOptFib c).elim false (leafQPoly m 2 g))) +
        (b2z (quad5CarryBool (idEnv56 g (coinOptFib c)) (leafQPoly m 3)) +
          (β ⟨0, by decide⟩ * β ⟨1, by decide⟩) *
            b2z ((coinOptFib c).elim false (leafQPoly m 3 g))) +
        b2z (leafPhi m g (coinOptFib c)) =
        mk * (basisBits 4 m 2 * (1 + basisBits 8 (altFin256_2 y) 6) +
          basisBits 4 m 3 * (1 + basisBits 8 (altFin256_2 y) 7)) := by
      have hz7 (a1 b1 a2 b2 a3 b3 a0 : ZMod 2) :
          (a1 + b1) + (a2 + b2) + (a3 + b3) + ((a1 + a2) + (a3 + a0)) =
            a0 + b1 + b2 + b3 := by
        ring_nf
        simp [show (2 : ZMod 2) = 0 from rfl]
      refine Eq.trans (b := b2z ((coinOptFib c).elim false (leafQPoly m 0 g)) +
          β ⟨0, by decide⟩ * b2z ((coinOptFib c).elim false (leafQPoly m 1 g)) +
          β ⟨1, by decide⟩ * b2z ((coinOptFib c).elim false (leafQPoly m 2 g)) +
          (β ⟨0, by decide⟩ * β ⟨1, by decide⟩) *
            b2z ((coinOptFib c).elim false (leafQPoly m 3 g))) (by
          simp only [leafPhi, b2z_xor]
          exact hz7 _ _ _ _ _ _ _) ?_
      dsimp only [mk]
      rw [pktKeepSel10_eq_optFib]
      rcases coinOptFib c with _ | f
      · simp [b2z]
      · refine Eq.trans (anf2_xor4_eval (fun r ↦ leafQRaw m r g f)
          (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)) ?_
        have hk_raw : b2z (keepRawBool ⟨bit01Nat (β ⟨0, by decide⟩) +
            2 * bit01Nat (β ⟨1, by decide⟩), bit01_pair_lt4 (β ⟨0, by decide⟩)
            (β ⟨1, by decide⟩)⟩ g f) = basisBits 10 kv f := by
          dsimp only [keepRawBool, kv]
          rw [b2z_z2b]
          exact congrArg (fun u : Fin 184 ↦
            basisBits 10 ⟨(pi145CompactTable u).keep % 1024, Nat.mod_lt _ (by decide)⟩ f) hy_top
        dsimp only [leafQRaw]
        rw [b2z_and, hk_raw, hy_top, b2z_xor, b2z_and, b2z_and, b2z_not, b2z_not,
          b2z_beq_one, b2z_beq_one, b2z_beq_one, b2z_beq_one]
        exact mul_comm _ _
    have hTbl (j : Fin 4) :
        (if alt4BoolTable idx12 j then (1 : ZMod 2) else 0) = loadedAlt4Bits y mk j := by
      rw [show alt4BoolTable idx12 j = (loadedAlt4Bits y mk j == 1) by
        unfold alt4BoolTable
        dsimp only [idx12, rAct12]
        simp only [hmod256, hdiv256]
        rfl]
      rcases bit_cases (loadedAlt4Bits y mk j) with hv | hv <;> rw [hv] <;> decide
    have hParityEq : (∑ j : Fin 4, basisBits 4 m j * basisBits 8 (altFin256_2 y) (ret4Idx j)) +
          mk * (basisBits 4 m 2 * (1 + basisBits 8 (altFin256_2 y) 6) +
            basisBits 4 m 3 * (1 + basisBits 8 (altFin256_2 y) 7)) =
        ((if parityPhaseTable 4 alt4BoolTable m idx12 then 1 else 0) : ZMod 2) := by
      rw [parityPhaseTable_zmod2 4 alt4BoolTable m idx12]
      simp_rw [hTbl]
      rw [hsum4, hsum4]
      simp only [loadedAlt4Bits, ret4Idx, Fin.val_zero, Fin.val_one,
        show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
        show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
        show ¬ (2 : ℕ) < 2 by decide, show ¬ (3 : ℕ) < 2 by decide, ↓reduceIte]
      ring
    have hket_pf (φ : BitAssignment 94 → ZMod 2) :
        (phaseFlipUnitary φ).1.mulVec (ket γ1) = bitSign (φ γ1) • ket γ1 := by
      rw [← ket_sdk_eq γ1, phaseFlipUnitary_mulVec_ket, bitSign_sdk_eq, ket_sdk_eq γ1]
    have hket_fix : (fix46x10C rHot94 rFib94 rHotFib94_ne (leafPhi m)).eval.1.mulVec (ket γ1) =
        bitSign (b2z (leafPhi m g (coinOptFib c))) • ket γ1 := by
      rw [← ket_sdk_eq γ1, ket_fix46x10C_sector _ _ _ _ γ1 g (coinOptFib c) hHot1 hFib1,
        ket_sdk_eq γ1]
    have hket_unrt : pLeafRt.toCircuit.eval⁻¹.1.mulVec (ket γ1) = ket β := by
      change pLeafRt.toCircuit.eval⁻¹.1.mulVec (GroupUnary.ket (pLeafRt.fwdBits β)) = _
      rw [revCompute_eval_inv_mulVec_ket, pLeafRt.invBits_fwdBits]
    have hrt_ket : pLeafRt.toCircuit.eval.1.mulVec (ket β) = ket γ1 :=
      pLeafRt.toCircuit_mulVec_ket β
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, leafMidPhaseC,
      SelectSwapQROM.eval_seq_mulVec]
    simp only [hrt_ket, hket_pf, hket_fix, hp0_ket, hket_unrt, mulVec_smul]
    rw [hqBit 1, hqBit 2, hqBit 3, hEnv1, h0_1, h1_1, h58_1]
    simp only [smul_smul, ← bitSign_add]
    rw [embed_diagPhaseUnitary_mulVec_ket,
      show ((basisBits 12).symm (fun i ↦ β (rAct12 i))).val = idx12 from rfl]
    refine congrArg (· • ket β) (Eq.trans
      (b := bitSign (if parityPhaseTable 4 alt4BoolTable m idx12 then 1 else 0))
      (congrArg bitSign (by
        rw [← hParityEq, ← hq_sum]
        ring)) ?_)
    have hlt12 : idx12 < 4096 := (localIdx rAct12 β).isLt
    by_cases hP : parityPhaseTable 4 alt4BoolTable m idx12 = true
    · rw [ite_eq_left hP, ite_eq_left ⟨hlt12, hP⟩]
      exact ite_eq_right (by decide : ¬ (1 : ZMod 2) = 0)
    · rw [ite_eq_right hP, ite_eq_right (fun h ↦ hP h.2), bitSign_zero2]
attribute [irreducible] leafQRaw leafQPoly leafPhi p0PhaseC leafMidPhaseC quad5StepDyn
/-! ### Word-Parametric `wOuter = 8` `PREP_out` (`268 + 3 * T` / `228 + 3 * T`) & Comb Wrappers -/
/-- Computable `4-T` (`0 TOFF`) Fredkin gate controlled on wire `13` using clean ancilla `14`. -/
def fredkinPair15Dyn2 {Var : Type} (v : Var) (a b : Wire 15) (hab : a ≠ b)
    (h13b : (13 : Wire 15) ≠ b) (hb14 : b ≠ 14) (ha14 : a ≠ 14) : DynamicCircuit Var 15 :=
  let pAnd : GroupUnary.RevCompute 15 := .andGate 13 b 14 h13b (by decide) hb14
  .seq (.circuit (Circuit.CNOT a b hab)) (.seq (Lac2Folded184Select.revComputeDyn pAnd)
    (.seq (.circuit (Circuit.CNOT 14 a ha14.symm)) (.seq
      (Lac2Folded184Select.revUncomputeDyn v pAnd) (.circuit (Circuit.CNOT a b hab)))))
/-- Computable `24-T` (`0 TOFF`, `15`-wire) guarded `4`-bit CSWAP matching `cswap15Dyn`. -/
def cswap15Dyn2 {Var : Type} (v : Var) : DynamicCircuit Var 15 :=
  .seq (.seq (.seq (.seq (.seq (Lac2Folded184Select.revComputeDyn guard2Rev)
    (fredkinPair15Dyn2 v ⟨(ret4Idx 0).val, by decide⟩ ⟨8 + (0 : Fin 4).val, by decide⟩
      (by decide) (by decide) (by decide) (by decide))) (fredkinPair15Dyn2 v
    ⟨(ret4Idx 1).val, by decide⟩ ⟨8 + (1 : Fin 4).val, by decide⟩ (by decide) (by decide)
    (by decide) (by decide))) (fredkinPair15Dyn2 v ⟨(ret4Idx 2).val, by decide⟩
    ⟨8 + (2 : Fin 4).val, by decide⟩ (by decide) (by decide) (by decide) (by decide)))
    (fredkinPair15Dyn2 v ⟨(ret4Idx 3).val, by decide⟩ ⟨8 + (3 : Fin 4).val, by decide⟩
      (by decide) (by decide) (by decide) (by decide)))
    (Lac2Folded184Select.revUncomputeDyn v guard2Rev)
theorem cswap15Dyn_eq {Var : Type} (v : Var) : cswap15Dyn2 v = cswap15Dyn v := by
  unfold cswap15Dyn2 cswap15Dyn fredkinPair15Dyn2 fredkinPair15Dyn
  rfl
attribute [irreducible] fredkinPair15Dyn2 cswap15Dyn2
@[simp] theorem countCswap15Dyn_toff2 {Var : Type} (v : Var) :
    (cswap15Dyn2 v).count .TOFF = 0 := by rw [cswap15Dyn_eq, countCswap15Dyn_toff]
@[simp] theorem countCswap15Dyn_t2 {Var : Type} (v : Var) :
    (cswap15Dyn2 v).count .T = 24 := by rw [cswap15Dyn_eq, countCswap15Dyn_t]
theorem cleanRealizesCswap15Dyn2 {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) :
    Solution.CleanDyn.CleanRealizes v (QRegister.block 0 12 (by decide) : QRegister 12 15)
      (QRegister.block 12 3 (by decide) : QRegister 3 15) cswap12Unitary (cswap15Dyn2 v) :=
  cswap15Dyn_eq v ▸ cleanRealizesCswap15Dyn v
/-- Word-parametric `wOuter = 8` forward `PREP_out` (`268 + 3 * wordCountT rotWord` `T`, `0 TOFF`).
-/
def hGadgetOuter8PrepOutWordFwdDyn {Var : Type} {N sScr : ℕ}
    (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N) (rScr : QRegister sScr N)
    (hs : 87 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) : DynamicCircuit Var N :=
  let rNA := rOut.compose nonAlt13Loc
  let rIA := rOut.compose idxAlt16Loc
  let rXA := rOut.compose xoAlt12Loc
  have hNAScr : rNA.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  have hIAScr : rIA.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  have hXAScr : rXA.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  .seq (DyadicXMeasPrepOut13.placeWithScr rNA rScr (by omega : 4 ≤ sScr) hNAScr
      (init17WordLocDyn rotWord v))
    (.seq (DyadicXMeasPrepOut13.placeWithScr rIA rScr hs hIAScr (hGadgetPreSwap103Dyn v))
      (DyadicXMeasPrepOut13.placeWithScr rXA rScr (by omega : 3 ≤ sScr) hXAScr (cswap15Dyn2 v)))
attribute [irreducible] hGadgetOuter8PrepOutWordFwdDyn
@[simp] theorem countHGadgetOuter8PrepOutWordFwdDyn_toff {Var : Type} {N sScr : ℕ}
    (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N) (rScr : QRegister sScr N)
    (hs : 87 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) :
    (hGadgetOuter8PrepOutWordFwdDyn rotWord v rOut rScr hs hOutScr).count .TOFF = 0 := by
  unfold hGadgetOuter8PrepOutWordFwdDyn
  dsimp only
  rw [count_seq2, count_seq2, DyadicXMeasPrepOut13.count_placeWithScr,
    DyadicXMeasPrepOut13.count_placeWithScr, DyadicXMeasPrepOut13.count_placeWithScr,
    countInit17WordLocDyn_toff, countHGadgetPreSwap103Dyn_toff, countCswap15Dyn_toff2]
@[simp] theorem countHGadgetOuter8PrepOutWordFwdDyn_t {Var : Type} {N sScr : ℕ}
    (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N) (rScr : QRegister sScr N)
    (hs : 87 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) :
    (hGadgetOuter8PrepOutWordFwdDyn rotWord v rOut rScr hs hOutScr).count .T =
      268 + 3 * wordCountT rotWord := by
  unfold hGadgetOuter8PrepOutWordFwdDyn
  dsimp only
  rw [count_seq2, count_seq2, DyadicXMeasPrepOut13.count_placeWithScr,
    DyadicXMeasPrepOut13.count_placeWithScr, DyadicXMeasPrepOut13.count_placeWithScr,
    countInit17WordLocDyn_t, countHGadgetPreSwap103Dyn_t, countCswap15Dyn_t2]
  omega
theorem cleanRealizesSetHGadgetOuter8PrepOutWordFwdDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N)
    (rScr : QRegister sScr N) (hs : 87 ≤ sScr) (hOutScr : rOut.DisjointWires rScr)
    (S_ext : Finset (Wire N)) (hScrSub : rScr.image ⊆ S_ext)
    (hDisjOut : Disjoint rOut.image S_ext) :
    CleanRealizesSet v S_ext (rOut.embedUnitary (outer8PrepOutWordImpl rotWord))
      (hGadgetOuter8PrepOutWordFwdDyn rotWord v rOut rScr hs hOutScr) := by
  unfold hGadgetOuter8PrepOutWordFwdDyn
  dsimp only
  let rNA := rOut.compose nonAlt13Loc
  let rIA := rOut.compose idxAlt16Loc
  let rXA := rOut.compose xoAlt12Loc
  have hd {m : ℕ} (loc : QRegister m (mOutUB 8)) :=
    CoherentAlias.compose_disjointWires_left loc hOutScr
  have h1 := placeWithScr_cleanRealizesSet rNA rScr (by omega : 4 ≤ sScr) (hd _) S_ext hScrSub
    (Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut)
    (cleanRealizesInit17WordLocDyn rotWord v)
  have h2 := placeWithScr_cleanRealizesSet rIA rScr hs (hd _) S_ext hScrSub
    (Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut)
    (cleanRealizesHGadgetPreSwap103Dyn v)
  have h3 := placeWithScr_cleanRealizesSet rXA rScr (by omega : 3 ≤ sScr) (hd _) S_ext hScrSub
    (Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut) (cleanRealizesCswap15Dyn2 v)
  have hAll := h1.seq (h2.seq h3)
  have hEq : (rXA.embedUnitary cswap12Unitary *
      rIA.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable)) *
      rNA.embedUnitary (init13Unitary (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord)) =
      rOut.embedUnitary (outer8PrepOutWordImpl rotWord) := by
    dsimp only [rXA, rIA, rNA, outer8PrepOutWordImpl, outer8PrepOutUnit]
    simp only [QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul]
  rwa [hEq] at hAll
theorem cleanRealizesHGadgetOuter8PrepOutWordFwdDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N)
    (rScr : QRegister sScr N) (hs : 87 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) :
    Solution.CleanDyn.CleanRealizes v rOut rScr (outer8PrepOutWordImpl rotWord)
      (hGadgetOuter8PrepOutWordFwdDyn rotWord v rOut rScr hs hOutScr) :=
  let h := (cleanRealizes_iff_set v rOut rScr (outer8PrepOutWordImpl rotWord) _).mpr
    (cleanRealizesSetHGadgetOuter8PrepOutWordFwdDyn rotWord v rOut rScr hs hOutScr rScr.image
      Finset.Subset.rfl (disjoint_image_of_disjointWires hOutScr))
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
/-- Word-parametric `wOuter = 8` `PREP_out†` (`228 + 3 * wordCountT rotWord` `T`, `0 TOFF`). -/
def hGadgetOuter8PrepOutWordBwdDyn {Var : Type} {N sScr : ℕ}
    (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N) (rScr : QRegister sScr N)
    (hs : 82 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) : DynamicCircuit Var N :=
  let rNA := rOut.compose nonAlt13Loc
  let rIdx12 := rOut.compose idx12Loc
  let rAlt4 := rOut.compose alt4Loc
  let rXA := rOut.compose xoAlt12Loc
  have hNAScr : rNA.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  have hIdxScr : rIdx12.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  have hXAScr : rXA.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  .seq (DyadicXMeasPrepOut13.placeWithScr rXA rScr (by omega : 3 ≤ sScr) hXAScr (cswap15Dyn2 v))
    (.seq (measureXResetAndBranch v 4 rAlt4 (fun m ↦ DyadicXMeasPrepOut13.placeWithScr rIdx12
        rScr hs hIdxScr (hGadgetLeaf94Dyn v m)))
      (DyadicXMeasPrepOut13.placeWithScr rNA rScr (by omega : 4 ≤ sScr) hNAScr
        (uninit17WordLocDyn rotWord v)))
@[simp] theorem countHGadgetOuter8PrepOutWordBwdDyn_toff {Var : Type} {N sScr : ℕ}
    (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N) (rScr : QRegister sScr N)
    (hs : 82 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) :
    (hGadgetOuter8PrepOutWordBwdDyn rotWord v rOut rScr hs hOutScr).count .TOFF = 0 := by
  have hbr (m : Fin (2 ^ 4)) :
      (DyadicXMeasPrepOut13.placeWithScr (rOut.compose idx12Loc) rScr hs
        (CoherentAlias.compose_disjointWires_left _ hOutScr)
        (hGadgetLeaf94Dyn v m)).count .TOFF = 0 := by
    rw [DyadicXMeasPrepOut13.count_placeWithScr, countHGadgetLeaf94Dyn_toff]
  simp only [hGadgetOuter8PrepOutWordBwdDyn, DynamicCircuit.count,
    DyadicXMeasPrepOut13.count_placeWithScr, countCswap15Dyn_toff2,
    count_measureXResetAndBranch_toff _ 4 _ _ hbr, countUninit17WordLocDyn_toff]
@[simp] theorem countHGadgetOuter8PrepOutWordBwdDyn_t {Var : Type} {N sScr : ℕ}
    (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N) (rScr : QRegister sScr N)
    (hs : 82 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) :
    (hGadgetOuter8PrepOutWordBwdDyn rotWord v rOut rScr hs hOutScr).count .T =
      228 + 3 * wordCountT rotWord := by
  have hbr (m : Fin (2 ^ 4)) :
      (DyadicXMeasPrepOut13.placeWithScr (rOut.compose idx12Loc) rScr hs
        (CoherentAlias.compose_disjointWires_left _ hOutScr)
        (hGadgetLeaf94Dyn v m)).count .T = 152 := by
    rw [DyadicXMeasPrepOut13.count_placeWithScr, countHGadgetLeaf94Dyn_t]
  simp only [hGadgetOuter8PrepOutWordBwdDyn, DynamicCircuit.count,
    DyadicXMeasPrepOut13.count_placeWithScr, countCswap15Dyn_t2,
    count_measureXResetAndBranch_t_eq _ 4 152 _ _ hbr, countUninit17WordLocDyn_t]
  omega
theorem cleanUnloadsSetHGadgetOuter8PrepOutWordBwdDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N)
    (rScr : QRegister sScr N) (hs : 82 ≤ sScr) (hOutScr : rOut.DisjointWires rScr)
    (S_ext : Finset (Wire N)) (hScrSub : rScr.image ⊆ S_ext)
    (hDisjOut : Disjoint rOut.image S_ext) :
    CleanUnloadsSet v (S_ext ∪ (rOut.compose alt4Loc).image) (rOut.compose alt4Loc).image
      (rOut.embedUnitary (outer8PrepOutWordImpl rotWord)) 1
      (hGadgetOuter8PrepOutWordBwdDyn rotWord v rOut rScr hs hOutScr) := by
  let rNA := rOut.compose nonAlt13Loc
  let rIdx12 := rOut.compose idx12Loc
  let rAlt4 := rOut.compose alt4Loc
  let rIA := rOut.compose idxAlt16Loc
  let rXA := rOut.compose xoAlt12Loc
  let M_alt := rAlt4.image
  let S := S_ext ∪ M_alt
  have hNAScr : rNA.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  have hIdxScr : rIdx12.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  have hXAScr : rXA.DisjointWires rScr := CoherentAlias.compose_disjointWires_left _ hOutScr
  have hSdiff : S \ M_alt = S_ext := Finset.union_sdiff_cancel_right
    ((Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut).symm)
  have hIdxAlt : rIdx12.DisjointWires rAlt4 := QRegister.disjoint_iff.mpr fun i j hij ↦
    (by decide : idx12Loc.DisjointWires alt4Loc).ne i j (rOut.wires.injective hij)
  have hDisjNAS : Disjoint rNA.image S :=
    Finset.disjoint_union_right.mpr ⟨Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut,
      disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr fun i j hij ↦
        (by decide : nonAlt13Loc.DisjointWires alt4Loc).ne i j (rOut.wires.injective hij))⟩
  have hDisjIdxS : Disjoint rIdx12.image S := Finset.disjoint_union_right.mpr
    ⟨Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut,
      disjoint_image_of_disjointWires hIdxAlt⟩
  let W_cswap := rXA.embedUnitary cswap12Unitary
  let W_xor := rIA.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable)
  let W_init := rNA.embedUnitary
    (init13Unitary (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord))
  have hInitCr : CleanRealizesSet v S W_init⁻¹ (DyadicXMeasPrepOut13.placeWithScr rNA rScr
      (by omega : 4 ≤ sScr) hNAScr (uninit17WordLocDyn rotWord v)) := by
    dsimp only [W_init]
    rw [← QRegister.embedUnitary_inv]
    exact placeWithScr_cleanRealizesSet rNA rScr (by omega : 4 ≤ sScr) hNAScr S
      (hScrSub.trans Finset.subset_union_left) hDisjNAS
      (cleanRealizesUninit17WordLocDyn rotWord v)
  have hInitPres : AliasPrep.PreservesWires W_init.1 S :=
    AliasPrep.preservesWires_embedMatrix_of_disjoint rNA _ S hDisjNAS
  have hU3 := cleanUnloadsSet_empty_of_cleanRealizesSet_inv hInitCr
    (AliasPrep.preservesWires_comm_zeroProjOn hInitPres Finset.Subset.rfl)
  have hLeafCr (m : Fin (2 ^ 4)) : CleanRealizesSet v S
      (1 * rIdx12.embedUnitary (diagPhaseUnitary 12 4096 (parityPhaseTable 4 alt4BoolTable m)))
      (DyadicXMeasPrepOut13.placeWithScr rIdx12 rScr hs hIdxScr (hGadgetLeaf94Dyn v m)) := by
    rw [one_mul]
    exact placeWithScr_cleanRealizesSet rIdx12 rScr hs hIdxScr S
      (hScrSub.trans Finset.subset_union_left) hDisjIdxS (cleanRealizesHGadgetLeaf94Dyn v m)
  have hU2 := cleanUnloadsSet_measureXResetAndBranch v S 4 4096 alt4BoolTable rIdx12 rAlt4
    hIdxAlt Finset.subset_union_right 1 (fun m ↦ DyadicXMeasPrepOut13.placeWithScr rIdx12 rScr
      hs hIdxScr (hGadgetLeaf94Dyn v m)) hLeafCr
  have hConcatEq : rIdx12.concat rAlt4 hIdxAlt = rIA := CoherentAlias.qreg_ext fun k ↦ by
    dsimp only [rIdx12, rAlt4, rIA, idxAlt16Loc]
    rcases finSumFinEquiv.surjective k with ⟨i | j, rfl⟩
    · simp only [finSumFinEquiv_apply_left, QRegister.concat_apply_left, QRegister.compose_apply]
    · simp only [finSumFinEquiv_apply_right, QRegister.concat_apply_right, QRegister.compose_apply]
  rw [show (rIdx12.concat rAlt4 hIdxAlt).embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable) =
    W_xor by rw [hConcatEq], ← Finset.sdiff_empty (s := S)] at hU2
  have hU23 := hU2.seq (Finset.empty_subset S) hU3
    (AliasPrep.preservesWires_comm_zeroProjOn hInitPres Finset.sdiff_subset)
  rw [Finset.union_empty] at hU23
  have hCswapInv : W_cswap⁻¹ = W_cswap := inv_eq_self_of_mul_self W_cswap (by
    dsimp only [W_cswap]
    rw [← QRegister.embedUnitary_mul, cswap12Unitary_mul_self, QRegister.embedUnitary_one])
  have hDisjXAE : Disjoint rXA.image S_ext :=
    Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut
  let dCswap := DyadicXMeasPrepOut13.placeWithScr rXA rScr (by omega : 3 ≤ sScr) hXAScr
    (cswap15Dyn2 v)
  have hCswapCr : CleanRealizesSet v S_ext W_cswap⁻¹ dCswap := by
    rw [hCswapInv]
    exact placeWithScr_cleanRealizesSet rXA rScr (by omega : 3 ≤ sScr) hXAScr S_ext hScrSub
      hDisjXAE (cleanRealizesCswap15Dyn2 v)
  have hU1 : CleanUnloadsSet v (S \ M_alt) ∅ W_cswap 1 dCswap := by
    rw [hSdiff]
    exact cleanUnloadsSet_empty_of_cleanRealizesSet_inv hCswapCr
      (AliasPrep.preservesWires_comm_zeroProjOn
        (AliasPrep.preservesWires_embedMatrix_of_disjoint rXA _ S_ext hDisjXAE) Finset.Subset.rfl)
  have hComm23 : (W_xor * W_init).1 * zeroProjOn (S \ M_alt) =
      zeroProjOn (S \ M_alt) * (W_xor * W_init).1 := by
    rw [hSdiff, show W_xor * W_init = rOut.embedUnitary
        (idxAlt16Loc.embedUnitary (xorLoadUnitary 12 4 4096 alt4BoolTable) *
          nonAlt13Loc.embedUnitary (init13Unitary
            (OptU2Grover184PrepOut13.prepUnif184WordImpl rotWord))) by
      dsimp only [W_xor, W_init, rIA, rNA]
      rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_compose,
        QRegister.embedUnitary_compose]]
    exact AliasPrep.preservesWires_comm_zeroProjOn
      (AliasPrep.preservesWires_embedMatrix_of_disjoint rOut _ S_ext hDisjOut) Finset.Subset.rfl
  have hFull := hU1.seq Finset.subset_union_right hU23 hComm23
  rw [Finset.empty_union] at hFull
  have hFullEq :
      W_cswap * (W_xor * W_init) = rOut.embedUnitary (outer8PrepOutWordImpl rotWord) := by
    dsimp only [W_cswap, W_xor, W_init, rXA, rIA, rNA, outer8PrepOutWordImpl, outer8PrepOutUnit]
    simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_compose, mul_assoc]
  rwa [hFullEq] at hFull
theorem cleanUnloadsWpHGadgetOuter8PrepOutWordBwdDyn_ext {Var : Type} [Fintype Var]
    [DecidableEq Var] {N sScr : ℕ} (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N)
    (rScr : QRegister sScr N) (hs : 82 ≤ sScr) (hOutScr : rOut.DisjointWires rScr)
    (S_ext : Finset (Wire N)) (hScrSub : rScr.image ⊆ S_ext)
    (hDisjOut : Disjoint rOut.image S_ext) : CleanUnloadsWp v
      (S_ext ∪ (rOut.compose (MobiusOptSubcube163Walk.outZeroPrefixReg 8 4 (by decide))).image)
      (rOut.embedUnitary (outer8PrepOutWordImpl rotWord))
      (hGadgetOuter8PrepOutWordBwdDyn rotWord v rOut rScr hs hOutScr) :=
  CleanUnloadsWp.of_cleanUnloadsSet (cleanUnloadsSetHGadgetOuter8PrepOutWordBwdDyn rotWord v rOut
    rScr hs hOutScr S_ext hScrSub hDisjOut)
theorem cleanUnloadsWpHGadgetOuter8PrepOutWordBwdDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (rotWord : List Gate1) (v : Var) (rOut : QRegister (mOutUB 8) N)
    (rScr : QRegister sScr N) (hs : 82 ≤ sScr) (hOutScr : rOut.DisjointWires rScr) :
    CleanUnloadsWp v (rScr.image ∪
      (rOut.compose (MobiusOptSubcube163Walk.outZeroPrefixReg 8 4 (by decide))).image)
      (rOut.embedUnitary (outer8PrepOutWordImpl rotWord))
      (hGadgetOuter8PrepOutWordBwdDyn rotWord v rOut rScr hs hOutScr) :=
  cleanUnloadsWpHGadgetOuter8PrepOutWordBwdDyn_ext rotWord v rOut rScr hs hOutScr rScr.image
    Finset.Subset.rfl (disjoint_image_of_disjointWires hOutScr)
attribute [irreducible] hGadgetOuter8PrepOutWordBwdDyn
end PrepOutOuter8Impl
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetPrepOutOuter8
