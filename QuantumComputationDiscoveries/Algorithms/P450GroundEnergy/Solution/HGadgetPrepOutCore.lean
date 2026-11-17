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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HGadgetSympQrom

@[expose] public section

/-! # Hadamard-Gadget `wOuter = 8` `PREP_out` Core (`cFib11`, `quad5GadC` & `fix46x10C`)
`22-T` `cFib11` coin-fiber decoder, `12-T` `5`-pair Hadamard gadget `quad5GadC`, and `0-T`
`fix46x10C` phase sweep (Babbush et al., *Phys. Rev. X* **8**, 041015, 2018; Gidney, *Quantum*
**2**, 74, 2018; Low, Kliuchnikov, and Schaeffer, *Quantum* **8**, 1375, 2024,
DOI: `10.22331/q-2024-06-17-1375`). -/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetPrepOutOuter8
open QuantumComputation.Specs QuantumComputation.Specs.P450

section PrepOutCoreImpl

open Operator QProg Matrix Circuit Real HermitianMat
open QuantumComputation QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution QuantumComputation.Specs.P450
open BlockEncodingCore
open CoherentAlias
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MidReflCtxRetain (hotCtxPhaseLoop)
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepAnfAndCoin14Core (
  count_hotCtxPhaseLoop_toff2
  count_hotCtxPhaseLoop_t2 ket_hotCtxPhaseLoop)
open HGadgetSympQrom
open OuterWeights.GroverUniform
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators hiding
  ket bit_cases matrix_ext_ket zeroProjOn
  zeroProjOn_mulVec_ket zeroProjOn_conjTranspose ket_Z
open SelectSwapQROM
open OptFactoredMag30AndCoin9
open ReordOuter13Bridge
open Phase2MidSandwich
open MobiusOptSubcube163Walk
open CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepOuter8Pi145Outer hiding b2z
open StepOuter8Pi145L1
open Pi145Fast2RotCore
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Outer8Pi145Compact2RotDyn hiding
  b2z_xor b2z_and
open Outer8Pi145Compact2RotOuter
open _root_.Function (update update_of_ne update_self update_idem update_eq_self)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit (
  xorWireUnitary xorWireUnitary_mulVec_ket phaseFlipUnitary
  phaseFlipUnitary_mulVec_ket xMeasUnloadWireDyn count_xMeasUnloadWireDyn_toff
  count_xMeasUnloadWireDyn_t wp_xMeasUnloadWireDyn_update_self cleanFinsetProj
  restrictAssertionToCleanFinset restrictAssertionToCleanFinset_coe
  restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowPrep12Core (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Part B: `22-T` `cFib11` Coin Router, `12-T` `5`-Pair Gadget & `192-T` / `152-T` `PREP_out` -/

theorem bitSign_sdk_eq (x : ZMod 2) : XMeasCircuit.bitSign x = bitSign x := by
  rcases bit_cases x with rfl | rfl <;> rfl

theorem TransRealizes.xMeasUnloadWire {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) (q : Wire N) (f : BitAssignment N → ZMod 2)
    (hf : ∀ β val, f (update β q val) = f β)
    (S : BitAssignment N → Bool) (hq0 : ∀ β, S β = true → β q = 0)
    (cFix : Circuit N) (htoff : cFix.count .TOFF = 0)
    (hevalFix : ∀ γ, γ q = 0 →
      cFix.eval.1.mulVec (XMeasCircuit.ket γ) = bitSign (f γ) • XMeasCircuit.ket γ) :
    TransRealizes v (fun γ ↦ S (update γ q (γ q + f γ))) S
      (xorWireUnitary q f hf) (xMeasUnloadWireDyn v q (.circuit cFix)) := by
  let U_x := xorWireUnitary q f hf
  let S_pre : BitAssignment N → Bool := fun γ ↦ S (update γ q (γ q + f γ))
  have hUx_sq : U_x * U_x = 1 := Subtype.ext <| XMeasCircuit.matrix_ext_ket fun γ ↦ by
    change (U_x.1 * U_x.1).mulVec _ = (1 : Operator _).mulVec _
    rw [← mulVec_mulVec, xorWireUnitary_mulVec_ket, xorWireUnitary_mulVec_ket, one_mulVec,
      update_self, hf, update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, update_eq_self]
  have hUx_val_sq : U_x.1 * U_x.1 = 1 := congrArg Subtype.val hUx_sq
  have hUx_adj : U_x.1ᴴ = U_x.1 := conjTranspose_eq_self_of_mul_self U_x hUx_sq
  have hmap : U_x.1 * GroupUnary.predProj S_pre = GroupUnary.predProj S * U_x.1 := by
    apply SelectSwapQROM.matrix_ext_ket
    intro γ
    rw [← mulVec_mulVec, ← mulVec_mulVec, predProj_mulVec_ket, ← ket_sdk_eq,
      xorWireUnitary_mulVec_ket, ket_sdk_eq, predProj_mulVec_ket]
    dsimp only [S_pre]
    by_cases hS : S (update γ q (γ q + f γ)) = true
    · rw [ite_t hS, ite_t hS, ← ket_sdk_eq, xorWireUnitary_mulVec_ket, ket_sdk_eq]
    · rw [ite_f hS, ite_f hS, mulVec_zero]
  have hswap : U_x.1 * GroupUnary.predProj S = GroupUnary.predProj S_pre * U_x.1 := by
    calc U_x.1 * GroupUnary.predProj S
        = U_x.1 * (GroupUnary.predProj S * U_x.1) * U_x.1 := by
          rw [mul_assoc _ _ U_x.1, mul_assoc (GroupUnary.predProj S), hUx_val_sq, mul_one]
      _ = (U_x.1 * U_x.1) * GroupUnary.predProj S_pre * U_x.1 := by
          rw [← hmap]
          simp only [mul_assoc]
      _ = GroupUnary.predProj S_pre * U_x.1 := by rw [hUx_val_sq, one_mul]
  have hZP : cleanFinsetProj ({q} : Finset (Wire N)) = zeroProjOn {q} := by
    unfold cleanFinsetProj zeroProjOn
    congr 1
  have hAbs : GroupUnary.predProj S * cleanFinsetProj {q} = GroupUnary.predProj S := by
    apply SelectSwapQROM.matrix_ext_ket
    intro β
    rw [← mulVec_mulVec, hZP, zeroProjOn_mulVec_ket]
    by_cases h0 : ∀ w ∈ ({q} : Finset (Wire N)), β w = 0
    · rw [ite_t h0]
    · rw [ite_f h0, mulVec_zero, predProj_mulVec_ket]
      exact (ite_f fun hS ↦ h0 fun w hw ↦ Finset.mem_singleton.mp hw ▸ hq0 β hS).symm
  have hcFix_proj : cFix.eval.1 * cleanFinsetProj {q} =
      (phaseFlipUnitary f).1 * cleanFinsetProj {q} := by
    refine XMeasCircuit.matrix_ext_ket fun γ ↦ ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, hZP, ket_sdk_eq γ, zeroProjOn_mulVec_ket]
    by_cases h0 : ∀ w ∈ ({q} : Finset (Wire N)), γ w = 0
    · rw [ite_t h0, ← ket_sdk_eq γ, hevalFix γ (h0 q (Finset.mem_singleton_self q)),
        phaseFlipUnitary_mulVec_ket, bitSign_sdk_eq]
    · rw [ite_f h0, mulVec_zero, mulVec_zero]
  have hadjFix : cleanFinsetProj {q} * cFix.eval.1ᴴ =
      cleanFinsetProj {q} * (phaseFlipUnitary f).1ᴴ := by
    have h' := congrArg conjTranspose hcFix_proj
    simpa [conjTranspose_mul, hZP, zeroProjOn_conjTranspose] using h'
  refine ⟨by simp [count_xMeasUnloadWireDyn_toff, htoff], hmap,
    fun Θ _ σ val ↦ wp_xMeasUnloadWireDyn_update_self v q (.circuit cFix) Θ σ val,
    fun Θ hΘ ↦ ?_⟩
  have hFix : restrictAssertionToCleanFinset (wp (DynamicCircuit.circuit cFix).compile Θ) {q} =
      restrictAssertionToCleanFinset (qcWpQAssign (phaseFlipUnitary f) Θ) {q} := by
    funext σ
    apply Subtype.ext
    simp only [restrictAssertionToCleanFinset_coe, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, star_eq_conjTranspose, conj_conj, hadjFix]
  have hCore := restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn v q {q}
    (Finset.mem_singleton_self q) f hf (.circuit cFix) Θ hΘ hFix
  funext σ
  apply Subtype.ext
  have h1 := congrArg
    (fun M : HermitianMat (Fin (2 ^ N)) ℂ ↦ M.conj (U_x.1 * GroupUnary.predProj S))
    (congrArg Subtype.val (congrFun hCore σ))
  simp only [restrictAssertionToCleanFinset_coe, GroupUnary.restrictPred_coe, qcWpQAssign,
    qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star, star_eq_conjTranspose, conj_conj]
    at h1 ⊢
  have hLHS : (U_x.1 * GroupUnary.predProj S) * (cleanFinsetProj {q} * U_x.1ᴴ) =
      GroupUnary.predProj S_pre := by
    calc (U_x.1 * GroupUnary.predProj S) * (cleanFinsetProj {q} * U_x.1ᴴ)
        = U_x.1 * ((GroupUnary.predProj S * cleanFinsetProj {q}) * U_x.1) := by
          rw [hUx_adj]
          simp only [mul_assoc]
      _ = U_x.1 * (U_x.1 * GroupUnary.predProj S_pre) := by rw [hAbs, ← hmap]
      _ = GroupUnary.predProj S_pre := by rw [← mul_assoc, hUx_val_sq, one_mul]
  have hRHS : (U_x.1 * GroupUnary.predProj S) * cleanFinsetProj {q} =
      GroupUnary.predProj S_pre * U_x.1ᴴ := by
    rw [mul_assoc, hAbs, hswap, hUx_adj]
  rwa [hLHS, hRHS] at h1

/-- Fiber index `0..9` selected by `pktKeepSel10` at coin state `c < 16` (`none` at `15`). -/
abbrev coinOptFib (c : Fin (2 ^ 4)) : Option (Fin 10) :=
  match c.val with
  | 0 | 1 => some 2
  | 2 | 3 => some 7
  | 4 => some 6
  | 5 => some 8
  | 6 => some 3
  | 7 => some 4
  | 8 | 10 => some 9
  | 9 | 11 => some 5
  | 12 | 14 => some 1
  | 13 => some 0
  | _ => none

theorem basisBits4_0 (c : Fin (2 ^ 4)) :
    basisBits 4 c 0 = if c.val % 2 = 1 then 1 else 0 := by
  revert c
  decide

theorem basisBits4_1 (c : Fin (2 ^ 4)) :
    basisBits 4 c 1 = if (c.val / 2) % 2 = 1 then 1 else 0 := by
  revert c
  decide

theorem basisBits4_2 (c : Fin (2 ^ 4)) :
    basisBits 4 c 2 = if (c.val / 4) % 2 = 1 then 1 else 0 := by
  revert c
  decide

theorem basisBits4_3 (c : Fin (2 ^ 4)) :
    basisBits 4 c 3 = if (c.val / 8) % 2 = 1 then 1 else 0 := by
  revert c
  decide

theorem pktKeepSel10_eq_optFib (kb : Fin 10 → ZMod 2) (c : Fin (2 ^ 4)) :
    pktKeepSel10 kb (basisBits 4 c) =
      match coinOptFib c with
      | some f => kb f
      | none => 0 := by
  dsimp only [pktKeepSel10]
  rw [basisBits4_0, basisBits4_1, basisBits4_2, basisBits4_3]
  fin_cases c <;>
    simp [coinOptFib, ParamDyadicOuter13.mux2Bit_zero, ParamDyadicOuter13.mux2Bit_one]

/-- Local wire `cOff + s` (`s < 16`) for the `22-T` `cFib11` coin-fiber router. -/
abbrev cSlot {N : ℕ} (cOff : ℕ) (hN : cOff + 16 ≤ N) (s : Fin 16) : Wire N :=
  ⟨cOff + s.val, by omega⟩

theorem cSlot_eq_iff {N : ℕ} (cOff : ℕ) (hN : cOff + 16 ≤ N) (a b : Fin 16) :
    cSlot cOff hN a = cSlot cOff hN b ↔ a = b := by
  refine ⟨fun h ↦ Fin.ext ?_, fun h ↦ h ▸ rfl⟩
  have hv := congrArg Fin.val h
  dsimp [cSlot] at hv
  omega

/-- Stage-1 `w0` slot indices (`R = 4`) of `cFib11`. -/
def cS4_0 : Fin 4 → Fin 16 := ![6, 9, 1, 11]
/-- Stage-1 `w1` slot indices (`R = 4`) of `cFib11`. -/
def cS4_1 : Fin 4 → Fin 16 := ![8, 5, 0, 12]
/-- Stage-3 `w0` slot indices (`R = 5`) of `cFib11`. -/
def cS5_0 : Fin 5 → Fin 16 := ![2, 6, 8, 0, 13]
/-- Stage-3 `w1` slot indices (`R = 5`) of `cFib11`. -/
def cS5_1 : Fin 5 → Fin 16 := ![7, 3, 4, 10, 14]

theorem cSplitValid {N R : ℕ} (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N)
    (ctrlIdx : Fin 12) (s0 s1 : Fin R → Fin 16)
    (hinj0 : Function.Injective s0) (hinj1 : Function.Injective s1)
    (hne01 : ∀ i j, s0 i ≠ s1 j) (hq0 : ∀ i, (15 : Fin 16) ≠ s0 i)
    (hq1 : ∀ i, (15 : Fin 16) ≠ s1 i) :
    WSplitValid R ⟨ctrlIdx.val, by omega⟩ (fun i ↦ cSlot cOff hN (s0 i))
      (fun i ↦ cSlot cOff hN (s1 i)) (cSlot cOff hN 15) where
  w0_inj i j h := hinj0 ((cSlot_eq_iff cOff hN _ _).mp h)
  w1_inj i j h := hinj1 ((cSlot_eq_iff cOff hN _ _).mp h)
  w01_ne i j h := hne01 i j ((cSlot_eq_iff cOff hN _ _).mp h)
  ctrl_w0 i h := by
    have hv := congrArg Fin.val h
    dsimp [cSlot] at hv
    omega
  ctrl_w1 i h := by
    have hv := congrArg Fin.val h
    dsimp [cSlot] at hv
    omega
  q_ctrl h := by
    have hv := congrArg Fin.val h
    dsimp [cSlot] at hv
    omega
  q_w0 i h := hq0 i ((cSlot_eq_iff cOff hN _ _).mp h)
  q_w1 i h := hq1 i ((cSlot_eq_iff cOff hN _ _).mp h)

theorem cSplit4Valid {N : ℕ} (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N) :
    WSplitValid 4 ⟨8, by omega⟩ (fun i ↦ cSlot cOff hN (cS4_0 i))
      (fun i ↦ cSlot cOff hN (cS4_1 i)) (cSlot cOff hN 15) :=
  cSplitValid cOff h12 hN ⟨8, by decide⟩ cS4_0 cS4_1 (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem cSplit5Valid {N : ℕ} (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N) :
    WSplitValid 5 ⟨9, by omega⟩ (fun i ↦ cSlot cOff hN (cS5_0 i))
      (fun i ↦ cSlot cOff hN (cS5_1 i)) (cSlot cOff hN 15) :=
  cSplitValid cOff h12 hN ⟨9, by decide⟩ cS5_0 cS5_1 (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- `1`-AND (`4-T`) 1-hot decoder of `(c₂, c₃)` onto `cSlot {11, 6, 9, 1}`. -/
def cInit4Rev {N : ℕ} (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N) :
    GroupUnary.RevCompute N :=
  let c2 : Wire N := ⟨10, by omega⟩
  let c3 : Wire N := ⟨11, by omega⟩
  let s (k : Fin 16) := cSlot cOff hN k
  have hc2 (k : Fin 16) : c2 ≠ s k := fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp [c2, s, cSlot] at hv
    omega
  have hc3 (k : Fin 16) : c3 ≠ s k := fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp [c3, s, cSlot] at hv
    omega
  have hc23 : c2 ≠ c3 := fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp [c2, c3] at hv
    omega
  have hss (a b : Fin 16) (hab : a ≠ b) : s a ≠ s b := fun h ↦
    hab ((cSlot_eq_iff cOff hN a b).mp h)
  .seq (.andGate c2 c3 (s 1) hc23 (hc2 1) (hc3 1))
    (.seq (.cnot c3 (s 9) (hc3 9))
      (.seq (.cnot (s 1) (s 9) (hss 1 9 (by decide)))
        (.seq (.cnot c2 (s 6) (hc2 6))
          (.seq (.cnot (s 1) (s 6) (hss 1 6 (by decide)))
            (.seq (.x (s 11))
              (.seq (.cnot c2 (s 11) (hc2 11))
                (.cnot (s 9) (s 11) (hss 9 11 (by decide)))))))))

theorem cInit4Rev_fwdBits_clean {N : ℕ} (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N)
    (β : BitAssignment N) (h1 : β (cSlot cOff hN 1) = 0) (h6 : β (cSlot cOff hN 6) = 0)
    (h9 : β (cSlot cOff hN 9) = 0) (h11 : β (cSlot cOff hN 11) = 0) :
    (cInit4Rev cOff h12 hN).fwdBits β =
      update (update (update (update β
        (cSlot cOff hN 1) (β ⟨10, by omega⟩ * β ⟨11, by omega⟩))
        (cSlot cOff hN 9) (β ⟨11, by omega⟩ + β ⟨10, by omega⟩ * β ⟨11, by omega⟩))
        (cSlot cOff hN 6) (β ⟨10, by omega⟩ + β ⟨10, by omega⟩ * β ⟨11, by omega⟩))
        (cSlot cOff hN 11)
        (1 + β ⟨10, by omega⟩ + (β ⟨11, by omega⟩ + β ⟨10, by omega⟩ * β ⟨11, by omega⟩)) := by
  let c2 : Wire N := ⟨10, by omega⟩
  let c3 : Wire N := ⟨11, by omega⟩
  let s (k : Fin 16) := cSlot cOff hN k
  have hc2 (k : Fin 16) : c2 ≠ s k := fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp [c2, s, cSlot] at hv
    omega
  have hc3 (k : Fin 16) : c3 ≠ s k := fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp [c3, s, cSlot] at hv
    omega
  have hss (a b : Fin 16) (hab : a ≠ b) : s a ≠ s b := fun h ↦
    hab ((cSlot_eq_iff cOff hN a b).mp h)
  set g1 := update β (s 1) (β (s 1) + β c2 * β c3)
  set g2 := update g1 (s 9) (g1 (s 9) + g1 c3)
  set g3 := update g2 (s 9) (g2 (s 9) + g2 (s 1))
  set g4 := update g3 (s 6) (g3 (s 6) + g3 c2)
  set g5 := update g4 (s 6) (g4 (s 6) + g4 (s 1))
  set g6 := update g5 (s 11) (g5 (s 11) + 1)
  set g7 := update g6 (s 11) (g6 (s 11) + g6 c2)
  set g8 := update g7 (s 11) (g7 (s 11) + g7 (s 9))
  have hg_eq : (cInit4Rev cOff h12 hN).fwdBits β = g8 := rfl
  have hv1 : β (s 1) + β c2 * β c3 = β c2 * β c3 := by
    dsimp [s]
    rw [h1, zero_add]
  have hg1 : g1 = update β (s 1) (β c2 * β c3) := by
    dsimp only [g1]
    rw [hv1]
  have hv2 : g1 (s 9) + g1 c3 = β c3 := by
    rw [hg1, update_of_ne (hss 9 1 (by decide)), update_of_ne (hc3 1)]
    dsimp [s]
    rw [h9, zero_add]
  have hg2 : g2 = update g1 (s 9) (β c3) := by
    dsimp only [g2]
    rw [hv2]
  have hv3 : g2 (s 9) + g2 (s 1) = β c3 + β c2 * β c3 := by
    rw [hg2, update_self, update_of_ne (hss 1 9 (by decide)), hg1, update_self]
  have hg3 : g3 = update g1 (s 9) (β c3 + β c2 * β c3) := by
    dsimp only [g3]
    rw [hv3, hg2, update_idem]
  have hv4 : g3 (s 6) + g3 c2 = β c2 := by
    rw [hg3, update_of_ne (hss 6 9 (by decide)), update_of_ne (hc2 9),
      hg1, update_of_ne (hss 6 1 (by decide)), update_of_ne (hc2 1)]
    dsimp [s]
    rw [h6, zero_add]
  have hg4 : g4 = update g3 (s 6) (β c2) := by
    dsimp only [g4]
    rw [hv4]
  have hv5 : g4 (s 6) + g4 (s 1) = β c2 + β c2 * β c3 := by
    rw [hg4, update_self, update_of_ne (hss 1 6 (by decide)),
      hg3, update_of_ne (hss 1 9 (by decide)), hg1, update_self]
  have hg5 : g5 = update g3 (s 6) (β c2 + β c2 * β c3) := by
    dsimp only [g5]
    rw [hv5, hg4, update_idem]
  have hv6 : g5 (s 11) + 1 = 1 := by
    rw [hg5, update_of_ne (hss 11 6 (by decide)),
      hg3, update_of_ne (hss 11 9 (by decide)), hg1, update_of_ne (hss 11 1 (by decide))]
    dsimp [s]
    rw [h11, zero_add]
  have hg6 : g6 = update g5 (s 11) 1 := by
    dsimp only [g6]
    rw [hv6]
  have hv7 : g6 (s 11) + g6 c2 = 1 + β c2 := by
    rw [hg6, update_self, update_of_ne (hc2 11),
      hg5, update_of_ne (hc2 6), hg3, update_of_ne (hc2 9), hg1, update_of_ne (hc2 1)]
  have hg7 : g7 = update g5 (s 11) (1 + β c2) := by
    dsimp only [g7]
    rw [hv7, hg6, update_idem]
  have hv8 : g7 (s 11) + g7 (s 9) = 1 + β c2 + (β c3 + β c2 * β c3) := by
    rw [hg7, update_self, update_of_ne (hss 9 11 (by decide)),
      hg5, update_of_ne (hss 9 6 (by decide)), hg3, update_self]
  have hg8 : g8 = update g5 (s 11) (1 + β c2 + (β c3 + β c2 * β c3)) := by
    dsimp only [g8]
    rw [hv8, hg7, update_idem]
  rw [hg_eq, hg8, hg5, hg3, hg1]

/-- `0`-AND (`0-T`) 5-CNOT fan-in merging `{11, 12} -> 2` and `{9, 5, 1} -> 13`. -/
def cFan5Rev {N : ℕ} (cOff : ℕ) (hN : cOff + 16 ≤ N) : GroupUnary.RevCompute N :=
  let s (k : Fin 16) := cSlot cOff hN k
  have hss (a b : Fin 16) (hab : a ≠ b) : s a ≠ s b := fun h ↦
    hab ((cSlot_eq_iff cOff hN a b).mp h)
  .seq (.cnot (s 11) (s 2) (hss 11 2 (by decide)))
    (.seq (.cnot (s 12) (s 2) (hss 12 2 (by decide)))
      (.seq (.cnot (s 9) (s 13) (hss 9 13 (by decide)))
        (.seq (.cnot (s 5) (s 13) (hss 5 13 (by decide)))
          (.cnot (s 1) (s 13) (hss 1 13 (by decide))))))

theorem cFan5Rev_fwdBits_clean {N : ℕ} (cOff : ℕ) (hN : cOff + 16 ≤ N)
    (γ : BitAssignment N) (h2 : γ (cSlot cOff hN 2) = 0) (h13 : γ (cSlot cOff hN 13) = 0) :
    (cFan5Rev cOff hN).fwdBits γ =
      update (update γ
        (cSlot cOff hN 2) (γ (cSlot cOff hN 11) + γ (cSlot cOff hN 12)))
        (cSlot cOff hN 13)
        (γ (cSlot cOff hN 9) + (γ (cSlot cOff hN 5) + γ (cSlot cOff hN 1))) := by
  let s (k : Fin 16) := cSlot cOff hN k
  have hss (a b : Fin 16) (hab : a ≠ b) : s a ≠ s b := fun h ↦
    hab ((cSlot_eq_iff cOff hN a b).mp h)
  set g1 := update γ (s 2) (γ (s 2) + γ (s 11))
  set g2 := update g1 (s 2) (g1 (s 2) + g1 (s 12))
  set g3 := update g2 (s 13) (g2 (s 13) + g2 (s 9))
  set g4 := update g3 (s 13) (g3 (s 13) + g3 (s 5))
  set g5 := update g4 (s 13) (g4 (s 13) + g4 (s 1))
  have hg_eq : (cFan5Rev cOff hN).fwdBits γ = g5 := rfl
  have hv1 : γ (s 2) + γ (s 11) = γ (s 11) := by
    dsimp [s]
    rw [h2, zero_add]
  have hg1 : g1 = update γ (s 2) (γ (s 11)) := by
    dsimp only [g1]
    rw [hv1]
  have hv2 : g1 (s 2) + g1 (s 12) = γ (s 11) + γ (s 12) := by
    rw [hg1, update_self, update_of_ne (hss 12 2 (by decide))]
  have hg2 : g2 = update γ (s 2) (γ (s 11) + γ (s 12)) := by
    dsimp only [g2]
    rw [hv2, hg1, update_idem]
  have hv3 : g2 (s 13) + g2 (s 9) = γ (s 9) := by
    rw [hg2, update_of_ne (hss 13 2 (by decide)), update_of_ne (hss 9 2 (by decide))]
    dsimp [s]
    rw [h13, zero_add]
  have hg3 : g3 = update g2 (s 13) (γ (s 9)) := by
    dsimp only [g3]
    rw [hv3]
  have hv4 : g3 (s 13) + g3 (s 5) = γ (s 9) + γ (s 5) := by
    rw [hg3, update_self, update_of_ne (hss 5 13 (by decide)),
      hg2, update_of_ne (hss 5 2 (by decide))]
  have hg4 : g4 = update g2 (s 13) (γ (s 9) + γ (s 5)) := by
    dsimp only [g4]
    rw [hv4, hg3, update_idem]
  have hv5 : g4 (s 13) + g4 (s 1) = γ (s 9) + (γ (s 5) + γ (s 1)) := by
    rw [hg4, update_self, update_of_ne (hss 1 13 (by decide)),
      hg2, update_of_ne (hss 1 2 (by decide)), add_assoc]
  have hg5 : g5 = update g2 (s 13) (γ (s 9) + (γ (s 5) + γ (s 1))) := by
    dsimp only [g5]
    rw [hv5, hg4, update_idem]
  rw [hg_eq, hg5, hg2]

/-- `10`-AND classical reversible reference of `cFib11FwdDyn`. -/
def cFib11Rev {N : ℕ} (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N) :
    GroupUnary.RevCompute N :=
  .seq
    (.seq
      (.seq (cInit4Rev cOff h12 hN)
        (splitRevLoop ⟨8, by omega⟩ 4 _ _ (cSplit4Valid cOff h12 hN).toWPairDisj))
      (cFan5Rev cOff hN))
    (splitRevLoop ⟨9, by omega⟩ 5 _ _ (cSplit5Valid cOff h12 hN).toWPairDisj)

/-- `22-T` (`0 TOFF`) W-state `11`-fiber coin decoder on `cOff .. cOff + 15`. -/
def cFib11FwdDyn {Var : Type} {N : ℕ} (v : Var) (cOff : ℕ) (h12 : 12 ≤ cOff)
    (hN : cOff + 16 ≤ N) : DynamicCircuit Var N :=
  .seq
    (.seq
      (.seq (Lac2Folded184Select.revComputeDyn (cInit4Rev cOff h12 hN))
        (dWExpandDet1 v 4 ⟨8, by omega⟩ _ _ (cSlot cOff hN 15) (cSplit4Valid cOff h12 hN)))
      (Lac2Folded184Select.revComputeDyn (cFan5Rev cOff hN)))
    (dWExpandDet1 v 5 ⟨9, by omega⟩ _ _ (cSlot cOff hN 15) (cSplit5Valid cOff h12 hN))

@[simp]
theorem count_cFib11FwdDyn_toff {Var : Type} {N : ℕ} (v : Var) (cOff : ℕ)
    (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N) :
    (cFib11FwdDyn v cOff h12 hN).count .TOFF = 0 := by
  simp [cFib11FwdDyn, DynamicCircuit.count]

@[simp]
theorem count_cFib11FwdDyn_t {Var : Type} {N : ℕ} (v : Var) (cOff : ℕ)
    (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N) :
    (cFib11FwdDyn v cOff h12 hN).count .T = 22 := by
  simp [cFib11FwdDyn, DynamicCircuit.count, cInit4Rev, cFan5Rev, GroupUnary.RevCompute.numAnd]

/-- Swap disjoint `Fin 16` slot pairs when `b = true`. -/
def slotCswap (b : Bool) : List (Fin 16 × Fin 16) → (Fin 16 → Bool) → Fin 16 → Bool
  | [], st, s => st s
  | (a, c) :: ps, st, s =>
      if b && decide (s = a) then st c
      else if b && decide (s = c) then st a
      else slotCswap b ps st s

/-- Stage-0 slot bits of `cFib11` after `cInit4Rev`. -/
def cSt0 (b2 b3 : Bool) (s : Fin 16) : Bool :=
  ((s == 11) && !b2 && !b3) || ((s == 6) && b2 && !b3) ||
    ((s == 9) && !b2 && b3) || ((s == 1) && b2 && b3)

/-- Stage-1 slot bits of `cFib11` after `R = 4` split on `c₀`. -/
def cSt1 (b0 b2 b3 : Bool) : Fin 16 → Bool :=
  slotCswap b0 [(6, 8), (9, 5), (1, 0), (11, 12)] (cSt0 b2 b3)

/-- Stage-2 slot bits of `cFib11` after `cFan5Rev`. -/
def cSt2 (b0 b2 b3 : Bool) (s : Fin 16) : Bool :=
  if s == 2 then xor (cSt1 b0 b2 b3 11) (cSt1 b0 b2 b3 12)
  else if s == 13 then xor (cSt1 b0 b2 b3 9) (xor (cSt1 b0 b2 b3 5) (cSt1 b0 b2 b3 1))
  else cSt1 b0 b2 b3 s

/-- Stage-3 slot bits of `cFib11` after `R = 5` split on `c₁`. -/
def cSt3 (b0 b1 b2 b3 : Bool) : Fin 16 → Bool :=
  slotCswap b1 [(2, 7), (6, 3), (8, 4), (0, 10), (13, 14)] (cSt2 b0 b2 b3)

/-- Active `1`-hot index in `Fin 4` before Stage 1 of `cFib11`. -/
def cIStar0 (b2 b3 : Bool) : Fin 4 :=
  if b2 && !b3 then 0 else if !b2 && b3 then 1 else if b2 && b3 then 2 else 3

/-- Active `1`-hot index in `Fin 5` before Stage 3 of `cFib11`. -/
def cIStar2 (b0 b2 b3 : Bool) : Fin 5 :=
  if !b2 && !b3 then 0
  else if b2 && !b3 && !b0 then 1
  else if b2 && !b3 && b0 then 2
  else if b2 && b3 && b0 then 3
  else 4

theorem cSt0_inv_props (b2 b3 : Bool) :
    cSt0 b2 b3 15 = false ∧ (∀ i : Fin 4, cSt0 b2 b3 (cS4_1 i) = false) ∧
    cSt0 b2 b3 (cS4_0 (cIStar0 b2 b3)) = true ∧
    (∀ i : Fin 4, i ≠ cIStar0 b2 b3 → cSt0 b2 b3 (cS4_0 i) = false) := by
  revert b3 b2
  decide

theorem cSt1_step_props (b0 b2 b3 : Bool) :
    (∀ i : Fin 4, cSt1 b0 b2 b3 (cS4_0 i) =
      if b0 then cSt0 b2 b3 (cS4_1 i) else cSt0 b2 b3 (cS4_0 i)) ∧
    (∀ i : Fin 4, cSt1 b0 b2 b3 (cS4_1 i) =
      if b0 then cSt0 b2 b3 (cS4_0 i) else cSt0 b2 b3 (cS4_1 i)) ∧
    (∀ s : Fin 16, (∀ i, s ≠ cS4_0 i) → (∀ i, s ≠ cS4_1 i) →
      cSt1 b0 b2 b3 s = cSt0 b2 b3 s) ∧
    cSt1 b0 b2 b3 2 = false ∧ cSt1 b0 b2 b3 13 = false := by
  revert b3 b2 b0
  decide

theorem cSt2_inv_props (b0 b2 b3 : Bool) :
    cSt2 b0 b2 b3 15 = false ∧ (∀ i : Fin 5, cSt2 b0 b2 b3 (cS5_1 i) = false) ∧
    cSt2 b0 b2 b3 (cS5_0 (cIStar2 b0 b2 b3)) = true ∧
    (∀ i : Fin 5, i ≠ cIStar2 b0 b2 b3 → cSt2 b0 b2 b3 (cS5_0 i) = false) := by
  revert b3 b2 b0
  decide

theorem cSt3_step_props (b0 b1 b2 b3 : Bool) :
    (∀ i : Fin 5, cSt3 b0 b1 b2 b3 (cS5_0 i) =
      if b1 then cSt2 b0 b2 b3 (cS5_1 i) else cSt2 b0 b2 b3 (cS5_0 i)) ∧
    (∀ i : Fin 5, cSt3 b0 b1 b2 b3 (cS5_1 i) =
      if b1 then cSt2 b0 b2 b3 (cS5_0 i) else cSt2 b0 b2 b3 (cS5_1 i)) ∧
    (∀ s : Fin 16, (∀ i, s ≠ cS5_0 i) → (∀ i, s ≠ cS5_1 i) →
      cSt3 b0 b1 b2 b3 s = cSt2 b0 b2 b3 s) := by
  revert b3 b2 b1 b0
  decide

theorem cSt3_coinOptFib (c : Fin (2 ^ 4)) (f : Fin 10) :
    cSt3 (z2b (basisBits 4 c 0)) (z2b (basisBits 4 c 1))
      (z2b (basisBits 4 c 2)) (z2b (basisBits 4 c 3)) ⟨f.val, by omega⟩ =
      (coinOptFib c == some f) := by
  revert f c
  decide

theorem cswap_cSlot_eq {N R : ℕ} (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N)
    (ctrlIdx : Fin 12) (s0 s1 : Fin R → Fin 16)
    (hv : WSplitValid R ⟨ctrlIdx.val, by omega⟩ (fun i ↦ cSlot cOff hN (s0 i))
      (fun i ↦ cSlot cOff hN (s1 i)) (cSlot cOff hN 15))
    (γ : BitAssignment N) (st st' : Fin 16 → Bool)
    (hγ : ∀ s : Fin 16, γ (cSlot cOff hN s) = b2z (st s))
    (h0 : ∀ i : Fin R,
      st' (s0 i) = if z2b (γ ⟨ctrlIdx.val, by omega⟩) then st (s1 i) else st (s0 i))
    (h1 : ∀ i : Fin R,
      st' (s1 i) = if z2b (γ ⟨ctrlIdx.val, by omega⟩) then st (s0 i) else st (s1 i))
    (ho : ∀ s : Fin 16, (∀ i, s ≠ s0 i) → (∀ i, s ≠ s1 i) → st' s = st s) :
    let γ' := cswapRangeBits R ⟨ctrlIdx.val, by omega⟩
      (fun i ↦ cSlot cOff hN (s0 i)) (fun i ↦ cSlot cOff hN (s1 i)) γ
    (∀ s : Fin 16, γ' (cSlot cOff hN s) = b2z (st' s)) ∧
    (∀ u : Wire N, (u.val < cOff ∨ cOff + 16 ≤ u.val) → γ' u = γ u) := by
  intro γ'
  dsimp only [γ']
  have hinj (a b : Fin 16) (h : cSlot cOff hN a = cSlot cOff hN b) : a = b :=
    (cSlot_eq_iff cOff hN a b).mp h
  have huNe (u : Wire N) (hu : u.val < cOff ∨ cOff + 16 ≤ u.val) (k : Fin 16) :
      u ≠ cSlot cOff hN k := fun he ↦ by
    have hv := congrArg Fin.val he
    dsimp [cSlot] at hv
    omega
  refine ⟨fun s ↦ ?_, fun u hu ↦ cswapRangeBits_other γ
    (fun i ↦ huNe u hu (s0 i)) (fun i ↦ huNe u hu (s1 i))⟩
  by_cases hs0 : ∃ i, s = s0 i
  · obtain ⟨i, rfl⟩ := hs0
    rw [cswapRangeBits_w0 hv.toWPairDisj γ i, hγ, hγ, h0 i]
    rcases bit_cases (γ ⟨ctrlIdx.val, by omega⟩) with hc | hc <;> simp [hc, z2b]
  · by_cases hs1 : ∃ i, s = s1 i
    · obtain ⟨i, rfl⟩ := hs1
      rw [cswapRangeBits_w1 hv.toWPairDisj γ i, hγ, hγ, h1 i]
      rcases bit_cases (γ ⟨ctrlIdx.val, by omega⟩) with hc | hc <;> simp [hc, z2b]
    · rw [cswapRangeBits_other γ (fun i he ↦ hs0 ⟨i, hinj _ _ he⟩)
        (fun i he ↦ hs1 ⟨i, hinj _ _ he⟩), hγ,
        ho s (fun i he ↦ hs0 ⟨i, he⟩) (fun i he ↦ hs1 ⟨i, he⟩)]

theorem cFib11_equiv_and_spec {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) (cOff : ℕ) (h12 : 12 ≤ cOff) (hN : cOff + 16 ≤ N)
    (S : BitAssignment N → Bool)
    (hClean16 : ∀ β, S β = true → ∀ s : Fin 16, β (cSlot cOff hN s) = 0) :
    EquivRev v S (cFib11Rev cOff h12 hN) (cFib11FwdDyn v cOff h12 hN) ∧
    ∀ β, S β = true →
      let γ := (cFib11Rev cOff h12 hN).fwdBits β
      let c : Fin (2 ^ 4) := Comparators.localIdx (QRegister.block 8 4 (by omega)) β
      (∀ u : Wire N, (u.val < cOff ∨ cOff + 16 ≤ u.val) → γ u = β u) ∧
      ∀ f : Fin 10,
        γ (cSlot cOff hN ⟨f.val, by omega⟩) = b2z (coinOptFib c == some f) := by
  let p0 := cInit4Rev cOff h12 hN
  let p1 := splitRevLoop (N := N) ⟨8, by omega⟩ 4 _ _ (cSplit4Valid cOff h12 hN).toWPairDisj
  let p2 := cFan5Rev cOff hN
  let p3 := splitRevLoop (N := N) ⟨9, by omega⟩ 5 _ _ (cSplit5Valid cOff h12 hN).toWPairDisj
  have hTrace (β : BitAssignment N) (hS : S β = true) :
      p0.validOn β = true ∧
      InvWSplitDet 4 (fun i ↦ cSlot cOff hN (cS4_0 i)) (fun i ↦ cSlot cOff hN (cS4_1 i))
        (cSlot cOff hN 15) (p0.fwdBits β) ∧
      InvWSplitDet 5 (fun i ↦ cSlot cOff hN (cS5_0 i)) (fun i ↦ cSlot cOff hN (cS5_1 i))
        (cSlot cOff hN 15) (((p0.seq p1).seq p2).fwdBits β) ∧
      (∀ u : Wire N, (u.val < cOff ∨ cOff + 16 ≤ u.val) →
        (cFib11Rev cOff h12 hN).fwdBits β u = β u) ∧
      ∀ f : Fin 10,
        (cFib11Rev cOff h12 hN).fwdBits β (cSlot cOff hN ⟨f.val, by omega⟩) =
          b2z (coinOptFib
            (Comparators.localIdx (QRegister.block 8 4 (by omega)) β) == some f) := by
    have hc := hClean16 β hS
    set b0 := z2b (β ⟨8, by omega⟩)
    set b1 := z2b (β ⟨9, by omega⟩)
    set b2 := z2b (β ⟨10, by omega⟩)
    set b3 := z2b (β ⟨11, by omega⟩)
    have hv0 : p0.validOn β = true := by simp [p0, cInit4Rev, GroupUnary.RevCompute.validOn, hc 1]
    have hcs (w : Wire N) (hw : w.val < cOff ∨ cOff + 16 ≤ w.val) (k : Fin 16) :
        w ≠ cSlot cOff hN k := fun h ↦ by
      have hv := congrArg Fin.val h
      dsimp [cSlot] at hv
      omega
    set γ0 := p0.fwdBits β
    have hγ0_clean := cInit4Rev_fwdBits_clean cOff h12 hN β (hc 1) (hc 6) (hc 9) (hc 11)
    have hγ0_out (u : Wire N) (hu : u.val < cOff ∨ cOff + 16 ≤ u.val) : γ0 u = β u := by
      rw [show γ0 = (cInit4Rev cOff h12 hN).fwdBits β from rfl, hγ0_clean,
        update_of_ne (hcs u hu 11), update_of_ne (hcs u hu 6),
        update_of_ne (hcs u hu 9), update_of_ne (hcs u hu 1)]
    have hγ0_slot (s : Fin 16) : γ0 (cSlot cOff hN s) = b2z (cSt0 b2 b3 s) := by
      rw [show γ0 = (cInit4Rev cOff h12 hN).fwdBits β from rfl, hγ0_clean]
      simp only [Function.update_apply, Fin.ext_iff]
      fin_cases s <;>
        (rcases bit_cases (β ⟨10, by omega⟩) with h2 | h2 <;>
          rcases bit_cases (β ⟨11, by omega⟩) with h3 | h3 <;>
          simp [b2, b3, h2, h3, hc, cSt0, z2b, b2z])
    obtain ⟨hq0_15, hw4_1, hi4_1, hi4_0⟩ := cSt0_inv_props b2 b3
    have hInv1 : InvWSplitDet 4 (fun i ↦ cSlot cOff hN (cS4_0 i))
        (fun i ↦ cSlot cOff hN (cS4_1 i)) (cSlot cOff hN 15) γ0 :=
      ⟨by
        rw [hγ0_slot, hq0_15]
        rfl,
        fun i ↦ by
          rw [hγ0_slot, hw4_1 i]
          rfl,
        cIStar0 b2 b3,
        by
          rw [hγ0_slot, hi4_1]
          rfl,
        fun i hi ↦ by
          rw [hγ0_slot, hi4_0 i hi]
          rfl⟩
    set γ1 := p1.fwdBits γ0
    have hγ1_eq : γ1 = cswapRangeBits 4 ⟨8, by omega⟩ _ _ γ0 :=
      (splitRevLoop_spec ⟨8, by omega⟩ 4 _ _ (cSplit4Valid cOff h12 hN).toWPairDisj γ0 hInv1.2.1).2
    have h8lt : (⟨8, by omega⟩ : Wire N).val < cOff := by
      dsimp
      omega
    have hb0_γ0 : z2b (γ0 ⟨8, by omega⟩) = b0 := by rw [hγ0_out _ (Or.inl h8lt)]
    obtain ⟨hs1_0, hs1_1, hs1_o, hc1_2, hc1_13⟩ := cSt1_step_props b0 b2 b3
    obtain ⟨hγ1_slot, hγ1_out⟩ := cswap_cSlot_eq cOff h12 hN ⟨8, by decide⟩ cS4_0 cS4_1
      (cSplit4Valid cOff h12 hN) γ0 (cSt0 b2 b3) (cSt1 b0 b2 b3) hγ0_slot
      (fun i ↦ by
        dsimp
        rw [hb0_γ0]
        exact hs1_0 i)
      (fun i ↦ by
        dsimp
        rw [hb0_γ0]
        exact hs1_1 i) hs1_o
    rw [← hγ1_eq] at hγ1_slot hγ1_out
    set γ2 := p2.fwdBits γ1
    have hγ1_s2 : γ1 (cSlot cOff hN 2) = 0 := by
      rw [hγ1_slot, hc1_2]
      rfl
    have hγ1_s13 : γ1 (cSlot cOff hN 13) = 0 := by
      rw [hγ1_slot, hc1_13]
      rfl
    have hγ2_clean := cFan5Rev_fwdBits_clean cOff hN γ1 hγ1_s2 hγ1_s13
    have hγ2_out (u : Wire N) (hu : u.val < cOff ∨ cOff + 16 ≤ u.val) : γ2 u = β u := by
      have h : γ2 u = γ1 u := by
        rw [show γ2 = (cFan5Rev cOff hN).fwdBits γ1 from rfl, hγ2_clean,
          update_of_ne (hcs u hu 13), update_of_ne (hcs u hu 2)]
      exact h.trans ((hγ1_out u hu).trans (hγ0_out u hu))
    have hγ2_slot (s : Fin 16) : γ2 (cSlot cOff hN s) = b2z (cSt2 b0 b2 b3 s) := by
      rw [show γ2 = (cFan5Rev cOff hN).fwdBits γ1 from rfl, hγ2_clean]
      simp only [Function.update_apply, Fin.ext_iff, hγ1_slot]
      fin_cases s <;>
        simp [cSt2, b2z_xor]
    obtain ⟨hq2_15, hw5_1, hi5_1, hi5_0⟩ := cSt2_inv_props b0 b2 b3
    have hInv2 : InvWSplitDet 5 (fun i ↦ cSlot cOff hN (cS5_0 i))
        (fun i ↦ cSlot cOff hN (cS5_1 i)) (cSlot cOff hN 15) γ2 :=
      ⟨by
        rw [hγ2_slot, hq2_15]
        rfl,
        fun i ↦ by
          rw [hγ2_slot, hw5_1 i]
          rfl,
        cIStar2 b0 b2 b3,
        by
          rw [hγ2_slot, hi5_1]
          rfl,
        fun i hi ↦ by
          rw [hγ2_slot, hi5_0 i hi]
          rfl⟩
    set γ3 := p3.fwdBits γ2
    have hγ3_eq : γ3 = cswapRangeBits 5 ⟨9, by omega⟩ _ _ γ2 :=
      (splitRevLoop_spec ⟨9, by omega⟩ 5 _ _ (cSplit5Valid cOff h12 hN).toWPairDisj γ2 hInv2.2.1).2
    have h9lt : (⟨9, by omega⟩ : Wire N).val < cOff := by
      dsimp
      omega
    have hb1_γ2 : z2b (γ2 ⟨9, by omega⟩) = b1 := by rw [hγ2_out _ (Or.inl h9lt)]
    obtain ⟨hs3_0, hs3_1, hs3_o⟩ := cSt3_step_props b0 b1 b2 b3
    obtain ⟨hγ3_slot, hγ3_out⟩ := cswap_cSlot_eq cOff h12 hN ⟨9, by decide⟩ cS5_0 cS5_1
      (cSplit5Valid cOff h12 hN) γ2 (cSt2 b0 b2 b3) (cSt3 b0 b1 b2 b3) hγ2_slot
      (fun i ↦ by
        dsimp
        rw [hb1_γ2]
        exact hs3_0 i)
      (fun i ↦ by
        dsimp
        rw [hb1_γ2]
        exact hs3_1 i) hs3_o
    rw [← hγ3_eq] at hγ3_slot hγ3_out
    let c := Comparators.localIdx (QRegister.block 8 4 (by omega)) β
    have hcb (j : Fin 4) : basisBits 4 c j = β ⟨8 + j.val, by omega⟩ := by
      change basisBits 4 ((basisBits 4).symm _) j = _
      rw [Comparators.basisBits_basisBitsEquiv_symm]
      rfl
    refine ⟨hv0, hInv1, hInv2, fun u hu ↦ (hγ3_out u hu).trans (hγ2_out u hu), fun f ↦ ?_⟩
    change γ3 (cSlot cOff hN ⟨f.val, by omega⟩) = b2z (coinOptFib c == some f)
    rw [hγ3_slot, ← cSt3_coinOptFib c f]
    simp only [hcb 0, hcb 1, hcb 2, hcb 3, Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 4).val = 3 from rfl, add_zero, b0, b1, b2, b3]
  have e0 : EquivRev v S p0 (Lac2Folded184Select.revComputeDyn p0) :=
    EquivRev.ofRevCompute v S p0 fun β hS ↦ (hTrace β hS).1
  have e1 : EquivRev v (fun γ ↦ S (p0.invBits γ)) p1
      (dWExpandDet1 v 4 ⟨8, by omega⟩ _ _ (cSlot cOff hN 15) (cSplit4Valid cOff h12 hN)) :=
    EquivRev.ofDWExpandDet1 v 4 _ _ _ _ (cSplit4Valid cOff h12 hN) _ fun γ hγ ↦ by
      have h := (hTrace (p0.invBits γ) hγ).2.1
      rwa [p0.fwdBits_invBits] at h
  have e2 : EquivRev v (fun γ ↦ S ((p0.seq p1).invBits γ)) p2
      (Lac2Folded184Select.revComputeDyn p2) :=
    EquivRev.ofRevCompute v _ p2 fun _ _ ↦ rfl
  have e3 : EquivRev v (fun γ ↦ S (((p0.seq p1).seq p2).invBits γ)) p3
      (dWExpandDet1 v 5 ⟨9, by omega⟩ _ _ (cSlot cOff hN 15) (cSplit5Valid cOff h12 hN)) :=
    EquivRev.ofDWExpandDet1 v 5 _ _ _ _ (cSplit5Valid cOff h12 hN) _ fun γ hγ ↦ by
      have h := (hTrace (((p0.seq p1).seq p2).invBits γ) hγ).2.2.1
      rwa [((p0.seq p1).seq p2).fwdBits_invBits] at h
  exact ⟨((e0.seq e1).seq e2).seq e3, fun β hS ↦ ⟨(hTrace β hS).2.2.2.1, (hTrace β hS).2.2.2.2⟩⟩

theorem revDisjRange_cFib11Rev {N : ℕ} (cOff : ℕ) (h16 : 16 ≤ cOff) (hN : cOff + 16 ≤ N) :
    RevDisjRange 12 16 (cFib11Rev cOff (by omega) hN) := by
  have hs (k : Fin 16) : (cSlot cOff hN k).val < 12 ∨ 16 ≤ (cSlot cOff hN k).val :=
    Or.inr (by
      dsimp [cSlot]
      omega)
  have hc (w : ℕ) (hw : w < 12) : w < 12 ∨ 16 ≤ w := Or.inl hw
  have h8 : (⟨8, by omega⟩ : Wire N).val < 12 ∨ 16 ≤ (⟨8, by omega⟩ : Wire N).val :=
    Or.inl (by
      dsimp
      omega)
  have h9 : (⟨9, by omega⟩ : Wire N).val < 12 ∨ 16 ≤ (⟨9, by omega⟩ : Wire N).val :=
    Or.inl (by
      dsimp
      omega)
  refine ⟨⟨⟨?_,
    revDisjRange_splitRevLoop 12 16 ⟨8, by omega⟩ h8 4 _ _ _
      (fun _ ↦ hs _) (fun _ ↦ hs _)⟩, ?_⟩,
    revDisjRange_splitRevLoop 12 16 ⟨9, by omega⟩ h9 5 _ _ _
      (fun _ ↦ hs _) (fun _ ↦ hs _)⟩
  · dsimp [cInit4Rev, RevDisjRange]
    exact ⟨⟨hc 10 (by omega), hc 11 (by omega), hs 1⟩, ⟨hc 11 (by omega), hs 9⟩, ⟨hs 1, hs 9⟩,
      ⟨hc 10 (by omega), hs 6⟩, ⟨hs 1, hs 6⟩, hs 11, ⟨hc 10 (by omega), hs 11⟩, ⟨hs 9, hs 11⟩⟩
  · dsimp [cFan5Rev, RevDisjRange]
    exact ⟨⟨hs 11, hs 2⟩, ⟨hs 12, hs 2⟩, ⟨hs 9, hs 13⟩, ⟨hs 5, hs 13⟩, ⟨hs 1, hs 13⟩⟩

/-! ### `12-T` `5`-Pair Hadamard Gadget (`quad5GadC`), `quad5FixC`, and `fix46x10C` -/

theorem anf2_eval_zmod2 (F : Fin 4 → ZMod 2) (x0 x1 : ZMod 2) :
    F 0 + x0 * (F 0 + F 1) + x1 * (F 0 + F 2) + (x0 * x1) * (F 0 + F 1 + F 2 + F 3) =
      F ⟨bit01Nat x0 + 2 * bit01Nat x1, by
        have h0 := bit01Nat_le_one x0
        have h1 := bit01Nat_le_one x1
        omega⟩ := by
  revert x1 x0 F
  decide

/-- `56`-variable type `Sum (Fin 46) (Fin 10)` for `(rHot46, rFib10)`. -/
abbrev Var56 : Type := Sum (Fin 46) (Fin 10)

/-- `Var56` list of active `Fin 46` group indices `< m` in `mask`. -/
def hotVars46 (mask : Fin 46 → Bool) : (m : ℕ) → m ≤ 46 → List Var56
  | 0, _ => []
  | m + 1, hm =>
      if mask ⟨m, hm⟩ then Sum.inl ⟨m, hm⟩ :: hotVars46 mask m (Nat.le_of_succ_le hm)
      else hotVars46 mask m (Nat.le_of_succ_le hm)

theorem b2z_hotVars46 (mask : Fin 46 → Bool) (f : Var56 → Bool) :
    ∀ (m : ℕ) (hm : m ≤ 46),
      b2z (evLin f (hotVars46 mask m hm)) =
        ∑ j : Fin m, b2z (mask ⟨j.val, j.isLt.trans_le hm⟩) *
          b2z (f (Sum.inl ⟨j.val, j.isLt.trans_le hm⟩))
  | 0, _ => rfl
  | m + 1, hm => by
      rw [Fin.sum_univ_castSucc]
      dsimp only [hotVars46]
      by_cases hr : mask ⟨m, hm⟩
      · simp only [hr, ↓reduceIte, evLin, b2z_xor, Fin.val_castSucc, Fin.val_last, b2z_true,
          one_mul, b2z_hotVars46 mask f m (Nat.le_of_succ_le hm)]
        exact add_comm _ _
      · simp only [hr, Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Fin.val_last, b2z_false,
          zero_mul, add_zero, b2z_hotVars46 mask f m (Nat.le_of_succ_le hm)]

/-- Ideal `Var56` environment at one-hot group `g : Fin 46` and optional fiber `optF`. -/
abbrev idEnv56 (g : Fin 46) (optF : Option (Fin 10)) : Var56 → Bool
  | .inl i => decide (i = g)
  | .inr j => optF == some j

theorem b2z_hotVars46_idEnv (mask : Fin 46 → Bool) (g : Fin 46) (optF : Option (Fin 10)) :
    b2z (evLin (idEnv56 g optF) (hotVars46 mask 46 le_rfl)) = b2z (mask g) := by
  rw [b2z_hotVars46, Finset.sum_eq_single g]
  · simp [idEnv56, b2z]
  · intro j _ hj
    simp [idEnv56, hj, b2z]
  · intro h
    exact False.elim (h (Finset.mem_univ g))

/-- Bilinear `Var56` pair `(F_b ⊕ R_a(g), F_a ⊕ R_b(g))` for `M : Fin 46 → Fin 10 → Bool`. -/
def quad5Pair (M : Fin 46 → Fin 10 → Bool) (a b : Fin 10) : AffPair Var56 :=
  ((false, Sum.inr b :: hotVars46 (fun g ↦ M g a) 46 le_rfl),
   (false, Sum.inr a :: hotVars46 (fun g ↦ M g b) 46 le_rfl))

/-- `5` bilinear `Var56` pairs factoring `46 × 10` matrix `M`. -/
def quad5Pairs (M : Fin 46 → Fin 10 → Bool) : List (AffPair Var56) :=
  [quad5Pair M 0 1, quad5Pair M 2 3, quad5Pair M 4 5, quad5Pair M 6 7, quad5Pair M 8 9]

/-- Diagonal `Fin 46` mask `⨁_{t=0}^4 (M_{g,2t} ∧ M_{g,2t+1})` cancelling `F = 0` cross terms. -/
def quad5DiagMask (M : Fin 46 → Fin 10 → Bool) (g : Fin 46) : Bool :=
  xor (xor (M g 0 && M g 1) (M g 2 && M g 3))
    (xor (M g 4 && M g 5) (xor (M g 6 && M g 7) (M g 8 && M g 9)))

/-- Diagonal `Var56` linear correction list for `quad5Pairs M`. -/
def quad5Diag (M : Fin 46 → Fin 10 → Bool) : List Var56 :=
  hotVars46 (quad5DiagMask M) 46 le_rfl

theorem xorPairs_quad5_idEnv56 (M : Fin 46 → Fin 10 → Bool) (g : Fin 46)
    (optF : Option (Fin 10)) :
    xor (xorPairs (idEnv56 g optF) (quad5Pairs M)) (evLin (idEnv56 g optF) (quad5Diag M)) =
      match optF with
      | some f => M g f
      | none => false := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  rcases optF with _ | f
  · dsimp only
    rw [← z2b_b2z (xor _ _), ← z2b_b2z false]
    congr 1
    simp only [quad5Pairs, quad5Pair, quad5Diag, xorPairs, evStep, evLin, Bool.xor_false,
      b2z_xor, b2z_and, b2z_hotVars46_idEnv, quad5DiagMask, idEnv56]
    simp only [show ∀ k : Fin 10, (none == some k) = false from fun _ ↦ rfl, b2z_false]
    ring_nf
    simp [h2]
  · dsimp only
    rw [← z2b_b2z (xor _ _), ← z2b_b2z (M g f)]
    congr 1
    simp only [quad5Pairs, quad5Pair, quad5Diag, xorPairs, evStep, evLin, Bool.xor_false,
      b2z_xor, b2z_and, b2z_hotVars46_idEnv, quad5DiagMask]
    have hf2 (h : 2 < 10) : (⟨2, h⟩ : Fin 10) = 2 := rfl
    have hf3 (h : 3 < 10) : (⟨3, h⟩ : Fin 10) = 3 := rfl
    have hf4 (h : 4 < 10) : (⟨4, h⟩ : Fin 10) = 4 := rfl
    have hf5 (h : 5 < 10) : (⟨5, h⟩ : Fin 10) = 5 := rfl
    have hf6 (h : 6 < 10) : (⟨6, h⟩ : Fin 10) = 6 := rfl
    have hf7 (h : 7 < 10) : (⟨7, h⟩ : Fin 10) = 7 := rfl
    have hf8 (h : 8 < 10) : (⟨8, h⟩ : Fin 10) = 8 := rfl
    have hf9 (h : 9 < 10) : (⟨9, h⟩ : Fin 10) = 9 := rfl
    have hbeq (a b : Fin 10) : (some a == some b) = decide (a.val = b.val) := by
      revert b a
      decide
    fin_cases f <;> (
      dsimp only [idEnv56]
      simp only [Fin.zero_eta, Fin.mk_one, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hbeq,
        Fin.val_zero, Fin.val_one,
        show (2 : Fin 10).val = 2 from rfl, show (3 : Fin 10).val = 3 from rfl,
        show (4 : Fin 10).val = 4 from rfl, show (5 : Fin 10).val = 5 from rfl,
        show (6 : Fin 10).val = 6 from rfl, show (7 : Fin 10).val = 7 from rfl,
        show (8 : Fin 10).val = 8 from rfl, show (9 : Fin 10).val = 9 from rfl,
        Nat.reduceEqDiff, decide_true, decide_false, b2z_true, b2z_false]
      ring_nf
      simp [h2])

/-- Read `Var56 → Bool` from `(rHot, rFib)` on `γ : BitAssignment N`. -/
abbrev env56 {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N) (γ : BitAssignment N) :
    Var56 → Bool
  | .inl i => z2b (γ (rHot i))
  | .inr j => z2b (γ (rFib j))

/-- Map `Var56` to `CtrlWire N t` for `(rHot, rFib)` disjoint from `t`. -/
def vCtrl56 {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N) (t : Wire N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) : Var56 → CtrlWire N t
  | .inl i => ⟨rHot i, hHT i⟩
  | .inr j => ⟨rFib j, hFT j⟩

theorem ctrl_env56 {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N) (t : Wire N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) (γ : BitAssignment N) :
    (fun c : CtrlWire N t ↦ z2b (γ c.1)) ∘ vCtrl56 rHot rFib t hHT hFT = env56 rHot rFib γ := by
  funext v
  rcases v with _ | _ <;> rfl

theorem env56_upd {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N) {w : Wire N}
    (hHT : ∀ i, rHot i ≠ w) (hFT : ∀ j, rFib j ≠ w) (γ : BitAssignment N) (val : ZMod 2) :
    env56 rHot rFib (update γ w val) = env56 rHot rFib γ := by
  funext v
  rcases v with i | j
  · exact congrArg z2b (update_of_ne (hHT i) val γ)
  · exact congrArg z2b (update_of_ne (hFT j) val γ)

/-- Raw `ZMod 2` bit computed by `quad5GadC` on `γ : BitAssignment N`. -/
abbrev quad5Bit {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (M : Fin 46 → Fin 10 → Bool) (γ : BitAssignment N) : ZMod 2 :=
  b2z (xor (xorPairs (env56 rHot rFib γ) (quad5Pairs M))
    (evLin (env56 rHot rFib γ) (quad5Diag M)))

theorem quad5Bit_upd {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N) {w : Wire N}
    (hHT : ∀ i, rHot i ≠ w) (hFT : ∀ j, rFib j ≠ w) (M : Fin 46 → Fin 10 → Bool)
    (γ : BitAssignment N) (val : ZMod 2) :
    quad5Bit rHot rFib M (update γ w val) = quad5Bit rHot rFib M γ := by
  simp only [quad5Bit, env56_upd rHot rFib hHT hFT]

/-- Boolean carry phase `s₂` of `lempelSch (quad5Pairs M)` on `env : Var56 → Bool`. -/
abbrev quad5CarryBool (env : Var56 → Bool) (M : Fin 46 → Fin 10 → Bool) : Bool :=
  let sch := lempelSch (quad5Pairs M)
  (evalHGad env sch.1 sch.2.1 sch.2.2.1 sch.2.2.2).2.2.2

/-- `12-T` (`0 TOFF`) `5`-pair Hadamard gadget loading `quad5Bit` onto clean wire `t`. -/
def quad5GadC {N : ℕ} (t : Wire N) (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) (M : Fin 46 → Fin 10 → Bool) : Circuit N :=
  let sch := lempelSch (quad5Pairs M)
  let emb := vCtrl56 rHot rFib t hHT hFT
  hGadC t (sch.1.map (mapAff emb)) (sch.2.1.map (mapAff emb)) sch.2.2.1 (sch.2.2.2.map emb) ;;ᶜ
    pLinsC t ((quad5Diag M).map emb)

@[simp]
theorem count_quad5GadC_toff {N : ℕ} (t : Wire N) (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) (M : Fin 46 → Fin 10 → Bool) :
    (quad5GadC t rHot rFib hHT hFT M).count .TOFF = 0 := by simp [quad5GadC]

@[simp]
theorem count_quad5GadC_t {N : ℕ} (t : Wire N) (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) (M : Fin 46 → Fin 10 → Bool) :
    (quad5GadC t rHot rFib hHT hFT M).count .T = 12 := by
  have hl := lempel_lens (quad5Pairs M)
  have hp : (quad5Pairs M).length = 5 := rfl
  simp only [quad5GadC, Circuit.count_seq, count_hGadgetCirc_t, count_parLinsCirc_t,
    List.length_map, hl.1, hl.2, hp]

theorem evLin_map {α β : Type} (f : β → Bool) (g : α → β) :
    ∀ l : List α, evLin f (l.map g) = evLin (f ∘ g) l
  | [] => rfl
  | _ :: xs => by simp [evLin, evLin_map f g xs]

theorem ket_quad5GadC_zero {N : ℕ} (t : Wire N) (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) (M : Fin 46 → Fin 10 → Bool)
    (γ : BitAssignment N) (ht0 : γ t = 0) :
    (quad5GadC t rHot rFib hHT hFT M).eval.1.mulVec (XMeasCircuit.ket γ) =
      bitSign (b2z (quad5CarryBool (env56 rHot rFib γ) M)) •
        XMeasCircuit.ket (update γ t (quad5Bit rHot rFib M γ)) := by
  set sch := lempelSch (quad5Pairs M)
  set emb := vCtrl56 rHot rFib t hHT hFT
  obtain ⟨hacc, hs0, hs1⟩ := evalHGad_lempel (env56 rHot rFib γ) (quad5Pairs M)
  have hevMap : evalHGad (fun c ↦ z2b (γ c.1)) (sch.1.map (mapAff emb))
      (sch.2.1.map (mapAff emb)) sch.2.2.1 (sch.2.2.2.map emb) =
      evalHGad (env56 rHot rFib γ) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2 := by
    simpa [emb, ctrl_env56] using
      evalHGad_map (fun c ↦ z2b (γ c.1)) emb sch.1 sch.2.1 sch.2.2
  have hlen8 : ((sch.1.map (mapAff emb)).length : ZMod 8) +
      7 * ((sch.2.1.map (mapAff emb)).length : ZMod 8) = 0 := by
    have hl := lempel_lens (quad5Pairs M)
    have hp : (quad5Pairs M).length = 5 := rfl
    rw [List.length_map, List.length_map, hl.1, hl.2, hp]
    decide
  have haccMap : (evalHGad (fun c ↦ z2b (γ c.1)) (sch.1.map (mapAff emb))
      (sch.2.1.map (mapAff emb)) sch.2.2.1 (sch.2.2.2.map emb)).1 = false := by
    rw [hevMap]
    exact hacc
  have hs0Map : (evalHGad (fun c ↦ z2b (γ c.1)) (sch.1.map (mapAff emb))
      (sch.2.1.map (mapAff emb)) sch.2.2.1 (sch.2.2.2.map emb)).2.1 = false := by
    rw [hevMap]
    exact hs0
  have hG := ket_hGad_zero t (sch.1.map (mapAff emb)) (sch.2.1.map (mapAff emb))
    sch.2.2.1 (sch.2.2.2.map emb) hlen8 γ ht0 haccMap hs0Map
  rw [hevMap, hs1] at hG
  change (hGadC t _ _ _ _ ;;ᶜ pLinsC t ((quad5Diag M).map emb)).eval.1.mulVec _ = _
  rw [eval_seq_mv, hG, mulVec_smul, ket_parLinsCirc_upd, evLin_map, ctrl_env56]

/-- `0-T` single-qubit `Z` sweep over `ws : List (Wire n)`. -/
def zLinsC {n : ℕ} : List (Wire n) → Circuit n
  | [] => .identity
  | w :: ws => Circuit.Z w ;;ᶜ zLinsC ws

@[simp]
theorem count_zLinsC_toff {n : ℕ} (ws : List (Wire n)) : (zLinsC ws).count .TOFF = 0 := by
  induction ws with
  | nil => rfl
  | cons _ _ ih => simp [zLinsC, ih]

@[simp]
theorem count_zLinsC_t {n : ℕ} (ws : List (Wire n)) : (zLinsC ws).count .T = 0 := by
  induction ws with
  | nil => rfl
  | cons _ _ ih => simp [zLinsC, ih]

theorem ket_zLinsC {n : ℕ} (ws : List (Wire n)) (γ : BitAssignment n) :
    (zLinsC ws).eval.1.mulVec (XMeasCircuit.ket γ) =
      bitSign (b2z (evLin (fun w ↦ z2b (γ w)) ws)) • XMeasCircuit.ket γ := by
  induction ws with
  | nil =>
      rw [zLinsC, Circuit.eval_identity, Submonoid.coe_one, one_mulVec, evLin, b2z_false,
        bitSign_zero2, one_smul]
  | cons w ws ih =>
      rw [zLinsC, eval_seq_mv, ket_sdk_eq γ, ket_Z, ← ket_sdk_eq γ, mulVec_smul, ih,
        smul_smul, ← bitSign_add, evLin, b2z_xor, b2z_z2b]

/-- `0-T` (`0 TOFF`) X-measurement phase fixup matching `quad5Bit rHot rFib M` when `γ t = 0`. -/
def quad5FixC {N : ℕ} (t : Wire N) (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) (M : Fin 46 → Fin 10 → Bool) : Circuit N :=
  let emb := vCtrl56 rHot rFib t hHT hFT
  andPairsC t ((quad5Pairs M).map fun p ↦ (mapAff emb p.1, mapAff emb p.2)) ;;ᶜ
    zLinsC ((quad5Diag M).map fun u ↦ (emb u).1)

@[simp] theorem count_quad5FixC_toff {N : ℕ} (t : Wire N) (rHot : QRegister 46 N)
    (rFib : QRegister 10 N) (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t)
    (M : Fin 46 → Fin 10 → Bool) : (quad5FixC t rHot rFib hHT hFT M).count .TOFF = 0 := by
  simp [quad5FixC]
@[simp] theorem count_quad5FixC_t {N : ℕ} (t : Wire N) (rHot : QRegister 46 N)
    (rFib : QRegister 10 N) (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t)
    (M : Fin 46 → Fin 10 → Bool) : (quad5FixC t rHot rFib hHT hFT M).count .T = 0 := by
  simp [quad5FixC]

theorem ket_quad5FixC_zero {N : ℕ} (t : Wire N) (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHT : ∀ i, rHot i ≠ t) (hFT : ∀ j, rFib j ≠ t) (M : Fin 46 → Fin 10 → Bool)
    (γ : BitAssignment N) (ht0 : γ t = 0) :
    (quad5FixC t rHot rFib hHT hFT M).eval.1.mulVec (XMeasCircuit.ket γ) =
      bitSign (quad5Bit rHot rFib M γ) • XMeasCircuit.ket γ := by
  dsimp only [quad5FixC]
  rw [eval_seq_mv, ket_andPairsCirc_zero _ _ γ ht0, mulVec_smul, ket_zLinsC, smul_smul,
    ← bitSign_add, xorPairs_map, evLin_map, ctrl_env56]
  have hf : (fun w ↦ z2b (γ w)) ∘ (fun u ↦ (vCtrl56 rHot rFib t hHT hFT u).1) =
      env56 rHot rFib γ := ctrl_env56 rHot rFib t hHT hFT γ
  rw [hf, ← b2z_xor]

/-- `0-T` `(Z, CZ)` phase circuit applying `phi g optF` on `(rHot, rFib)` one-hot sectors. -/
def fix46x10C {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHF : ∀ g f, rHot g ≠ rFib f) (phi : Fin 46 → Option (Fin 10) → Bool) : Circuit N :=
  hotCtxPhaseLoop 10 46 rHot rFib hHF (fun g ↦ b2z (phi g none))
    (fun g f ↦ b2z (xor (phi g (some f)) (phi g none))) 46 le_rfl

theorem fix46x10C_def {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHF : ∀ g f, rHot g ≠ rFib f) (phi : Fin 46 → Option (Fin 10) → Bool) :
    fix46x10C rHot rFib hHF phi =
      hotCtxPhaseLoop 10 46 rHot rFib hHF (fun g ↦ b2z (phi g none))
        (fun g f ↦ b2z (xor (phi g (some f)) (phi g none))) 46 le_rfl := rfl

@[simp] theorem count_fix46x10C_toff {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHF : ∀ g f, rHot g ≠ rFib f) (phi : Fin 46 → Option (Fin 10) → Bool) :
    (fix46x10C rHot rFib hHF phi).count .TOFF = 0 :=
  count_hotCtxPhaseLoop_toff2 rHot rFib hHF _ _ 46 le_rfl
@[simp] theorem count_fix46x10C_t {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHF : ∀ g f, rHot g ≠ rFib f) (phi : Fin 46 → Option (Fin 10) → Bool) :
    (fix46x10C rHot rFib hHF phi).count .T = 0 :=
  count_hotCtxPhaseLoop_t2 rHot rFib hHF _ _ 46 le_rfl

theorem ket_fix46x10C_sector {N : ℕ} (rHot : QRegister 46 N) (rFib : QRegister 10 N)
    (hHF : ∀ g f, rHot g ≠ rFib f) (phi : Fin 46 → Option (Fin 10) → Bool)
    (γ : BitAssignment N) (g : Fin 46) (optF : Option (Fin 10))
    (hHot : ∀ i : Fin 46, γ (rHot i) = if i = g then 1 else 0)
    (hFib : ∀ f : Fin 10, γ (rFib f) = b2z (optF == some f)) :
    (fix46x10C rHot rFib hHF phi).eval.1.mulVec (XMeasCircuit.ket γ) =
      bitSign (b2z (phi g optF)) • XMeasCircuit.ket γ := by
  rw [fix46x10C, ket_sdk_eq γ, ket_hotCtxPhaseLoop, ← ket_sdk_eq γ]
  refine congrArg (· • XMeasCircuit.ket γ) (congrArg bitSign ?_)
  rw [Finset.sum_eq_single g]
  · simp only [Fin.eta, hHot g, ↓reduceIte, one_mul]
    rcases optF with _ | f0
    · have hz : (∑ f : Fin 10, b2z (xor (phi g (some f)) (phi g none)) * γ (rFib f)) = 0 :=
        Finset.sum_eq_zero fun f _ ↦ by
          rw [hFib f]
          simp [b2z]
      rw [hz, add_zero]
    · rw [Finset.sum_eq_single f0]
      · rw [hFib f0, show (some f0 == some f0) = true from beq_self_eq_true _, b2z_true, mul_one,
          b2z_xor]
        cases phi g (some f0) <;> cases phi g none <;> decide
      · intro f _ hf
        have hne : (some f0 == some f) = false :=
          beq_eq_false_iff_ne.mpr fun h ↦ hf (Option.some.inj h.symm)
        rw [hFib f, hne, b2z_false, mul_zero]
      · intro h
        exact False.elim (h (Finset.mem_univ f0))
  · intro i _ hi
    simp [Fin.eta, hHot i, hi]
  · intro h
    exact False.elim (h (Finset.mem_univ g))

/-! ### Involutive Circuit Realization & Raw `keep` Fiber Bit -/

theorem TransRealizes.of_circuit_invUnitary {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) {S1 S2 : BitAssignment N → Bool} (c : Circuit N) (U : Unitary (2 ^ N))
    (htoff : c.count .TOFF = 0) (hU2 : U * U = 1)
    (hU_map : U.1 * GroupUnary.predProj S1 = GroupUnary.predProj S2 * U.1)
    (hVU : c.eval.1 * GroupUnary.predProj S1 = U.1 * GroupUnary.predProj S1) :
    TransRealizes v S1 S2 U (.circuit c) := by
  have hU_val2 : U.1 * U.1 = 1 := congrArg Subtype.val hU2
  have hU_adj : U.1ᴴ = U.1 := conjTranspose_eq_self_of_mul_self U hU2
  have hV_inv : c.eval.1ᴴ * c.eval.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (SetLike.coe_mem c.eval).1
  have h1 : c.eval.1ᴴ * GroupUnary.predProj S2 = GroupUnary.predProj S1 * U.1 := by
    calc c.eval.1ᴴ * GroupUnary.predProj S2
        = c.eval.1ᴴ * (GroupUnary.predProj S2 * (U.1 * U.1)) := by rw [hU_val2, mul_one]
      _ = c.eval.1ᴴ * ((GroupUnary.predProj S2 * U.1) * U.1) := by
        rw [mul_assoc (GroupUnary.predProj S2)]
      _ = c.eval.1ᴴ * ((c.eval.1 * GroupUnary.predProj S1) * U.1) := by rw [← hU_map, ← hVU]
      _ = (c.eval.1ᴴ * c.eval.1) * GroupUnary.predProj S1 * U.1 := by simp only [mul_assoc]
      _ = GroupUnary.predProj S1 * U.1 := by rw [hV_inv, one_mul]
  have h2 := congrArg conjTranspose h1
  simp only [conjTranspose_mul, conjTranspose_conjTranspose,
    GroupUnary.predProj_conjTranspose, hU_adj] at h2
  exact (TransRealizes.of_circuit v c htoff (hVU.trans h2.symm)).congr_unitary hU_map hVU

/-- Raw `keep` fiber bit `f < 10` at item `4 * g + r < 184` of `pi145CompactTable`. -/
abbrev keepRawBool (r : Fin 4) (g : Fin 46) (f : Fin 10) : Bool :=
  z2b (basisBits 10 ⟨(pi145CompactTable ⟨4 * g.val + r.val, by omega⟩).keep % 1024,
    Nat.mod_lt _ (by decide)⟩ f)

attribute [irreducible]
  cS4_0 cS4_1 cS5_0 cS5_1 cInit4Rev cFan5Rev cFib11Rev cFib11FwdDyn
  slotCswap cSt0 cSt1 cSt2 cSt3 cIStar0 cIStar2
  hotVars46 quad5Pair quad5Pairs quad5DiagMask quad5Diag
  vCtrl56 quad5GadC zLinsC quad5FixC fix46x10C

end PrepOutCoreImpl

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetPrepOutOuter8
