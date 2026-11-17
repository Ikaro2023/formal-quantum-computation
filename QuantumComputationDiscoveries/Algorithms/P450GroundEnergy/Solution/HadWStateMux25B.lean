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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HadWStateMux25A
/-!
# Compact `50-T` `Mux25` & `46-T` `Mux23` `W`-State CSWAP
Instantiates `(p0, sKick, muxBit)` Hadamard-target `W`-state mux-CSWAP to `50-T` (`17 ≤ s`)
`hadWMuxSwap25Dyn` / `hadWMuxSwap25Dyn`, `46-T` (`16 ≤ s`) `hadWMuxSwapCore23Dyn`, `64-T`
`hadWZeroCmpGenPrepMid{,Inv}Dyn`, and the `wInner2 = 20` `hadAltZeroCmpPrepMid20FromSlice` suite.
Refs: C. Jones, *Phys. Rev. A* **87**, 022328 (2013), DOI: 10.1103/PhysRevA.87.022328; R. Babbush
et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015; D. W. Berry et al.,
*Quantum* **3**, 208 (2019), DOI: 10.22331/q-2019-12-02-208; G. H. Low et al., *Phys. Rev. X*
**15**, 041016 (2025), DOI: 10.1103/pb2g-j9cw.
-/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HadWStateMux25CompactB
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution CoherentAlias AliasPrep
    TopIntegrationBridge
  Phase2MidSandwich CompactBilinearPrep MidReflCtxRetain OptXMeasUnload21
  OptFactoredMag30AndCoin9 Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast
  Tuned162ScheduledSympQrom21 OptStepSympAnfQrom21 Tuned162StepSympAnfQrom21
  OptU2Grover184PrepOut13 MobiusOptSubcube163Walk CompactTuned162StepWalk
  CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam CompactStepZeroCmp20OuterParam
  StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20 HadWStateMux25CompactA
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowHad25B (k : ℕ) : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k two_ne_zero⟩
/-- `(p0 + 1)` nested `4-T` `andSandwichDyn` gadgets wrapping `xorFanIn ;; kickDyn ;; xorFanIn`. -/
def andLoopGenDyn (p0 sKick : ℕ) {Var : Type} (v : Var) (kickDyn : DynamicCircuit Var (14 +
    sKick)) : (m : ℕ) → m ≤ p0 + 1 → DynamicCircuit Var (nLocGen p0 sKick)
  | 0, _ =>
      let rFan := QRegister.block 0 (nActGen p0 + (p0 + 1)) (by dsimp [nLocGen, nScrGen]; omega)
      let cXor := (xorFanInPre p0 p0 le_rfl).onRegister rFan
      .seq (.circuit cXor)
        (.seq (Solution.XMeasCircuit.dynOnRegister (placeKickGen p0 sKick) kickDyn) (.circuit cXor))
  | m + 1, hm => SelectSwapQROM.andSandwichDyn v ⟨p0 - m, by dsimp [nLocGen, nActGen]; omega⟩
        ⟨(p0 + 1) + (p0 - m), by dsimp [nLocGen, nActGen]; omega⟩
        ⟨nActGen p0 + (p0 - m), by dsimp [nLocGen, nScrGen]; omega⟩
        (Fin.ne_of_val_ne (by dsimp; omega)) (Fin.ne_of_val_ne (by dsimp [nActGen]; omega))
        (Fin.ne_of_val_ne (by dsimp [nActGen]; omega))
        (andLoopGenDyn p0 sKick v kickDyn m (by omega))
theorem countAndLoopGenDyn_arity3 (p0 sKick : ℕ) {Var : Type} (v : Var) {kickDyn : DynamicCircuit
    Var (14 + sKick)} (g : PrimitiveGate 3) (hK : kickDyn.count g = 0) : ∀ (m : ℕ) (hm : m ≤ p0 +
    1), (andLoopGenDyn p0 sKick v kickDyn m hm).count g = 0
  | 0, _ => by
      simp only [andLoopGenDyn, DynamicCircuit.count, Circuit.count_onRegister,
        Solution.XMeasCircuit.count_dynOnRegister, hK, countXorFanInPre_arity3]
  | m + 1, _ => by cases g; simp [andLoopGenDyn,
      countAndLoopGenDyn_arity3 p0 sKick v .TOFF hK m (by omega)]
theorem countAndLoopGenDyn_t (p0 sKick : ℕ) {Var : Type} (v : Var) (kickDyn : DynamicCircuit Var
    (14 + sKick)) : ∀ (m : ℕ) (hm : m ≤ p0 + 1), (andLoopGenDyn p0 sKick v kickDyn m hm).count .T
    = kickDyn.count .T + 4 * m
  | 0, _ => by
      simp only [andLoopGenDyn, DynamicCircuit.count, Circuit.count_onRegister,
        Solution.XMeasCircuit.count_dynOnRegister, countXorFanInPre_t]; omega
  | m + 1, _ => by
      simp only [andLoopGenDyn, SelectSwapQROM.count_andSandwichDyn_t, countAndLoopGenDyn_t
        p0 sKick v kickDyn m (by omega)]; omega
theorem cleanRealizesSetAndLoopGenDyn (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) {kickDyn : DynamicCircuit Var (14 +
    sKick)} (hKick : Solution.XMeasCircuit.CleanRealizes v (actKick rfl) (scrKick rfl)
    (Solution.XMeasCircuit.phaseFlipUnitary (keepKickPhaseOf muxBit)) kickDyn) : ∀ (m : ℕ) (hm : m ≤
      p0 + 1),
    SelectSwapQROM.CleanRealizesSet v (loopScrGen p0 sKick m hm).image
    (Solution.XMeasCircuit.phaseFlipUnitary (loopPhaseGen p0 sKick muxBit m))
      (andLoopGenDyn p0 sKick v
    kickDyn m hm)
  | 0, hm => by
      let rFan : QRegister (nActGen p0 + (p0 + 1)) (nLocGen p0 sKick) :=
        QRegister.block 0 (nActGen p0 + (p0 + 1)) (by dsimp [nLocGen, nScrGen]; omega)
      let wPar : Wire (nLocGen p0 sKick) := ⟨nActGen p0 + p0, by dsimp [nLocGen, nScrGen]; omega⟩
      let rPlace := placeKickGen p0 sKick
      have hScrEq : rPlace.compose (scrKick rfl) = loopScrGen p0 sKick 0 hm :=
        CoherentAlias.qreg_ext fun j ↦ by
          have hj := j.isLt; dsimp only [rPlace, placeKickGen, scrKick, loopScrGen]
          rw [QRegister.compose_apply, mkReg_apply_val, QRegister.block_apply_val,
            QRegister.block_apply_val]; dsimp only [nActGen]; split_ifs <;> omega
      have hDisjFan : rFan.DisjointWires (loopScrGen p0 sKick 0 hm) := QRegister.disjoint_iff.mpr
        fun i _ hij ↦ by
          have hv := congrArg Fin.val hij; have hi := i.isLt; dsimp only [rFan, loopScrGen] at hv
          rw [QRegister.block_apply_val, QRegister.block_apply_val] at hv
          dsimp only [nActGen] at hi hv; omega
      have hXorCr := (SelectSwapQROM.cleanRealizes_iff_set v rFan (loopScrGen p0 sKick 0 hm)
        (xorFanInPre p0 p0 le_rfl).eval (.circuit ((xorFanInPre p0 p0 le_rfl).onRegister
        rFan))).mp (Solution.CleanDyn.CleanRealizes.circuit v rFan
          (loopScrGen p0 sKick 0 hm) hDisjFan
        (xorFanInPre p0 p0 le_rfl) (countXorFanInPre_arity3 p0 .TOFF p0 le_rfl))
      have hCoreCr := (SelectSwapQROM.cleanRealizes_iff_set v (rPlace.compose (actKick rfl))
        (rPlace.compose (scrKick rfl)) (Solution.XMeasCircuit.phaseFlipUnitary
          (keepKickPhaseOf muxBit))
        (Solution.XMeasCircuit.dynOnRegister rPlace kickDyn)).mp
          ((AliasPrep.cleanRealizes_sbx_iff v _ _ _
        _).mp (hKick.onRegister rPlace))
      rw [hScrEq] at hCoreCr
      refine (hXorCr.seq (hCoreCr.seq hXorCr)).congr_unitary fun β _ ↦ ?_
      have hLtPar (γ : BitAssignment (nLocGen p0 sKick)) (b : ZMod 2) (w : Wire (nLocGen p0 sKick))
        (hw : w.val < nActGen p0 + p0) : Function.update γ wPar b w = γ w :=
        Function.update_of_ne (Fin.ne_of_val_ne (by dsimp [wPar]; omega)) _ _
      let S := ∑ j : Fin p0, β ⟨nActGen p0 + j.val, by dsimp [nLocGen, nScrGen]; omega⟩
      have hPhEq : keepKickPhaseOf muxBit (fun k ↦ Function.update β wPar (β wPar + S)
        ((rPlace.compose (actKick rfl)) k)) = loopPhaseGen p0 sKick muxBit 0 β := by
        have h0 : (rPlace.compose (actKick rfl)) 0 = wPar := Fin.ext <| by
          dsimp only [rPlace, placeKickGen, actKick, wPar]
          rw [QRegister.compose_apply, mkReg_apply_val, QRegister.block_apply_val]; simp
        have hPkt (i : Fin 4) : (rPlace.compose (actKick rfl)) ⟨1 + i.val, by omega⟩ =
            ⟨2 * (p0 + 1) + i.val, by dsimp [nLocGen, nActGen]; omega⟩ := Fin.ext <| by
          have := i.isLt; dsimp only [rPlace, placeKickGen, actKick]
          rw [QRegister.compose_apply, mkReg_apply_val, QRegister.block_apply_val]
          dsimp only; split_ifs <;> omega
        have hKp (j : Fin 9) : (rPlace.compose (actKick rfl)) ⟨5 + j.val, by omega⟩ =
            ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nLocGen, nActGen]; omega⟩ := Fin.ext <| by
          have := j.isLt; dsimp only [rPlace, placeKickGen, actKick]
          rw [QRegister.compose_apply, mkReg_apply_val, QRegister.block_apply_val]
          dsimp only; split_ifs <;> omega
        have hPU (i : Fin 4) : Function.update β wPar (β wPar + S)
            ⟨2 * (p0 + 1) + i.val, by dsimp [nLocGen, nActGen]; omega⟩ =
            β ⟨2 * (p0 + 1) + i.val, by dsimp [nLocGen, nActGen]; omega⟩ :=
          hLtPar _ _ _ (by dsimp [nActGen]; omega)
        have hKU (j : Fin 9) : Function.update β wPar (β wPar + S)
            ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nLocGen, nActGen]; omega⟩ =
            β ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nLocGen, nActGen]; omega⟩ :=
          hLtPar _ _ _ (by dsimp [nActGen]; omega)
        dsimp only [keepKickPhaseOf, loopPhaseGen, swGenBit]
        simp only [h0, Function.update_self, hPkt, hKp, hPU, hKU,
          show ∀ r : Fin (p0 + 1), ¬ (p0 + 1 - 0 ≤ r.val) by intro r; have := r.isLt; omega,
          ↓reduceIte, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
        exact congrArg (· * _) (add_comm (β wPar) S)
      have hXor1 := xorFanInPre_mulVec_ket p0 sKick p0 le_rfl β
      have hXor2 := xorFanInPre_mulVec_ket p0 sKick p0 le_rfl (Function.update β wPar (β wPar +
        S))
      have hSumEq : (∑ j : Fin p0, Function.update β wPar (β wPar + S)
          ⟨nActGen p0 + j.val, by dsimp [nLocGen, nScrGen]; omega⟩) = S :=
        Finset.sum_congr rfl fun j _ ↦ hLtPar _ _ _ (by have := j.isLt; dsimp; omega)
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [show SelectSwapQROM.ket β = Solution.XMeasCircuit.ket β from rfl, hXor1,
        Solution.XMeasCircuit.embedUnitary_phaseFlipUnitary,
          Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket,
        Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket, Matrix.mulVec_smul, hXor2, hSumEq]
      dsimp only [wPar, S] at hPhEq ⊢
      rw [hPhEq, Function.update_idem, Function.update_self, zmod2_add_cancel_rightHad,
        Function.update_eq_self]
  | m + 1, hm => by
      let c₁ : Wire (nLocGen p0 sKick) := ⟨p0 - m, by dsimp [nLocGen, nActGen]; omega⟩
      let c₂ : Wire (nLocGen p0 sKick) := ⟨(p0 + 1) + (p0 - m), by dsimp [nLocGen, nActGen]; omega⟩
      let anc : Wire (nLocGen p0 sKick) :=
        ⟨nActGen p0 + (p0 - m), by dsimp [nLocGen, nScrGen]; omega⟩
      have h12 : c₁ ≠ c₂ := Fin.ne_of_val_ne (by dsimp [c₁, c₂]; omega)
      have h1a : c₁ ≠ anc := Fin.ne_of_val_ne (by dsimp [c₁, anc, nActGen]; omega)
      have h2a : c₂ ≠ anc := Fin.ne_of_val_ne (by dsimp [c₂, anc, nActGen]; omega)
      let gT : Circuit (nLocGen p0 sKick) := Circuit.gate .toffoli (QRegister.triple c₁ c₂ anc h12
        h1a h2a)
      have hErase : (loopScrGen p0 sKick (m + 1) hm).image.erase anc = (loopScrGen p0 sKick m
        (by omega)).image := by
        ext w; simp only [Finset.mem_erase, ne_eq, QRegister.mem_image, loopScrGen, Fin.ext_iff,
          QRegister.block_apply_val]
        have hanc : anc.val = nActGen p0 + (p0 - m) := rfl; rw [hanc]
        exact ⟨fun ⟨_, ⟨j, hj⟩⟩ ↦ ⟨⟨j.val - 1, by have := j.isLt; omega⟩, by dsimp only; omega⟩,
          fun ⟨j, hj⟩ ↦ ⟨by omega, ⟨⟨j.val + 1, by have := j.isLt; omega⟩, by dsimp only; omega⟩⟩⟩
      have hAncMem : anc ∈ (loopScrGen p0 sKick (m + 1) hm).image :=
        (QRegister.mem_image _ _).mpr ⟨⟨0, by omega⟩, Fin.ext (by simp [loopScrGen, anc]; omega)⟩
      have hNotScr {w : Wire (nLocGen p0 sKick)} (hw : w.val < nActGen p0) : w ∉ (loopScrGen p0
        sKick (m + 1) hm).image := fun h ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp h
        have hv := congrArg Fin.val hj; simp [loopScrGen] at hv; omega
      have hPrev := cleanRealizesSetAndLoopGenDyn p0 sKick muxBit v hKick m (by omega)
      rw [← hErase] at hPrev
      have hStepKet (β : BitAssignment (nLocGen p0 sKick)) (hS : ∀ w ∈ (loopScrGen p0 sKick (m +
        1) hm).image,
          β w = 0) : (gT.eval * Solution.XMeasCircuit.phaseFlipUnitary (loopPhaseGen p0 sKick
        muxBit m) * gT.eval).1.mulVec (SelectSwapQROM.ket β) =
          (Solution.XMeasCircuit.phaseFlipUnitary
        (loopPhaseGen p0 sKick muxBit (m + 1))).1.mulVec (SelectSwapQROM.ket β) := by
        have hAnc0 : β anc = 0 := hS anc hAncMem; have hUpdAnc := update_bit_eq_selfHad hAnc0
        have hLtAct (u : Wire (nLocGen p0 sKick)) (hu : u.val < nActGen p0) : Function.update β anc
          (β c₁ * β c₂) u = β u :=
          Function.update_of_ne (Fin.ne_of_val_ne (by simp only [anc]; omega)) _ _
        have hPh : loopPhaseGen p0 sKick muxBit m (Function.update β anc (β c₁ * β c₂)) =
          loopPhaseGen p0 sKick muxBit (m + 1) β := by
          dsimp only [loopPhaseGen]
          rw [swGenBit_update_not_sel p0 sKick muxBit β anc
            (Or.inr (by simp only [anc]; omega))]
          refine congrArg (· * swGenBit p0 sKick muxBit β) (Finset.sum_congr rfl fun r _ ↦ ?_)
          by_cases hr1 : p0 + 1 - m ≤ r.val
          · simp only [hr1, show p0 + 1 - (m + 1) ≤ r.val by omega, ↓reduceIte]
            rw [hLtAct _ (by have := r.isLt; dsimp [nActGen]; omega),
              hLtAct _ (by have := r.isLt; dsimp [nActGen]; omega)]
          · by_cases hr2 : r.val = p0 - m
            · have ha_r : (⟨nActGen p0 + r.val, by dsimp [nLocGen, nScrGen]; omega⟩ :
                  Wire (nLocGen p0 sKick)) = anc := Fin.ext (by simp [anc, hr2])
              have hc1_r : (⟨r.val, by dsimp [nLocGen, nActGen]; omega⟩ :
                  Wire (nLocGen p0 sKick)) = c₁ := Fin.ext (by simp [c₁, hr2])
              have hc2_r : (⟨(p0 + 1) + r.val, by dsimp [nLocGen, nActGen]; omega⟩ :
                  Wire (nLocGen p0 sKick)) = c₂ := Fin.ext (by simp [c₂, hr2])
              simp only [hr1, show p0 + 1 - (m + 1) ≤ r.val by omega, ↓reduceIte,
                ha_r, hc1_r, hc2_r, Function.update_self]
            · simp only [hr1, show ¬ (p0 + 1 - (m + 1) ≤ r.val) by omega, ↓reduceIte,
                Function.update_of_ne (Fin.ne_of_val_ne (by simp [anc]; omega) :
                  ⟨nActGen p0 + r.val, by dsimp [nLocGen, nScrGen]; omega⟩ ≠ anc)]
        simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]; dsimp only [gT]
        rw [SelectSwapQROM.ket_TOFF, hAnc0, zero_add]
        change _ = (Solution.XMeasCircuit.phaseFlipUnitary _).1.mulVec (Solution.XMeasCircuit.ket β)
        rw [show SelectSwapQROM.ket _ = Solution.XMeasCircuit.ket _ from rfl,
          Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket,
            Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket,
          Matrix.mulVec_smul, show Solution.XMeasCircuit.ket _ = SelectSwapQROM.ket _ from rfl,
          SelectSwapQROM.ket_TOFF]
        simp only [Function.update_idem, Function.update_self,
          hLtAct c₁ (by simp [c₁, nActGen]; omega), hLtAct c₂ (by simp [c₂, nActGen]; omega),
          zmod2_add_selfHad, hUpdAnc, hPh]
      dsimp only [gT] at hStepKet
      refine (SelectSwapQROM.CleanRealizesSet.andSandwich h12 h1a h2a hAncMem
        (hNotScr (by simp [c₁, nActGen]; omega)) (hNotScr (by simp [c₂, nActGen]; omega)) hPrev
        fun β hS ↦ ?_).congr_unitary hStepKet
      dsimp only; rw [hStepKet β hS]
      change ((QRegister.singleton anc).basisOutcomeProjector 0).mulVec
        ((Solution.XMeasCircuit.phaseFlipUnitary _).1.mulVec (Solution.XMeasCircuit.ket β)) =
          (Solution.XMeasCircuit.phaseFlipUnitary
        _).1.mulVec (Solution.XMeasCircuit.ket β)
      rw [Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket, Matrix.mulVec_smul,
        Solution.XMeasCircuit.ket_projector_zero]; simp [hS anc hAncMem]
/-- Pre-conjugation `2`-wire circuit `CNOT 1 0 ;; H 1` (`0 T`). -/
def pairPreCirc2 : Circuit 2 := Circuit.CNOT 1 0 (by decide) ;;ᶜ Circuit.H 1
/-- Post-conjugation `2`-wire circuit `H 1 ;; CNOT 1 0` (`0 T`). -/
def pairPostCirc2 : Circuit 2 := Circuit.H 1 ;;ᶜ Circuit.CNOT 1 0 (by decide)
/-- Conjugates `d` on pairs `(r, (p0 + 1) + r)` for `r < k` by `pairPreCirc2`/`pairPostCirc2`.
-/
def pairConjWrapGenDyn (p0 sKick : ℕ) {Var : Type} : (k : ℕ) → k ≤ p0 + 1 → DynamicCircuit Var
    (nLocGen p0 sKick) → DynamicCircuit Var (nLocGen p0 sKick)
  | 0, _, d => d
  | k + 1, hk, d =>
      let rP := QRegister.pair ⟨k, by dsimp [nLocGen, nActGen]; omega⟩
        ⟨(p0 + 1) + k, by dsimp [nLocGen, nActGen]; omega⟩ (Fin.ne_of_val_ne (by dsimp; omega))
      .seq (.circuit (pairPreCirc2.onRegister rP))
        (.seq (pairConjWrapGenDyn p0 sKick k (by omega) d) (.circuit (pairPostCirc2.onRegister
          rP)))
/-- Local `nLocGen p0 sKick`-wire Hadamard-target `W`-state mux-CSWAP around `kickDyn`. -/
def hadWMuxSwapLocalGenDyn (p0 sKick : ℕ) {Var : Type} (v : Var) (kickDyn : DynamicCircuit Var (14
    + sKick)) : DynamicCircuit Var (nLocGen p0 sKick) := pairConjWrapGenDyn p0 sKick (p0 + 1)
    le_rfl (andLoopGenDyn p0 sKick v kickDyn (p0 + 1) le_rfl)
theorem countPairConjWrapGenDyn_arity3 (p0 sKick : ℕ) {Var : Type} (g : PrimitiveGate 3) (d :
    DynamicCircuit Var (nLocGen p0 sKick)) : ∀ (k : ℕ) (hk : k ≤ p0 + 1), (pairConjWrapGenDyn p0
    sKick k hk d).count g = d.count g
  | 0, _ => rfl
  | k + 1, _ => by
      have hPre : pairPreCirc2.count g = 0 := by cases g; rfl
      have hPost : pairPostCirc2.count g = 0 := by cases g; rfl
      simp only [pairConjWrapGenDyn, DynamicCircuit.count, Circuit.count_onRegister,
        countPairConjWrapGenDyn_arity3 p0 sKick g d k (by omega), hPre, hPost]; omega
theorem countPairConjWrapGenDyn_t (p0 sKick : ℕ) {Var : Type} (d : DynamicCircuit Var (nLocGen p0
    sKick)) : ∀ (k : ℕ) (hk : k ≤ p0 + 1), (pairConjWrapGenDyn p0 sKick k hk d).count .T = d.count
    .T
  | 0, _ => rfl
  | k + 1, _ => by
      simp only [pairConjWrapGenDyn, DynamicCircuit.count, Circuit.count_onRegister,
        countPairConjWrapGenDyn_t p0 sKick d k (by omega), show pairPreCirc2.count .T = 0 from
        rfl, show pairPostCirc2.count .T = 0 from rfl]; omega
theorem countHadWMuxSwapLocalGenDyn_arity3 (p0 sKick : ℕ) {Var : Type} (v : Var) {kickDyn :
    DynamicCircuit Var (14 + sKick)} (g : PrimitiveGate 3) (hK : kickDyn.count g = 0) :
    (hadWMuxSwapLocalGenDyn p0 sKick v kickDyn).count g = 0 := by
  rw [hadWMuxSwapLocalGenDyn, countPairConjWrapGenDyn_arity3, countAndLoopGenDyn_arity3 p0
    sKick v g hK]
theorem countHadWMuxSwapLocalGenDyn_t (p0 sKick : ℕ) {Var : Type} (v : Var) (kickDyn :
    DynamicCircuit Var (14 + sKick)) : (hadWMuxSwapLocalGenDyn p0 sKick v kickDyn).count .T =
    kickDyn.count .T + 4 * (p0 + 1) := by
  rw [hadWMuxSwapLocalGenDyn, countPairConjWrapGenDyn_t, countAndLoopGenDyn_t]
/-- Prefix bit-permutation swapping `(r, (p0 + 1) + r)` for `r < k` when `swGenBit = 1`. -/
def swapPrefixBitsGen (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (k : ℕ) (hk : k ≤
    p0 + 1) (β : BitAssignment (nLocGen p0 sKick)) : BitAssignment (nLocGen p0 sKick) := fun w ↦ if
    swGenBit p0 sKick muxBit β = 1 then
    if _ : w.val < k then β ⟨(p0 + 1) + w.val, by dsimp [nLocGen, nActGen]; omega⟩
    else if _ : p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + k then
      β ⟨w.val - (p0 + 1), by dsimp [nLocGen, nActGen]; omega⟩
    else β w
  else β w
theorem swGenBitSwapPrefixBitsGen (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (k
    : ℕ) (hk : k ≤ p0 + 1) (β : BitAssignment (nLocGen p0 sKick)) : swGenBit p0 sKick muxBit
    (swapPrefixBitsGen p0 sKick muxBit k hk β) = swGenBit p0 sKick muxBit β := by
  have hGe (u : Wire (nLocGen p0 sKick)) (h1 : 2 * (p0 + 1) ≤ u.val) : swapPrefixBitsGen p0 sKick
    muxBit k hk β u = β u := by
    dsimp [swapPrefixBitsGen]
    simp [show ¬ (u.val < k) by omega, show ¬ (u.val < (p0 + 1) + k) by omega]
  dsimp only [swGenBit]
  simp only [fun i : Fin 4 ↦ hGe ⟨2 * (p0 + 1) + i.val, by dsimp [nLocGen, nActGen]; omega⟩
      (by dsimp; omega),
    fun j : Fin 9 ↦ hGe ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nLocGen, nActGen]; omega⟩
      (by dsimp; omega)]
theorem swapPrefixBitsGen_invol (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (k : ℕ)
    (hk : k ≤ p0 + 1) : Function.Involutive (swapPrefixBitsGen p0 sKick muxBit k hk) := fun β ↦ by
  funext w; conv_lhs => rw [swapPrefixBitsGen]
  rw [swGenBitSwapPrefixBitsGen]
  by_cases hsw : swGenBit p0 sKick muxBit β = 1
  · by_cases h1 : w.val < k
    · simp only [hsw, h1, ↓reduceIte, ↓reduceDIte, swapPrefixBitsGen,
        show ¬ ((p0 + 1) + w.val < k) by omega,
        show p0 + 1 ≤ (p0 + 1) + w.val ∧ (p0 + 1) + w.val < (p0 + 1) + k by omega, and_self]
      exact congrArg β (Fin.ext (by dsimp; omega))
    · by_cases h2 : p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + k
      · simp only [hsw, h1, h2, ↓reduceIte, ↓reduceDIte, swapPrefixBitsGen,
          show w.val - (p0 + 1) < k by omega]
        exact congrArg β (Fin.ext (by dsimp; omega))
      · simp only [hsw, h1, h2, ↓reduceIte, ↓reduceDIte, swapPrefixBitsGen]
  · simp only [hsw, ↓reduceIte, swapPrefixBitsGen]
/-- Involutive bit-permutation equivalence for `swapPrefixBitsGen p0 sKick muxBit k hk`. -/
def swapPrefixPermGen (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (k : ℕ) (hk : k ≤
    p0 + 1) : Equiv.Perm (BitAssignment (nLocGen p0 sKick)) := ⟨swapPrefixBitsGen p0 sKick muxBit
    k hk, swapPrefixBitsGen p0 sKick muxBit k hk, swapPrefixBitsGen_invol p0 sKick muxBit k hk,
    swapPrefixBitsGen_invol p0 sKick muxBit k hk⟩
/-- Residual phase polynomial on pairs `r ≥ k` after `k` conjugated pairs on `nLocGen`. -/
def swapPrefixPhaseGen (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (k : ℕ) (β :
    BitAssignment (nLocGen p0 sKick)) : ZMod 2 := (∑ r : Fin (p0 + 1), if k ≤ r.val then
      β ⟨r.val, by dsimp [nLocGen, nActGen]; omega⟩ *
        β ⟨(p0 + 1) + r.val, by dsimp [nLocGen, nActGen]; omega⟩
    else 0) * swGenBit p0 sKick muxBit β
theorem swapPrefixPhaseGen_bits_eq (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (k :
    ℕ) (hk : k ≤ p0 + 1) (β : BitAssignment (nLocGen p0 sKick)) : swapPrefixPhaseGen p0 sKick
    muxBit k (swapPrefixBitsGen p0 sKick muxBit k hk β) = swapPrefixPhaseGen p0 sKick muxBit k β
    := by
  dsimp only [swapPrefixPhaseGen]; rw [swGenBitSwapPrefixBitsGen]
  refine congrArg (· * swGenBit p0 sKick muxBit β) (Finset.sum_congr rfl fun r _ ↦ ?_)
  by_cases hr : k ≤ r.val
  · simp only [hr, ↓reduceIte, ↓reduceDIte, swapPrefixBitsGen, show ¬ (r.val < k) by omega,
      show ¬ (p0 + 1 ≤ r.val ∧ r.val < (p0 + 1) + k) by omega,
      show ¬ ((p0 + 1) + r.val < k) by omega,
      show ¬ (p0 + 1 ≤ (p0 + 1) + r.val ∧ (p0 + 1) + r.val < (p0 + 1) + k) by omega, ite_self]
  · simp [hr]
/-- Intermediate unitary after conjugating the first `k ≤ p0 + 1` swap pairs on `nLocGen`. -/
noncomputable def swapPrefixUnitaryGen (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (k : ℕ) (hk : k ≤ p0 + 1) : Unitary (2 ^ nLocGen p0 sKick) :=
      Solution.XMeasCircuit.phaseFlipUnitary
    (swapPrefixPhaseGen p0 sKick muxBit k) * CoherentAlias.bitPermUnitary (swapPrefixPermGen p0
    sKick muxBit k hk)
theorem swapPrefixUnitaryGen_mulVec_ket (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (k : ℕ) (hk : k ≤ p0 + 1) (β : BitAssignment (nLocGen p0 sKick)) : (swapPrefixUnitaryGen p0
    sKick muxBit k hk).1.mulVec (Solution.XMeasCircuit.ket β) =
      Solution.XMeasCircuit.bitSign (swapPrefixPhaseGen p0
    sKick muxBit k β) • Solution.XMeasCircuit.ket (swapPrefixBitsGen p0 sKick muxBit k hk β) := by
  rw [swapPrefixUnitaryGen, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    bitPermUnitary_mulVec_ketHad, show (swapPrefixPermGen p0 sKick muxBit k hk : _ → _) β =
    swapPrefixBitsGen p0 sKick muxBit k hk β from rfl,
      Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket,
    swapPrefixPhaseGen_bits_eq]
theorem ket_H_superposHad {n : ℕ} (b : Wire n) (δ : BitAssignment n) (s : ZMod 2) : (Circuit.H
    b).eval.1.mulVec (Solution.XMeasCircuit.sqrtHalf •
      Solution.XMeasCircuit.ket (Function.update δ b 0) +
    (Solution.XMeasCircuit.sqrtHalf * Solution.XMeasCircuit.bitSign s) •
      Solution.XMeasCircuit.ket (Function.update δ b 1)) =
    Solution.XMeasCircuit.ket (Function.update δ b s) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Solution.XMeasCircuit.ket_H,
    Solution.XMeasCircuit.ket_H]
  rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one s with rfl | rfl
  · ext i;
      simp only [Function.update_self, Function.update_idem, Solution.XMeasCircuit.bitSign_zero,
      Solution.XMeasCircuit.bitSign_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc _ = 2 * (Solution.XMeasCircuit.sqrtHalf * Solution.XMeasCircuit.sqrtHalf) *
          Solution.XMeasCircuit.ket (Function.update δ b 0) i := by ring
      _ = _ := by rw [Solution.XMeasCircuit.sqrtHalf_mul_sqrtHalf]; ring
  · ext i;
      simp only [Function.update_self, Function.update_idem, Solution.XMeasCircuit.bitSign_zero,
      Solution.XMeasCircuit.bitSign_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc _ = 2 * (Solution.XMeasCircuit.sqrtHalf * Solution.XMeasCircuit.sqrtHalf) *
          Solution.XMeasCircuit.ket (Function.update δ b 1) i := by ring
      _ = _ := by rw [Solution.XMeasCircuit.sqrtHalf_mul_sqrtHalf]; ring
theorem cleanRealizesSetPairConjWrapGenDyn (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) →
    Bool) {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) {kickDyn : DynamicCircuit Var (14 +
    sKick)} (hKick : Solution.XMeasCircuit.CleanRealizes v (actKick rfl) (scrKick rfl)
    (Solution.XMeasCircuit.phaseFlipUnitary (keepKickPhaseOf muxBit)) kickDyn) : ∀ (k : ℕ) (hk : k ≤
      p0 + 1),
    SelectSwapQROM.CleanRealizesSet v (loopScrGen p0 sKick (p0 + 1) le_rfl).image
    (swapPrefixUnitaryGen p0 sKick muxBit k hk) (pairConjWrapGenDyn p0 sKick k hk
    (andLoopGenDyn p0 sKick v kickDyn (p0 + 1) le_rfl))
  | 0, hk => (cleanRealizesSetAndLoopGenDyn p0 sKick muxBit v hKick (p0 + 1)
      le_rfl).congr_unitary fun β _ ↦ by
      change (Solution.XMeasCircuit.phaseFlipUnitary _).1.mulVec (Solution.XMeasCircuit.ket β) =
        (swapPrefixUnitaryGen
        p0 sKick muxBit 0 hk).1.mulVec (Solution.XMeasCircuit.ket β)
      have hPh : loopPhaseGen p0 sKick muxBit (p0 + 1) β = swapPrefixPhaseGen p0 sKick muxBit 0
        β := by
        dsimp only [loopPhaseGen, swapPrefixPhaseGen]; rw [Nat.sub_self]
        simp only [Nat.zero_le, ↓reduceIte]
      have hBt : swapPrefixBitsGen p0 sKick muxBit 0 hk β = β := funext fun w ↦ by
        dsimp [swapPrefixBitsGen]
        simp
      rw [Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket, swapPrefixUnitaryGen_mulVec_ket, hPh,
        hBt]
  | k + 1, hk => by
      let a : Wire (nLocGen p0 sKick) := ⟨k, by dsimp [nLocGen, nActGen]; omega⟩
      let b : Wire (nLocGen p0 sKick) := ⟨(p0 + 1) + k, by dsimp [nLocGen, nActGen]; omega⟩
      have hab : a ≠ b := Fin.ne_of_val_ne (by simp only [a, b]; omega)
      let rP := QRegister.pair a b hab; let rScrFull := loopScrGen p0 sKick (p0 + 1) le_rfl
      have hDisj : rP.DisjointWires rScrFull := QRegister.disjoint_iff.mpr fun i _ hij ↦ by
          have hv := congrArg Fin.val hij
          fin_cases i <;> (simp [rP, a, b, rScrFull, loopScrGen, nActGen] at hv; omega)
      have hPre := (SelectSwapQROM.cleanRealizes_iff_set v rP rScrFull pairPreCirc2.eval
        (.circuit (pairPreCirc2.onRegister rP))).mp (Solution.CleanDyn.CleanRealizes.circuit v rP
        rScrFull hDisj pairPreCirc2 rfl)
      have hPost := (SelectSwapQROM.cleanRealizes_iff_set v rP rScrFull pairPostCirc2.eval
        (.circuit (pairPostCirc2.onRegister rP))).mp (Solution.CleanDyn.CleanRealizes.circuit v rP
        rScrFull hDisj pairPostCirc2 rfl)
      refine (hPre.seq ((cleanRealizesSetPairConjWrapGenDyn p0 sKick muxBit v hKick k (by
        omega)).seq hPost)).congr_unitary fun β _ ↦ ?_
      let β₁ := Function.update β a (β a + β b)
      let δ := Function.update (swapPrefixBitsGen p0 sKick muxBit k (by omega) β) a (β a + β b)
      have hUpdB₁ (z : ZMod 2) (u : Wire (nLocGen p0 sKick)) (ha' : u.val ≠ k) (hb' : u.val ≠ (p0 +
        1) + k) : Function.update β₁ b z u = β u := (Function.update_of_ne (Fin.ne_of_val_ne hb') _
        _).trans (Function.update_of_ne (Fin.ne_of_val_ne ha') _ _)
      have hSwZ (z : ZMod 2) : swGenBit p0 sKick muxBit (Function.update β₁ b z) = swGenBit p0
        sKick muxBit β := (swGenBit_update_not_sel p0 sKick muxBit _ b
          (Or.inl (by simp only [b]; omega)) z).trans
          (swGenBit_update_not_sel p0 sKick muxBit β a
            (Or.inl (by simp only [a]; omega)) _)
      have hBtZ (z : ZMod 2) : swapPrefixBitsGen p0 sKick muxBit k (by omega) (Function.update β₁
        b z) = Function.update δ b z := by
        funext w; by_cases hwb : w = b
        · subst hwb; simp [swapPrefixBitsGen, hSwZ z, b, show ¬ ((p0 + 1) + k < k) by omega]
        · by_cases hwa : w = a
          · subst hwa; simp [Function.update_of_ne hab, δ, swapPrefixBitsGen, hSwZ z, β₁, a,
              show ¬ (p0 + 1 ≤ k) by omega]
          · have hwa' : w.val ≠ k := fun h ↦ hwa (Fin.ext h)
            have hwb' : w.val ≠ (p0 + 1) + k := fun h ↦ hwb (Fin.ext h)
            rw [Function.update_of_ne hwb, show δ w = swapPrefixBitsGen p0 sKick muxBit k (by
              omega) β w from Function.update_of_ne hwa _ _]
            dsimp only [swapPrefixBitsGen]; rw [hSwZ z]
            by_cases hsw : swGenBit p0 sKick muxBit β = 1
            · by_cases h1 : w.val < k
              · simp only [hsw, h1, ↓reduceIte, ↓reduceDIte,
                  hUpdB₁ z ⟨(p0 + 1) + w.val, _⟩ (by dsimp; omega) (by dsimp; omega)]
              · by_cases h2 : p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + k
                · simp only [hsw, h1, h2, and_self, ↓reduceIte, ↓reduceDIte,
                    hUpdB₁ z ⟨w.val - (p0 + 1), _⟩ (by dsimp; omega) (by dsimp; omega)]
                · simp only [hsw, h1, h2, ↓reduceIte, ↓reduceDIte, hUpdB₁ z w hwa' hwb']
            · simp only [hsw, ↓reduceIte, hUpdB₁ z w hwa' hwb']
      have hPhZ (z : ZMod 2) : swapPrefixPhaseGen p0 sKick muxBit k (Function.update β₁ b z) =
        swapPrefixPhaseGen p0 sKick muxBit (k + 1) β + ((β a + β b) * swGenBit p0 sKick muxBit
        β) * z := by
        have hTerm : ((β a + β b) * swGenBit p0 sKick muxBit β) * z = (∑ r : Fin (p0 + 1), if r =
          ⟨k, by omega⟩ then (β a + β b) * z else 0) * swGenBit p0 sKick muxBit β := by
          rw [Finset.sum_ite_eq' Finset.univ (⟨k, by omega⟩ : Fin (p0 + 1))]; simp [mul_right_comm]
        rw [hTerm]; dsimp only [swapPrefixPhaseGen]; rw [hSwZ z, ← add_mul, ←
          Finset.sum_add_distrib]
        refine congrArg (· * swGenBit p0 sKick muxBit β) (Finset.sum_congr rfl fun r _ ↦ ?_)
        by_cases hrk : r = ⟨k, by omega⟩
        · subst hrk; simp [β₁, a, b]
        · have hrne : r.val ≠ k := fun h ↦ hrk (Fin.ext h); by_cases hr : k ≤ r.val
          · simp [hr, hrk, show k + 1 ≤ r.val by omega,
              hUpdB₁ z ⟨r.val, _⟩ hrne (by dsimp; omega),
              hUpdB₁ z ⟨(p0 + 1) + r.val, _⟩ (by dsimp; omega) (by dsimp; omega)]
          · simp [hr, hrk, show ¬ (k + 1 ≤ r.val) by omega]
      rw [show SelectSwapQROM.ket β = Solution.XMeasCircuit.ket β from rfl]
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Circuit.eval_onRegister,
        pairPreCirc2, pairPostCirc2, Circuit.onRegister_seq, onRegister_cnotHad,
        onRegister_hHad, show rP 1 = b from rfl, show rP 0 = a from rfl, eval_seq_mulVecHad,
        ket_CNOTHad]
      rw [show Function.update β a (β a + β b) = β₁ from rfl, Solution.XMeasCircuit.ket_H,
        show β₁ b = β b from
        Function.update_of_ne hab.symm _ _, smul_add, smul_smul, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, swapPrefixUnitaryGen_mulVec_ket,
        swapPrefixUnitaryGen_mulVec_ket, hBtZ 0, hBtZ 1, hPhZ 0, hPhZ 1, mul_zero, add_zero,
        mul_one, Solution.XMeasCircuit.bitSign_add]
      let ph := Solution.XMeasCircuit.bitSign (swapPrefixPhaseGen p0 sKick muxBit (k + 1) β)
      let s' : ZMod 2 := β b + (β a + β b) * swGenBit p0 sKick muxBit β
      have hFactor : Solution.XMeasCircuit.sqrtHalf • (ph •
        Solution.XMeasCircuit.ket (Function.update δ b 0)) +
        (Solution.XMeasCircuit.sqrtHalf * Solution.XMeasCircuit.bitSign (β b)) • ((ph *
          Solution.XMeasCircuit.bitSign ((β a + β b) *
        swGenBit p0 sKick muxBit β)) • Solution.XMeasCircuit.ket (Function.update δ b 1)) = ph •
        (Solution.XMeasCircuit.sqrtHalf • Solution.XMeasCircuit.ket (Function.update δ b 0) +
          (Solution.XMeasCircuit.sqrtHalf *
        Solution.XMeasCircuit.bitSign s') • Solution.XMeasCircuit.ket (Function.update δ b 1)) := by
        simp only [s', Solution.XMeasCircuit.bitSign_add, smul_add, smul_smul]; congr 2 <;> ring
      rw [hFactor, Matrix.mulVec_smul, ket_H_superposHad b δ s', Matrix.mulVec_smul,
        ket_CNOTHad, swapPrefixUnitaryGen_mulVec_ket]
      have hSwAlg (x y s : ZMod 2) (hs : s = 0 ∨ s = 1) : x + y + (y + (x + y) * s) = (if s = 1 then
        y else x) ∧ y + (x + y) * s = (if s = 1 then x else y) := by
        rcases hs with rfl | rfl <;>
          rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one x with rfl | rfl
          <;>
            rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one y with rfl | rfl <;>
            decide
      have hAlg := hSwAlg (β a) (β b) (swGenBit p0 sKick muxBit β)
        (Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one _)
      refine congrArg (ph • Solution.XMeasCircuit.ket ·) (funext fun w ↦ ?_); by_cases hwa : w = a
      · subst hwa; simpa [Function.update_self, Function.update_of_ne hab, δ, s',
          swapPrefixBitsGen, a, b, show k < k + 1 by omega] using hAlg.1
      · by_cases hwb : w = b
        · subst hwb; simpa [Function.update_of_ne hab.symm, Function.update_self, s',
            swapPrefixBitsGen, b, show ¬ ((p0 + 1) + k < k + 1) by omega,
            show p0 + 1 ≤ (p0 + 1) + k ∧ (p0 + 1) + k < (p0 + 1) + (k + 1) by omega,
            show (⟨(p0 + 1) + k - (p0 + 1), by dsimp [nLocGen, nActGen]; omega⟩ :
              Wire (nLocGen p0 sKick)) = a from Fin.ext (by dsimp [a]; omega)] using hAlg.2
        · have hwa' : w.val ≠ k := fun h ↦ hwa (Fin.ext h)
          have hwb' : w.val ≠ (p0 + 1) + k := fun h ↦ hwb (Fin.ext h)
          rw [Function.update_of_ne hwa, Function.update_of_ne hwb,
            show δ w = swapPrefixBitsGen p0 sKick muxBit k (by omega) β w from
              Function.update_of_ne hwa _ _]
          dsimp only [swapPrefixBitsGen]
          by_cases hsw : swGenBit p0 sKick muxBit β = 1
          · by_cases h1 : w.val < k
            · simp only [hsw, h1, show w.val < k + 1 by omega, ↓reduceIte, ↓reduceDIte]
            · by_cases h2 : p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + k
              · simp only [hsw, h1, show ¬ (w.val < k + 1) by omega, h2,
                  show p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + (k + 1) by omega,
                  ↓reduceIte, ↓reduceDIte]
              · simp only [hsw, h1, show ¬ (w.val < k + 1) by omega, h2,
                  show ¬ (p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + (k + 1)) by omega,
                  ↓reduceIte, ↓reduceDIte]
          · simp only [hsw, ↓reduceIte]
theorem swapPrefixBitsGen_full_eq_writeReg (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) →
    Bool) (β : BitAssignment (nLocGen p0 sKick)) :
    let rActLoc := QRegister.block 0 (nActGen p0) (by dsimp [nLocGen]; omega)
    swapPrefixBitsGen p0 sKick muxBit (p0 + 1) le_rfl β = CoherentAlias.writeReg β rActLoc
      (pktMuxSwapGenPerm (p0 + 1) muxBit (fun i ↦ β (rActLoc.wires i))) := by
  intro rActLoc; let γAct : BitAssignment (nActGen p0) := fun i ↦ β (rActLoc.wires i)
  have hrAct (k : Fin (nActGen p0)) : rActLoc.wires k = ⟨k.val, by dsimp [nLocGen]; omega⟩ :=
    Fin.ext (Nat.zero_add k.val)
  funext w; by_cases hw : w.val < nActGen p0
  · have hwEq : rActLoc ⟨w.val, hw⟩ = w := Fin.ext (Nat.zero_add w.val)
    have hwRhs : CoherentAlias.writeReg β rActLoc (pktMuxSwapGenPerm (p0 + 1) muxBit γAct) w =
      pktMuxSwapGenBits (p0 + 1) muxBit γAct ⟨w.val, hw⟩ := (congrArg (CoherentAlias.writeReg β
      rActLoc (pktMuxSwapGenPerm (p0 + 1) muxBit γAct)) hwEq.symm).trans
      (CoherentAlias.writeReg_apply_reg β rActLoc (pktMuxSwapGenPerm (p0 + 1) muxBit γAct) ⟨w.val,
      hw⟩)
    rw [show CoherentAlias.writeReg β _ _ w = CoherentAlias.writeReg β rActLoc (pktMuxSwapGenPerm
      (p0 + 1) muxBit γAct) w from rfl, hwRhs]
    have hp : (fun i : Fin 4 ↦ decide (β ⟨2 * (p0 + 1) + i.val,
        by dsimp [nLocGen, nActGen]; omega⟩ = 1)) =
        fun i ↦ decide (γAct ⟨2 * (p0 + 1) + i.val, by dsimp [nActGen]; omega⟩ = 1) :=
      funext fun i ↦ congrArg (fun u ↦ decide (β u = 1))
        (hrAct ⟨2 * (p0 + 1) + i.val, by dsimp [nActGen]; omega⟩).symm
    have hk : (fun j : Fin 9 ↦ decide (β ⟨2 * (p0 + 1) + 4 + j.val,
        by dsimp [nLocGen, nActGen]; omega⟩ = 1)) =
        fun j ↦ decide (γAct ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nActGen]; omega⟩ = 1) :=
      funext fun j ↦ congrArg (fun u ↦ decide (β u = 1))
        (hrAct ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nActGen]; omega⟩).symm
    let bMux := muxBit
      (finOfBits 4 fun i ↦ decide (γAct ⟨2 * (p0 + 1) + i.val, by dsimp [nActGen]; omega⟩ = 1))
      (finOfBits 9 fun j ↦ decide (γAct ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nActGen]; omega⟩ = 1))
    have hSw : swGenBit p0 sKick muxBit β = if bMux then 1 else 0 := congrArg (fun b : Bool ↦ if b
      then (1 : ZMod 2) else 0) (congrArg₂ muxBit (congrArg (finOfBits 4) hp) (congrArg (finOfBits
      9) hk))
    change swapPrefixBitsGen p0 sKick muxBit (p0 + 1) le_rfl β w = if h1 : w.val < p0 + 1 then
        if bMux then γAct ⟨(p0 + 1) + w.val, by dsimp [nActGen]; omega⟩ else γAct ⟨w.val, hw⟩
      else if h2 : w.val < 2 * (p0 + 1) then
        if bMux then γAct ⟨w.val - (p0 + 1), by dsimp [nActGen]; omega⟩ else γAct ⟨w.val, hw⟩
      else γAct ⟨w.val, hw⟩
    dsimp only [swapPrefixBitsGen]; rw [hSw]; by_cases h1 : w.val < p0 + 1
    · by_cases hb : bMux = true
      · simp only [hb, h1, ↓reduceIte, ↓reduceDIte]
        exact congrArg β (hrAct ⟨(p0 + 1) + w.val, by dsimp [nActGen]; omega⟩).symm
      · simp only [hb, h1, ↓reduceDIte]; exact congrArg β hwEq.symm
    · by_cases h2 : w.val < 2 * (p0 + 1)
      · by_cases hb : bMux = true
        · simp only [hb, h1, h2, show p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + (p0 + 1) by omega,
            and_self, ↓reduceIte, ↓reduceDIte]
          exact congrArg β (hrAct ⟨w.val - (p0 + 1), by dsimp [nActGen]; omega⟩).symm
        · simp only [hb, h1, h2, ↓reduceDIte]; exact congrArg β hwEq.symm
      · by_cases hb : bMux = true
        · simp only [hb, h1, h2, show ¬ (p0 + 1 ≤ w.val ∧ w.val < (p0 + 1) + (p0 + 1)) by omega,
            ↓reduceIte, ↓reduceDIte]
          exact congrArg β hwEq.symm
        · simp only [hb, h1, h2, ↓reduceDIte]; exact congrArg β hwEq.symm
  · have hnm : w ∉ Set.range rActLoc.wires := fun ⟨j, hj⟩ ↦ by
      have hv := congrArg Fin.val hj; simp [rActLoc] at hv; omega
    rw [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnm]; dsimp only [swapPrefixBitsGen]
    simp [show ¬ (w.val < p0 + 1) by dsimp [nActGen] at hw; omega,
      show ¬ (w.val < (p0 + 1) + (p0 + 1)) by dsimp [nActGen] at hw; omega]
theorem cleanRealizesHadWMuxSwapLocalGenDyn (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) →
    Bool) {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) {kickDyn : DynamicCircuit Var (14 +
    sKick)} (hKick : Solution.XMeasCircuit.CleanRealizes v (actKick rfl) (scrKick rfl)
    (Solution.XMeasCircuit.phaseFlipUnitary (keepKickPhaseOf muxBit)) kickDyn) :
    Solution.XMeasCircuit.CleanRealizes v
      (QRegister.block 0 (nActGen p0) (by dsimp [nLocGen]; omega))
      (QRegister.block (nActGen p0) (nScrGen p0 sKick) (by dsimp [nLocGen]; omega))
      (pktMuxSwapGenUnitary (p0 + 1) muxBit) (hadWMuxSwapLocalGenDyn p0 sKick v kickDyn) := by
  let rActLoc : QRegister (nActGen p0) (nLocGen p0 sKick) :=
    QRegister.block 0 (nActGen p0) (by dsimp [nLocGen]; omega)
  let rScrLoc : QRegister (nScrGen p0 sKick) (nLocGen p0 sKick) :=
    QRegister.block (nActGen p0) (nScrGen p0 sKick) (by dsimp [nLocGen]; omega)
  have hScrImg : (loopScrGen p0 sKick (p0 + 1) le_rfl).image = rScrLoc.image := by
    ext w; dsimp only [loopScrGen, rScrLoc]
    simp only [QRegister.mem_image, Fin.ext_iff, QRegister.block_apply_val]
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨⟨j.val, by have := j.isLt; dsimp [nScrGen]; omega⟩, by dsimp; omega⟩,
      fun ⟨j, hj⟩ ↦ ⟨⟨j.val, by have := j.isLt; dsimp [nScrGen] at this; omega⟩, by dsimp; omega⟩⟩
  have hSet := cleanRealizesSetPairConjWrapGenDyn p0 sKick muxBit v hKick (p0 + 1) le_rfl
  rw [hScrImg] at hSet
  refine (AliasPrep.cleanRealizes_sbx_iff v rActLoc rScrLoc (pktMuxSwapGenUnitary (p0 + 1)
    muxBit) (hadWMuxSwapLocalGenDyn p0 sKick v kickDyn)).mpr
    ((SelectSwapQROM.cleanRealizes_iff_set v rActLoc rScrLoc (pktMuxSwapGenUnitary (p0 + 1)
    muxBit) (hadWMuxSwapLocalGenDyn p0 sKick v kickDyn)).mpr (hSet.congr_unitary fun β _ ↦ ?_))
  have hPh0 : swapPrefixPhaseGen p0 sKick muxBit (p0 + 1) β = 0 := by
    dsimp only [swapPrefixPhaseGen]
    simp [show ∀ r : Fin (p0 + 1), ¬ (p0 + 1 ≤ r.val) by intro r; have := r.isLt; omega]
  change (swapPrefixUnitaryGen p0 sKick muxBit (p0 +
    1) le_rfl).1.mulVec (Solution.XMeasCircuit.ket β) =
    (rActLoc.embedUnitary (pktMuxSwapGenUnitary (p0 + 1) muxBit)).1 *ᵥ CoherentAlias.ket β
  rw [swapPrefixUnitaryGen_mulVec_ket, hPh0, Solution.XMeasCircuit.bitSign_zero, one_smul,
    pktMuxSwapGenUnitary, embedUnitary_bitPermUnitary_mulVec_ket]
  exact congrArg CoherentAlias.ket (swapPrefixBitsGen_full_eq_writeReg p0 sKick muxBit β)
/-- Generic embedded `(2 * (p0 + 1) + 13)`-wire Hadamard-target `W`-state mux-CSWAP. -/
def hadWMuxSwapGenDyn (p0 sKick : ℕ) {Var : Type} {N s : ℕ} (v : Var) (kickDyn : DynamicCircuit
    Var (14 + sKick)) (rAct : QRegister (2 * (p0 + 1) + 13) N) (rScr : QRegister s N) (hs : (p0 + 1)
    + sKick ≤ s) : DynamicCircuit Var N := if h : ∀ i j, rAct i ≠ (rScr.compose (QRegister.block 0
    ((p0 + 1) +
      sKick) (by omega))) j then Solution.XMeasCircuit.dynOnRegister (rAct.concat (rScr.compose
    (QRegister.block 0 ((p0 + 1) + sKick) (by omega))) (QRegister.disjoint_iff.mpr h))
    (hadWMuxSwapLocalGenDyn p0 sKick v kickDyn) else .circuit Circuit.identity
theorem countHadWMuxSwapGenDyn_arity3 (p0 sKick : ℕ) {Var : Type} {N s : ℕ} (v : Var) {kickDyn :
    DynamicCircuit Var (14 + sKick)} (rAct : QRegister (2 * (p0 + 1) + 13) N) (rScr : QRegister s N)
    (hs : (p0 + 1) + sKick ≤ s) (g : PrimitiveGate 3) (hK : kickDyn.count g = 0) :
    (hadWMuxSwapGenDyn p0 sKick v kickDyn rAct rScr hs).count g = 0 := by
  dsimp only [hadWMuxSwapGenDyn]; split_ifs
  · rw [Solution.XMeasCircuit.count_dynOnRegister,
      countHadWMuxSwapLocalGenDyn_arity3 p0 sKick v g hK]
  · simp
theorem countHadWMuxSwapGenDyn_t (p0 sKick : ℕ) {Var : Type} {N s : ℕ} (v : Var) (kickDyn :
    DynamicCircuit Var (14 + sKick)) (rAct : QRegister (2 * (p0 + 1) + 13) N) (rScr : QRegister s N)
    (hs : (p0 + 1) + sKick ≤ s) (hdisj : rAct.DisjointWires rScr) : (hadWMuxSwapGenDyn p0 sKick v
    kickDyn rAct rScr hs).count .T = kickDyn.count .T + 4 * (p0 + 1) := by
  dsimp only [hadWMuxSwapGenDyn]; split_ifs with h
  · rw [Solution.XMeasCircuit.count_dynOnRegister, countHadWMuxSwapLocalGenDyn_t]
  · exact absurd (QRegister.disjoint_iff.mp
      (hdisj.compose_right (QRegister.block 0 ((p0 + 1) + sKick) (by omega)))) h
theorem cleanRealizesHadWMuxSwapGenDyn (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    {Var : Type} [Fintype Var] [DecidableEq Var] {N s : ℕ} (v : Var) {kickDyn : DynamicCircuit Var
    (14 + sKick)} (hKick : Solution.XMeasCircuit.CleanRealizes v (actKick rfl) (scrKick rfl)
    (Solution.XMeasCircuit.phaseFlipUnitary (keepKickPhaseOf muxBit)) kickDyn) (rAct :
      QRegister (2 * (p0 +
    1) + 13) N) (rScr : QRegister s N) (hs : (p0 + 1) + sKick ≤ s) (hdisj : rAct.DisjointWires rScr)
    : Solution.CleanDyn.CleanRealizes v rAct rScr (pktMuxSwapGenUnitary (p0 + 1) muxBit)
    (hadWMuxSwapGenDyn p0 sKick v kickDyn rAct rScr hs) := by
  dsimp only [hadWMuxSwapGenDyn]; split_ifs with h
  · let rSub := rScr.compose (QRegister.block 0 ((p0 + 1) + sKick) (by omega))
    let rAll := rAct.concat rSub (QRegister.disjoint_iff.mpr h)
    have hL : rAll.compose (QRegister.block 0 (nActGen p0) (by dsimp [nActGen]; omega)) = rAct :=
      CoherentAlias.qreg_ext fun i ↦ by
        change (rAll (QRegister.block 0 (nActGen p0) _ i)).val = (rAct i).val
        rw [show QRegister.block 0 (nActGen p0) _ i =
          Fin.castAdd ((p0 + 1) + sKick) i by ext; simp, QRegister.concat_apply_left]
    have hR : rAll.compose (QRegister.block (nActGen p0) (nScrGen p0 sKick)
        (by dsimp [nActGen, nScrGen]; omega)) = rSub :=
      CoherentAlias.qreg_ext fun j ↦ by
        change (rAll (QRegister.block (nActGen p0) (nScrGen p0 sKick) _ j)).val = (rSub j).val
        rw [show QRegister.block (nActGen p0) (nScrGen p0 sKick) _ j =
          Fin.natAdd (2 * (p0 + 1) + 13) j by ext; simp [Fin.val_natAdd, nActGen],
          QRegister.concat_apply_right]
    have hCr := (cleanRealizesHadWMuxSwapLocalGenDyn p0 sKick muxBit v hKick).onRegister rAll
    rw [hL, hR] at hCr
    exact ((AliasPrep.cleanRealizes_sbx_iff v rAct rSub (pktMuxSwapGenUnitary (p0 + 1)
      muxBit) _).mp hCr).extend_scr hdisj (rScr.image_compose_subset _)
  · exact absurd (QRegister.disjoint_iff.mp
      (hdisj.compose_right (QRegister.block 0 ((p0 + 1) + sKick) (by omega)))) h
theorem cleanRealizesHadWMuxSwapGenDyn_inv (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) →
    Bool) {Var : Type} [Fintype Var] [DecidableEq Var] {N s : ℕ} (v : Var) {kickDyn : DynamicCircuit
    Var (14 + sKick)} (hKick : Solution.XMeasCircuit.CleanRealizes v (actKick rfl) (scrKick rfl)
    (Solution.XMeasCircuit.phaseFlipUnitary (keepKickPhaseOf muxBit)) kickDyn) (rAct :
      QRegister (2 * (p0 +
    1) + 13) N) (rScr : QRegister s N) (hs : (p0 + 1) + sKick ≤ s) (hdisj : rAct.DisjointWires rScr)
    : Solution.CleanDyn.CleanRealizes v rAct rScr (pktMuxSwapGenUnitary (p0 + 1) muxBit)⁻¹
    (hadWMuxSwapGenDyn p0 sKick v kickDyn rAct rScr hs) := by
  rw [pktMuxSwapGenUnitary_inv]
  exact cleanRealizesHadWMuxSwapGenDyn p0 sKick muxBit v hKick rAct rScr hs hdisj
/-! ### Subsection 4C: `50-T` `Mux25`, `46-T` `Mux23` (`Core23`), and Literal `mux9Bit` Exports -/
/-- `23`-wire (`10 + 13`) mux-swap unitary gated by `mux9AltBit` (`46 T`, `16 ≤ s`). -/
noncomputable abbrev pktMuxSwapAlt23Unitary := pktMuxSwapGenUnitary 5 mux9AltBit
/-- `46-T`, `0`-Toffoli Hadamard-target `W`-state `23`-wire `pktMuxSwapAlt23Unitary` (`16≤s`). -/
def hadWMuxSwap23Dyn {Var : Type} {N s : ℕ} (v : Var) (rAct : QRegister (10 + 13) N)
    (rScr : QRegister s N) (hs : 16 ≤ s) : DynamicCircuit Var N :=
  hadWMuxSwapGenDyn 4 11 v (gatedKeepKickback25Dyn v) rAct rScr hs
@[simp] theorem countHadWMuxSwap23Dyn_arity3 {Var} {N s} (v : Var) (rAct : QRegister (10 + 13) N)
    (rScr : QRegister s N) (hs : 16 ≤ s) (g : PrimitiveGate 3) : (hadWMuxSwap23Dyn v rAct rScr
    hs).count g = 0 := countHadWMuxSwapGenDyn_arity3 4 11 v rAct rScr hs g
    (countGatedKeepKickback25Dyn_arity3 v g)
@[simp] theorem countHadWMuxSwap23Dyn_toff {Var} {N s} (v : Var) (rAct : QRegister (10 + 13) N)
    (rScr : QRegister s N) (hs : 16 ≤ s) : (hadWMuxSwap23Dyn v rAct rScr hs).count .TOFF = 0 :=
  countHadWMuxSwap23Dyn_arity3 v rAct rScr hs .TOFF
@[simp] theorem countHadWMuxSwap23Dyn_t {Var} {N s} (v : Var) (rAct : QRegister (10 + 13) N)
    (rScr : QRegister s N) (hs : 16 ≤ s) (hdisj : rAct.DisjointWires rScr) : (hadWMuxSwap23Dyn v
    rAct rScr hs).count .T = 46 := by
  rw [hadWMuxSwap23Dyn, countHadWMuxSwapGenDyn_t 4 11 v _ rAct rScr hs hdisj,
    countGatedKeepKickback25Dyn_t]
theorem cleanRealizesHadWMuxSwap23Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {N s : ℕ} (v :
    Var) (rAct : QRegister (10 + 13) N) (rScr : QRegister s N) (hs : 16 ≤ s) (hdisj :
    rAct.DisjointWires rScr) : Solution.CleanDyn.CleanRealizes v rAct rScr pktMuxSwapAlt23Unitary
    (hadWMuxSwap23Dyn v rAct rScr hs) := cleanRealizesHadWMuxSwapGenDyn 4 11 mux9AltBit v
    (cleanRealizesGatedKeepKickback25Dyn v) rAct rScr hs hdisj
theorem cleanRealizesHadWMuxSwap23Dyn_inv {Var : Type} [Fintype Var] [DecidableEq Var] {N s : ℕ}
    (v : Var) (rAct : QRegister (10 + 13) N) (rScr : QRegister s N) (hs : 16 ≤ s) (hdisj :
    rAct.DisjointWires rScr) : Solution.CleanDyn.CleanRealizes v rAct rScr pktMuxSwapAlt23Unitary⁻¹
    (hadWMuxSwap23Dyn v rAct rScr hs) := cleanRealizesHadWMuxSwapGenDyn_inv 4 11 mux9AltBit v
    (cleanRealizesGatedKeepKickback25Dyn v) rAct rScr hs hdisj
/-- Reorders `23`-wire `wInner2 = 18` core (`0..4 idx`, `5..9 alt`, `10..18 keep`, `19..22 pkt`)
  into
`(10 + 13)` mux-swap order (`0..9 ↦ 0..9`, `10..13 ↦ 19..22`, `14..22 ↦ 10..18`). -/
def core23MuxSwap23Reg : QRegister (10 + 13) 23 := mkReg (fun i ↦ if i.val < 10 then i.val else if
    i.val < 14 then i.val + 9 else i.val - 4) (fun i ↦ by have := i.isLt; split_ifs <;> omega) (fun
    i j h ↦ by have := i.isLt; have := j.isLt; split_ifs at h <;> omega)
/-- `23`-wire `wInner2 = 18` post-QROM controlled-SWAP bit-map (`0..4 ↔ 5..9` on `muxBit pkt keep`).
-/
def core23PostGenBits (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (β : BitAssignment 23) :
    BitAssignment 23 :=
  let sw := muxBit (finOfBits 4 fun i ↦ decide (β ⟨19 + i.val, by omega⟩ = 1)) (finOfBits 9 fun j ↦
    decide (β ⟨10 + j.val, by omega⟩ = 1))
  fun u ↦ if _ : u.val < 5 then if sw then β ⟨5 + u.val, by omega⟩ else β u else if _ : u.val < 10
    then if sw then β ⟨u.val - 5, by omega⟩ else β u else β u
theorem core23PostGenBits_invol (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) : Function.Involutive
    (core23PostGenBits muxBit) := fun β ↦ by
  have h10 (q : Wire 23) (hq : 10 ≤ q.val) : core23PostGenBits muxBit β q = β q := by
    dsimp only [core23PostGenBits]; simp [show ¬ q.val < 5 by omega, show ¬ q.val < 10 by omega]
  have hp : (fun i : Fin 4 ↦ decide (core23PostGenBits muxBit β ⟨19 + i.val, by omega⟩ = 1)) = fun
    i ↦ decide (β ⟨19 + i.val, by omega⟩ = 1) :=
    funext fun i ↦ by rw [h10 ⟨19 + i.val, by omega⟩ (by dsimp; omega)]
  have hk : (fun j : Fin 9 ↦ decide (core23PostGenBits muxBit β ⟨10 + j.val, by omega⟩ = 1)) = fun
    j ↦ decide (β ⟨10 + j.val, by omega⟩ = 1) :=
    funext fun j ↦ by rw [h10 ⟨10 + j.val, by omega⟩ (by dsimp; omega)]
  funext u; conv_lhs => rw [core23PostGenBits]
  dsimp only; rw [hp, hk]; by_cases h1 : u.val < 5
  · cases hsw : muxBit (finOfBits 4 fun i ↦ decide (β ⟨19 + i.val, by omega⟩ = 1))
        (finOfBits 9 fun j ↦ decide (β ⟨10 + j.val, by omega⟩ = 1))
    · simp [h1, core23PostGenBits, hsw]
    · simp only [h1, ↓reduceDIte, ↓reduceIte, core23PostGenBits, hsw,
        show ¬ (5 + u.val < 5) by omega, show 5 + u.val < 10 by omega]
      exact congrArg β (Fin.ext (by dsimp; omega))
  · by_cases h2 : u.val < 10
    · cases hsw : muxBit (finOfBits 4 fun i ↦ decide (β ⟨19 + i.val, by omega⟩ = 1))
          (finOfBits 9 fun j ↦ decide (β ⟨10 + j.val, by omega⟩ = 1))
      · simp [h1, h2, core23PostGenBits, hsw]
      · simp only [h1, h2, ↓reduceDIte, ↓reduceIte, core23PostGenBits, hsw,
          show u.val - 5 < 5 by omega]; exact congrArg β (Fin.ext (by dsimp; omega))
    · simp only [h1, h2, ↓reduceDIte, h10 u (by omega)]
/-- Involutive `23`-wire `wInner2 = 18` post-QROM controlled-SWAP permutation for `muxBit`. -/
def core23PostGenPerm (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) : Equiv.Perm (BitAssignment 23)
    := ⟨core23PostGenBits muxBit, core23PostGenBits muxBit, core23PostGenBits_invol muxBit,
    core23PostGenBits_invol muxBit⟩
@[simp] theorem core23PostGenPerm_apply (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (γ : BitAssignment 23) : core23PostGenPerm muxBit γ = core23PostGenBits muxBit γ := rfl
theorem embedUnitary_bitPermUnitary_eqHad {k n : ℕ} (r : QRegister k n)
    (p₁ : Equiv.Perm (BitAssignment k)) (p₂ : Equiv.Perm (BitAssignment n))
    (h : ∀ (β : BitAssignment n) (u : Wire n),
      CoherentAlias.writeReg β r (p₁ (fun i ↦ β (r.wires i))) u = p₂ β u) :
    r.embedUnitary (CoherentAlias.bitPermUnitary p₁) = CoherentAlias.bitPermUnitary p₂ := by
  apply Subtype.ext; refine Solution.XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [embedUnitary_bitPermUnitary_mulVec_ket, bitPermUnitary_mulVec_ketHad]
  exact congrArg CoherentAlias.ket (funext (h β))
theorem core23MuxSwap23Reg_embedPktMuxSwapGen23Unitary (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) →
    Bool) : core23MuxSwap23Reg.embedUnitary (pktMuxSwapGenUnitary 5 muxBit) =
    CoherentAlias.bitPermUnitary (core23PostGenPerm muxBit) := by
  have hReg (k : Fin (10 + 13)) (q : Wire 23) (hv : (if k.val < 10 then k.val else if k.val < 14
    then k.val + 9 else k.val - 4) = q.val) : core23MuxSwap23Reg.wires k = q := by
    ext; dsimp only [core23MuxSwap23Reg]
    rw [mkReg_apply_val]; exact hv
  rw [pktMuxSwapGenUnitary]
  refine embedUnitary_bitPermUnitary_eqHad core23MuxSwap23Reg (pktMuxSwapGenPerm 5 muxBit)
    (core23PostGenPerm muxBit) fun β u ↦ ?_
  rw [pktMuxSwapGenPerm_apply, core23PostGenPerm_apply]
  have hp : (fun i : Fin 4 ↦ decide (β (core23MuxSwap23Reg.wires ⟨10 + i.val, by omega⟩) = 1)) = fun
    i ↦ decide (β ⟨19 + i.val, by omega⟩ = 1) := funext fun i ↦ by
    rw [hReg ⟨10 + i.val, by omega⟩ ⟨19 + i.val, by omega⟩
      (by dsimp only; have := i.isLt; split_ifs <;> omega)]
  have hk : (fun j : Fin 9 ↦ decide (β (core23MuxSwap23Reg.wires ⟨14 + j.val, by omega⟩) = 1)) = fun
    j ↦ decide (β ⟨10 + j.val, by omega⟩ = 1) := funext fun j ↦ by
    rw [hReg ⟨14 + j.val, by omega⟩ ⟨10 + j.val, by omega⟩
      (by dsimp only; have := j.isLt; split_ifs <;> omega)]
  have hu_lt := u.isLt; by_cases h1 : u.val < 5
  · have hj := hReg ⟨u.val, by omega⟩ u (by dsimp only; split_ifs <;> omega)
    have hjB := hReg ⟨5 + u.val, by omega⟩ ⟨5 + u.val, by omega⟩
      (by dsimp only; split_ifs <;> omega)
    conv_lhs => rw [← hj, show core23MuxSwap23Reg.wires _ = core23MuxSwap23Reg _ from rfl,
      CoherentAlias.writeReg_apply_reg]
    dsimp only [pktMuxSwapGenBits, core23PostGenBits]; rw [hp, hk]
    simp only [h1, ↓reduceDIte, hjB, hj]
  · by_cases h2 : u.val < 10
    · have hj := hReg ⟨u.val, by omega⟩ u (by dsimp only; simp only [h2, ↓reduceIte])
      have hjA := hReg ⟨u.val - 5, by omega⟩ ⟨u.val - 5, by omega⟩
        (by dsimp only; split_ifs <;> omega)
      conv_lhs => rw [← hj, show core23MuxSwap23Reg.wires _ = core23MuxSwap23Reg _ from rfl,
        CoherentAlias.writeReg_apply_reg]
      dsimp only [pktMuxSwapGenBits, core23PostGenBits]; rw [hp, hk]
      simp only [h1, h2, ↓reduceDIte, hjA, hj]
    · by_cases h3 : u.val < 19
      · have hj := hReg ⟨u.val + 4, by omega⟩ u (by dsimp only; split_ifs <;> omega)
        conv_lhs => rw [← hj, show core23MuxSwap23Reg.wires _ = core23MuxSwap23Reg _ from rfl,
          CoherentAlias.writeReg_apply_reg]
        dsimp only [pktMuxSwapGenBits, core23PostGenBits]
        simp only [show ¬ (u.val + 4 < 5) by omega, show ¬ (u.val + 4 < 10) by omega, h1, h2,
          ↓reduceDIte, hj]
      · have hj := hReg ⟨u.val - 9, by omega⟩ u (by dsimp only; split_ifs <;> omega)
        conv_lhs => rw [← hj, show core23MuxSwap23Reg.wires _ = core23MuxSwap23Reg _ from rfl,
          CoherentAlias.writeReg_apply_reg]
        dsimp only [pktMuxSwapGenBits, core23PostGenBits]
        simp only [show ¬ (u.val - 9 < 5) by omega, show ¬ (u.val - 9 < 10) by omega, h1, h2,
          ↓reduceDIte, hj]
theorem mul_embedUnitary_col0_applyHad {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (hDisj : r₁.DisjointWires r₂) (A : Unitary (2 ^ k₁)) (B : Unitary (2 ^ k₂)) (h : Fin (2 ^ n)) :
    (r₁.embedUnitary A * r₂.embedUnitary B).1 h 0 = if r₂.replaceIndex (r₁.replaceIndex h 0) 0 = 0
    then A.1 (r₁.extractIndex h) 0 * B.1 (r₂.extractIndex h) 0 else 0 := by
  have hmv : (r₁.embedUnitary A * r₂.embedUnitary B).1 h 0 = (r₁.embedMatrix A.1 *ᵥ (r₂.embedMatrix
    B.1 *ᵥ Pi.single (M := fun _ ↦ ℂ) 0 1)) h := by
    rw [Matrix.mulVec_mulVec, ← QRegister.embedUnitary_val, ← QRegister.embedUnitary_val, ←
      Submonoid.coe_mul, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hmv, r₁.embedMatrix_mulVec_apply]
  change (∑ u : Fin (2 ^ k₁), A.1 (r₁.extractIndex h) u * (r₂.embedMatrix B.1 *ᵥ Pi.single (M := fun
    _ ↦ ℂ) 0 1) (r₁.replaceIndex h u)) = _
  rw [Finset.sum_eq_single 0]
  · rw [r₂.embedMatrix_mulVec_apply]
    change A.1 (r₁.extractIndex h) 0 * (∑ v : Fin (2 ^ k₂), B.1 (r₂.extractIndex (r₁.replaceIndex h
      0)) v * Pi.single (M := fun _ ↦ ℂ) 0 1 (r₂.replaceIndex (r₁.replaceIndex h 0) v)) = _
    rw [Finset.sum_eq_single 0]
    · rw [r₂.extractIndex_replaceIndex_of_disjoint r₁ hDisj.symm]
      by_cases h0 : r₂.replaceIndex (r₁.replaceIndex h 0) 0 = 0
      · simp only [h0, ↓reduceIte, Pi.single_eq_same, mul_one]
      · rw [Pi.single_eq_of_ne h0 1, mul_zero]; simp only [h0, ↓reduceIte, mul_zero]
    · intro v _ hv0
      have hne : r₂.replaceIndex (r₁.replaceIndex h 0) v ≠ 0 := fun heq ↦ hv0 <| by
        rw [← r₂.extractIndex_replaceIndex (r₁.replaceIndex h 0) v, heq, extractIndex_zeroHad]
      rw [Pi.single_eq_of_ne hne 1, mul_zero]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · intro u _ hu0
    rw [r₂.embedMatrix_mulVec_apply]
    change A.1 _ u * (∑ v : Fin (2 ^ k₂), _ * Pi.single (M := fun _ ↦ ℂ) 0 1 (r₂.replaceIndex
      (r₁.replaceIndex h u) v)) = 0
    suffices hs : (∑ v : Fin (2 ^ k₂), B.1 (r₂.extractIndex (r₁.replaceIndex h u)) v * Pi.single (M
      := fun _ ↦ ℂ) 0 1 (r₂.replaceIndex (r₁.replaceIndex h u) v)) = 0 by
      rw [hs, mul_zero]
    refine Finset.sum_eq_zero fun v _ ↦ ?_
    have hne : r₂.replaceIndex (r₁.replaceIndex h u) v ≠ 0 := fun heq ↦ hu0 <| by
      have hc := congrArg r₁.extractIndex heq
      rwa [r₁.extractIndex_replaceIndex_of_disjoint r₂ hDisj, r₁.extractIndex_replaceIndex,
        extractIndex_zeroHad] at hc
    rw [Pi.single_eq_of_ne hne 1, mul_zero]
  · intro h0; exact absurd (Finset.mem_univ _) h0
theorem mulVec_apply_of_ket_involHad {n : ℕ} (M : Operator (2 ^ n)) (σ : BitAssignment n →
    BitAssignment n) (hInvol : Function.Involutive σ) (hKet : ∀ δ,
      M *ᵥ Solution.XMeasCircuit.ket δ =
    Solution.XMeasCircuit.ket (σ δ)) (v : Fin (2 ^ n) → ℂ) (g : Fin (2 ^ n)) : (M *ᵥ v) g =
      v ((basisBits
    n).symm (σ (basisBits n g))) := by
  have hv : v = ∑ h : Fin (2 ^ n), v h • Solution.XMeasCircuit.ket (basisBits n h) := by
    ext i; rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [Solution.XMeasCircuit.ket, basisState]
    · intro h _ hne; simp [Solution.XMeasCircuit.ket, basisState, Pi.single_eq_of_ne hne.symm]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  conv_lhs => rw [hv, Matrix.mulVec_sum]
  rw [Finset.sum_apply, Finset.sum_eq_single ((basisBits n).symm (σ (basisBits n g)))]
  · simp [Matrix.mulVec_smul, hKet, hInvol (basisBits n g), Solution.XMeasCircuit.ket, basisState]
  · intro h _ hne
    rw [Matrix.mulVec_smul, hKet, Pi.smul_apply, Solution.XMeasCircuit.ket, basisState,
      Pi.single_eq_of_ne _ 1,
      smul_zero]; intro heq; apply hne; symm
    have h1 := congrArg (basisBits n) heq;
      rw [Solution.XMeasCircuit.basisBits_basisBitsEquiv_symm] at h1
    have h2 := congrArg σ h1; rw [hInvol (basisBits n h)] at h2; rw [h2]
    exact Solution.XMeasCircuit.basisBitsEquiv_symm_basisBits h
  · intro hi; exact absurd (Finset.mem_univ _) hi
/-- Lifts a local `k`-wire bit-assignment map `f` to `BitAssignment n` via `writeReg` on `r`. -/
noncomputable abbrev writePermHad {k n : ℕ} (r : QRegister k n)
    (f : BitAssignment k → BitAssignment k) (δ : BitAssignment n) : BitAssignment n :=
  CoherentAlias.writeReg δ r (f (fun i ↦ δ (r.wires i)))
theorem writePermHad_invol {k n : ℕ} (r : QRegister k n) {f : BitAssignment k → BitAssignment k}
    (hInvol : Function.Involutive f) : Function.Involutive (writePermHad r f) := fun δ ↦ by
  have hIn : (fun i ↦ writePermHad r f δ (r.wires i)) = f (fun i ↦ δ (r.wires i)) := funext fun i
    ↦ CoherentAlias.writeReg_apply_reg δ r _ i
  funext u; by_cases hu : u ∈ Set.range r.wires
  · obtain ⟨j, rfl⟩ := hu; change CoherentAlias.writeReg _ r _ (r j) = δ (r j)
    rw [CoherentAlias.writeReg_apply_reg, hIn, hInvol]
  · dsimp only [writePermHad]
    rw [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hu,
      CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hu]
theorem embedBitPerm_mul_col0_applyHad {k n : ℕ} (r : QRegister k n) (perm : Equiv.Perm
    (BitAssignment k)) (hInvol : Function.Involutive perm) (V : Unitary (2 ^ n)) (g : Fin (2 ^ n)) :
    (r.embedUnitary (CoherentAlias.bitPermUnitary perm) * V).1 g 0 = V.1 ((basisBits n).symm
    (writePermHad r perm (basisBits n g))) 0 := by
  have hmv (U : Unitary (2 ^ n)) (i : Fin (2 ^ n)) : U.1 i 0 = (U.1 *ᵥ Pi.single (M := fun _ ↦ ℂ) 0
    1) i := by rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hmv, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hmv V]
  exact mulVec_apply_of_ket_involHad _ (writePermHad r perm) (writePermHad_invol r hInvol)
    (fun δ ↦ embedUnitary_bitPermUnitary_mulVec_ket r perm δ) _ g
theorem embedBitPerm2_mul_col0_applyHad {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (p₁ : Equiv.Perm (BitAssignment k₁)) (p₂ : Equiv.Perm (BitAssignment k₂))
    (hp₁ : Function.Involutive p₁) (hp₂ : Function.Involutive p₂) (V : Unitary (2 ^ n))
    (g : Fin (2 ^ n)) : ((r₁.embedUnitary (CoherentAlias.bitPermUnitary p₁) *
      r₂.embedUnitary (CoherentAlias.bitPermUnitary p₂)) * V).1 g 0 =
    V.1 ((basisBits n).symm (writePermHad r₂ p₂
      (writePermHad r₁ p₁ (basisBits n g)))) 0 := by
  rw [mul_assoc, embedBitPerm_mul_col0_applyHad r₁ p₁ hp₁,
    embedBitPerm_mul_col0_applyHad r₂ p₂ hp₂, Solution.XMeasCircuit.basisBits_basisBitsEquiv_symm]
attribute [irreducible] andLoopGenDyn pairPreCirc2 pairPostCirc2 pairConjWrapGenDyn
  hadWMuxSwapLocalGenDyn hadWMuxSwapGenDyn hadWMuxSwap23Dyn

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HadWStateMux25CompactB
end
