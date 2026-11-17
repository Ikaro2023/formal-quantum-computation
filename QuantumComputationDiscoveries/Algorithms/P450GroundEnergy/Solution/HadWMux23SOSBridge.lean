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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HadWStateMux25B
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18Symp14Walk
/-!
# `46-T` `hadWMux23Bundle` & `wInner2 = 18` `PREP_mid` SOS Marginal Bridge (`HadWMux23SOSBridge`)
Bridges the `46-T`, `0`-Toffoli, `16`-scratch Hadamard-target `W`-state controlled-SWAP
(`hadWMuxSwap23Dyn` in `HadWStateMux25B`) onto `Inner18Symp14Walk` (`wInner2 = 18`, `mMidUB
18 = 24`): exports `hadWMux23Bundle : Mux23Bundle Var 16 46 mux9AltBit`, proves column-`0` `normSq`
invariance under `pktSwap56` and closed-form Walker-alias marginals matching `mux9Bit`, establishes
`b <
30` support on all `128` slices, and transfers `PrepMidValid`, `PrepMidValid128`, and
`QuantizedFactoredMag30.PrepMidQuant128` onto `prepMid18FromSlice` and `genPi128PrepMid18Of`
at `Quant56`, `Quant66`, `Quant72`, and `T72` (`factoredMag30T72Circuit.eval`).
## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: 10.1103/PhysRevA.87.022328.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary Basis
  Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208 (2019),
  DOI: 10.22331/q-2019-12-02-208.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush, "Even
  More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction," *PRX Quantum*
  **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
- G. H. Low, R. King, D. W. Berry, Q. Han, A. E. DePrince III, A. White, R. Babbush, R. D. Somma,
  and N. C. Rubin, "Fast Quantum Simulation of Electronic Structure by Spectrum Amplification,"
  *Phys. Rev. X* **15**, 041016 (2025), DOI: 10.1103/pb2g-j9cw.
-/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HadWMux23SOSBridge
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
    QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
    CoherentAlias CleanDyn AliasPrep
  TopIntegrationBridge Phase2MidSandwich CompactBilinearPrep MidReflCtxRetain OptXMeasUnload21
  OptFactoredMag30AndCoin9 QuantizedFactoredMag30 Cat11CompactPhase2Bridge ReordOuter13Bridge
  ZeroRcHotPrepMid21Fast Tuned162ScheduledSympQrom21 OptStepSympAnfQrom21
  Tuned162StepSympAnfQrom21 MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20
  CompactZeroCmp20OuterParam CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core
  CompactStepCompact2504ZeroCmp20 Pi145SOSPermBridge StepKeep9Symp14Data
  HadWStateMux25CompactA HadWStateMux25CompactB Inner18Symp14Walk
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowSos (k : ℕ) : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k two_ne_zero⟩
/-! ## Layer 1: `46-T` `hadWMux23Bundle` & `mux9AltBit` Fiber Weights -/
/-- `Inner18Symp14Walk.core23MuxSwap23Reg` and `HadWStateMux25CompactB.core23MuxSwap23Reg` denote
the same `(10 + 13)`-wire register inside `Wire 23`. -/
theorem core23MuxSwap23Reg_eq : Inner18Symp14Walk.core23MuxSwap23Reg =
    HadWStateMux25CompactB.core23MuxSwap23Reg :=
  CoherentAlias.qreg_ext fun _ ↦ rfl
/-- `pktMuxSwap23Perm muxBit` equals `pktMuxSwapGenPerm 5 muxBit` on `BitAssignment (10 + 13)`.
-/
theorem pktMuxSwap23Perm_eqPktMuxSwapGenPerm (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    pktMuxSwap23Perm muxBit = pktMuxSwapGenPerm 5 muxBit :=
  Equiv.ext fun β ↦ funext fun u ↦ by
    rw [pktMuxSwap23Perm_apply, pktMuxSwapGenPerm_apply]
    dsimp only [pktMuxSwap23Bits, pktMuxSwapGenBits]
/-- `pktMuxSwap23Unitary muxBit` equals `pktMuxSwapGenUnitary 5 muxBit` on `2 ^ (10 + 13)`. -/
theorem pktMuxSwap23Unitary_eqPktMuxSwapGenUnitary (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    : pktMuxSwap23Unitary muxBit = pktMuxSwapGenUnitary 5 muxBit := by
  rw [pktMuxSwap23Unitary_eq_bitPermUnitary, pktMuxSwapGenUnitary,
    pktMuxSwap23Perm_eqPktMuxSwapGenPerm]
/-- `false`-fiber weight of `mux9AltBit` under `coin9Weight` equals `k.val`. -/
theorem mux9AltBit_fiber_false (k : Fin (2 ^ 9)) : (∑ c : Fin (2 ^ 4), if mux9AltBit c k =
    false then coin9Weight c else 0) = k.val := by
  rw [← mux9_fiber_weight k, ← Equiv.sum_comp pktSwap56
    (fun c ↦ if mux9Bit c k = false then coin9Weight c else 0)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases hc1 : c = 1
  · subst hc1
    simp only [show pktSwap56 1 = 1 by decide, show coin9Weight 1 = 0 from rfl, ite_self]
  · rw [mux9AltBit_eqMux9Bit_swap hc1 k, coin9WeightPktSwap56 c]
/-- `true`-fiber weight of `mux9AltBit` under `coin9Weight` equals `2 ^ 9 - k.val`. -/
theorem mux9AltBit_fiber_true (k : Fin (2 ^ 9)) : (∑ c : Fin (2 ^ 4), if mux9AltBit c k = true
    then coin9Weight c else 0) = 2 ^ 9 - k.val := by
  change _ = 512 - k.val
  rw [← mux9_fiber_weight_true k, ← Equiv.sum_comp pktSwap56
    (fun c ↦ if mux9Bit c k = true then coin9Weight c else 0)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases hc1 : c = 1
  · subst hc1
    simp only [show pktSwap56 1 = 1 by decide, show coin9Weight 1 = 0 from rfl, ite_self]
  · rw [mux9AltBit_eqMux9Bit_swap hc1 k, coin9WeightPktSwap56 c]
/-- Rewrites `coin9Perm23 muxBit f` as `bitPermUnitary (core23PostGenPerm muxBit)` times the
`19`-wire QROM unitary `aliasTableXorUnitary 5 14 f`. -/
theorem coin9Perm23_eq (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (f : Fin (2 ^ 5) →
    BitAssignment 14) : coin9Perm23 muxBit f = bitPermUnitary (core23PostGenPerm muxBit) *
    core23Qrom19Reg.embedUnitary (aliasTableXorUnitary 5 14 f) := by
  rw [coin9Perm23, core23MuxSwap23Reg_eq, pktMuxSwap23Unitary_eqPktMuxSwapGenUnitary,
    core23MuxSwap23Reg_embedPktMuxSwapGen23Unitary]
/-! ## Layer 2: `core23` & `prepMid18FromSlice` Column-`0` `normSq` & Marginals -/
/-- Extracts the `5`-bit alternate index `alt` (`bits 0..4`) from a `14`-bit QROM row `f x`. -/
def altOf14 (f : Fin (2 ^ 5) → BitAssignment 14) (x : Fin (2 ^ 5)) : Fin (2 ^ 5) :=
  finOfBits 5 fun i ↦ decide (f x ⟨i.val, by omega⟩ = 1)
/-- Extracts the `9`-bit keep threshold `keep` (`bits 5..13`) from a `14`-bit QROM row `f x`. -/
def keepOf14 (f : Fin (2 ^ 5) → BitAssignment 14) (x : Fin (2 ^ 5)) : Fin (2 ^ 9) :=
  finOfBits 9 fun j ↦ decide (f x ⟨5 + j.val, by omega⟩ = 1)
/-- `core23IdxReg` (`0..4`) and `core23PktReg` (`19..22`) are wire-disjoint inside `Wire 23`. -/
theorem disjoint_core23IdxReg_core23PktReg : core23IdxReg.DisjointWires core23PktReg :=
  QRegister.disjoint_iff.mpr fun i _ hij ↦ by
    have hv := congrArg Fin.val hij
    have := i.isLt
    simp only [core23IdxReg, core23PktReg, QRegister.block_apply_val] at hv
    omega
/-- Involutive `19`-wire QROM bit-assignment permutation for `f : Fin (2 ^ 5) → BitAssignment 14`.
-/
def qrom19Perm (f : Fin (2 ^ 5) → BitAssignment 14) : Equiv.Perm (BitAssignment 19) :=
  ⟨aliasTableXorBits 5 14 f, aliasTableXorBits 5 14 f, aliasTableXorBits_self 5 14 f,
  aliasTableXorBits_self 5 14 f⟩
/-- Combined `23`-wire basis-index permutation for `coin9Perm23 muxBit f`. -/
noncomputable def coin9Equiv23 (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (f : Fin (2 ^ 5) → BitAssignment 14) : Equiv.Perm (Fin (2 ^ 23)) where
  toFun h := (basisBits 23).symm
    (core23PostGenBits muxBit (writePermHad core23Qrom19Reg (qrom19Perm f) (basisBits 23 h)))
  invFun g := (basisBits 23).symm
    (writePermHad core23Qrom19Reg (qrom19Perm f)
      (core23PostGenBits muxBit (basisBits 23 g)))
  left_inv h := by
    dsimp only
    rw [XMeasCircuit.basisBits_basisBitsEquiv_symm, core23PostGenBits_invol muxBit,
      show (qrom19Perm f : BitAssignment 19 → BitAssignment 19) = aliasTableXorBits 5 14 f
        from rfl,
      writePermHad_invol core23Qrom19Reg (aliasTableXorBits_self 5 14 f),
      XMeasCircuit.basisBitsEquiv_symm_basisBits]
  right_inv g := by
    dsimp only
    rw [XMeasCircuit.basisBits_basisBitsEquiv_symm,
      show (qrom19Perm f : BitAssignment 19 → BitAssignment 19) = aliasTableXorBits 5 14 f
        from rfl,
      writePermHad_invol core23Qrom19Reg (aliasTableXorBits_self 5 14 f),
      core23PostGenBits_invol muxBit, XMeasCircuit.basisBitsEquiv_symm_basisBits]
/-- Forward evaluation formula for `coin9Equiv23 muxBit f`. -/
theorem coin9Equiv23_apply (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (f : Fin (2 ^ 5) → BitAssignment 14) (h : Fin (2 ^ 23)) :
    coin9Equiv23 muxBit f h = (basisBits 23).symm
      (core23PostGenBits muxBit
        (writePermHad core23Qrom19Reg (qrom19Perm f) (basisBits 23 h))) := rfl
/-- Inverse evaluation formula for `(coin9Equiv23 muxBit f).symm`. -/
theorem coin9Equiv23_symm_apply (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (f : Fin (2 ^ 5) → BitAssignment 14) (g : Fin (2 ^ 23)) :
    (coin9Equiv23 muxBit f).symm g = (basisBits 23).symm
      (writePermHad core23Qrom19Reg (qrom19Perm f)
        (core23PostGenBits muxBit (basisBits 23 g))) := rfl
attribute [irreducible] coin9Equiv23
/-- `(coin9Equiv23 muxBit f).symm` preserves `core23PktReg.extractIndex`. -/
@[simp] theorem coin9Equiv23_symm_extract_pkt (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (f :
    Fin (2 ^ 5) → BitAssignment 14) (g : Fin (2 ^ 23)) : core23PktReg.extractIndex ((coin9Equiv23
    muxBit f).symm g) = core23PktReg.extractIndex g := by
  apply (basisBits 4).injective
  funext i
  rw [core23PktReg.basisBits_extractIndex, core23PktReg.basisBits_extractIndex,
    coin9Equiv23_symm_apply, XMeasCircuit.basisBits_basisBitsEquiv_symm]
  have hnm : core23PktReg i ∉ Set.range core23Qrom19Reg.wires := by
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    have := k.isLt
    simp only [core23Qrom19Reg, core23PktReg, QRegister.block_apply_val] at hv
    omega
  dsimp only [writePermHad]
  rw [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnm]
  dsimp only [core23PostGenBits]
  have hi := i.isLt
  have h1 : ¬ ((core23PktReg i).val < 5) := by
    simp [core23PktReg]
    omega
  have h2 : ¬ ((core23PktReg i).val < 10) := by
    simp [core23PktReg]
    omega
  simp only [h1, h2, ↓reduceDIte]
/-- Closed-form column-`0` entry of `core23 muxBit sliceFn uIdx rc` via `coin9Equiv23`. -/
theorem core23_col0_apply (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14)
    (uIdx : Unitary (2 ^ 5)) (rc : Fin (2 ^ 7)) (g : Fin (2 ^ 23)) :
    let h := (coin9Equiv23 muxBit (sliceFn rc)).symm g
    (core23 muxBit sliceFn uIdx rc).1 g 0 =
      if core23IdxReg.replaceIndex (core23PktReg.replaceIndex h 0) 0 = 0 then
        optCoin9Unitary.1 (core23PktReg.extractIndex h) 0 *
          uIdx.1 (core23IdxReg.extractIndex h) 0
      else 0 := by
  let f := sliceFn rc
  have hWh (δ : BitAssignment 23) :
      writePermHad (QRegister.whole 23) (core23PostGenPerm muxBit) δ =
        core23PostGenBits muxBit δ :=
    funext fun u ↦ CoherentAlias.writeReg_apply_reg δ (QRegister.whole 23) _ u
  dsimp only
  rw [core23, coin9Perm23_eq,
    ← QRegister.whole_embedUnitary (bitPermUnitary (core23PostGenPerm muxBit)),
    show aliasTableXorUnitary 5 14 f = bitPermUnitary (qrom19Perm f) from rfl,
    embedBitPerm2_mul_col0_applyHad (QRegister.whole 23) core23Qrom19Reg
      (core23PostGenPerm muxBit) (qrom19Perm f)
      (core23PostGenBits_invol muxBit) (aliasTableXorBits_self 5 14 f),
    hWh (basisBits 23 g), (coin9Equiv23_symm_apply muxBit f g).symm,
    mul_embedUnitary_col0_applyHad core23PktReg core23IdxReg
      disjoint_core23IdxReg_core23PktReg.symm]
/-- Embeds `(x : Fin (2 ^ 5), c : Fin (2 ^ 4))` into `Fin (2 ^ 23)` with `0` on wires `5..18`. -/
noncomputable def embIdxPkt23 (x : Fin (2 ^ 5)) (c : Fin (2 ^ 4)) : Fin (2 ^ 23) :=
  core23PktReg.replaceIndex (core23IdxReg.replaceIndex 0 x) c
/-- `core23IdxReg.extractIndex` recovers `x` from `embIdxPkt23 x c`. -/
@[simp] theorem embIdxPkt23_extract_idx (x : Fin (2 ^ 5)) (c : Fin (2 ^ 4)) :
    core23IdxReg.extractIndex (embIdxPkt23 x c) = x := by
  dsimp only [embIdxPkt23]
  rw [core23IdxReg.extractIndex_replaceIndex_of_disjoint core23PktReg
    disjoint_core23IdxReg_core23PktReg, core23IdxReg.extractIndex_replaceIndex]
/-- `core23PktReg.extractIndex` recovers `c` from `embIdxPkt23 x c`. -/
@[simp] theorem embIdxPkt23_extract_pkt (x : Fin (2 ^ 5)) (c : Fin (2 ^ 4)) :
  core23PktReg.extractIndex (embIdxPkt23 x c) = c := core23PktReg.extractIndex_replaceIndex _ c
/-- Uncurried `embIdxPkt23` is injective on `Fin (2 ^ 5) × Fin (2 ^ 4)`. -/
theorem embIdxPkt23_injective : Function.Injective (fun p : Fin (2 ^ 5) × Fin (2 ^ 4) ↦ embIdxPkt23
    p.1 p.2) := by
  intro p q hpq
  have h1 := congrArg core23IdxReg.extractIndex hpq
  have h2 := congrArg core23PktReg.extractIndex hpq
  rw [embIdxPkt23_extract_idx, embIdxPkt23_extract_idx] at h1
  rw [embIdxPkt23_extract_pkt, embIdxPkt23_extract_pkt] at h2
  exact Prod.ext h1 h2
/-- Clearing `core23PktReg` and `core23IdxReg` on `embIdxPkt23 x c` yields `0`. -/
@[simp] theorem embIdxPkt23_replace_zero (x : Fin (2 ^ 5)) (c : Fin (2 ^ 4)) :
    core23IdxReg.replaceIndex (core23PktReg.replaceIndex (embIdxPkt23 x c) 0) 0 = 0 := by
  apply (basisBits 23).injective
  funext q
  rw [CoherentAlias.basisBits_zero_apply]
  by_cases h1 : q ∈ Set.range core23IdxReg.wires
  · obtain ⟨i, rfl⟩ := h1
    rw [core23IdxReg.basisBits_replaceIndex_apply, CoherentAlias.basisBits_zero_apply]
  · rw [core23IdxReg.basisBits_replaceIndex_of_not_mem _ _ _ h1]
    by_cases h2 : q ∈ Set.range core23PktReg.wires
    · obtain ⟨j, rfl⟩ := h2
      rw [core23PktReg.basisBits_replaceIndex_apply, CoherentAlias.basisBits_zero_apply]
    · dsimp only [embIdxPkt23]
      rw [core23PktReg.basisBits_replaceIndex_of_not_mem _ _ _ h2,
        core23PktReg.basisBits_replaceIndex_of_not_mem _ _ _ h2,
        core23IdxReg.basisBits_replaceIndex_of_not_mem _ _ _ h1,
        CoherentAlias.basisBits_zero_apply]
/-- Any `h : Fin (2 ^ 23)` vanishing outside `core23IdxReg` and `core23PktReg` is `embIdxPkt23`. -/
theorem eq_embIdxPkt23_of_replace_zero {h : Fin (2 ^ 23)} (h0 : core23IdxReg.replaceIndex
    (core23PktReg.replaceIndex h 0) 0 = 0) : h = embIdxPkt23 (core23IdxReg.extractIndex h)
    (core23PktReg.extractIndex h) := by
  apply (basisBits 23).injective
  funext q
  dsimp only [embIdxPkt23]
  by_cases h2 : q ∈ Set.range core23PktReg.wires
  · obtain ⟨j, rfl⟩ := h2
    rw [core23PktReg.basisBits_replaceIndex_apply, core23PktReg.basisBits_extractIndex]
  · rw [core23PktReg.basisBits_replaceIndex_of_not_mem _ _ _ h2]
    by_cases h1 : q ∈ Set.range core23IdxReg.wires
    · obtain ⟨i, rfl⟩ := h1
      rw [core23IdxReg.basisBits_replaceIndex_apply, core23IdxReg.basisBits_extractIndex]
    · rw [core23IdxReg.basisBits_replaceIndex_of_not_mem _ _ _ h1,
        CoherentAlias.basisBits_zero_apply]
      have hq := congrArg (fun z ↦ basisBits 23 z q) h0
      rwa [core23IdxReg.basisBits_replaceIndex_of_not_mem _ _ _ h1,
        core23PktReg.basisBits_replaceIndex_of_not_mem _ _ _ h2,
        CoherentAlias.basisBits_zero_apply] at hq
/-- Walker-alias output index of `coin9Equiv23 muxBit f` on `embIdxPkt23 x c`. -/
theorem coin9Equiv23_embIdxPkt23_extract_idx (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (f : Fin
    (2 ^ 5) → BitAssignment 14) (x : Fin (2 ^ 5)) (c : Fin (2 ^ 4)) : core23IdxReg.extractIndex
    (coin9Equiv23 muxBit f (embIdxPkt23 x c)) = if muxBit c (keepOf14 f x) then altOf14 f x
    else x := by
  let β₀ := basisBits 23 (embIdxPkt23 x c)
  have hβIdx (i : Fin 5) : β₀ ⟨i.val, by omega⟩ = basisBits 5 x i := by
    have hnm : core23IdxReg i ∉ Set.range core23PktReg.wires := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have := i.isLt
      simp only [core23IdxReg, core23PktReg, QRegister.block_apply_val] at hv
      omega
    have hw : (⟨i.val, by omega⟩ : Wire 23) = core23IdxReg i := Fin.ext (by simp [core23IdxReg])
    dsimp only [β₀, embIdxPkt23]
    rw [hw, core23PktReg.basisBits_replaceIndex_of_not_mem _ _ _ hnm,
      core23IdxReg.basisBits_replaceIndex_apply]
  have hβMid (k : Fin 14) : β₀ ⟨5 + k.val, by omega⟩ = 0 := by
    have hnmP : (⟨5 + k.val, by omega⟩ : Wire 23) ∉ Set.range core23PktReg.wires := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have := k.isLt
      simp only [core23PktReg, QRegister.block_apply_val] at hv
      omega
    have hnmI : (⟨5 + k.val, by omega⟩ : Wire 23) ∉ Set.range core23IdxReg.wires := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      have := i.isLt
      simp only [core23IdxReg, QRegister.block_apply_val] at hv
      omega
    dsimp only [β₀, embIdxPkt23]
    rw [core23PktReg.basisBits_replaceIndex_of_not_mem _ _ _ hnmP,
      core23IdxReg.basisBits_replaceIndex_of_not_mem _ _ _ hnmI, CoherentAlias.basisBits_zero_apply]
  have hβPkt (i : Fin 4) : β₀ ⟨19 + i.val, by omega⟩ = basisBits 4 c i := by
    have hw : (⟨19 + i.val, by omega⟩ : Wire 23) = core23PktReg i :=
      Fin.ext (by simp [core23PktReg])
    dsimp only [β₀, embIdxPkt23]
    rw [hw, core23PktReg.basisBits_replaceIndex_apply]
  let γ := writePermHad core23Qrom19Reg (qrom19Perm f) β₀
  have hAddr : (basisBits 5).symm
      (fun i : Fin 5 ↦ β₀ (core23Qrom19Reg.wires ⟨i.val, by omega⟩)) = x := by
    have hb : (fun i : Fin 5 ↦ β₀ (core23Qrom19Reg.wires ⟨i.val, by omega⟩)) = basisBits 5 x :=
      funext fun i ↦ by
        rw [show core23Qrom19Reg.wires ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ from
          Fin.ext (by simp [core23Qrom19Reg]), hβIdx i]
    rw [hb, XMeasCircuit.basisBitsEquiv_symm_basisBits]
  have hγIdx (i : Fin 5) : γ ⟨i.val, by omega⟩ = basisBits 5 x i := by
    have hw : (⟨i.val, by omega⟩ : Wire 23) = core23Qrom19Reg ⟨i.val, by omega⟩ :=
      Fin.ext (by simp [core23Qrom19Reg])
    dsimp only [γ, writePermHad]
    rw [hw, CoherentAlias.writeReg_apply_reg]
    dsimp only [qrom19Perm, Equiv.coe_fn_mk, aliasTableXorBits]
    simp only [show ¬ (5 ≤ i.val) by omega, ↓reduceDIte]
    rw [show core23Qrom19Reg.wires ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ from
      Fin.ext (by simp [core23Qrom19Reg]), hβIdx i]
  have hγOut (k : Fin 14) : γ ⟨5 + k.val, by omega⟩ = f x k := by
    have hw : (⟨5 + k.val, by omega⟩ : Wire 23) = core23Qrom19Reg ⟨5 + k.val, by omega⟩ :=
      Fin.ext (by simp [core23Qrom19Reg])
    dsimp only [γ, writePermHad]
    rw [hw, CoherentAlias.writeReg_apply_reg]
    dsimp only [qrom19Perm, Equiv.coe_fn_mk, aliasTableXorBits]
    simp only [show 5 ≤ 5 + k.val by omega, ↓reduceDIte, hAddr,
      show core23Qrom19Reg.wires ⟨5 + k.val, by omega⟩ = ⟨5 + k.val, by omega⟩ from
        Fin.ext (by simp [core23Qrom19Reg]),
      hβMid k, zero_add]
    exact congrArg (f x) (Fin.ext (by
      dsimp
      omega))
  have hPkt : finOfBits 4 (fun i ↦ decide (γ ⟨19 + i.val, by omega⟩ = 1)) = c := by
    have hb : (fun i : Fin 4 ↦ decide (γ ⟨19 + i.val, by omega⟩ = 1)) = bitsOfFin 4 c :=
      funext fun i ↦ by
        have hnm : (⟨19 + i.val, by omega⟩ : Wire 23) ∉ Set.range core23Qrom19Reg.wires := by
          rintro ⟨u, hu⟩
          have hv := congrArg Fin.val hu
          have := u.isLt
          simp only [core23Qrom19Reg, QRegister.block_apply_val] at hv
          omega
        have hγP : γ ⟨19 + i.val, by omega⟩ = basisBits 4 c i := by
          dsimp only [γ, writePermHad]
          rw [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnm, hβPkt i]
        dsimp only [bitsOfFin]
        exact congrArg (fun z ↦ decide (z = 1)) hγP
    rw [hb, finOfBits_bitsOfFin]
  have hKeep : finOfBits 9 (fun j ↦ decide (γ ⟨10 + j.val, by omega⟩ = 1)) = keepOf14 f x := by
    dsimp only [keepOf14]
    refine congrArg (finOfBits 9) (funext fun j ↦ ?_)
    have heq : (⟨10 + j.val, by omega⟩ : Wire 23) = ⟨5 + (⟨5 + j.val, by omega⟩ : Fin 14).val,
        by omega⟩ := Fin.ext (by
          dsimp
          omega)
    rw [heq, hγOut ⟨5 + j.val, by omega⟩]
  rw [← finOfBits_bitsOfFin 5 (core23IdxReg.extractIndex _)]
  have hBits (i : Fin 5) :
      bitsOfFin 5 (core23IdxReg.extractIndex (coin9Equiv23 muxBit f (embIdxPkt23 x c))) i =
        if muxBit c (keepOf14 f x) then decide (f x ⟨i.val, by omega⟩ = 1)
        else bitsOfFin 5 x i := by
    have hBitZ :
        basisBits 5 (core23IdxReg.extractIndex (coin9Equiv23 muxBit f (embIdxPkt23 x c))) i =
          if muxBit c (keepOf14 f x) then f x ⟨i.val, by omega⟩ else basisBits 5 x i := by
      rw [coin9Equiv23_apply, core23IdxReg.basisBits_extractIndex,
        XMeasCircuit.basisBits_basisBitsEquiv_symm,
        show core23IdxReg i = ⟨i.val, by omega⟩ from Fin.ext (by simp [core23IdxReg])]
      change core23PostGenBits muxBit γ ⟨i.val, by omega⟩ = _
      dsimp only [core23PostGenBits]
      rw [hPkt, hKeep]
      simp only [i.isLt, ↓reduceDIte]
      cases muxBit c (keepOf14 f x)
      · simp only [Bool.false_eq_true, ↓reduceIte, hγIdx i]
      · simp only [↓reduceIte, hγOut ⟨i.val, by omega⟩]
    have heq := congrArg (fun z ↦ decide (z = 1)) hBitZ
    dsimp only [bitsOfFin]
    rw [heq]
    cases muxBit c (keepOf14 f x) <;> rfl
  rw [show bitsOfFin 5 (core23IdxReg.extractIndex (coin9Equiv23 muxBit f (embIdxPkt23 x c))) = _
    from funext hBits]
  cases muxBit c (keepOf14 f x)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact finOfBits_bitsOfFin 5 x
  · simp only [↓reduceIte]
    rfl
/-- Closed-form Walker-alias `idx` marginal of `core23 muxBit sliceFn uIdx rc` for any `muxBit`
with `false`/`true` fiber weights `k.val` and `2 ^ 9 - k.val`. -/
theorem core23_idx_marginal {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool} (hfF : ∀ k : Fin (2 ^ 9),
    (∑ c : Fin (2 ^ 4), if muxBit c k = false then coin9Weight c else 0) = k.val) (hfT : ∀ k :
    Fin (2 ^ 9), (∑ c : Fin (2 ^ 4), if muxBit c k = true then coin9Weight c else 0) = 2 ^ 9 -
    k.val) (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (uIdx : Unitary (2 ^ 5)) (rc :
    Fin (2 ^ 7)) (b : Fin (2 ^ 5)) : (∑ g : Fin (2 ^ 23), if core23IdxReg.extractIndex g = b then
    Complex.normSq ((core23 muxBit sliceFn uIdx rc).1 g 0) else 0) = ∑ x : Fin (2 ^ 5),
    Complex.normSq (uIdx.1 x 0) * (((if x = b then (keepOf14 (sliceFn rc) x).val else 0) + (if
    altOf14 (sliceFn rc) x = b then 2 ^ 9 - (keepOf14 (sliceFn rc) x).val else 0) : ℕ) : ℝ) /
    512 := by
  let f := sliceFn rc
  let σ := coin9Equiv23 muxBit f
  let embEmb : Fin (2 ^ 5) × Fin (2 ^ 4) ↪ Fin (2 ^ 23) :=
    ⟨fun p ↦ embIdxPkt23 p.1 p.2, embIdxPkt23_injective⟩
  rw [← Equiv.sum_comp σ (fun g ↦ if core23IdxReg.extractIndex g = b then
    Complex.normSq ((core23 muxBit sliceFn uIdx rc).1 g 0) else 0),
    ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map embEmb))]
  · rw [Finset.sum_map, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    let k := keepOf14 f x
    let a := altOf14 f x
    let p := Complex.normSq (uIdx.1 x 0)
    have hTerm (c : Fin (2 ^ 4)) :
        (if core23IdxReg.extractIndex (σ (embEmb (x, c))) = b then
          Complex.normSq ((core23 muxBit sliceFn uIdx rc).1 (σ (embEmb (x, c))) 0) else 0) =
          (p / 512) * (((if x = b then if muxBit c k = false then coin9Weight c else 0 else 0) +
            (if a = b then if muxBit c k = true then coin9Weight c else 0 else 0) : ℕ) : ℝ) := by
      change (if core23IdxReg.extractIndex (σ (embIdxPkt23 x c)) = b then
        Complex.normSq ((core23 muxBit sliceFn uIdx rc).1 (σ (embIdxPkt23 x c)) 0) else 0) = _
      rw [coin9Equiv23_embIdxPkt23_extract_idx, core23_col0_apply,
        show (coin9Equiv23 muxBit (sliceFn rc)).symm (σ (embIdxPkt23 x c)) = embIdxPkt23 x c
          from σ.symm_apply_apply _,
        embIdxPkt23_replace_zero, embIdxPkt23_extract_pkt, embIdxPkt23_extract_idx]
      simp only [↓reduceIte, map_mul, optCoin9Unitary_col_zero_normSq]
      change (if (if muxBit c k then a else x) = b then
        ((coin9Weight c : ℝ) / 512) * p else 0) = _
      cases muxBit c k
      · by_cases hxb : x = b
        · simp [hxb]
          ring
        · simp [hxb]
      · by_cases hab : a = b
        · simp [hab]
          ring
        · simp [hab]
    simp_rw [hTerm, ← Finset.mul_sum, ← Nat.cast_sum, Finset.sum_add_distrib]
    have hSumF : (∑ c : Fin (2 ^ 4),
        if x = b then if muxBit c k = false then coin9Weight c else 0 else 0) =
        if x = b then k.val else 0 := by by_cases hxb : x = b <;> simp [hxb, hfF k]
    have hSumT : (∑ c : Fin (2 ^ 4),
        if a = b then if muxBit c k = true then coin9Weight c else 0 else 0) =
        if a = b then 2 ^ 9 - k.val else 0 := by by_cases hab : a = b <;> simp [hab, hfT k]
    rw [hSumF, hSumT]
    ring
  · intro h _ hnm
    rw [core23_col0_apply,
      show (coin9Equiv23 muxBit (sliceFn rc)).symm (σ h) = h from σ.symm_apply_apply h]
    have hne : core23IdxReg.replaceIndex (core23PktReg.replaceIndex h 0) 0 ≠ 0 := fun h0 ↦
      hnm (Finset.mem_map.mpr ⟨(core23IdxReg.extractIndex h, core23PktReg.extractIndex h),
        Finset.mem_univ _, (eq_embIdxPkt23_of_replace_zero h0).symm⟩)
    simp only [hne, ↓reduceIte, map_zero, ite_self]
/-- Column-`0` Euclidean norm-squared sum of any unitary `U : Unitary d` equals `1`. -/
theorem unitary_col0_norm_sq_sum {d : ℕ} [NeZero d] (U : Unitary d) : (∑ g : Fin d, ‖(U.1 *ᵥ
    basisState 0) g‖ ^ 2) = 1 := by
  have hgv (g : Fin d) : (U.1 *ᵥ basisState 0) g = U.1 g 0 := by
    rw [show (basisState 0 : Fin d → ℂ) = Pi.single 0 1 from rfl,
      Matrix.mulVec_single_one, Matrix.col_apply]
  simp_rw [hgv, ← Complex.normSq_eq_norm_sq]
  have hunit : (U.1ᴴ * U.1) 0 0 = 1 := by
    have hu : U.1ᴴ * U.1 = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using (SetLike.coe_mem U).1
    rw [hu]
    rfl
  have hsum_re : ((U.1ᴴ * U.1) 0 0).re = ∑ g : Fin d, Complex.normSq (U.1 g 0) := by
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [Matrix.conjTranspose_apply]
    simp [Complex.normSq_apply]
  have h1 : ((U.1ᴴ * U.1) 0 0).re = 1 := by
    rw [hunit]
    rfl
  exact hsum_re.symm.trans h1
/-- Exact `1 / 2` spin marginal on all `128` `rc` slices (including `126, 127`) for any `muxBit`,
`sliceFn`, and `uIdx`. -/
theorem prepMid18FromSlice_spin_marginal_half (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (uIdx : Unitary (2 ^ 5)) (rc : Fin (2
    ^ 7)) (si : Fin 2) : (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB 18) ↦ (rSigInLoc
    18).extractIndex m = si), Complex.normSq ((prepMid18FromSlice muxBit sliceFn uIdx rc).1 m 0))
    = 1 / 2 := by
  rw [prepMid18FromSlice, show mid18Core23Reg = QRegister.block 0 23 (by decide) from rfl]
  generalize core23 muxBit sliceFn uIdx rc = U
  let r0 : QRegister 0 23 := QRegister.block 0 0 (by decide)
  let r0Ext : QRegister 0 (mMidUB 18) := QRegister.block 0 0 (by decide)
  obtain ⟨_, hsum⟩ := prepPlusHadamard_vanish_and_sum (m := 23) (d := 0) U r0 r0Ext (by
    ext i
    exact Fin.elim0 i)
  have h1 := hsum 0 si
  have hfilt : Finset.univ.filter (fun m : Fin (2 ^ mMidUB 18) ↦
      (r0Ext.extractIndex m).val = (0 : Fin 1).val ∧
        (QRegister.block 23 1 (by decide)).extractIndex m = si) =
      Finset.univ.filter (fun m : Fin (2 ^ mMidUB 18) ↦ (rSigInLoc 18).extractIndex m = si) := by
    ext m
    have hz : (r0Ext.extractIndex m).val = 0 := by omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hz, Fin.val_zero, rSigInLoc]
  rw [hfilt] at h1
  change _ = (1 / 2 : ℝ)
  rw [show rSigInLoc 18 = QRegister.block 23 1 (by decide) from rfl, h1]
  have hall (g : Fin (2 ^ 23)) : r0.extractIndex g = 0 :=
    Fin.ext (by
      have := (r0.extractIndex g).isLt
      omega)
  simp only [hall, ↓reduceIte, unitary_col0_norm_sq_sum U]
  ring
/-- Closed-form joint `(b, si)` marginal of `prepMid18FromSlice` for any `muxBit` with fiber
weights `k.val` and `2 ^ 9 - k.val`. -/
theorem prepMid18FromSlice_joint_marginal {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool} (hfF : ∀ k
    : Fin (2 ^ 9), (∑ c : Fin (2 ^ 4), if muxBit c k = false then coin9Weight c else 0) = k.val)
    (hfT : ∀ k : Fin (2 ^ 9), (∑ c : Fin (2 ^ 4), if muxBit c k = true then coin9Weight c else 0)
    = 2 ^ 9 - k.val) (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (uIdx : Unitary (2 ^
    5)) (rc : Fin (2 ^ 7)) (b : Fin (2 ^ 5)) (si : Fin 2) : (∑ m ∈ Finset.univ.filter (fun m : Fin
    (2 ^ mMidUB 18) ↦ ((rBLoc 18).extractIndex m).val = b.val ∧ (rSigInLoc 18).extractIndex m =
    si), Complex.normSq ((prepMid18FromSlice muxBit sliceFn uIdx rc).1 m 0)) = (1 / 2) * ∑ x :
    Fin (2 ^ 5), Complex.normSq (uIdx.1 x 0) * (((if x = b then (keepOf14 (sliceFn rc) x).val
    else 0) + (if altOf14 (sliceFn rc) x = b then 2 ^ 9 - (keepOf14 (sliceFn rc) x).val else 0)
    : ℕ) : ℝ) / 512 := by
  obtain ⟨_, hsum⟩ := prepPlusHadamard_vanish_and_sum (m := 23) (d := 5)
    (core23 muxBit sliceFn uIdx rc) core23IdxReg (rBLoc 18) (by
      ext i
      simp [core23IdxReg, rBLoc])
  have hm := hsum b si
  have hgv (g : Fin (2 ^ 23)) :
      ‖((core23 muxBit sliceFn uIdx rc).1 *ᵥ basisState 0) g‖ ^ 2 =
        Complex.normSq ((core23 muxBit sliceFn uIdx rc).1 g 0) := by
    rw [show (basisState 0 : Fin (2 ^ 23) → ℂ) = Pi.single 0 1 from rfl,
      Matrix.mulVec_single_one, Matrix.col_apply, ← Complex.normSq_eq_norm_sq]
  simp_rw [hgv] at hm
  rw [prepMid18FromSlice, show rSigInLoc 18 = QRegister.block 23 1 (by decide) from rfl,
    show mid18Core23Reg = QRegister.block 0 23 (by decide) from rfl, hm,
    core23_idx_marginal hfF hfT sliceFn uIdx rc b]
/-! ## Layer 3: `keep9SliceTargetFn14` `b < 30` Active-Column Support Across All `128` Slices -/
/-- `finOfBits k b = z` whenever `b i = z.val.testBit i.val` for every `i : Fin k`. -/
theorem finOfBits_eq_of_testBit (k : ℕ) (b : Fin k → Bool) (z : Fin (2 ^ k)) (h : ∀ i : Fin k, b i
    = z.val.testBit i.val) : finOfBits k b = z := by
  have hb : b = bitsOfFin k z := funext fun i ↦ by
    dsimp only [bitsOfFin]
    rw [basisBits_eq_testBit, h i]
    cases z.val.testBit i.val <;> decide
  rw [hb, finOfBits_bitsOfFin]
/-- `decide (keep9SliceTargetFn14 rc x k = 1)` equals `keep9Hot24BoolTable rc x k`. -/
theorem decideKeep9SliceTargetFn14_eq_one (rc : Fin (2 ^ 7)) (x : Fin (2 ^ 5)) (k : Fin 14) :
    decide (keep9SliceTargetFn14 rc x k = 1) = keep9Hot24BoolTable rc x k := by
  have hk : keep9SliceTargetFn14 rc x k = if keep9Hot24BoolTable rc x k then 1 else 0 := rfl
  exact (congrArg (fun z : ZMod 2 ↦ decide (z = 1)) hk).trans
    (by cases keep9Hot24BoolTable rc x k <;> decide)
/-- On `rc.val < 126` and `x.val < 30`, `altOf14 (keep9SliceTargetFn14 rc) x` unpacks `alt`. -/
theorem altOf14Keep9_of_lt {rc : Fin (2 ^ 7)} {x : Fin (2 ^ 5)} (hc : rc.val < 126)
    (hx : x.val < 30) :
    altOf14 (keep9SliceTargetFn14 rc) x =
      ⟨((keep9InnerAliasTable ⟨rc.val, hc⟩ ⟨x.val, hx⟩).alt).val, by
        have := ((keep9InnerAliasTable ⟨rc.val, hc⟩ ⟨x.val, hx⟩).alt).isLt
        omega⟩ := by
  apply finOfBits_eq_of_testBit 5 _ _ fun i ↦ ?_
  rw [decideKeep9SliceTargetFn14_eq_one, keep9Hot24BoolTable_of_lt hc hx ⟨i.val, by omega⟩]
  dsimp only [keep9InnerAliasBits]
  simp only [i.isLt, ↓reduceIte]
/-- On `rc.val < 126` and `x.val < 30`, `keepOf14 (keep9SliceTargetFn14 rc) x` unpacks `keep`.
-/
theorem keepOf14Keep9_of_lt {rc : Fin (2 ^ 7)} {x : Fin (2 ^ 5)} (hc : rc.val < 126) (hx :
    x.val < 30) : keepOf14 (keep9SliceTargetFn14 rc) x = ⟨(keep9InnerAliasTable ⟨rc.val, hc⟩
    ⟨x.val, hx⟩).keep, keep9InnerAliasTable_keep_lt ⟨rc.val, hc⟩ ⟨x.val, hx⟩⟩ := by
  apply finOfBits_eq_of_testBit 9 _ _ fun j ↦ ?_
  rw [decideKeep9SliceTargetFn14_eq_one, keep9Hot24BoolTable_of_lt hc hx ⟨5 + j.val, by omega⟩]
  dsimp only [keep9InnerAliasBits]
  simp only [show ¬ (5 + j.val < 5) by omega, ↓reduceIte,
    show 5 + j.val - 5 = j.val by omega]
/-- On padding slices `126 ≤ rc.val`, `altOf14 (keep9SliceTargetFn14 rc) x = 0`. -/
theorem altOf14Keep9_of_ge {rc : Fin (2 ^ 7)} (hc : 126 ≤ rc.val) (x : Fin (2 ^ 5)) :
    altOf14 (keep9SliceTargetFn14 rc) x = 0 := by
  apply finOfBits_eq_of_testBit 5 _ 0 fun i ↦ ?_
  rw [decideKeep9SliceTargetFn14_eq_one, keep9Hot24BoolTable_of_ge hc x ⟨i.val, by omega⟩,
    Fin.val_zero, Nat.zero_testBit]
/-- Column-`0` amplitudes of `prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc` vanish
wherever `30 ≤ ((rBLoc 18).extractIndex m).val` across all `128` slices (`rc : Fin (2 ^ 7)`). -/
theorem prepMid18FromSliceKeep9_vanish {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool} (hfF : ∀ k
    : Fin (2 ^ 9), (∑ c : Fin (2 ^ 4), if muxBit c k = false then coin9Weight c else 0) = k.val)
    (hfT : ∀ k : Fin (2 ^ 9), (∑ c : Fin (2 ^ 4), if muxBit c k = true then coin9Weight c else 0)
    = 2 ^ 9 - k.val) {uIdx : Unitary (2 ^ 5)} (huVanish : ∀ x : Fin (2 ^ 5), 30 ≤ x.val → (uIdx.1
    *ᵥ basisState 0) x = 0) (rc : Fin (2 ^ 7)) (m : Fin (2 ^ mMidUB 18)) (hm : 30 ≤ ((rBLoc
    18).extractIndex m).val) : (prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc).1 m 0 =
    0 := by
  obtain ⟨hvan, _⟩ := prepPlusHadamard_vanish_and_sum (m := 23) (d := 5)
    (core23 muxBit keep9SliceTargetFn14 uIdx rc) core23IdxReg (rBLoc 18) (by
      ext i
      simp [core23IdxReg, rBLoc])
  let i₀ := (rBLoc 18).extractIndex m
  have hgv (g : Fin (2 ^ 23)) :
      ‖((core23 muxBit keep9SliceTargetFn14 uIdx rc).1 *ᵥ basisState 0) g‖ ^ 2 =
        Complex.normSq ((core23 muxBit keep9SliceTargetFn14 uIdx rc).1 g 0) := by
    rw [show (basisState 0 : Fin (2 ^ 23) → ℂ) = Pi.single 0 1 from rfl,
      Matrix.mulVec_single_one, Matrix.col_apply, ← Complex.normSq_eq_norm_sq]
  have h0 : (∑ g : Fin (2 ^ 23), if core23IdxReg.extractIndex g = i₀ then
      ‖((core23 muxBit keep9SliceTargetFn14 uIdx rc).1 *ᵥ basisState 0) g‖ ^ 2 else 0) = 0 := by
    simp_rw [hgv]
    rw [core23_idx_marginal hfF hfT keep9SliceTargetFn14 uIdx rc i₀]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_cases hx : x.val < 30
    · have hxb : x ≠ i₀ := fun h ↦ by
        have := congrArg Fin.val h
        dsimp [i₀] at this
        omega
      have hab : altOf14 (keep9SliceTargetFn14 rc) x ≠ i₀ := by
        by_cases hrc : rc.val < 126
        · rw [altOf14Keep9_of_lt hrc hx]
          intro h
          have hv := congrArg Fin.val h
          have hlt := ((keep9InnerAliasTable ⟨rc.val, hrc⟩ ⟨x.val, hx⟩).alt).isLt
          dsimp [i₀] at hv
          omega
        · rw [altOf14Keep9_of_ge (by omega) x]
          intro h
          have hv := congrArg Fin.val h
          dsimp [i₀] at hv
          omega
      simp [hxb, hab]
    · have hux : uIdx.1 x 0 = 0 := by
        simpa [basisState, Matrix.mulVec_single_one, Matrix.col_apply] using
          huVanish x (by omega)
      simp [hux]
  have hvan' := hvan m i₀ rfl h0
  rwa [prepMid18FromSlice, show rSigInLoc 18 = QRegister.block 23 1 (by decide) from rfl,
    show mid18Core23Reg = QRegister.block 0 23 (by decide) from rfl]
/-! ## Layer 4: `QuantizedFactoredMag30.PrepMidQuant128`, Splitters (`56`/`66`/`72`/`T72`) & SOS
-/
/-- Quantized `126 × 30` inner distribution induced by `uIdx : Unitary (2 ^ 5)` through
`keep9InnerAliasTable`. -/
noncomputable def keep9QuantInnerProb (uIdx : Unitary (2 ^ 5)) (rc : Fin 126) (b : Fin 30) : ℝ :=
  ∑ x : Fin 30, Complex.normSq ((uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) *
    ((((if x = b then (keep9InnerAliasTable rc x).keep else 0) +
        (if (keep9InnerAliasTable rc x).alt = b then
          2 ^ 9 - (keep9InnerAliasTable rc x).keep else 0) : ℕ) : ℝ) / 512)
/-- `keep9QuantInnerProb uIdx rc b` is pointwise non-negative. -/
theorem keep9QuantInnerProb_nonneg (uIdx : Unitary (2 ^ 5)) (rc : Fin 126) (b : Fin 30) : 0 ≤
    keep9QuantInnerProb uIdx rc b :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Complex.normSq_nonneg _) (by positivity)
/-- `keep9QuantInnerProb uIdx rc` sums to `1` whenever `uIdx` vanishes on `30 ≤ x.val`. -/
theorem keep9QuantInnerProb_sum_eq_one {uIdx : Unitary (2 ^ 5)} (huVanish : ∀ x : Fin (2 ^ 5), 30
    ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0) (rc : Fin 126) : (∑ b : Fin 30, keep9QuantInnerProb
    uIdx rc b) = 1 := by
  dsimp only [keep9QuantInnerProb]
  rw [Finset.sum_comm]
  have hrow (x : Fin 30) :
      (∑ b : Fin 30, Complex.normSq ((uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) *
        ((((if x = b then (keep9InnerAliasTable rc x).keep else 0) +
            (if (keep9InnerAliasTable rc x).alt = b then
              2 ^ 9 - (keep9InnerAliasTable rc x).keep else 0) : ℕ) : ℝ) / 512)) =
      Complex.normSq ((uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) := by
    rw [← Finset.mul_sum, ← Finset.sum_div, ← Nat.cast_sum, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    have h512 : (keep9InnerAliasTable rc x).keep +
        (2 ^ 9 - (keep9InnerAliasTable rc x).keep) = 512 := by
      have := keep9InnerAliasTable_keep_lt rc x
      omega
    rw [h512]
    ring
  simp_rw [hrow]
  let emb30 : Fin 30 ↪ Fin (2 ^ 5) :=
    ⟨fun x ↦ ⟨x.val, by omega⟩, fun a b h ↦ Fin.ext (Fin.mk.inj h)⟩
  have hsum32 : (∑ x : Fin 30, Complex.normSq ((uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩)) =
      ∑ y : Fin (2 ^ 5), ‖(uIdx.1 *ᵥ basisState 0) y‖ ^ 2 := by
    simp_rw [← Complex.normSq_eq_norm_sq]
    refine (Finset.sum_map Finset.univ emb30
      (fun y ↦ Complex.normSq ((uIdx.1 *ᵥ basisState 0) y))).symm.trans ?_
    refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy ↦ ?_
    have hge : 30 ≤ y.val := by
      by_contra hlt
      exact hy (Finset.mem_map.mpr ⟨⟨y.val, Nat.lt_of_not_ge hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [huVanish y hge, map_zero]
  rw [hsum32]
  exact unitary_col0_norm_sq_sum uIdx
/-- Walker-alias `L¹` contraction for `keep9QuantInnerProb uIdx rc` against `p450ExactInnerProb`.
-/
theorem keep9QuantInnerProb_l1_le (uIdx : Unitary (2 ^ 5)) (rc : Fin 126) : (∑ b : Fin 30,
    |keep9QuantInnerProb uIdx rc b - p450ExactInnerProb rc b|) ≤ ∑ x : Fin 30, |Complex.normSq
    ((uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) - 1 / 30| := by
  let K (x b : Fin 30) : ℝ :=
    ((((if x = b then (keep9InnerAliasTable rc x).keep else 0) +
        (if (keep9InnerAliasTable rc x).alt = b then
          2 ^ 9 - (keep9InnerAliasTable rc x).keep else 0) : ℕ) : ℝ) / 512)
  let d (x : Fin 30) : ℝ := Complex.normSq ((uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) - 1 / 30
  have hK_nn (x b : Fin 30) : 0 ≤ K x b := by
    dsimp only [K]
    positivity
  have hK_sum (x : Fin 30) : (∑ b : Fin 30, K x b) = 1 := by
    dsimp only [K]
    rw [← Finset.sum_div, ← Nat.cast_sum, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    have h512 : (keep9InnerAliasTable rc x).keep +
        (2 ^ 9 - (keep9InnerAliasTable rc x).keep) = 512 := by
      have := keep9InnerAliasTable_keep_lt rc x
      omega
    rw [h512]
    norm_num
  have hdiff (b : Fin 30) :
      keep9QuantInnerProb uIdx rc b - p450ExactInnerProb rc b = ∑ x : Fin 30, d x * K x b := by
    have hw : p450ExactInnerProb rc b = ∑ x : Fin 30, (1 / 30 : ℝ) * K x b := by
      unfold p450ExactInnerProb
      have hvb := (isValidAliasTableKeep9InnerAliasTable_mantissa rc).2 b
      dsimp only at hvb
      rw [← hvb, Nat.cast_sum]
      dsimp only [K]
      rw [← Finset.mul_sum, ← Finset.sum_div]
      ring
    dsimp only [keep9QuantInnerProb]
    change (∑ x : Fin 30, _ * K x b) - _ = _
    rw [hw, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by
      dsimp only [d]
      ring
  calc (∑ b : Fin 30, |keep9QuantInnerProb uIdx rc b - p450ExactInnerProb rc b|)
      ≤ ∑ b : Fin 30, ∑ x : Fin 30, |d x| * K x b := by
        refine Finset.sum_le_sum fun b _ ↦ ?_
        rw [hdiff b]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg (hK_nn x b)]
    _ = ∑ x : Fin 30, |d x| * (∑ b : Fin 30, K x b) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum _ _ _).symm
    _ = ∑ x : Fin 30, |d x| := by simp_rw [hK_sum, mul_one]
/-- Active `(rc < 126, b < 30)` joint marginal of `prepMid18FromSlice` at
`keep9SliceTargetFn14` equals `keep9QuantInnerProb uIdx rc b / 2`. -/
theorem prepMid18FromSliceKeep9_joint_marginal {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool}
    (hfF : ∀ k : Fin (2 ^ 9), (∑ c : Fin (2 ^ 4), if muxBit c k = false then coin9Weight c else
    0) = k.val) (hfT : ∀ k : Fin (2 ^ 9), (∑ c : Fin (2 ^ 4), if muxBit c k = true then
    coin9Weight c else 0) = 2 ^ 9 - k.val) {uIdx : Unitary (2 ^ 5)} (huVanish : ∀ x : Fin (2 ^
    5), 30 ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0) (rc : Fin 126) (b : Fin 30) (si : Fin 2) : (∑
    m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB 18) ↦ ((rBLoc 18).extractIndex m).val = b.val ∧
    (rSigInLoc 18).extractIndex m = si), Complex.normSq ((prepMid18FromSlice muxBit
    keep9SliceTargetFn14 uIdx ⟨rc.val, by omega⟩).1 m 0)) = keep9QuantInnerProb uIdx rc b / 2
    := by
  let rc7 : Fin (2 ^ 7) := ⟨rc.val, by omega⟩
  let i₀ : Fin (2 ^ 5) := ⟨b.val, by omega⟩
  change (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB 18) ↦
      ((rBLoc 18).extractIndex m).val = i₀.val ∧ (rSigInLoc 18).extractIndex m = si),
    Complex.normSq ((prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc7).1 m 0)) = _
  rw [prepMid18FromSlice_joint_marginal hfF hfT keep9SliceTargetFn14 uIdx rc7 i₀ si]
  let emb30 : Fin 30 ↪ Fin (2 ^ 5) :=
    ⟨fun x ↦ ⟨x.val, by omega⟩,
      show Function.Injective (fun x : Fin 30 ↦ (⟨x.val, by omega⟩ : Fin (2 ^ 5))) from
        fun a c h ↦ Fin.ext (Fin.mk.inj h)⟩
  have hemb (x : Fin 30) : emb30 x = ⟨x.val, by omega⟩ := rfl
  have hsum30 :
      (∑ y : Fin (2 ^ 5), Complex.normSq (uIdx.1 y 0) *
        (((if y = i₀ then (keepOf14 (keep9SliceTargetFn14 rc7) y).val else 0) +
          (if altOf14 (keep9SliceTargetFn14 rc7) y = i₀ then
            2 ^ 9 - (keepOf14 (keep9SliceTargetFn14 rc7) y).val else 0) : ℕ) : ℝ) / 512) =
      keep9QuantInnerProb uIdx rc b := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map emb30))]
    · rw [Finset.sum_map]
      dsimp only [keep9QuantInnerProb]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hemb]
      have hcol : uIdx.1 ⟨x.val, by omega⟩ 0 = (uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩ := by
        simp [basisState, Matrix.col_apply]
      have hxEq : ((⟨x.val, by omega⟩ : Fin (2 ^ 5)) = i₀) ↔ x = b := by simp [i₀, Fin.ext_iff]
      have hrc7 : rc7.val < 126 := rc.isLt
      have haEq : (altOf14 (keep9SliceTargetFn14 rc7) ⟨x.val, by omega⟩ = i₀) ↔
          (keep9InnerAliasTable rc x).alt = b := by
        rw [altOf14Keep9_of_lt hrc7 x.isLt]
        simp [rc7, i₀, Fin.ext_iff]
      have hkVal : (keepOf14 (keep9SliceTargetFn14 rc7) ⟨x.val, by omega⟩).val =
          (keep9InnerAliasTable rc x).keep := by
        rw [keepOf14Keep9_of_lt hrc7 x.isLt]
      simp only [hcol, hxEq, haEq, hkVal]
      ring
    · intro y _ hy
      have hge : 30 ≤ y.val := by
        by_contra hlt
        exact hy (Finset.mem_map.mpr
          ⟨⟨y.val, Nat.lt_of_not_ge hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have huy : uIdx.1 y 0 = 0 := by
        simpa [basisState, Matrix.mulVec_single_one, Matrix.col_apply] using huVanish y hge
      simp [huy]
  rw [hsum30]
  ring
/-- Transfers `QuantizedFactoredMag30.PrepMidQuant128` directly onto `prepMid18FromSlice
mux9AltBit keep9SliceTargetFn14 uIdx` for any `uIdx` vanishing on `30 ≤ x.val`. -/
theorem prepMidQuant128PrepMid18Keep9 {uIdx : Unitary (2 ^ 5)} (huVanish : ∀ x : Fin (2 ^ 5),
    30 ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0) : QuantizedFactoredMag30.PrepMidQuant128
    (keep9QuantInnerProb uIdx) (prepMid18FromSlice mux9AltBit keep9SliceTargetFn14 uIdx) :=
  ⟨fun rc m hm ↦ prepMid18FromSliceKeep9_vanish mux9AltBit_fiber_false
      mux9AltBit_fiber_true huVanish ⟨rc.val, by omega⟩ m hm,
    prepMid18FromSliceKeep9_joint_marginal mux9AltBit_fiber_false mux9AltBit_fiber_true
      huVanish,
    prepMid18FromSlice_spin_marginal_half mux9AltBit keep9SliceTargetFn14 uIdx⟩
/-- Ancilla-free `T72` (`72-T`, `factoredMag30T72Circuit.eval`) inner distribution on
`keep9InnerAliasTable`. -/
noncomputable abbrev keep9T72Prob : Fin 126 → Fin 30 → ℝ := keep9QuantInnerProb
  factoredMag30T72Circuit.eval
/-- Concrete `(pi145XoEquiv, pi128Equiv)` inner-quantized `PulledSOSBlockEncoding` at `wInner2 = 18`
with exact outer `PrepOutValidPerm256`. -/
theorem pulledSOSBlockEncoding_pi145PrepMid18Mux9AltBit_quantInner {wOuter : ℕ} {prepOutIdeal
  : Unitary (2 ^ mOutUB wOuter)} (hOut : PrepOutValidPerm256 pi145XoEquiv prepOutIdeal) {uIdx :
  Unitary (2 ^ 5)} (huVanish : ∀ x : Fin (2 ^ 5), 30 ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0)
  (selectPure : Unitary (2 ^ nUB wOuter 18)) (hSelAct : SelectActiveOn pi145XoEquiv
  (genPi128PrepMid18Of mux9AltBit keep9SliceTargetFn14 pi128Equiv uIdx) selectPure) :
  PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB 18) (quantInnerP450HBlocked (keep9QuantInnerProb
  uIdx)) dfthcLowerBound 97.3864 (ubDirectXo7PureUnitary prepOutIdeal (genPi128PrepMid18Of
  mux9AltBit keep9SliceTargetFn14 pi128Equiv uIdx) selectPure) :=
  pulledSOSBlockEncoding_pi145_quantInner hOut (prepMidQuant128PrepMid18Keep9 huVanish)
  selectPure hSelAct
/-- Generic `AgreesOnElectronSector 58 η` bound for `quantInnerP450HBlocked (keep9QuantInnerProb
uIdx)` from splitter `L¹` error `εIn`. -/
theorem agreesOnElectronSectorKeep9_quantInner {uIdx : Unitary (2 ^ 5)} (huVanish : ∀ x : Fin (2
  ^ 5), 30 ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0) {εIn δH : ℝ} (hl1U : (∑ x : Fin 30,
  |Complex.normSq ((uIdx.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) - 1 / 30|) ≤ εIn) (hδ : (4 * 97.3864
  * 144553 / 188416) * εIn ≤ δH) (η : ℕ) : AgreesOnElectronSector 58 η (quantInnerP450HBlocked
  (keep9QuantInnerProb uIdx)) BlockEncodingCore.p450HBlocked δH :=
  agreesOnElectronSector_quantInner_of_l1 (keep9QuantInnerProb_nonneg uIdx)
  (keep9QuantInnerProb_sum_eq_one huVanish) (fun rc ↦ (keep9QuantInnerProb_l1_le uIdx rc).trans
  hl1U) hδ η
/-- Exact-outer `AgreesOnElectronSector 58 η` for `keep9T72Prob` (`265 / 10 ^ 9`). -/
theorem agreesOnElectronSectorKeep9T72_inner (η : ℕ := 63) :
    AgreesOnElectronSector 58 η (quantInnerP450HBlocked keep9T72Prob)
      BlockEncodingCore.p450HBlocked (265 / 10 ^ 9) :=
  agreesOnElectronSectorKeep9_quantInner factoredMag30T72Circuit_vanish
    factoredMag30T72Circuit_l1_le (by norm_num) η
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HadWMux23SOSBridge
end
