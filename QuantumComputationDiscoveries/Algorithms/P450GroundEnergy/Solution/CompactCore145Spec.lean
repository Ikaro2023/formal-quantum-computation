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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellRouter57Pure
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellPersistCore

/-!
# Compact `(159 - d)`-Inner-Scratch `Core145Bundle` (`0 ≤ d ≤ 10`) & `57`-AND `SELECT` Slices

Constructs the table-parametric `(159 - d)`-inner-scratch `Core145Bundle`
(`compactParamCore145Bundle`,
costing `compactCoreTCount d = 11818 + 448 * d + 4 * (d - 1)` `T`) and instantiates both the
single-pass (`12510 + 448 * d + 4 * (d - 1)` `T`) and Bell two-pass (`24788 + 896 * d +
8 * (d - 1) + pTurn.count .T` `T`) `57`-AND `π145` `SiZero` `SELECT` circuits.

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactCore145Bundle
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge Solution.CompactStepFast176Select
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open Solution.LowBitPi145Select
open Solution.ZeroRcHotPrepMid21Fast WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Solution.PhaseB154Pi145Select
open Solution.BellRouter57 Solution.BellRouter57Pure Solution.BellPersistCore

/-! ## Section 1: Table-Parametric `(159 - d)`-Inner-Scratch `Core145Bundle` -/

def compactCoreTCount (d : ℕ) : ℕ := 11818 + 448 * d + 4 * (d - 1)
/-- Canonical ambient wire count `((58 + 10) + 11) + (159 - d)` of the compact Stage-2 core. -/
abbrev mCanCore (d : ℕ) : ℕ := ((58 + 10) + 11) + (159 - d)
/-- Canonical `Core145Layout (159 - d)` on `mCanCore d` wires. -/
def canCoreLayout (d : ℕ) : Core145Layout (159 - d) (mCanCore d) :=
  { rFull := QRegister.whole (mCanCore d) }
/-- Wire bijection embedding `238` logical `Phase2Bal161Layout` wires into `mCanCore d + d` with
the `d` compact Givens wires placed in the trailing `d` virtual wires `mCanCore d ..`. -/
def extWireMap (d : ℕ) (hd : d ≤ 10) (idx : Fin 238) : Fin (mCanCore d + d) :=
  if _h1 : idx.val < 93 - d then ⟨idx.val, by dsimp [mCanCore]; omega⟩
  else if _h2 : idx.val < 93 then ⟨mCanCore d + (idx.val - (93 - d)), by dsimp [mCanCore]; omega⟩
  else ⟨idx.val - d, by dsimp [mCanCore]; omega⟩
theorem extWireMap_val_of_lt (d : ℕ) (hd : d ≤ 10) (idx : Fin 238) (h : idx.val < 93 - d) :
    (extWireMap d hd idx).val = idx.val := by dsimp only [extWireMap]; rw [dite_eq_left h]
theorem extWireMap_val_of_mid (d : ℕ) (hd : d ≤ 10) (idx : Fin 238)
    (h1 : ¬ idx.val < 93 - d) (h2 : idx.val < 93) :
    (extWireMap d hd idx).val = mCanCore d + (idx.val - (93 - d)) := by
  dsimp only [extWireMap]; rw [dite_eq_right h1, dite_eq_left h2]
theorem extWireMap_val_of_ge (d : ℕ) (hd : d ≤ 10) (idx : Fin 238) (h : 93 ≤ idx.val) :
    (extWireMap d hd idx).val = idx.val - d := by
  dsimp only [extWireMap]; rw [dite_eq_right (by omega), dite_eq_right (by omega)]
theorem extWireMap_injective (d : ℕ) (hd : d ≤ 10) : Function.Injective (extWireMap d hd) := by
  have hval (x : Fin 238) : (x.val < 93 - d ∧ (extWireMap d hd x).val = x.val) ∨
      (93 - d ≤ x.val ∧ x.val < 93 ∧ (extWireMap d hd x).val = mCanCore d + (x.val - (93 - d))) ∨
      (93 ≤ x.val ∧ (extWireMap d hd x).val = x.val - d) := by
    by_cases h1 : x.val < 93 - d
    · exact Or.inl ⟨h1, extWireMap_val_of_lt d hd x h1⟩
    · by_cases h2 : x.val < 93
      · exact Or.inr (Or.inl ⟨by omega, h2, extWireMap_val_of_mid d hd x h1 h2⟩)
      · exact Or.inr (Or.inr ⟨by omega, extWireMap_val_of_ge d hd x (by omega)⟩)
  intro a b h; have := a.isLt; have := b.isLt; have hv := congrArg Fin.val h
  have hm : mCanCore d = 238 - d := by dsimp [mCanCore]; omega
  rcases hval a with ⟨_, ha⟩ | ⟨_, _, ha⟩ | ⟨_, ha⟩ <;>
    rcases hval b with ⟨_, hb⟩ | ⟨_, _, hb⟩ | ⟨_, hb⟩ <;>
    (rw [ha, hb] at hv; exact Fin.ext (by omega))
/-- Extended `238`-wire `Phase2Bal161Layout` on `mCanCore d + d` placing the `d` unused Givens
wires in `[mCanCore d .. mCanCore d + d)` and the rest in `trimLeftReg (mCanCore d) d`. -/
def extCanLayout (d : ℕ) (hd : d ≤ 10) : Phase2Bal161Layout (mCanCore d + d) :=
  { rFull := ⟨⟨extWireMap d hd, extWireMap_injective d hd⟩⟩ }
theorem extCanLayout_lt (d : ℕ) (hd : d ≤ 10) :
    let L := extCanLayout d hd
    (∀ i, (L.rSpin i).val < mCanCore d) ∧ (∀ i, (L.rCtrlTail146 i).val < mCanCore d) ∧
    (∀ i, (L.rCat11 i).val < mCanCore d) ∧ (L.wHot0).val < mCanCore d ∧
    (∀ i, ((L.rGivens22.slice 0 (22 - d) (by omega)) i).val < mCanCore d) := by
  intro L
  have hf (k : Fin 238) (hk : k.val < 93 - d ∨ 93 ≤ k.val) : (L.rFull k).val < mCanCore d := by
    change (extWireMap d hd k).val < mCanCore d
    rcases hk with hk1 | hk2
    · rw [extWireMap_val_of_lt d hd k hk1]; dsimp [mCanCore]; omega
    · rw [extWireMap_val_of_ge d hd k hk2]; dsimp [mCanCore]; omega
  refine ⟨fun i ↦ by rw [L.rSpin_eq]; exact hf _ (Or.inl (by dsimp; omega)),
    fun i ↦ by
      obtain ⟨k, hk, hcond⟩ := L.rCtrlTail146_in_rFull i; rw [hk]
      exact hf k (by rcases hcond with h1 | h2 | h3 <;> [left; left; right] <;> omega),
    fun i ↦ by rw [L.rCat11_eq]; exact hf _ (Or.inl (by dsimp; omega)),
    by dsimp [Phase2Bal161Layout.wHot0]; rw [L.rOneHot145_eq]
       exact hf _ (Or.inr (by dsimp; omega)),
    fun i ↦ ?_⟩
  rw [QRegister.slice_apply]; dsimp only [Phase2Bal161Layout.rGivens22]
  by_cases hi8 : i.val < 8
  · rw [show (⟨0 + i.val, by omega⟩ : Fin (8 + 14)) = Fin.castAdd 14 ⟨i.val, hi8⟩ by ext; simp,
      QRegister.concat_apply_left, L.rSelPair8_eq]
    exact hf _ (Or.inl (by dsimp; omega))
  · rw [show (⟨0 + i.val, by omega⟩ : Fin (8 + 14)) = Fin.natAdd 8 ⟨i.val - 8, by omega⟩ by
        ext; simp; omega,
      QRegister.concat_apply_right, L.rGivRest14_eq]
    exact hf _ (Or.inl (by dsimp; omega))
theorem extCan_hsc (d : ℕ) (hd : d ≤ 10) :
    (projReg (extCanLayout d hd).rSpin (extCanLayout_lt d hd).1).DisjointWires
      (projReg (extCanLayout d hd).rCtrlTail146 (extCanLayout_lt d hd).2.1) :=
  disj_projReg (extCanLayout_lt d hd).1 (extCanLayout_lt d hd).2.1
    (extCanLayout d hd).hSpinTail146
theorem extCan_hac (d : ℕ) (hd : d ≤ 10) :
    let L := extCanLayout d hd; let hlt := extCanLayout_lt d hd
    ((projReg L.rSpin hlt.1).concat (projReg L.rCtrlTail146 hlt.2.1)
      (extCan_hsc d hd)).DisjointWires (projReg L.rCat11 hlt.2.2.1) := by
  intro L hlt; refine QRegister.disjointWires_concat_left (extCan_hsc d hd)
    (disj_projReg hlt.1 hlt.2.2.1 (QRegister.disjoint_iff.mpr fun i k h ↦
      QRegister.disjoint_iff.mp L.hSpinTail146Cat (Fin.castAdd _ i) k
        (by rw [QRegister.concat_apply_left]; exact h)))
    (disj_projReg hlt.2.1 hlt.2.2.1 (QRegister.disjoint_iff.mpr fun j k h ↦
      QRegister.disjoint_iff.mp L.hSpinTail146Cat (Fin.natAdd _ j) k
        (by rw [QRegister.concat_apply_right]; exact h)))
theorem extCan_hWork0 (d : ℕ) (hd : d ≤ 10) :
    let L := extCanLayout d hd; let hlt := extCanLayout_lt d hd
    (projReg (L.rGivens22.slice 0 (22 - d) (by omega)) hlt.2.2.2.2).DisjointWires
      (QRegister.singleton (⟨(L.wHot0).val, hlt.2.2.2.1⟩ : Wire (mCanCore d))) := by
  intro L hlt; rw [QRegister.disjoint_iff]; intro i z; fin_cases z; intro h
  rw [QRegister.singleton_apply] at h
  have hv : (L.rGivens22.slice 0 (22 - d) (by omega)) i = L.wHot0 :=
    Fin.ext (congrArg (Fin.val : Fin (mCanCore d) → ℕ) h)
  rw [QRegister.slice_apply] at hv
  exact QRegister.disjoint_iff.mp L.hGiv22Hot0 _ 0 (hv.trans (QRegister.singleton_apply _ _).symm)
theorem extCan_hdisjPlus (d : ℕ) (hd : d ≤ 10) :
    let L := extCanLayout d hd; let hlt := extCanLayout_lt d hd
    (((projReg L.rSpin hlt.1).concat (projReg L.rCtrlTail146 hlt.2.1) (extCan_hsc d hd)).concat
      (projReg L.rCat11 hlt.2.2.1) (extCan_hac d hd)).DisjointWires
      ((projReg (L.rGivens22.slice 0 (22 - d) (by omega)) hlt.2.2.2.2).concat
        (QRegister.singleton (⟨(L.wHot0).val, hlt.2.2.2.1⟩ : Wire (mCanCore d)))
        (extCan_hWork0 d hd)) := by
  intro L hlt
  let rSpinC := projReg L.rSpin hlt.1; let rTailC := projReg L.rCtrlTail146 hlt.2.1
  let rCatC := projReg L.rCat11 hlt.2.2.1
  let rWorkC := projReg (L.rGivens22.slice 0 (22 - d) (by omega)) hlt.2.2.2.2
  rw [QRegister.disjoint_iff]; intro a
  have hA : (((L.rSpin.concat L.rCtrlTail146 L.hSpinTail146).concat L.rCat11
      L.hSpinTail146Cat) a).val =
      (((rSpinC.concat rTailC (extCan_hsc d hd)).concat rCatC (extCan_hac d hd)) a).val := by
    refine Fin.addCases (fun ij ↦ ?_) (fun k ↦ ?_) a
    · rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) ij
      · rw [QRegister.concat_apply_left, QRegister.concat_apply_left]; simp [rSpinC]
      · rw [QRegister.concat_apply_right, QRegister.concat_apply_right]; simp [rTailC]
    · rw [QRegister.concat_apply_right, QRegister.concat_apply_right]; simp [rCatC]
  refine Fin.addCases (fun j h ↦ ?_) (fun z h ↦ ?_)
  · rw [QRegister.concat_apply_left] at h
    have hB : (L.rGivens22 ⟨0 + j.val, by omega⟩).val = (rWorkC j).val := by simp [rWorkC]
    exact QRegister.disjoint_iff.mp L.hSpinTail146CatGiv22Hot0 a
      (Fin.castAdd 1 ⟨0 + j.val, by omega⟩)
      (Fin.ext (by rw [QRegister.concat_apply_left, hA, hB]; exact congrArg Fin.val h))
  · fin_cases z; rw [QRegister.concat_apply_right, QRegister.singleton_apply] at h
    exact QRegister.disjoint_iff.mp L.hSpinTail146CatGiv22Hot0 a (Fin.natAdd 22 0)
      (Fin.ext (by
        rw [QRegister.concat_apply_right, QRegister.singleton_apply, hA]
        exact congrArg Fin.val h))
/-- Canonical `mCanCore d`-wire compact `Lac = 2` cascade for `orbitalOf`. -/
def compactCascadeCanDyn (d : ℕ) (hd : d ≤ 10) (orbitalOf : Fin 145 → Bool → Fin 319) :
    DynamicCircuit Unit (mCanCore d) :=
  let L := extCanLayout d hd; let hlt := extCanLayout_lt d hd
  compactLac2CascadeCtrl22Dyn () hd OneHotMux.h58_gt_1
    (p450Bal145OrbitalTable orbitalOf)
    (projReg L.rSpin hlt.1) (projReg L.rCtrlTail146 hlt.2.1) (extCan_hsc d hd)
    actIdx146 selHot144 subIdx146 ⟨(L.wHot0).val, hlt.2.2.2.1⟩ (projReg L.rCat11 hlt.2.2.1)
    (projReg (L.rGivens22.slice 0 (22 - d) (by omega)) hlt.2.2.2.2) le_rfl
    (extCan_hac d hd) (extCan_hWork0 d hd) (extCan_hdisjPlus d hd)
/-- Pre-cascade Clifford glue on `extCanLayout d hd`. -/
def compactExtPreCircuit (d : ℕ) (hd : d ≤ 10) (actFlipMask : Fin 145 → Bool)
    (negMask : Fin 145 → Bool) : Circuit (mCanCore d + d) :=
  let L := extCanLayout d hd
  flipAct145Circuit actFlipMask L ;;ᶜ Circuit.X L.wOne ;;ᶜ
    zMaskAct145Circuit negMask L ;;ᶜ
    Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne L.rSelPair8 L.rOneHot145
      (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i)
/-- Post-cascade Clifford glue on `extCanLayout d hd`. -/
def compactExtPostCircuit (d : ℕ) (hd : d ≤ 10) (actFlipMask : Fin 145 → Bool) :
    Circuit (mCanCore d + d) :=
  let L := extCanLayout d hd
  Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne L.rSelPair8 L.rOneHot145
      (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i) ;;ᶜ
    Circuit.X L.wOne ;;ᶜ flipAct145Circuit actFlipMask L
theorem inLeftCircuitB_seq {m d : ℕ} {c₁ c₂ : Circuit (m + d)} (h₁ : inLeftCircuitB m d c₁ = true)
    (h₂ : inLeftCircuitB m d c₂ = true) : inLeftCircuitB m d (c₁ ;;ᶜ c₂) = true := by
  dsimp only [inLeftCircuitB]; rw [h₁, h₂]; rfl
theorem inLeftCircuitB_single {m d : ℕ} (g : PrimitiveGate 1) (q : Wire (m + d)) (hq : q.val < m) :
    inLeftCircuitB m d (Circuit.single g q) = true :=
  decide_eq_true fun i ↦ by fin_cases i; exact hq
theorem inLeftCircuitB_CNOT {m d : ℕ} (c t : Wire (m + d)) (h : c ≠ t)
    (hc : c.val < m) (ht : t.val < m) : inLeftCircuitB m d (Circuit.CNOT c t h) = true :=
  decide_eq_true fun i ↦ by fin_cases i <;> simp [hc, ht]
theorem inLeftCircuitB_cnotMaskReg (m d : ℕ) :
    ∀ (G : ℕ) (rSrc : QRegister G (m + d)) (dst : Wire (m + d)) (mask : Fin G → Bool)
      (hdisj : ∀ g, rSrc g ≠ dst), (∀ g, (rSrc g).val < m) → dst.val < m →
      inLeftCircuitB m d (Solution.CircuitModular.UnsignedGivens.cnotMaskReg G rSrc dst mask hdisj)
        = true
  | 0, _, _, _, _, _, _ => rfl
  | G + 1, rSrc, dst, mask, hdisj, hr, hd => by
      have ih := inLeftCircuitB_cnotMaskReg m d G (rSrc.slice 1 G (by omega)) dst
        (fun g ↦ mask g.succ)
        (fun g ↦ by rw [QRegister.slice_apply]; exact hdisj ⟨1 + g.val, by omega⟩)
        (fun g ↦ by rw [QRegister.slice_apply]; exact hr ⟨1 + g.val, by omega⟩) hd
      dsimp only [Solution.CircuitModular.UnsignedGivens.cnotMaskReg];
        refine inLeftCircuitB_seq ?_ ih
      split_ifs; · exact inLeftCircuitB_CNOT _ _ _ (hr 0) hd
      · rfl
theorem inLeftCircuitB_xorFiltered (m d : ℕ) :
    ∀ (k : ℕ) (keep : Fin k → Bool) (rSrc : QRegister k (m + d)) (wDst : Wire (m + d))
      (hne : ∀ i, rSrc i ≠ wDst), (∀ i, (rSrc i).val < m) → wDst.val < m →
      inLeftCircuitB m d
        (Lac2Fused184Select.xorFilteredRegToWireCircuit k keep rSrc wDst hne) = true
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, keep, rSrc, wDst, hne, hr, hw => by
      dsimp only [Lac2Fused184Select.xorFilteredRegToWireCircuit]
      have ih := inLeftCircuitB_xorFiltered m d k (fun i ↦ keep i.castSucc)
        (OneHotSimulates.regInit rSrc) wDst (fun i ↦ hne i.castSucc) (fun i ↦ hr i.castSucc) hw
      split_ifs; · exact inLeftCircuitB_seq ih (inLeftCircuitB_CNOT _ _ _ (hr _) hw)
      · exact ih
theorem inLeftCircuitB_xorOneHot (m d : ℕ) :
    ∀ (k G : ℕ) (rIdx : QRegister k (m + d)) (rOH : QRegister G (m + d))
      (hne : ∀ i g, rOH g ≠ rIdx i), (∀ i, (rIdx i).val < m) → (∀ g, (rOH g).val < m) →
      inLeftCircuitB m d (Lac2Fused184Select.xorOneHotToIdxCircuit k G rIdx rOH hne) = true
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, G, rIdx, rOH, hne, hI, hO => by
      dsimp only [Lac2Fused184Select.xorOneHotToIdxCircuit]
      exact inLeftCircuitB_seq
        (inLeftCircuitB_xorOneHot m d k G (OneHotSimulates.regInit rIdx) rOH
          (fun i g ↦ hne i.castSucc g) (fun i ↦ hI i.castSucc) hO)
        (inLeftCircuitB_xorFiltered m d G _ rOH _ (hne (Fin.last k)) hO (hI _))
theorem inLeft_compactExtGlue (d : ℕ) (hd : d ≤ 10) (actFlipMask : Fin 145 → Bool)
    (negMask : Fin 145 → Bool) :
    inLeftDynB (mCanCore d) d (dEnc145Dyn () (extCanLayout d hd)) = true ∧
    inLeftCircuitB (mCanCore d) d (compactExtPreCircuit d hd actFlipMask negMask) = true ∧
    inLeftCircuitB (mCanCore d) d (compactExtPostCircuit d hd actFlipMask) = true ∧
    inLeftDynB (mCanCore d) d (dDec145Dyn () (extCanLayout d hd)) = true := by
  let L := extCanLayout d hd
  have hf (k : Fin 238) (hk : k.val < 93 - d ∨ 93 ≤ k.val) : (L.rFull k).val < mCanCore d := by
    change (extWireMap d hd k).val < mCanCore d; rcases hk with h1 | h2
    · rw [extWireMap_val_of_lt d hd k h1]; dsimp [mCanCore]; omega
    · rw [extWireMap_val_of_ge d hd k h2]; dsimp [mCanCore]; omega
  have hOH (g : Fin 145) : (L.rOneHot145 g).val < mCanCore d := by
    rw [L.rOneHot145_eq]; exact hf _ (Or.inr (by dsimp; omega))
  have hPair (i : Fin 8) : (L.rSelPair8 i).val < mCanCore d := by
    rw [L.rSelPair8_eq]; exact hf _ (Or.inl (by dsimp; omega))
  have hAct : L.wAct.val < mCanCore d := by
    dsimp [Phase2Bal161Layout.wAct]; rw [L.rCtrl10_eq]
    exact hf _ (Or.inl (by dsimp [Lac2Fused184Select.actIdx10]; omega))
  have hOne : L.wOne.val < mCanCore d := by
    rw [Phase2Bal161Layout.wOne, L.rGivRest14_eq]; exact hf _ (Or.inl (by dsimp; omega))
  have hPh : L.wPh.val < mCanCore d := by
    rw [Phase2Bal161Layout.wPh, L.rGivRest14_eq]; exact hf _ (Or.inl (by dsimp; omega))
  have hFlip : inLeftCircuitB (mCanCore d) d (flipAct145Circuit actFlipMask L) = true :=
    inLeftCircuitB_cnotMaskReg _ _ 145 _ _ _ _ hOH hAct
  have hFan : inLeftCircuitB (mCanCore d) d (Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne
      L.rSelPair8 L.rOneHot145 (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i)) =
      true :=
    inLeftCircuitB_seq (inLeftCircuitB_xorFiltered _ _ 145 _ _ _ _ hOH hOne)
      (inLeftCircuitB_xorOneHot _ _ 8 145 _ _ _ hPair hOH)
  have hZ : inLeftCircuitB (mCanCore d) d (zMaskAct145Circuit negMask L) = true := by
    simp [zMaskAct145Circuit, Solution.CircuitModular.UnsignedGivens.czCircuit, inLeftCircuitB,
      inLeftCircuitB_cnotMaskReg _ _ 145 _ _ _ _ hOH hPh, hPh, hAct]
  have h1 : inLeftDynB (mCanCore d) d (dEnc145Dyn () (extCanLayout d hd)) = true := by
    interval_cases d <;>
      (have hs : hd = by decide := Subsingleton.elim _ _; subst hs; decide +kernel)
  have h4 : inLeftDynB (mCanCore d) d (dDec145Dyn () (extCanLayout d hd)) = true := by
    interval_cases d <;>
      (have hs : hd = by decide := Subsingleton.elim _ _; subst hs; decide +kernel)
  have hX := inLeftCircuitB_single (m := mCanCore d) (d := d) .X L.wOne hOne
  dsimp only [L] at hFlip hZ hFan; dsimp only [L, inLeftCircuitB] at hX
  exact ⟨h1, by dsimp only [compactExtPreCircuit, inLeftCircuitB]; rw [hFlip, hX, hZ, hFan]; rfl,
    by dsimp only [compactExtPostCircuit, inLeftCircuitB]; rw [hFan, hX, hFlip]; rfl, h4⟩
/-- Canonical `mCanCore d`-wire compact Stage-2 core (`11818 + 448 * d + 4 * (d - 1)` `T`). -/
def compactCanCoreUnitDyn (d : ℕ) (hd : d ≤ 10) (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) :
    DynamicCircuit Unit (mCanCore d) :=
  .seq (trimDyn (mCanCore d) d (dEnc145Dyn () (extCanLayout d hd)))
    (.seq (.circuit (trimCircuit (mCanCore d) d (compactExtPreCircuit d hd actFlipMask negMask)))
      (.seq (compactCascadeCanDyn d hd orbitalOf)
        (.seq (.circuit (trimCircuit (mCanCore d) d (compactExtPostCircuit d hd actFlipMask)))
          (trimDyn (mCanCore d) d (dDec145Dyn () (extCanLayout d hd))))))
/-- Extended `mCanCore d + d`-wire core matching `compactCanCoreUnitDyn.onRegister`. -/
def compactExtCoreDyn (d : ℕ) (hd : d ≤ 10) (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) :
    DynamicCircuit Unit (mCanCore d + d) :=
  let L := extCanLayout d hd
  .seq (dEnc145Dyn () L)
    (.seq (.circuit (compactExtPreCircuit d hd actFlipMask negMask))
      (.seq ((compactCascadeCanDyn d hd orbitalOf).onRegister (trimLeftReg (mCanCore d) d))
        (.seq (.circuit (compactExtPostCircuit d hd actFlipMask)) (dDec145Dyn () L))))
theorem onRegister_trimLeftReg_compactCanCoreUnitDyn (d : ℕ) (hd : d ≤ 10)
    (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) :
    (compactCanCoreUnitDyn d hd actFlipMask orbitalOf negMask).onRegister
        (trimLeftReg (mCanCore d) d) =
      compactExtCoreDyn d hd actFlipMask orbitalOf negMask := by
  obtain ⟨h1, h2, h3, h4⟩ := inLeft_compactExtGlue d hd actFlipMask negMask
  simp only [compactCanCoreUnitDyn, compactExtCoreDyn, DynamicCircuit.onRegister_seq,
    DynamicCircuit.onRegister_circuit, onRegister_trimLeftReg_trimDyn _ _ _ h1,
    onRegister_trimLeftReg_trimCircuit _ _ _ h2, onRegister_trimLeftReg_trimCircuit _ _ _ h3,
    onRegister_trimLeftReg_trimDyn _ _ _ h4]
@[simp] theorem count_compactCanCoreUnitDyn_toff (d : ℕ) (hd : d ≤ 10)
    (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) :
    (compactCanCoreUnitDyn d hd actFlipMask orbitalOf negMask).count .TOFF = 0 := by
  rw [← DynamicCircuit.count_onRegister .TOFF (trimLeftReg (mCanCore d) d),
    onRegister_trimLeftReg_compactCanCoreUnitDyn]
  simp [compactExtCoreDyn, compactExtPreCircuit, compactExtPostCircuit, compactCascadeCanDyn,
    DynamicCircuit.count]
@[simp] theorem count_compactCanCoreUnitDyn_t (d : ℕ) (hd : d ≤ 10)
    (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) :
    (compactCanCoreUnitDyn d hd actFlipMask orbitalOf negMask).count .T = compactCoreTCount d := by
  rw [← DynamicCircuit.count_onRegister .T (trimLeftReg (mCanCore d) d),
    onRegister_trimLeftReg_compactCanCoreUnitDyn]
  dsimp only [compactExtCoreDyn, compactExtPreCircuit, compactExtPostCircuit, compactCascadeCanDyn,
    compactCoreTCount, DynamicCircuit.count]
  simp only [DynamicCircuit.count_onRegister, Circuit.count_seq, count_dEnc145Dyn_t,
    count_dDec145Dyn_t, count_flipAct145Circuit_t, count_zMaskAct145Circuit_t,
    Lac2Fused184Select.count_fanoutActIdxCircuit_t, count_compactLac2CascadeCtrl22Dyn_t]
  have hX : (Circuit.X (extCanLayout d hd).wOne).count .T = 0 := rfl
  rw [hX]; omega
attribute [irreducible] compactCanCoreUnitDyn
theorem diagProjSimulates_compactExtCoreDyn (d : ℕ) (hd : d ≤ 10)
    (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) :
    let L := extCanLayout d hd
    let rSC := L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)
    ∃ wPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)),
      DiagProjSimulates (ketPredProj (sValid145 L))
        ((rSC.concat L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary
          (UnsignedGivens.muxCtrlUnitary wPhased))
        (compactExtCoreDyn d hd actFlipMask orbitalOf negMask) ∧
      ∀ (c10 : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
        (wPhased c10).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) =
          prodState
            ((phase2Bal145PhasedBranch actFlipMask orbitalOf negMask c10).1 *ᵥ ψ)
            (phaseGradientLowFactor 11 3) := by
  intro L rSC
  have : NeZero (2 ^ (mCanCore d)) := ⟨(Nat.two_pow_pos _).ne'⟩
  have : NeZero (2 ^ (mCanCore d + d)) := ⟨(Nat.two_pow_pos _).ne'⟩
  let hlt := extCanLayout_lt d hd
  let rSpinC := projReg L.rSpin hlt.1; let rTailC := projReg L.rCtrlTail146 hlt.2.1
  let rCatC := projReg L.rCat11 hlt.2.2.1
  let wHot0C : Wire (mCanCore d) := ⟨(L.wHot0).val, hlt.2.2.2.1⟩
  let rWorkC := projReg (L.rGivens22.slice 0 (22 - d) (by omega)) hlt.2.2.2.2
  let hscC := extCan_hsc d hd; let hacC := extCan_hac d hd
  let hWork0C := extCan_hWork0 d hd; let hdisjPlusC := extCan_hdisjPlus d hd
  obtain ⟨wAff, hSimCan, hcatAff⟩ := diagProjSimulates_compactLac2CascadeCtrl22Dyn () hd
    OneHotMux.h58_gt_1 (p450Bal145OrbitalTable orbitalOf) rSpinC rTailC hscC actIdx146 selHot144
    subIdx146 wHot0C rCatC rWorkC le_rfl hacC hWork0C hdisjPlusC
  rw [← compactCascadeCanDyn] at hSimCan
  let rCan := rSpinC.concat rCatC (OneHotMux.disj_sys_cat_of hscC hacC)
  let rActCan := rCan.concat rTailC (OneHotMux.disj_sysCat_ctrl_of hscC hacC)
  let sCan (γ : BitAssignment (mCanCore d)) : Prop :=
    (∃ g₀ : Fin (144 + 1), UnsignedGivens.IsOneHotBits g₀
      (Fin.cases (γ wHot0C) (fun g ↦ γ ((rTailC.compose selHot144) g)))) ∧
      ∀ j : Fin (22 - d), γ (rWorkC j) = 0
  have hSimPush := diagProjSimulates_onRegister (trimLeftReg (mCanCore d) d) sCan
    (rActCan.embedUnitary (UnsignedGivens.muxCtrlUnitary wAff))
      (compactCascadeCanDyn d hd orbitalOf) hSimCan
  let uAff : Unitary (2 ^ (mCanCore d + d)) :=
    (rSC.concat L.rCtrlTail146
      (OneHotMux.disj_sysCat_ctrl_of L.hSpinTail146 L.hSpinTail146Cat)).embedUnitary
      (UnsignedGivens.muxCtrlUnitary wAff)
  have huAffEq : (trimLeftReg (mCanCore d) d).embedUnitary
      (rActCan.embedUnitary (UnsignedGivens.muxCtrlUnitary wAff)) = uAff := by
    rw [← QRegister.embedUnitary_compose]; congr 1; refine CoherentAlias.qreg_ext fun idx ↦ ?_
    refine Fin.addCases (fun sc ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.compose_apply]; dsimp only [rActCan, rCan, rSC]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) sc
      · rw [QRegister.concat_apply_left, QRegister.concat_apply_left]; rfl
      · rw [QRegister.concat_apply_right, QRegister.concat_apply_right]; rfl
    · rw [QRegister.compose_apply]; dsimp only [rActCan]
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]; rfl
  rw [huAffEq] at hSimPush
  let wPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)) := fun c10 ↦
    let cF := flipActCtrl10_145 actFlipMask c10
    (if ctrl10RawPhase145 negMask cF then negOneUnitary (58 + 11) else 1) *
      wAff (ctrl10ToTail146Idx cF)
  let uPhased : Unitary (2 ^ (mCanCore d + d)) :=
    (rSC.concat L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary
      (UnsignedGivens.muxCtrlUnitary wPhased)
  have hcFanEq : Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne L.rSelPair8 L.rOneHot145
      (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i) = cFan145 L := by
    unfold cFan145; rfl
  obtain ⟨cFanU, hcFanU⟩ : ∃ cFanU, (cFan145 L).eval = cFanU := ⟨_, rfl⟩
  obtain ⟨hnotC, hnotI, _, _⟩ := rSC145_not_mem L
  have hsWr (β : BitAssignment (mCanCore d + d)) (l : Fin (2 ^ (58 + 11))) :
      sValid145 L (UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)) ↔ sValid145 L β := by
    have hpLoc : UnsignedGivens.localIdx L.rSelPair8 (UnsignedGivens.writeReg β rSC (basisBits (58 +
      11) l)) =
        UnsignedGivens.localIdx L.rSelPair8 β :=
      localIdx_congr L.rSelPair8 fun i ↦ UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _
        (hnotC (Lac2Fused184Select.selPair10 i))
    have hi (idx : Fin 159) : UnsignedGivens.writeReg β rSC (basisBits (58 +
      11) l) (L.rInner159 idx) =
        β (L.rInner159 idx) := UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnotI idx)
    dsimp only [sValid145]; simp only [hpLoc, hi]
  have hCommTgt : uPhased.1 * ketPredProj (sValid145 L) = ketPredProj (sValid145 L) * uPhased.1 :=
    embed_muxCtrl_comm_ketPredProj rSC L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac) wPhased
      (sValid145 L) hsWr
  refine ⟨wPhased, SubspaceStepU.toDiagProjSimulates ⟨sValid145 L, rfl⟩ hCommTgt ?_,
    fun c10 ψ ↦ ?_⟩
  · let R_enc := ketMapOp (sValid145 L) (fun β ↦ Solution.XMeasCircuit.ket (encAssign145 L β))
    let βFOf (β : BitAssignment (mCanCore d + d)) := flipAct145Assign actFlipMask L β
    let β₂Of (β : BitAssignment (mCanCore d + d)) :=
      Lac2Fused184Select.fanoutActIdxAssign 8 145 L.wOne L.rSelPair8 L.rOneHot145
        (Function.update (encAssign145 L (βFOf β)) L.wOne 1)
    let phOf (β : BitAssignment (mCanCore d + d)) : ℂ :=
      if ctrl10RawPhase145 negMask (UnsignedGivens.localIdx L.rCtrl10 (βFOf β)) then -1 else 1
    let R_mid1 := ketMapOp (sValid145 L) (fun β ↦ phOf β • Solution.XMeasCircuit.ket (β₂Of β))
    have hMid1 : (compactExtPreCircuit d hd actFlipMask negMask).eval.1 * R_enc = R_mid1 := by
      dsimp only [compactExtPreCircuit]; rw [hcFanEq, mul_ketMapOp]
      refine ketMapOp_congr fun β hS ↦ ?_
      have hSF : sValid145 L (βFOf β) := (sValid145_flipAct145Assign actFlipMask L β).mpr hS
      have ho0 : encAssign145 L (βFOf β) L.wOne = 0 := by
        dsimp only [encAssign145]; rw [Function.update_of_ne (oh145_ne_rest L _ 0).symm]
        exact rest14_zero_of_sValid hSF 0
      have hx1 :
        (Circuit.X L.wOne).eval.1.mulVec (Solution.XMeasCircuit.ket (encAssign145 L (βFOf β))) =
          OneHotSimulates.ket (Function.update (encAssign145 L (βFOf β)) L.wOne 1) := by
        simpa only [ho0,
          zero_add] using UnsignedGivens.evolve_X_ket L.wOne (encAssign145 L (βFOf β))
      have hf1 : cFanU.1.mulVec
          (OneHotSimulates.ket (Function.update (encAssign145 L (βFOf β)) L.wOne 1)) =
          Solution.XMeasCircuit.ket (β₂Of β) := by rw [← hcFanU]; exact ket_cFan145 L _
      rw [StepEncK.eval_seq_mulVec, StepEncK.eval_seq_mulVec,
        StepEncK.eval_seq_mulVec, hcFanU, flipAct145Circuit_enc_ket actFlipMask L hS, hx1,
        zMask145_enc_ket negMask L hSF, Matrix.mulVec_smul, hf1]
    let sPush (β : BitAssignment (mCanCore d + d)) : Prop := sCan fun u ↦ β (trimLeftReg _ _ u)
    have hCascClean : ketPredProj sPush * R_mid1 = R_mid1 := by
      classical
      rw [mul_ketMapOp]; refine ketMapOp_congr fun β hS ↦ ?_
      have hSF : sValid145 L (βFOf β) := (sValid145_flipAct145Assign actFlipMask L β).mpr hS
      obtain ⟨⟨g₀, hoh⟩, hgiv0⟩ := fanout_enc_sCascValid145 L hSF
      have hs2 : sPush (β₂Of β) := by
        dsimp only [sPush, sCan];
          refine ⟨⟨g₀, Eq.mp (congrArg (UnsignedGivens.IsOneHotBits g₀) ?_) hoh⟩,
          fun j ↦ ?_⟩
        · funext k; cases k using Fin.cases with
          | zero => exact congrArg (β₂Of β) (Fin.ext rfl)
          | succ g => exact congrArg (β₂Of β) (Fin.ext rfl)
        · have hjw : trimLeftReg (mCanCore d) d (rWorkC j) =
              L.rGivens22 ⟨0 + j.val, by omega⟩ := Fin.ext rfl
          rw [hjw]; exact hgiv0 ⟨0 + j.val, by omega⟩
      have hket2 : Solution.XMeasCircuit.ket (β₂Of β) = OneHotSimulates.ket (β₂Of β) := rfl
      rw [Matrix.mulVec_smul, hket2, ketPredProj_mulVec_ket, ite_posE hs2, ← hket2]
    have hFanSq : cFanU.1 * cFanU.1 = 1 := by rw [← hcFanU]; exact cFan145_eval_mul_self L
    have hMid3 : (compactExtPostCircuit d hd actFlipMask).eval.1 * (uAff.1 * R_mid1) =
        R_enc * uPhased.1 := by
      dsimp only [compactExtPostCircuit]; rw [hcFanEq]
      classical
      refine Solution.XMeasCircuit.matrix_ext_ket fun β ↦ ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ketMapOp_mulVec_ket]
      by_cases hS : sValid145 L β
      · rw [ite_posE hS]
        have hSF : sValid145 L (βFOf β) := (sValid145_flipAct145Assign actFlipMask L β).mpr hS
        have hLocSC := (writeReg_fanout145_comm actFlipMask L β 0).1
        have hket2 : Solution.XMeasCircuit.ket (β₂Of β) = UnsignedGivens.ket (β₂Of β) := rfl
        have hket0 : Solution.XMeasCircuit.ket β = UnsignedGivens.ket β := rfl
        have hCtrlEq := localIdx_ctrl10_flipAct145Assign actFlipMask L β
        rw [Matrix.mulVec_smul, hket2, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
          localIdx_tail146_fanout L hSF, hCtrlEq, QRegister.embedUnitary_val,
          UnsignedGivens.embedMatrix_mulVec_ket, hLocSC, Finset.smul_sum, Matrix.mulVec_sum]
        have hrhs : uPhased.1.mulVec (Solution.XMeasCircuit.ket β) =
            ∑ l : Fin (2 ^ (58 + 11)), phOf β •
              ((wAff (ctrl10ToTail146Idx (flipActCtrl10_145 actFlipMask
                (UnsignedGivens.localIdx L.rCtrl10 β)))).1 l (UnsignedGivens.localIdx rSC β) •
                UnsignedGivens.ket (UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l))) := by
          rw [hket0, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket]
          dsimp only [wPhased, phOf]; rw [hCtrlEq]
          by_cases hph : ctrl10RawPhase145 negMask
              (flipActCtrl10_145 actFlipMask (UnsignedGivens.localIdx L.rCtrl10 β)) = true
          · simp only [hph, ↓reduceIte, QRegister.embedUnitary_val, Submonoid.coe_mul,
              negOneUnitary_val, Matrix.smul_mul, Matrix.one_mul, rSC.embedMatrix_smul,
              Matrix.smul_mulVec, UnsignedGivens.embedMatrix_mulVec_ket, Finset.smul_sum]
          · simp only [hph, Bool.false_eq_true, ↓reduceIte, one_mul, one_smul,
              QRegister.embedUnitary_val, UnsignedGivens.embedMatrix_mulVec_ket]
        rw [hrhs, Matrix.mulVec_sum]; refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
        congr 2
        let γL := UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)
        have hSγ : sValid145 L γL := (hsWr β l).mpr hS
        have hSFγ : sValid145 L (βFOf γL) := (sValid145_flipAct145Assign actFlipMask L γL).mpr hSγ
        have hfanBack : cFanU.1.mulVec (OneHotSimulates.ket (β₂Of γL)) =
            OneHotSimulates.ket (Function.update (encAssign145 L (βFOf γL)) L.wOne 1) := by
          have hf1 : cFanU.1.mulVec
              (OneHotSimulates.ket (Function.update (encAssign145 L (βFOf γL)) L.wOne 1)) =
              OneHotSimulates.ket (β₂Of γL) := by rw [← hcFanU]; exact ket_cFan145 L _
          rw [← hf1, Matrix.mulVec_mulVec, hFanSq, Matrix.one_mulVec]
        have ho0γ : encAssign145 L (βFOf γL) L.wOne = 0 := by
          dsimp only [encAssign145]; rw [Function.update_of_ne (oh145_ne_rest L _ 0).symm]
          exact rest14_zero_of_sValid hSFγ 0
        have hclr1 : Function.update (Function.update (encAssign145 L (βFOf γL)) L.wOne 1) L.wOne
            (Function.update (encAssign145 L (βFOf γL)) L.wOne 1 L.wOne + 1) =
            encAssign145 L (βFOf γL) := by
          rw [Function.update_self, Function.update_idem]
          exact Function.update_eq_self_iff.mpr ho0γ.symm
        have hxBack : (Circuit.X L.wOne).eval.1.mulVec
            (OneHotSimulates.ket (Function.update (encAssign145 L (βFOf γL)) L.wOne 1)) =
            Solution.XMeasCircuit.ket (encAssign145 L (βFOf γL)) := by
          simpa only [hclr1] using UnsignedGivens.evolve_X_ket L.wOne
            (Function.update (encAssign145 L (βFOf γL)) L.wOne 1)
        have hflBack : (flipAct145Circuit actFlipMask L).eval.1.mulVec
            (Solution.XMeasCircuit.ket (encAssign145 L (βFOf γL))) =
                Solution.XMeasCircuit.ket (encAssign145 L γL) := by
          rw [flipAct145Circuit_enc_ket actFlipMask L hSFγ]
          dsimp only [βFOf]; rw [flipAct145Assign_involutive]
        have hketEq : UnsignedGivens.ket (β₂Of γL) = OneHotSimulates.ket (β₂Of γL) := rfl
        have hketγ : UnsignedGivens.ket γL = Solution.XMeasCircuit.ket γL := rfl
        rw [(writeReg_fanout145_comm actFlipMask L β l).2, hketEq, hketγ, ketMapOp_mulVec_ket,
          ite_posE hSγ, StepEncK.eval_seq_mulVec, StepEncK.eval_seq_mulVec, hcFanU,
          hfanBack, hxBack, hflBack]
      · have hket0 : Solution.XMeasCircuit.ket β = UnsignedGivens.ket β := rfl
        rw [ite_negE hS, Matrix.mulVec_zero, Matrix.mulVec_zero, hket0,
          UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket, QRegister.embedUnitary_val,
          UnsignedGivens.embedMatrix_mulVec_ket, Matrix.mulVec_sum]
        symm; refine Finset.sum_eq_zero fun l _ ↦ ?_
        have hketL : UnsignedGivens.ket (UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)) =
            Solution.XMeasCircuit.ket (UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)) := rfl
        rw [Matrix.mulVec_smul, hketL, ketMapOp_mulVec_ket, ite_negE (mt (hsWr β l).mp hS),
          smul_zero]
    have hDecR := SubspaceStepU.congr rfl hCommTgt.symm
      (SubspaceStepU.mul_right uPhased.1 (dDec145Dyn_step () L))
    dsimp only [compactExtCoreDyn]
    exact SubspaceStepU.seq (dEnc145Dyn_step () L)
      (SubspaceStepU.seq (SubspaceStepU.of_circuit (Var := Unit) _ hMid1)
        (SubspaceStepU.seq (SubspaceStepU.of_diagProjSimulates hSimPush hCascClean)
          (SubspaceStepU.seq (SubspaceStepU.of_circuit (Var := Unit) _ hMid3) hDecR)))
  · dsimp only [wPhased, phase2Bal145PhasedBranch, phase2Bal145RawPhasedBranch]
    let cF := flipActCtrl10_145 actFlipMask c10
    have hpg : phaseGradientLowFactor 11 3 = phaseGradientFineLow 11 3 := rfl
    by_cases hph : ctrl10RawPhase145 negMask cF = true
    · simp only [cF, hph, ↓reduceIte, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hpg, hcatAff, affCascadeBranch_bal145_ctrl10ToTail146Idx, negOneUnitary_val,
        Matrix.smul_mulVec, Matrix.one_mulVec, negOneUnitary_val, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      funext G; simp [prodState, Solution.CircuitModular.prodStateOf]
    · simp only [cF, hph, Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [hpg, hcatAff, affCascadeBranch_bal145_ctrl10ToTail146Idx]
attribute [irreducible] compactCascadeCanDyn compactExtPreCircuit compactExtPostCircuit
attribute [irreducible] compactExtCoreDyn
/-- Relocated `(159 - d)`-inner-scratch compact Stage-2 core for arbitrary `L : Core145Layout`. -/
def compactStepCoreUnitDyn (d : ℕ) (hd : d ≤ 10) (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) {n : ℕ}
    (L : Core145Layout (159 - d) n) : DynamicCircuit Unit n :=
  (compactCanCoreUnitDyn d hd actFlipMask orbitalOf negMask).onRegister L.rFull

/-- Table-parametric `(159 - d)`-inner-scratch `Core145Bundle` (`0 ≤ d ≤ 10`). -/
noncomputable def compactParamCore145Bundle (d : ℕ) (hd : d ≤ 10)
    (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) :
    Core145Bundle (159 - d) (compactCoreTCount d) actFlipMask orbitalOf negMask where
  hk6 := by omega
  coreUnitDyn := compactStepCoreUnitDyn d hd actFlipMask orbitalOf negMask
  count_toff _ := by simp [compactStepCoreUnitDyn]
  count_t _ := by simp [compactStepCoreUnitDyn]
  simCore {n} L := by
    have : NeZero (2 ^ n) := ⟨(Nat.two_pow_pos n).ne'⟩
    have : NeZero (2 ^ (mCanCore d)) := ⟨(Nat.two_pow_pos _).ne'⟩
    have : NeZero (2 ^ (mCanCore d + d)) := ⟨(Nat.two_pow_pos _).ne'⟩
    let C := canCoreLayout d; let L_ext := extCanLayout d hd
    obtain ⟨wPhased, hSimExt, hBr⟩ :=
      diagProjSimulates_compactExtCoreDyn d hd actFlipMask orbitalOf negMask
    rw [← onRegister_trimLeftReg_compactCanCoreUnitDyn] at hSimExt
    let rC_3 := C.rSpin.concat C.rCat11 (OneHotMux.disj_sys_cat_of C.hsc C.hac)
    let rActC := rC_3.concat C.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of C.hsc C.hac)
    let uCan := rActC.embedUnitary (UnsignedGivens.muxCtrlUnitary wPhased)
    have huExtEq : (trimLeftReg (mCanCore d) d).embedUnitary uCan =
        ((L_ext.rSpin.concat L_ext.rCat11 (OneHotMux.disj_sys_cat_of L_ext.hsc L_ext.hac)).concat
          L_ext.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L_ext.hsc L_ext.hac)).embedUnitary
          (UnsignedGivens.muxCtrlUnitary wPhased) := by
      dsimp only [uCan]; rw [← QRegister.embedUnitary_compose]; congr 1
      refine CoherentAlias.qreg_ext fun idx ↦ Fin.addCases (fun sc ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.compose_apply]; dsimp only [rActC]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
        refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) sc
        · dsimp only [rC_3]; rw [QRegister.concat_apply_left, QRegister.concat_apply_left,
            L_ext.rSpin_eq, show L_ext.rFull _ = extWireMap d hd _ from rfl,
            extWireMap_val_of_lt d hd _ (by dsimp; omega)]
          simp [C, canCoreLayout, Core145Layout.rSpin]
        · dsimp only [rC_3]; rw [QRegister.concat_apply_right, QRegister.concat_apply_right,
            L_ext.rCat11_eq, show L_ext.rFull _ = extWireMap d hd _ from rfl,
            extWireMap_val_of_lt d hd _ (by dsimp; omega)]
          simp [C, canCoreLayout, Core145Layout.rCat11]
      · rw [QRegister.compose_apply]; dsimp only [rActC]
        rw [QRegister.concat_apply_right, QRegister.concat_apply_right, L_ext.rCtrl10_eq,
          show L_ext.rFull _ = extWireMap d hd _ from rfl,
          extWireMap_val_of_lt d hd _ (by dsimp; omega)]
        simp [C, canCoreLayout, Core145Layout.rCtrl10]
    rw [← huExtEq] at hSimExt
    have hCommCan : uCan.1 * ketPredProj (sValidCore C) = ketPredProj (sValidCore C) * uCan.1 := by
      refine embed_muxCtrl_comm_ketPredProj rC_3 C.rCtrl10
        (OneHotMux.disj_sysCat_ctrl_of C.hsc C.hac) wPhased (sValidCore C) fun β l ↦ ?_
      have hnSC_C (u : Fin 10) : C.rCtrl10 u ∉ Set.range rC_3.wires :=
        fun ⟨sc, hsc⟩ ↦
          QRegister.disjoint_iff.mp (OneHotMux.disj_sysCat_ctrl_of C.hsc C.hac) sc u hsc
      have hnSC_I (idx : Fin (159 - d)) : C.rInner idx ∉ Set.range rC_3.wires := by
        rintro ⟨sc, hsc⟩; revert hsc; refine Fin.addCases (fun i hsc ↦ ?_) (fun k hsc ↦ ?_) sc
        · dsimp only [rC_3] at hsc; rw [QRegister.concat_apply_left] at hsc
          have hv := congrArg Fin.val hsc
          simp [C, canCoreLayout, mCanCore, Core145Layout.rSpin, Core145Layout.rInner] at hv; omega
        · dsimp only [rC_3] at hsc; rw [QRegister.concat_apply_right] at hsc
          have hv := congrArg Fin.val hsc
          simp [C, canCoreLayout, mCanCore, Core145Layout.rCat11, Core145Layout.rInner] at hv
          omega
      have hpLoc :
        UnsignedGivens.localIdx C.rSelPair8 (UnsignedGivens.writeReg β rC_3 (basisBits (58 +
        11) l)) =
          UnsignedGivens.localIdx C.rSelPair8 β :=
        localIdx_congr C.rSelPair8 fun i ↦ UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _
          (hnSC_C (Lac2Fused184Select.selPair10 i))
      have hi (idx : Fin (159 - d)) :
          UnsignedGivens.writeReg β rC_3 (basisBits (58 + 11) l) (C.rInner idx) =
            β (C.rInner idx) :=
        UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnSC_I idx)
      dsimp only [sValidCore]; simp only [hpLoc, hi]
    have hSimCan : DiagProjSimulates (ketPredProj (sValidCore C)) uCan
        (compactCanCoreUnitDyn d hd actFlipMask orbitalOf negMask) := by
      refine diagProjSimulates_of_onRegister (trimLeftReg (mCanCore d) d) (sValidCore C)
        (sValid145 L_ext) uCan _ hSimExt hCommCan fun x ↦ ?_
      let g₀ := (trimLeftReg (mCanCore d) d).basisSplitEquiv.symm (x, 0)
      have hleft (w : Fin (mCanCore d)) :
          basisBits (mCanCore d + d) g₀ (trimLeftReg (mCanCore d) d w) =
            basisBits (mCanCore d) x w := by
        rw [← QRegister.basisBits_extractIndex, ← QRegister.basisSplitEquiv_apply_fst,
          Equiv.apply_symm_apply]
      have hright (w : Fin (mCanCore d + d)) (hw : mCanCore d ≤ w.val) :
          basisBits (mCanCore d + d) g₀ w = 0 := by
        have hnot : w ∉ Set.range (trimLeftReg (mCanCore d) d).wires := by
          rintro ⟨u, rfl⟩; exact Nat.not_le.mpr u.isLt hw
        have hsnd : ((trimLeftReg (mCanCore d) d).basisSplitEquiv g₀).2 = 0 := by simp [g₀]
        simpa only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply] using
          congrFun hsnd ⟨w, hnot⟩
      have hpEq : UnsignedGivens.localIdx L_ext.rSelPair8 (basisBits (mCanCore d + d) g₀) =
          UnsignedGivens.localIdx C.rSelPair8 (basisBits (mCanCore d) x) :=
        congrArg (basisBits 8).symm (funext fun i ↦ by
          rw [L_ext.rSelPair8_eq]
          have hs : (Lac2Fused184Select.selPair10 i).val = 2 + i.val := by fin_cases i <;> rfl
          have hwEq : L_ext.rFull ⟨60 + i.val, by omega⟩ =
              trimLeftReg (mCanCore d) d (C.rSelPair8 i) := by
            ext; rw [show L_ext.rFull _ = extWireMap d hd _ from rfl,
              extWireMap_val_of_lt d hd _ (by dsimp; omega)]
            simp [C, canCoreLayout, Core145Layout.rSelPair8, Core145Layout.rCtrl10, hs]; omega
          rw [hwEq, hleft])
      dsimp only [sValid145, sValidCore]; rw [hpEq]; refine and_congr_right fun _ ↦ ⟨fun hI j ↦ ?_,
        fun hC idx ↦ ?_⟩
      · by_cases hj : j.val < 14 - d
        · have hwEq : L_ext.rInner159 ⟨j.val, by omega⟩ =
              trimLeftReg (mCanCore d) d (C.rInner j) := by
            rw [L_ext.rInner159_eq]; ext
            rw [show L_ext.rFull _ = extWireMap d hd _ from rfl,
              extWireMap_val_of_lt d hd _ (by dsimp; omega)]
            simp [C, canCoreLayout, Core145Layout.rInner]
          have h0 := hI ⟨j.val, by omega⟩; rwa [hwEq, hleft] at h0
        · have hwEq : L_ext.rInner159 ⟨j.val + d, by omega⟩ =
              trimLeftReg (mCanCore d) d (C.rInner j) := by
            rw [L_ext.rInner159_eq]; ext
            rw [show L_ext.rFull _ = extWireMap d hd _ from rfl,
              extWireMap_val_of_ge d hd _ (by dsimp; omega)]
            simp [C, canCoreLayout, Core145Layout.rInner]; omega
          have h0 := hI ⟨j.val + d, by omega⟩; rwa [hwEq, hleft] at h0
      · rw [L_ext.rInner159_eq]
        by_cases h1 : idx.val < 14 - d
        · have hwEq : L_ext.rFull ⟨79 + idx.val, by omega⟩ =
              trimLeftReg (mCanCore d) d (C.rInner ⟨idx.val, by omega⟩) := by
            ext; rw [show L_ext.rFull _ = extWireMap d hd _ from rfl,
              extWireMap_val_of_lt d hd _ (by dsimp; omega)]
            simp [C, canCoreLayout, Core145Layout.rInner]
          rw [hwEq, hleft]; exact hC _
        · by_cases h2 : idx.val < 14
          · apply hright
            rw [show L_ext.rFull _ = extWireMap d hd _ from rfl,
              extWireMap_val_of_mid d hd _ (by dsimp; omega) (by dsimp; omega)]; omega
          · have hwEq : L_ext.rFull ⟨79 + idx.val, by omega⟩ =
                trimLeftReg (mCanCore d) d (C.rInner ⟨idx.val - d, by omega⟩) := by
              ext; rw [show L_ext.rFull _ = extWireMap d hd _ from rfl,
                extWireMap_val_of_ge d hd _ (by dsimp; omega)]
              simp [C, canCoreLayout, Core145Layout.rInner]; omega
            rw [hwEq, hleft]; exact hC _
    have hPushL := diagProjSimulates_onRegister L.rFull (sValidCore C) uCan
      (compactCanCoreUnitDyn d hd actFlipMask orbitalOf negMask) hSimCan
    have hSEq : ketPredProj (fun β ↦ sValidCore C (fun i ↦ β (L.rFull i))) =
        ketPredProj (sValidCore L) := ketPredProj_congr fun β ↦ by
      have hp : UnsignedGivens.localIdx C.rSelPair8 (fun i ↦ β (L.rFull i)) =
          UnsignedGivens.localIdx L.rSelPair8 β := by
        dsimp [UnsignedGivens.localIdx, C, canCoreLayout, Core145Layout.rSelPair8,
          Core145Layout.rCtrl10]
      dsimp only [sValidCore]; rw [hp]; rfl
    have hUEq : L.rFull.embedUnitary uCan =
        (((L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)).concat L.rCtrl10
          (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary
          (UnsignedGivens.muxCtrlUnitary wPhased)) := by
      dsimp only [uCan]; rw [← QRegister.embedUnitary_compose]; congr 1
      refine CoherentAlias.qreg_ext fun idx ↦ Fin.addCases (fun sc ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.compose_apply]; dsimp only [rActC]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
        refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) sc
        · dsimp only [rC_3]; rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
          simp [C, canCoreLayout, Core145Layout.rSpin]
        · dsimp only [rC_3]; rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
          simp [C, canCoreLayout, Core145Layout.rCat11]
      · rw [QRegister.compose_apply]; dsimp only [rActC]
        rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
        simp [C, canCoreLayout, Core145Layout.rCtrl10]
    rw [hSEq, hUEq] at hPushL; exact ⟨wPhased, hPushL, hBr⟩
attribute [irreducible] compactStepCoreUnitDyn

/-! ## Section 2: `57`-AND & `61`-AND `Core145Bundle` Instantiations -/

/-- Closed-form Bell-singlet two-pass `SELECT` `T`-count (excluding turnaround `pTurn`) with
`57`-AND router: `2 * compactCoreTCount d + 696 + 4 * (2 * 14 + 43 + 43) = 24788 + 896 * d +
8 * (d - 1)`. -/
def compactBellSelect57TCount (d : ℕ) : ℕ := 24788 + 896 * d + 8 * (d - 1)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactCore145Bundle
end
