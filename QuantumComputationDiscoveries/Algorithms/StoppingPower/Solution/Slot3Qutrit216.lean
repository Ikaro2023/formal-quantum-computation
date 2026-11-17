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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80RevCert
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MergedVepCoreSlice

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Slot3Exact216Oracle80
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Exact216Oracle80 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-!
# Exact `27 × 8 = 216` 3-Qutrit Slot-3 Momentum Oracle (`Slot3Exact216Oracle80`)

- **Sub-block A**: `wThird37` (`37 T` `{H, S, T}` qutrit synthesis), `cPrepQutrit2`
  (`39 T` / qutrit), and `uPrep3_216` / `dPrep3_216` (`tPrep216 = 2469 T`).
- **Sub-block B**: Ternary-decoded `73`-wire persistent unary context `fmkCtxUnary73Ternary`
  (`72` `TempAnd`s) wrapping `fmkMidKickInner353` (`1,476` `TempAnd`s) for
  `progMidKick216_437` (`1,548` `TempAnd`s = `6,192 T`).
- **Sub-block C**: `validStatic216_275` (`52` `TempAnd`s, without `< 65448` cutoff),
  `fwdPrep216_275` (`tFwd216 = 1649` `TempAnd`s), `midFixed216_437`
  (`tMidFixed216 = 47` `TempAnd`s), and `dSlot3Exact216` (`tSlot3Exact216 = 24510 T`, `0 .TOFF`).
- **Sub-block D**: Exact-`216` block-encoding weight `alphaSlot3_216 ≤ 20,123` Ha,
  `epsIntr = 27 / 10000000 ≤ 3 / 1000000`, `s3_hadamard_topBlock_coin6_216`, and
  `slot3Exact216Oracle80 : MomSingleSlotOracle 80 48 3`.
-/

namespace Slot3Exact216Oracle80

section ConfigSlot3Exact216Oracle80
set_option exponentiation.threshold 256

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real

section Slot3Exact216

/-! ## Sub-block C2: Exact-216 Core Involution, Catalyst Intertwining, `149`-Wire Reduction &
  `dSlot3Exact216` -/

section SubpartC2a
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open FullSysMomSlots0135Concrete
open Slot5MatrixAndScaleCert
open SpecsAux.DyadicSubgridToeplitz512AndShift
open TwosCompAndWire0Cancel DyadicQft64 DyadicQft64.PhasePerm
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open MomSlots35Slot3ProjNuclear

/-- Exact-216 Slot-3 core acceptance predicate (`coin = 6`, `ProjTwosGridState x`,
`validShellNu3 u22 s3`, and `sTrue * u38 + sTrue < cRad7Computable μ + 1`; NO `< 65448` cutoff). -/
noncomputable def s3Accept216 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : Bool :=
  let coin := (momCoinReg mPayload).extractIndex z
  let xSys := (momSysReg mPayload).extractIndex z
  let u22 := (s3U22Core hmPay).extractIndex z
  let s3 := (s3S3Core hmPay).extractIndex z
  let c8 := (s3C8Core hmPay).extractIndex z
  let f30 := (s3Fine30Core hmPay).extractIndex z
  let st0 := s3ProjStepHw (projAxisField xSys 0) (shellMagCoord3 u22 0) (signBit3 s3 0)
  let st1 := s3ProjStepHw (projAxisField xSys 1) (shellMagCoord3 u22 1) (signBit3 s3 1)
  let st2 := s3ProjStepHw (projAxisField xSys 2) (shellMagCoord3 u22 2) (signBit3 s3 2)
  let sTrue := st0.2.1 * st0.2.1 + st1.2.1 * st1.2.1 + st2.2.1 * st2.2.1
  let u38 := f30.val + 2 ^ 30 * c8.val
  let cRad := cRad7Computable (shellMu3 u22)
  decide (coin.val = 6) &&
    s3ProjGridBool xSys &&
    validShellNu3 u22 s3 &&
    decide (sTrue * u38 + sTrue < cRad + 1)

end SubpartC2a

section SubpartC2c

set_option maxRecDepth 2000

open MomSlot0CircuitHalf (padZeroBits)
open FullSysMomSlots0135Concrete (momCoreWires)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven shellMagCoord3 s3C8Core s3Fine30Core
  s3ShellMagCoord3_lt_128)
open StepBBlock0 (s3DitePos s3DiteNeg bitsVal_eq_of_testBit bitsVal_split_add seqClean_spec hmPay80
  embedAlpha107 embedAlpha107_fields padZeroBits149_clean padZeroBits149_lt)
open Prod57BoothHoist (boothConst57 p57ProjW p57S3W p57U38W p57MW p57OutW sTrue18WDefault
  sTrueRawValPBuf sTrueRawVal sTrue18FwdPBuf275 sTrue18RevPBuf275 boothAdd57_275 boothSub57_275
  sTrue18FwdPBuf275_spec sTrue18RevPBuf275_spec boothAdd57_275_spec boothSub57_275_spec)
open scoped Matrix BigOperators

open StepBOuter

def fwdPrep216_275 : TempPhaseProg 437 := .seq coinMuXor275 (.seq magUnpack275 (.seq
    validStatic216_275 (.seq axisStep3_275 (.seq sTrue18FwdPBuf275 (.seq boothAdd57_275
    accXor275)))))

/-- Static reverse uncomputation stages 12–18 (`1,164` `tempAnd`s). -/
def revUncomp216_275 : TempPhaseProg 437 := .seq accXor275 (.seq boothSub57_275 (.seq
    sTrue18RevPBuf275 (.seq axisStep3_275 (.seq validStatic216_275 (.seq magUnpack275
    coinMuXor275)))))

theorem fwdPrep216_275_def :
    fwdPrep216_275 = .seq coinMuXor275 (.seq magUnpack275 (.seq validStatic216_275
      (.seq axisStep3_275 (.seq sTrue18FwdPBuf275 (.seq boothAdd57_275 accXor275))))) := rfl

theorem revUncomp216_275_def :
    revUncomp216_275 = .seq accXor275 (.seq boothSub57_275 (.seq sTrue18RevPBuf275
      (.seq axisStep3_275 (.seq validStatic216_275 (.seq magUnpack275 coinMuXor275))))) := rfl

theorem fwdPrep216_275_evalBits (x : BitAssignment 437) :
    fwdPrep216_275.evalBits x = accXor275.evalBits (boothAdd57_275.evalBits
      (sTrue18FwdPBuf275.evalBits (axisStep3_275.evalBits
        (validStatic216_275.evalBits (magUnpack275.evalBits (coinMuXor275.evalBits x)))))) := by
  rw [fwdPrep216_275_def]
  repeat rw [tempPhaseProg216_seq_evalBits]

theorem revUncomp216_275_evalBits (x : BitAssignment 437) :
    revUncomp216_275.evalBits x = coinMuXor275.evalBits (magUnpack275.evalBits
      (validStatic216_275.evalBits (axisStep3_275.evalBits
        (sTrue18RevPBuf275.evalBits (boothSub57_275.evalBits (accXor275.evalBits x)))))) := by
  rw [revUncomp216_275_def]
  repeat rw [tempPhaseProg216_seq_evalBits]

attribute [local irreducible] progMidKick216_437

private def PresOut437 (S : ℕ → Prop) (α β : BitAssignment 437) : Prop :=
  ∀ q : Wire 437, ¬ S q.val → β q = α q

private theorem PresOut437.trans {S₁ S₂ : ℕ → Prop} {α β γ : BitAssignment 437}
    (h₁ : PresOut437 S₁ α β) (h₂ : PresOut437 S₂ β γ) :
    PresOut437 (fun n ↦ S₁ n ∨ S₂ n) α γ :=
  fun q hq ↦ (h₂ q fun h ↦ hq (.inr h)).trans (h₁ q fun h ↦ hq (.inl h))

private theorem PresOut437.of_mem {S B : ℕ → Prop} {α β : BitAssignment 437}
    (h : PresOut437 S α β) (hSB : ∀ n, B n → ¬ S n) {q : Wire 437} (hq : B q.val) :
    β q = α q :=
  h q (hSB q.val hq)

private theorem PresOut437.zero_of_mem {S B : ℕ → Prop} {α : BitAssignment 149}
    {β : BitAssignment 437} (h : PresOut437 S (padZeroBits (mClean := 288) α) β)
    (hGe : ∀ n, B n → 149 ≤ n) (hSB : ∀ n, B n → ¬ S n) {q : Wire 437} (hq : B q.val) :
    β q = 0 :=
  (h.of_mem hSB hq).trans (padZeroBits149_clean α q (by
    have := hGe q.val hq
    omega))

private structure Stage275 (S : ℕ → Prop) (p : TempPhaseProg 437) : Prop where
  valid : ValidCleanRem 437 (437 - 275) p
  sign : ∀ β, cleanRem 437 (437 - 275) β → p.evalSign β = 0
  clean : ∀ β, cleanRem 437 (437 - 275) β → cleanRem 437 (437 - 275) (p.evalBits β)
  pres : ∀ β, cleanRem 437 (437 - 275) β → PresOut437 S β (p.evalBits β)

private theorem Stage275.seq {S₁ S₂ : ℕ → Prop} {p₁ p₂ : TempPhaseProg 437}
    (h₁ : Stage275 S₁ p₁) (h₂ : Stage275 S₂ p₂) :
    Stage275 (fun n ↦ S₁ n ∨ S₂ n) (.seq p₁ p₂) := by
  obtain ⟨hv, _, hs, hcl, hb⟩ :=
    seqClean_spec (by decide) h₁.valid h₂.valid h₁.sign h₂.sign h₁.clean h₂.clean
  exact ⟨hv, hs, hcl, fun β hβ ↦ by
    rw [hb β]
    exact (h₁.pres β hβ).trans (h₂.pres _ (h₁.clean β hβ))⟩

private theorem Stage275.of_eq {S : ℕ → Prop} {p q : TempPhaseProg 437} (hp : p = q)
    (h : Stage275 S q) : Stage275 S p := hp ▸ h

private abbrev b216_1 (n : ℕ) : Prop := n = 198 ∨ (174 ≤ n ∧ n < 177)
private abbrev b216_2 (n : ℕ) : Prop := 177 ≤ n ∧ n < 198
private abbrev b216_3 (n : ℕ) : Prop := n = 258
private abbrev b216_4 (n : ℕ) : Prop := 150 ≤ n ∧ n < 174
private abbrev b216_5 (n : ℕ) : Prop := (199 ≤ n ∧ n < 201) ∨ (259 ≤ n ∧ n < 275)
private abbrev b216_6 (n : ℕ) : Prop := 201 ≤ n ∧ n < 258
private abbrev b216_7 (n : ℕ) : Prop := n = 149

private theorem b216_1_mu (j : Fin 3) : b216_1 (muW j).val := by
  dsimp [b216_1, muW]
  omega
private theorem b216_2_m (w : Fin 3) (b : Fin 7) : b216_2 (p57MW w b).val := by
  dsimp [b216_2, p57MW]
  omega
private theorem b216_4_pbuf (w : Fin 3) (b : Fin 8) : b216_4 (pBufW w b).val := by
  dsimp [b216_4, pBufW]
  omega
private theorem b216_5_strue (j : Fin 18) : b216_5 (sTrue18WDefault j).val :=
  sTrue18WDefault216_bounds j
private theorem b216_6_out (m : Fin 57) : b216_6 (p57OutW m).val := by
  dsimp [b216_6, p57OutW]
  omega

private theorem st275_coinMu : Stage275 b216_1 coinMuXor275 :=
  let h := coinMuXor275_spec.1
  ⟨h.1, h.2.1, h.2.2.1, fun β hcl q hq ↦ h.2.2.2 β hcl q fun hm ↦ by
    rcases hm with rfl | ⟨j, rfl⟩
    · exact hq (.inl rfl)
    · exact hq (b216_1_mu j)⟩
private theorem st275_mag : Stage275 b216_2 magUnpack275 :=
  let h := magUnpack275_spec.1
  ⟨h.1, h.2.1, h.2.2.1, fun β hcl q hq ↦ h.2.2.2 β hcl q fun ⟨w, b, hm⟩ ↦ hq (hm ▸ b216_2_m w b)⟩
private theorem st275_vs : Stage275 b216_3 validStatic216_275 :=
  let h := validStatic216_275_spec.1
  ⟨h.1, h.2.1, h.2.2.1, fun β hcl q hq ↦ h.2.2.2 β hcl q fun hm ↦ hq (congrArg Fin.val hm)⟩
private theorem st275_ax : Stage275 b216_4 axisStep3_275 :=
  let h := axisStep3_275_spec.1
  ⟨h.1, h.2.1, h.2.2.1,
    fun β hcl q hq ↦ h.2.2.2 β hcl q fun ⟨w, b, hm⟩ ↦ hq (hm ▸ b216_4_pbuf w b)⟩
private theorem st275_acc : Stage275 b216_7 accXor275 :=
  let h := accXor275_spec.1
  ⟨h.1, h.2.1, h.2.2.1, fun β hcl q hq ↦ h.2.2.2 β hcl q fun hm ↦ hq (congrArg Fin.val hm)⟩
private theorem st275_sfwd : Stage275 b216_5 sTrue18FwdPBuf275 :=
  let ⟨hv, _, hs, h⟩ := sTrue18FwdPBuf275_spec
  ⟨hv, hs, fun β hβ ↦ (h β hβ).1,
    fun β hβ q hq ↦ (h β hβ).2.1 q fun j hj ↦ hq (hj ▸ sTrue18WDefault216_bounds j)⟩
private theorem st275_srev : Stage275 b216_5 sTrue18RevPBuf275 :=
  let ⟨hv, _, hs, h⟩ := sTrue18RevPBuf275_spec
  ⟨hv, hs, fun β hβ ↦ (h β hβ).1,
    fun β hβ q hq ↦ (h β hβ).2.1 q fun j hj ↦ hq (hj ▸ sTrue18WDefault216_bounds j)⟩
private theorem st275_badd : Stage275 b216_6 boothAdd57_275 :=
  let ⟨hv, _, hs, h⟩ := boothAdd57_275_spec
  ⟨hv, hs, fun β hβ ↦ (h β hβ).1, fun β hβ q hq ↦ (h β hβ).2.1 q fun m hm ↦ hq (hm ▸ b216_6_out m)⟩
private theorem st275_bsub : Stage275 b216_6 boothSub57_275 :=
  let ⟨hv, _, hs, h⟩ := boothSub57_275_spec
  ⟨hv, hs, fun β hβ ↦ (h β hβ).1, fun β hβ q hq ↦ (h β hβ).2.1 q fun m hm ↦ hq (hm ▸ b216_6_out m)⟩

private def EqLt149 (α β : BitAssignment 437) : Prop :=
  ∀ q : Wire 437, q.val < 149 → β q = α q

private theorem EqLt149.of_pres {S : ℕ → Prop} {α β : BitAssignment 437}
    (h : PresOut437 S α β) (hS : ∀ n, n < 149 → ¬ S n) : EqLt149 α β :=
  fun q hq ↦ h q (hS q.val hq)

private theorem EqLt149.symm {α β : BitAssignment 437} (h : EqLt149 α β) : EqLt149 β α :=
  fun q hq ↦ (h q hq).symm

private theorem EqLt149.trans {α β γ : BitAssignment 437}
    (h₁ : EqLt149 α β) (h₂ : EqLt149 β γ) : EqLt149 α γ :=
  fun q hq ↦ (h₂ q hq).trans (h₁ q hq)

private theorem EqLt149.u22 {α β : BitAssignment 437} (h : EqLt149 α β) :
    getU22 β = getU22 α :=
  getU22_congr fun i ↦ h _ (by
    dsimp [u22WAux]
    omega)
private theorem EqLt149.coin {α β : BitAssignment 437} (h : EqLt149 α β) :
    (fun b ↦ β (coinW b)) = fun b ↦ α (coinW b) :=
  funext fun b ↦ h _ (by
    dsimp [coinW]
    omega)
private theorem EqLt149.u16 {α β : BitAssignment 437} (h : EqLt149 α β) :
    (fun i ↦ β (u16WAux i)) = fun i ↦ α (u16WAux i) :=
  funext fun i ↦ h _ (by
    dsimp [u16WAux]
    omega)
private theorem EqLt149.top7 {α β : BitAssignment 437} (h : EqLt149 α β) :
    (fun i ↦ β (top7W i)) = fun i ↦ α (top7W i) :=
  funext fun i ↦ h _ (by
    dsimp [top7W]
    omega)
private theorem EqLt149.s3 {α β : BitAssignment 437} (h : EqLt149 α β) (w : Fin 3) :
    β (p57S3W w) = α (p57S3W w) :=
  h _ (by
    dsimp [p57S3W]
    omega)
private theorem EqLt149.projFn {α β : BitAssignment 437} (h : EqLt149 α β) (w : Fin 3) :
    (fun b ↦ β (p57ProjW w b)) = fun b ↦ α (p57ProjW w b) :=
  funext fun b ↦ h _ (by
    dsimp [p57ProjW]
    omega)
private theorem EqLt149.proj {α β : BitAssignment 437} (h : EqLt149 α β) (w : Fin 3) :
    getProj β w = getProj α w :=
  getProj_congr fun b ↦ h _ (by
    dsimp [p57ProjW]
    omega)
private theorem EqLt149.u38 {α β : BitAssignment 437} (h : EqLt149 α β) :
    (fun k ↦ β (p57U38W k)) = fun k ↦ α (p57U38W k) :=
  funext fun k ↦ h _ (lt_trans (p57U38W216_lt107 k) (by decide))

set_option maxHeartbeats 1600000 in -- Large circuit/arithmetic proof
theorem fwdPrep216_275_spec :
    ValidCleanRem 437 (437 - 275) fwdPrep216_275 ∧
      (∀ β, cleanRem 437 (437 - 275) β → fwdPrep216_275.evalSign β = 0) ∧
      (∀ β, cleanRem 437 (437 - 275) β → cleanRem 437 (437 - 275) (fwdPrep216_275.evalBits β)) ∧
      (∀ α : BitAssignment 149,
        let γ := fwdPrep216_275.evalBits (padZeroBits (mClean := 288) α)
        (∀ k : Fin 149, γ ⟨k.val, by omega⟩ = α k) ∧ RetainedInv216 γ) := by
  have hcs := Stage275.of_eq fwdPrep216_275_def (st275_coinMu.seq (st275_mag.seq
    (st275_vs.seq (st275_ax.seq (st275_sfwd.seq (st275_badd.seq st275_acc))))))
  refine ⟨hcs.valid, hcs.sign, hcs.clean, fun α ↦ ?_⟩
  let β₀ := padZeroBits (mClean := 288) α
  have hcl₀ : cleanRem 437 (437 - 275) β₀ := cleanRem_anti (by decide) (padZeroBits149_clean α)
  have hz₀ : ∀ q : Wire 437, 149 ≤ q.val → β₀ q = 0 :=
    fun q hq ↦ padZeroBits149_clean α q (by omega)
  let β₁ := coinMuXor275.evalBits β₀
  let β₂ := magUnpack275.evalBits β₁
  let β₃ := validStatic216_275.evalBits β₂
  let β₄ := axisStep3_275.evalBits β₃
  let β₅ := sTrue18FwdPBuf275.evalBits β₄
  let β₆ := boothAdd57_275.evalBits β₅
  let β₇ := accXor275.evalBits β₆
  have hcl₁ : cleanRem 437 (437 - 275) β₁ := st275_coinMu.clean β₀ hcl₀
  have hcl₂ : cleanRem 437 (437 - 275) β₂ := st275_mag.clean β₁ hcl₁
  have hcl₃ : cleanRem 437 (437 - 275) β₃ := st275_vs.clean β₂ hcl₂
  have hcl₄ : cleanRem 437 (437 - 275) β₄ := st275_ax.clean β₃ hcl₃
  have hcl₅ : cleanRem 437 (437 - 275) β₅ := st275_sfwd.clean β₄ hcl₄
  have hcl₆ : cleanRem 437 (437 - 275) β₆ := st275_badd.clean β₅ hcl₅
  have hcl₇ : cleanRem 437 (437 - 275) β₇ := st275_acc.clean β₆ hcl₆
  have hp1 : PresOut437 b216_1 β₀ β₁ := st275_coinMu.pres β₀ hcl₀
  have hp2 : PresOut437 b216_2 β₁ β₂ := st275_mag.pres β₁ hcl₁
  have hp3 : PresOut437 b216_3 β₂ β₃ := st275_vs.pres β₂ hcl₂
  have hp4 : PresOut437 b216_4 β₃ β₄ := st275_ax.pres β₃ hcl₃
  have hp5 : PresOut437 b216_5 β₄ β₅ := st275_sfwd.pres β₄ hcl₄
  have hp6 : PresOut437 b216_6 β₅ β₆ := st275_badd.pres β₅ hcl₅
  have hp7 : PresOut437 b216_7 β₆ β₇ := st275_acc.pres β₆ hcl₆
  have hp02 := hp1.trans hp2
  have hp03 := hp02.trans hp3
  have hp04 := hp03.trans hp4
  have hp05 := hp04.trans hp5
  have hp06 := hp05.trans hp6
  have hp37 := hp4.trans (hp5.trans (hp6.trans hp7))
  have hp27 := hp3.trans hp37
  have hp17 := hp2.trans hp27
  have hlt1 := EqLt149.of_pres hp1 (by omega)
  have hlt2 := EqLt149.of_pres hp02 (by omega)
  have hlt3 := EqLt149.of_pres hp03 (by omega)
  have hlt4 := EqLt149.of_pres hp04 (by omega)
  have hlt5 := EqLt149.of_pres hp05 (by omega)
  have hlt6 := EqLt149.of_pres hp06 (by omega)
  have hlt7 := EqLt149.of_pres (hp06.trans hp7) (by omega)
  have hEq₇ : fwdPrep216_275.evalBits β₀ = β₇ := fwdPrep216_275_evalBits β₀
  rw [hEq₇]
  have hcoin₁ : β₁ coinOkW = if bitsVal (fun b ↦ β₀ (coinW b)) = 6 then 1 else 0 := by
    dsimp only [β₁]
    rw [(coinMuXor275_spec.2 β₀ hcl₀).1, hz₀ coinOkW (by decide), zero_add]
  have hcoin₇ : β₇ coinOkW = if bitsVal (fun b ↦ β₇ (coinW b)) = 6 then 1 else 0 := by
    rw [hp17 coinOkW (by decide), hlt7.coin, hcoin₁]
  have hmu₁ :
      ∀ j : Fin 3, β₁ (muW j) = if (shellMu3 (getU22 β₀)).testBit j.val then 1 else 0 :=
    fun j ↦ by
      dsimp only [β₁]
      rw [(coinMuXor275_spec.2 β₀ hcl₀).2 j,
        hz₀ (muW j) (by
          have := b216_1_mu j
          omega),
        zero_add, top7_eq_shellMu3_216 β₀]
  have hmu_val₁ : bitsVal (fun j ↦ β₁ (muW j)) = shellMu3 (getU22 β₁) := by
    rw [hlt1.u22]
    exact bitsVal_eq_of_testBit _ _ (lt_trans (shellMu3_lt_seven _) (by decide)) hmu₁
  have hmu₇ :
      ∀ j : Fin 3, β₇ (muW j) = if (shellMu3 (getU22 β₇)).testBit j.val then 1 else 0 :=
    fun j ↦ by rw [hp17.of_mem (by omega) (b216_1_mu j), hlt7.u22, hmu₁ j]
  have hm₂ : ∀ (w : Fin 3) (b : Fin 7),
      β₂ (p57MW w b) = if (shellMagCoord3 (getU22 β₀) w).testBit b.val then 1 else 0 :=
    fun w b ↦ by
      have he := magUnpack275_spec.2 β₁ hcl₁ hmu_val₁ w b
      dsimp only [β₂]
      rw [he, hp1.zero_of_mem (by omega) (by omega) (b216_2_m w b), zero_add]
      change (if (shellMagCoord3 (getU22 β₁) w).testBit b.val then (1 : ZMod 2) else 0) = _
      rw [hlt1.u22]
  have hm₇ : ∀ (w : Fin 3) (b : Fin 7),
      β₇ (p57MW w b) = if (shellMagCoord3 (getU22 β₇) w).testBit b.val then 1 else 0 :=
    fun w b ↦ by rw [hp27.of_mem (by omega) (b216_2_m w b), hlt7.u22, hm₂ w b]
  have hm_val₂ :
      ∀ w : Fin 3, bitsVal (fun b ↦ β₂ (p57MW w b)) = shellMagCoord3 (getU22 β₂) w :=
    fun w ↦ by
      rw [hlt2.u22]
      exact bitsVal_eq_of_testBit _ _ (s3ShellMagCoord3_lt_128 _ w) (hm₂ w)
  have hm_val₄ :
      ∀ w : Fin 3, bitsVal (fun b ↦ β₄ (p57MW w b)) = shellMagCoord3 (getU22 β₄) w :=
    fun w ↦ by
      rw [show (fun b ↦ β₄ (p57MW w b)) = fun b ↦ β₂ (p57MW w b) from
        funext fun b ↦ (hp3.trans hp4).of_mem (by omega) (b216_2_m w b),
        hm_val₂ w, hlt2.u22, hlt4.u22]
  have hvs₃ : β₃ validStaticW = validStaticVal216 β₇ := by
    have hmu₂ : bitsVal (fun j ↦ β₂ (muW j)) = shellMu3 (getU22 β₂) := by
      rw [show (fun j ↦ β₂ (muW j)) = fun j ↦ β₁ (muW j) from
        funext fun j ↦ hp2.of_mem (by omega) (b216_1_mu j), hmu_val₁, hlt1.u22, hlt2.u22]
    have he := validStatic216_275_spec.2.2 β₂ hcl₂ hmu₂ hm_val₂
    dsimp -failIfUnchanged only at he
    dsimp only [β₃]
    rw [he, (hp02 validStaticW (by decide)).trans (hz₀ validStaticW (by decide)),
      zero_add]
    have hc₂ : β₂ coinOkW = if bitsVal (fun b ↦ β₇ (coinW b)) = 6 then 1 else 0 := by
      rw [hp2 coinOkW (by decide), hcoin₁, hlt7.coin]
    change β₂ coinOkW * (if 32768 ≤ (getU22 β₂).val ∧ 2 ^ shellMu3 (getU22 β₂) ≤
      max (shellMagCoord3 (getU22 β₂) 0) (max (shellMagCoord3 (getU22 β₂) 1)
      (shellMagCoord3 (getU22 β₂) 2)) ∧ (∀ w : Fin 3, ¬(shellMagCoord3 (getU22 β₂) w =
      0 ∧ (β₂ (p57S3W w)).val = 1)) then 1 else 0) = validStaticVal216 β₇
    unfold validStaticVal216
    simp only [hc₂, hlt2.u22, hlt7.u22, fun w ↦ (hlt7.symm.trans hlt2).s3 w]
  have hpbuf₄ : ∀ (w : Fin 3) (b : Fin 8), β₄ (pBufW w b) = if (axisFastVal
      (getProj β₄ w) (shellMagCoord3 (getU22 β₄) w) (β₄ (p57S3W w)).val).testBit b.val
      then 1 else 0 := fun w b ↦ by
    dsimp only [β₄]
    rw [axisStep3_275_spec.2.2 β₃ hcl₃ w b,
      hp03.zero_of_mem (by omega) (by omega) (b216_4_pbuf w b), zero_add,
      show (⟨bitsVal (fun j ↦ β₃ (p57ProjW w j)), bitsVal_lt_two_pow _⟩ : Fin 256) =
        getProj β₄ w from Fin.ext (congrArg bitsVal ((hlt4.symm.trans hlt3).projFn w)),
      show bitsVal (fun j ↦ β₃ (p57MW w j)) = shellMagCoord3 (getU22 β₄) w by
        rw [show (fun j ↦ β₃ (p57MW w j)) = fun j ↦ β₂ (p57MW w j) from
          funext fun j ↦ hp3.of_mem (by omega) (b216_2_m w j), hm_val₂ w, hlt2.u22, hlt4.u22],
      (hlt4.symm.trans hlt3).s3 w]
  have hpbuf₇ : ∀ (w : Fin 3) (b : Fin 8), β₇ (pBufW w b) = if (axisFastVal
      (getProj β₇ w) (shellMagCoord3 (getU22 β₇) w) (β₇ (p57S3W w)).val).testBit b.val
      then 1 else 0 := fun w b ↦ by
    rw [(hp5.trans (hp6.trans hp7)).of_mem (by omega) (b216_4_pbuf w b), hpbuf₄ w b,
      (hlt7.symm.trans hlt4).proj w, hlt4.u22, hlt7.u22, (hlt7.symm.trans hlt4).s3 w]
  have hstrue₅ : bitsVal (fun j ↦ β₅ (sTrue18WDefault j)) = sTrueRawVal β₇ := by
    rw [(sTrue18FwdPBuf275_spec.2.2.2 β₄ hcl₄).2.2
      (fun j ↦ hp04.zero_of_mem (by omega) (by omega) (b216_5_strue j)),
      elecsTrueRawValPBuf_eq β₄ hm_val₄ (fun w ↦ hpbuf₄ w ⟨7, by decide⟩),
      sTrueRawVal216_congr (fun w b ↦ congrFun ((hlt7.symm.trans hlt4).projFn w) b)
        (fun w b ↦ ((hp3.trans hp4).of_mem (by omega) (b216_2_m w b)).trans
          (hp27.of_mem (by omega) (b216_2_m w b)).symm)
        (fun w ↦ (hlt7.symm.trans hlt4).s3 w)]
  have hstrue₇ : bitsVal (fun j ↦ β₇ (sTrue18WDefault j)) = sTrueRawVal β₇ := by
    rw [show (fun j ↦ β₇ (sTrue18WDefault j)) = fun j ↦ β₅ (sTrue18WDefault j) from
      funext fun j ↦ (hp6.trans hp7).of_mem (by omega) (b216_5_strue j), hstrue₅]
  have hprod₆ : bitsVal (fun m ↦ β₆ (p57OutW m)) = prod57Val216 β₇ := by
    rw [(boothAdd57_275_spec.2.2.2 β₅ hcl₅).2.2
      (fun m ↦ hp05.zero_of_mem (by omega) (by omega) (b216_6_out m)),
      hstrue₅, (hlt7.symm.trans hlt5).u38]
    rfl
  have hacc₇ : β₇ accWAux = accVal216 β₇ := by
    have hmu₆ : bitsVal (fun i ↦ β₆ (muW i)) = shellMu3 (getU22 β₇) := by
      rw [show (fun i ↦ β₆ (muW i)) = fun i ↦ β₁ (muW i) from
        funext fun i ↦ (hp2.trans (hp3.trans (hp4.trans (hp5.trans hp6)))).of_mem
          (by omega) (b216_1_mu i), hmu_val₁, hlt1.u22, hlt7.u22]
    dsimp only [β₇]
    rw [accXor275_spec.2.2 β₆ hcl₆ (shellMu3 (getU22 β₇)) (shellMu3_lt_seven _) hmu₆,
      (hp06 accWAux (by decide)).trans (hz₀ accWAux (by decide)), zero_add,
      (hp4.trans (hp5.trans hp6)) validStaticW (by decide), hvs₃, hprod₆]
    have hp_all : (∀ w : Fin 3, bitsVal (fun b ↦ β₆ (p57ProjW w b)) ≠ 128) ↔
        (∀ w : Fin 3, (getProj β₇ w).val ≠ 128) :=
      forall_congr' fun w ↦ by
        rw [(hlt7.symm.trans hlt6).projFn w]
        rfl
    simp only [hp_all]
    rfl
  exact ⟨fun k ↦ (hlt7 ⟨k.val, by omega⟩ k.isLt).trans (padZeroBits149_lt α k),
    ⟨hcl₇, hcoin₇, hmu₇, hm₇,
      (hp37 validStaticW (by decide)).trans hvs₃, hstrue₇,
      (bitsVal_congr_fn (funext fun m ↦ hp7.of_mem (by omega) (b216_6_out m))).trans hprod₆,
      hpbuf₇, hacc₇⟩⟩

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
theorem revUncomp216_275_spec :
    ValidCleanRem 437 (437 - 275) revUncomp216_275 ∧
      (∀ γ, cleanRem 437 (437 - 275) γ → revUncomp216_275.evalSign γ = 0) ∧
      (∀ γ, cleanRem 437 (437 - 275) γ → cleanRem 437 (437 - 275) (revUncomp216_275.evalBits γ)) ∧
      (∀ γ, RetainedInv216 γ →
        revUncomp216_275.evalBits γ =
          padZeroBits (mClean := 288) (fun k : Fin 149 ↦ γ ⟨k.val, by omega⟩)) := by
  have hcs := Stage275.of_eq revUncomp216_275_def (st275_acc.seq (st275_bsub.seq
    (st275_srev.seq (st275_ax.seq (st275_vs.seq (st275_mag.seq st275_coinMu))))))
  refine ⟨hcs.valid, hcs.sign, hcs.clean, fun γ₀ hInv ↦ ?_⟩
  have hcl₀ := hInv.hcl
  let γ₁ := accXor275.evalBits γ₀
  let γ₂ := boothSub57_275.evalBits γ₁
  let γ₃ := sTrue18RevPBuf275.evalBits γ₂
  let γ₄ := axisStep3_275.evalBits γ₃
  let γ₅ := validStatic216_275.evalBits γ₄
  let γ₆ := magUnpack275.evalBits γ₅
  let γ₇ := coinMuXor275.evalBits γ₆
  have hcl₁ : cleanRem 437 (437 - 275) γ₁ := st275_acc.clean γ₀ hcl₀
  have hcl₂ : cleanRem 437 (437 - 275) γ₂ := st275_bsub.clean γ₁ hcl₁
  have hcl₃ : cleanRem 437 (437 - 275) γ₃ := st275_srev.clean γ₂ hcl₂
  have hcl₄ : cleanRem 437 (437 - 275) γ₄ := st275_ax.clean γ₃ hcl₃
  have hcl₅ : cleanRem 437 (437 - 275) γ₅ := st275_vs.clean γ₄ hcl₄
  have hcl₆ : cleanRem 437 (437 - 275) γ₆ := st275_mag.clean γ₅ hcl₅
  have hcl₇ : cleanRem 437 (437 - 275) γ₇ := st275_coinMu.clean γ₆ hcl₆
  have gp1 : PresOut437 b216_7 γ₀ γ₁ := st275_acc.pres γ₀ hcl₀
  have gp2 : PresOut437 b216_6 γ₁ γ₂ := st275_bsub.pres γ₁ hcl₁
  have gp3 : PresOut437 b216_5 γ₂ γ₃ := st275_srev.pres γ₂ hcl₂
  have gp4 : PresOut437 b216_4 γ₃ γ₄ := st275_ax.pres γ₃ hcl₃
  have gp5 : PresOut437 b216_3 γ₄ γ₅ := st275_vs.pres γ₄ hcl₄
  have gp6 : PresOut437 b216_2 γ₅ γ₆ := st275_mag.pres γ₅ hcl₅
  have gp7 : PresOut437 b216_1 γ₆ γ₇ := st275_coinMu.pres γ₆ hcl₆
  have gp02 := gp1.trans gp2
  have gp03 := gp02.trans gp3
  have gp04 := gp03.trans gp4
  have gp05 := gp04.trans gp5
  have gp06 := gp05.trans gp6
  have gp57 := gp6.trans gp7
  have gp47 := gp5.trans gp57
  have gp37 := gp4.trans gp47
  have gp27 := gp3.trans gp37
  have glt1 := EqLt149.of_pres gp1 (by omega)
  have glt2 := EqLt149.of_pres gp02 (by omega)
  have glt3 := EqLt149.of_pres gp03 (by omega)
  have glt4 := EqLt149.of_pres gp04 (by omega)
  have glt5 := EqLt149.of_pres gp05 (by omega)
  have glt6 := EqLt149.of_pres gp06 (by omega)
  have glt7 := EqLt149.of_pres (gp06.trans gp7) (by omega)
  have hEq₇ : revUncomp216_275.evalBits γ₀ = γ₇ := revUncomp216_275_evalBits γ₀
  rw [hEq₇]
  refine eq_padZeroBits149_216_of_lt_and_ge γ₇ _
    (fun k ↦ glt7 ⟨k.val, by omega⟩ k.isLt) (fun q hq ↦ ?_)
  by_cases h275 : 275 ≤ q.val
  · exact hcl₇ q (by omega)
  by_cases h149 : q.val = 149
  · rw [show q = accWAux from Fin.ext h149, (gp2.trans gp27) accWAux (by decide)]
    dsimp only [γ₁]
    rw [accXor275_spec.2.2 γ₀ hcl₀ (shellMu3 (getU22 γ₀)) (shellMu3_lt_seven _) hInv.mu_val,
      hInv.hacc, hInv.hvs, hInv.hprod]
    exact zMod2_216_add_self _
  by_cases h150 : 150 ≤ q.val ∧ q.val < 174
  · let w : Fin 3 := ⟨(q.val - 150) / 8, by omega⟩
    let b : Fin 8 := ⟨(q.val - 150) % 8, by omega⟩
    rw [show q = pBufW w b from Fin.ext (by
        dsimp [pBufW, w, b]
        omega),
      gp47.of_mem (by omega) (b216_4_pbuf w b)]
    dsimp only [γ₄]
    rw [axisStep3_275_spec.2.2 γ₃ hcl₃ w b,
      gp03.of_mem (by omega) (b216_4_pbuf w b), hInv.hpbuf w b,
      show (⟨bitsVal (fun j ↦ γ₃ (p57ProjW w j)), bitsVal_lt_two_pow _⟩ : Fin 256) =
        getProj γ₀ w from Fin.ext (congrArg bitsVal (glt3.projFn w)),
      show bitsVal (fun j ↦ γ₃ (p57MW w j)) = shellMagCoord3 (getU22 γ₀) w by
        rw [show (fun j ↦ γ₃ (p57MW w j)) = fun j ↦ γ₀ (p57MW w j) from
          funext fun j ↦ gp03.of_mem (by omega) (b216_2_m w j), hInv.m_val w],
      glt3.s3 w]
    exact zMod2_216_add_self _
  by_cases h174 : 174 ≤ q.val ∧ q.val < 177
  · let j : Fin 3 := ⟨q.val - 174, by omega⟩
    rw [show q = muW j from Fin.ext (by
      dsimp [muW, j]
      omega)]
    dsimp only [γ₇]
    rw [(coinMuXor275_spec.2 γ₆ hcl₆).2 j, gp06.of_mem (by omega) (b216_1_mu j), hInv.hmu j]
    simp only [glt6.top7]
    rw [top7_eq_shellMu3_216 γ₀]
    exact zMod2_216_add_self _
  by_cases h177 : 177 ≤ q.val ∧ q.val < 198
  · let w : Fin 3 := ⟨(q.val - 177) / 7, by omega⟩
    let b : Fin 7 := ⟨(q.val - 177) % 7, by omega⟩
    have hmu₅ : bitsVal (fun j ↦ γ₅ (muW j)) = shellMu3 (getU22 γ₅) := by
      rw [show (fun j ↦ γ₅ (muW j)) = fun j ↦ γ₀ (muW j) from
        funext fun j ↦ gp05.of_mem (by omega) (b216_1_mu j), hInv.mu_val, glt5.u22]
    have he := magUnpack275_spec.2 γ₅ hcl₅ hmu₅ w b
    rw [show q = p57MW w b from Fin.ext (by
        dsimp [p57MW, w, b]
        omega),
      gp7.of_mem (by omega) (b216_2_m w b)]
    dsimp only [γ₆]
    rw [he, gp05.of_mem (by omega) (b216_2_m w b), hInv.hm w b]
    change (if (shellMagCoord3 (getU22 γ₀) w).testBit b.val then (1 : ZMod 2) else 0) +
      (if (shellMagCoord3 (getU22 γ₅) w).testBit b.val then 1 else 0) = 0
    rw [glt5.u22]
    exact zMod2_216_add_self _
  by_cases h198 : q.val = 198
  · rw [show q = coinOkW from Fin.ext h198]
    dsimp only [γ₇]
    rw [(coinMuXor275_spec.2 γ₆ hcl₆).1, gp06 coinOkW (by decide), hInv.hcoin, glt6.coin]
    exact zMod2_216_add_self _
  by_cases h201 : 201 ≤ q.val ∧ q.val < 258
  · let m : Fin 57 := ⟨q.val - 201, by omega⟩
    have hout₁ : bitsVal (fun m ↦ γ₁ (p57OutW m)) = bitsVal (fun j ↦ γ₁ (sTrue18WDefault j)) *
        (bitsVal (fun k ↦ γ₁ (p57U38W k)) + 1) + boothConst57 := by
      rw [show (fun m ↦ γ₁ (p57OutW m)) = fun m ↦ γ₀ (p57OutW m) from
          funext fun m ↦ gp1.of_mem (by omega) (b216_6_out m),
        show (fun j ↦ γ₁ (sTrue18WDefault j)) = fun j ↦ γ₀ (sTrue18WDefault j) from
          funext fun j ↦ gp1.of_mem (by omega) (b216_5_strue j),
        glt1.u38, hInv.hprod, hInv.hstrue]
      rfl
    rw [show q = p57OutW m from Fin.ext (by
        dsimp [p57OutW, m]
        omega),
      gp27.of_mem (by omega) (b216_6_out m)]
    exact (boothSub57_275_spec.2.2.2 γ₁ hcl₁).2.2 hout₁ m
  by_cases h258 : q.val = 258
  · have hmu₄ : bitsVal (fun j ↦ γ₄ (muW j)) = shellMu3 (getU22 γ₄) := by
      rw [show (fun j ↦ γ₄ (muW j)) = fun j ↦ γ₀ (muW j) from
        funext fun j ↦ gp04.of_mem (by omega) (b216_1_mu j), hInv.mu_val, glt4.u22]
    have hm₄ : ∀ w : Fin 3, bitsVal (fun b ↦ γ₄ (p57MW w b)) = shellMagCoord3 (getU22 γ₄) w :=
      fun w ↦ by
        rw [show (fun b ↦ γ₄ (p57MW w b)) = fun j ↦ γ₀ (p57MW w j) from
          funext fun b ↦ gp04.of_mem (by omega) (b216_2_m w b), hInv.m_val w, glt4.u22]
    have he := validStatic216_275_spec.2.2 γ₄ hcl₄ hmu₄ hm₄
    dsimp only at he
    rw [show q = validStaticW from Fin.ext h258, gp57 validStaticW (by decide)]
    dsimp only [γ₅]
    rw [he, gp04 validStaticW (by decide), hInv.hvs]
    change validStaticVal216 γ₀ + γ₄ coinOkW * (if 32768 ≤ (getU22 γ₄).val ∧ 2 ^
      shellMu3 (getU22 γ₄) ≤ max (shellMagCoord3 (getU22 γ₄) 0) (max (shellMagCoord3
      (getU22 γ₄) 1) (shellMagCoord3 (getU22 γ₄) 2)) ∧ (∀ w : Fin 3, ¬(shellMagCoord3
      (getU22 γ₄) w = 0 ∧ (γ₄ (p57S3W w)).val = 1)) then 1 else 0) = 0
    rw [gp04 coinOkW (by decide), hInv.hcoin]
    simp only [glt4.u22, glt4.s3]
    exact zMod2_216_add_self _
  have hs_mem : ∃ j : Fin 18, q = sTrue18WDefault j := by
    by_cases h199 : 199 ≤ q.val ∧ q.val < 201
    · refine ⟨⟨q.val - 199 + 16, by omega⟩, Fin.ext ?_⟩
      dsimp [sTrue18WDefault]
      all_goals
        omega
    · refine ⟨⟨q.val - 259, by omega⟩, Fin.ext ?_⟩
      dsimp [sTrue18WDefault]
      try split_ifs
      all_goals
        dsimp -failIfUnchanged
        omega
  obtain ⟨j, rfl⟩ := hs_mem
  have hst₂ : bitsVal (fun i ↦ γ₂ (sTrue18WDefault i)) = sTrueRawValPBuf γ₂ := by
    rw [show (fun i ↦ γ₂ (sTrue18WDefault i)) = fun i ↦ γ₀ (sTrue18WDefault i) from
        funext fun i ↦ gp02.of_mem (by omega) (b216_5_strue i),
      sTrueRawValPBuf_congr
        (fun w ↦ glt2 _ (by
          dsimp [p57ProjW]
          omega))
        (fun w ↦ gp02.of_mem (by omega) (b216_4_pbuf w ⟨7, by decide⟩))
        glt2.s3
        (fun w b ↦ gp02.of_mem (by omega) (b216_2_m w b)),
      elecsTrueRawValPBuf_eq γ₀ hInv.m_val (fun w ↦ hInv.hpbuf w ⟨7, by decide⟩),
      hInv.hstrue]
  rw [gp37.of_mem (by omega) (b216_5_strue j)]
  exact (sTrue18RevPBuf275_spec.2.2.2 γ₂ hcl₂).2.2 hst₂ j
attribute [local irreducible] fwdPrep216_275 revUncomp216_275

theorem u38_216_val_eq (α107 : BitAssignment 107) {γ : BitAssignment 437}
    (hlt107 : ∀ k : Fin 107, γ ⟨k.val, by omega⟩ = α107 k) :
    let z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
    bitsVal (fun k : Fin 38 ↦ γ (p57U38W k)) =
      ((s3Fine30Core hmPay80).extractIndex z80).val +
        2 ^ 30 * ((s3C8Core hmPay80).extractIndex z80).val := by
  intro z80
  obtain ⟨_, _, _, _, hC8, hF30, _, _⟩ := embedAlpha107_fields α107
  have hsp := bitsVal_split_add 30 8 (fun k : Fin (30 + 8) ↦ γ (p57U38W k))
  change bitsVal (fun k : Fin 38 ↦ γ (p57U38W k)) =
    bitsVal (fun i : Fin 30 ↦ γ (p57U38W ⟨i.val, by omega⟩)) +
      2 ^ 30 * bitsVal (fun j : Fin 8 ↦ γ (p57U38W ⟨30 + j.val, by omega⟩)) at hsp
  have hf_eq : (fun i : Fin 30 ↦ γ (p57U38W ⟨i.val, by omega⟩)) =
      fun i : Fin 30 ↦ α107 ⟨60 + i.val, by omega⟩ := funext fun i ↦ by
    have hp : p57U38W ⟨i.val, by omega⟩ = ⟨60 + i.val, by omega⟩ := by
      dsimp [p57U38W]; rw [s3DitePos i.isLt]
    rw [hp, hlt107 ⟨60 + i.val, by omega⟩]
  have hc_eq : (fun j : Fin 8 ↦ γ (p57U38W ⟨30 + j.val, by omega⟩)) =
      fun j : Fin 8 ↦ α107 ⟨52 + j.val, by omega⟩ := funext fun j ↦ by
    have hp : p57U38W ⟨30 + j.val, by omega⟩ = ⟨52 + j.val, by omega⟩ := by
      dsimp [p57U38W]; rw [s3DiteNeg (by omega)]; exact Fin.ext (by dsimp; omega)
    rw [hp, hlt107 ⟨52 + j.val, by omega⟩]
  rw [hsp, hf_eq, hc_eq, hF30, hC8]

end SubpartC2c

/-! ## Sub-block D: Exact-`216` Weight `alphaSlot3_216 ≤ 20,123`, Top-Block Collapse &
  `slot3Exact216Oracle80` -/

section SubpartD

open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open MomSlots35Coulomb
open ModWrapCoarse8PureMomentum
open Slot5MatrixAndScaleCert
open SpecsAux.DyadicSubgridToeplitz512AndShift
open TwosCompAndWire0Cancel DyadicQft64 DyadicQft64.PhasePerm
open OctahedralOrbit
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open MomSlots35Slot3ProjNuclear
open scoped Matrix BigOperators Matrix.Norms.L2Operator NNReal ComplexOrder

attribute [local irreducible] box3D nonzeroBox3D

noncomputable def bTwosSlot3_216 (cfg : SpecsAux.SpecMirror.Configuration) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  open Classical in
  Matrix.of fun x y ↦
    if ProjTwosGridState x ∧ ProjTwosGridState y ∧
        (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
          elecAxisField x i w = elecAxisField y i w) then
      s3SynthStructureFactor216 42 cfg
        (twosMomentum x .projectile - twosMomentum y .projectile) *
      (dampedModWrapKernelApprox 38 36 127 (2 / 42) 2
        (twosMomentum x .projectile - twosMomentum y .projectile) : ℂ)
    else 0

theorem norm_s3ProjWeightedOp_le
    (F : (Fin 3 → ℤ) → ℂ) (C : ℝ) (hC_nn : 0 ≤ C)
    (hF_le : ∀ Δ : Fin 3 → ℤ, ‖F Δ‖ ≤ C) :
    let A : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
      open Classical in
      Matrix.of fun x y ↦
        if ProjTwosGridState x ∧ ProjTwosGridState y ∧
            (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
              elecAxisField x i w = elecAxisField y i w) then
          F (twosMomentum x .projectile - twosMomentum y .projectile) *
            (dampedModWrapKernelApprox 38 36 127 (2 / 42) 2
              (twosMomentum x .projectile - twosMomentum y .projectile) : ℂ)
        else 0
    ‖A‖ ≤ (8192 * C * (2 / 42 : ℝ)) * coulombCoarse8PreOAAProb 127 8192 := by
  intro A
  let M_val : (Fin 3 → ℤ) → Operator (2 ^ SpecsAux.SpecMirror.systemQubits) := fun ν ↦
    open Classical in
    Matrix.of fun x y ↦
      if ProjTwosGridState x ∧ ProjTwosGridState y ∧
          (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
            elecAxisField x i w = elecAxisField y i w) ∧
          modFold3D 127 (twosMomentum x .projectile - twosMomentum y .projectile) = ν then
        F (twosMomentum x .projectile - twosMomentum y .projectile) *
          (dampedModWrapKernelApprox 38 36 127 (2 / 42) 2
            (twosMomentum x .projectile - twosMomentum y .projectile) : ℂ)
      else 0
  have hsub_box : ∀ {x y}, ProjTwosGridState x → ProjTwosGridState y →
      twosMomentum x .projectile - twosMomentum y .projectile ∈ box3D (2 * (127 : ℤ)) :=
    fun hx hy ↦ mk_mem_box3D3 fun w ↦ by
      have := bounds_of_mem_box3D3 (twosMomentum_proj_mem_box3D_127 hx) w
      have := bounds_of_mem_box3D3 (twosMomentum_proj_mem_box3D_127 hy) w
      dsimp
      omega
  have hM_nz : ∀ {ν x y}, M_val ν x y ≠ 0 →
      ProjTwosGridState x ∧ ProjTwosGridState y ∧
      (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
        elecAxisField x i w = elecAxisField y i w) ∧
      modFold3D 127 (twosMomentum x .projectile - twosMomentum y .projectile) = ν :=
    fun h ↦ by_contra fun hnc ↦ h (by
      classical
      dsimp [M_val]
      exact ite_false_eq hnc _ _)
  have hpart : A = ∑ ν ∈ nonzeroBox3D (127 : ℤ), M_val ν := by
    classical
    dsimp only [A]
    ext x y
    rw [operator_sum_apply, Matrix.of_apply]
    by_cases hcond : ProjTwosGridState x ∧ ProjTwosGridState y ∧
        (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
          elecAxisField x i w = elecAxisField y i w)
    · rw [ite_true_eq hcond]
      set Δ : Fin 3 → ℤ := twosMomentum x .projectile - twosMomentum y .projectile
      by_cases hΔ : Δ = 0
      · have hfold0 : modFold3D 127 Δ = 0 := by
          rw [hΔ]
          ext w
          simp [modFold3D, modFoldCoord, modWrapCoord]
        rw [Finset.sum_eq_zero fun ν hν ↦ by
            dsimp [M_val]
            exact ite_false_eq (fun h ↦
              (ne_zero_of_mem_nonzeroBox3D3 hν) (h.2.2.2.symm.trans hfold0)) _ _,
          hΔ, dampedModWrapKernelApprox_zero]
        simp
      · have hmem : modFold3D 127 Δ ∈ nonzeroBox3D (127 : ℤ) :=
          modFold3D_mem_nonzeroBox3D 127
            (mk_mem_nonzeroBox3D3 hΔ (bounds_of_mem_box3D3 (hsub_box hcond.1 hcond.2.1)))
        rw [Finset.sum_eq_single (modFold3D 127 Δ)
          (fun ν _ hne ↦ by
            dsimp [M_val]
            exact ite_false_eq (fun h ↦ hne h.2.2.2.symm) _ _)
          (fun hnot ↦ (hnot hmem).elim)]
        dsimp [M_val]
        exact (ite_true_eq ⟨hcond.1, hcond.2.1, hcond.2.2, rfl⟩ _ _).symm
    · rw [ite_false_eq hcond, eq_comm]
      refine Finset.sum_eq_zero fun ν _ ↦ ?_
      dsimp [M_val]
      exact ite_false_eq (fun h ↦ hcond ⟨h.1, h.2.1, h.2.2.1⟩) _ _
  have hpiece : ∀ ν ∈ nonzeroBox3D (127 : ℤ), ‖M_val ν‖ ≤ C * (2 * coarseBoxRadKernel8 ν) := by
    intro ν hν_mem
    have hB_nn : 0 ≤ C * (2 * coarseBoxRadKernel8 ν) := mul_nonneg hC_nn (by
      unfold coarseBoxRadKernel8
      positivity)
    refine norm_le_of_weightedPartialPerm (M_val ν) hB_nn (fun x y₁ y₂ h1 h2 ↦ ?_)
      (fun x₁ x₂ y h1 h2 ↦ ?_) fun x y ↦ ?_
    · rcases hM_nz h1, hM_nz h2 with ⟨⟨hx, hy₁, he₁, hf₁⟩, ⟨_, hy₂, he₂, hf₂⟩⟩
      exact systemQubits_eq_of_fields (fun i w ↦ (he₁ i w).symm.trans (he₂ i w)) fun w ↦
        twosComp8Int_injective (congrFun (modFold3D_sub_inj_right 127
          (twosMomentum_proj_mem_box3D_127 hx) (twosMomentum_proj_mem_box3D_127 hy₁)
          (twosMomentum_proj_mem_box3D_127 hy₂) (hf₁.trans hf₂.symm)) w)
    · rcases hM_nz h1, hM_nz h2 with ⟨⟨hx₁, hy, he₁, hf₁⟩, ⟨hx₂, _, he₂, hf₂⟩⟩
      exact systemQubits_eq_of_fields (fun i w ↦ (he₁ i w).trans (he₂ i w).symm) fun w ↦
        twosComp8Int_injective (congrFun (modFold3D_sub_inj_left 127
          (twosMomentum_proj_mem_box3D_127 hx₁) (twosMomentum_proj_mem_box3D_127 hx₂)
          (twosMomentum_proj_mem_box3D_127 hy) (hf₁.trans hf₂.symm)) w)
    · dsimp [M_val]
      split_ifs with hc
      · have hk_nn : 0 ≤ dampedModWrapKernelApprox 38 36 127 (2 / 42) 2
            (twosMomentum x .projectile - twosMomentum y .projectile) := by
          rw [dampedModWrapKernelApprox_38_36_127_eq]
          unfold modWrapRadKernelApprox
          positivity
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk_nn]
        exact mul_le_mul (hF_le _)
          (fine38_le_two_pow_30_coarseEnv8 hν_mem (hsub_box hc.1 hc.2.1) hc.2.2.2) hk_nn hC_nn
      · simpa only [norm_zero] using hB_nn
  rw [hpart]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ν hν ↦ hpiece ν hν).trans_eq ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  unfold coulombCoarse8PreOAAProb
  ring

attribute [local irreducible] bTwosSlot3_216

/-! ### Exact-`216` Coin-`6` Hadamard Top-Block Collapse (`s3_hadamard_topBlock_coin6_216`) -/

theorem sel149_80_ge_3924 (i : Fin 149) :
    3924 ≤ (StepBBlock0.sel149 (le_refl 80) i).val := by
  fin_cases i <;> decide

end SubpartD

end Slot3Exact216

end

end ConfigSlot3Exact216Oracle80

end Slot3Exact216Oracle80
end
set_option exponentiation.threshold 256
end Slot3Exact216Oracle80

section Slot3StreamUncK35Shift3
local instance (priority := 1000000) instNeZeroTwoPow_Slot3StreamUncK35Shift3 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
# Post-Twist Slot-3 `piSwap3` Core Commutation and 9-Step `SingleCatSelectImpl`

Provides:
1. Generic register-commutation algebra `CommutesWithReg` and involutive wire-permutation
   transport `CommutesWithReg.unitaryConj_wirePerm`.
2. `piSwap3Wire` (`3954 + j <-> 4026 + j` for `j : Fin 3`), `uPiSwap3Core`, `uSlot3Swap3Eff`,
   and `commutesWithReg_rEC80_uSlot3Swap3Eff`.
3. Core `4034`-wire commutation `(uSlot3Swap3Eff cfg).1 * (uVepFusedTwistRest hm22 c').1 =
   (uVepFusedTwistRest hm22 c').1 * (uSlot3Swap3Eff cfg).1`.
4. 9-step `SingleCatSelectImpl` (`singleCatSelectImplHoistedSplit`) matching
   `HoistBorrow42ProjBridge.hoistedBorrow42SelectSpecOfPostTwist` by `rfl`.
-/

namespace Slot3StreamUncK35Shift3

section ConfigSlot3StreamUncK35Shift3
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority :=
  10) instLoc_Slot3StreamUncK35Shift3_1InstNeZeroTwoPowS3S (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside unitaryConj unitaryConj_val)
open TwosCompAndWire0Cancel (proj3Axes projAxisField)
open FullSysCatSegmentBridge
open FullSysMomSlots0135Concrete
open Slot5MatrixAndScaleCert
open MomSlots35Slot3ProjNuclear
open Slot3Exact216Oracle80
open NuclearTwistRealizes
open ProjZ512QftAndTwist288
open CatalystPrep (U_cat_B_normalized)
open PolymorphicTopClosure (intertwinesCat_mul_gen)
open SingleCatClosure
open scoped Matrix BigOperators

/- ## Section 1: Generic Register-Commutation Algebra (`CommutesWithReg`) -/

/-- Operator `A` on `2 ^ N` commutes with every embedded operator on `r : QRegister m N`. -/
def CommutesWithReg {m N : ℕ} (r : QRegister m N) (A : Operator (2 ^ N)) : Prop :=
  ∀ W : Operator (2 ^ m), A * r.embedMatrix W = r.embedMatrix W * A

theorem CommutesWithReg.one {m N : ℕ} (r : QRegister m N) :
    CommutesWithReg r (1 : Operator (2 ^ N)) :=
  fun W ↦ by rw [Matrix.one_mul, Matrix.mul_one]

theorem CommutesWithReg.mul {m N : ℕ} {r : QRegister m N} {A B : Operator (2 ^ N)}
    (hA : CommutesWithReg r A) (hB : CommutesWithReg r B) :
    CommutesWithReg r (A * B) := fun W ↦ by
  rw [Matrix.mul_assoc, hB W, ← Matrix.mul_assoc, hA W, Matrix.mul_assoc]

theorem CommutesWithReg.conjTranspose {m N : ℕ} {r : QRegister m N} {A : Operator (2 ^ N)}
    (hA : CommutesWithReg r A) :
    CommutesWithReg r (Aᴴ) := fun W ↦ by
  have h := congrArg Matrix.conjTranspose (hA (Wᴴ))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    QRegister.embedMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose] at h
  exact h.symm

theorem CommutesWithReg.unitaryConj {m N : ℕ} {r : QRegister m N} {U M : Unitary (2 ^ N)}
    (hU : CommutesWithReg r U.1) (hM : CommutesWithReg r M.1) : CommutesWithReg r
    (PosMomSelectDynamic.unitaryConj U M).1 := by
  rw [PosMomSelectDynamic.unitaryConj_val]
  exact (hU.conjTranspose.mul hM).mul hU

theorem CommutesWithReg.of_disjoint_embed {m k N : ℕ} {r : QRegister m N} {s : QRegister k N}
    (hDisj : r.DisjointWires s) (M : Operator (2 ^ k)) : CommutesWithReg r (s.embedMatrix M)
    := fun W ↦ (r.embedMatrix_comm_of_disjoint s hDisj W M).symm

theorem CommutesWithReg.of_diagonal {m N : ℕ} {r : QRegister m N} {d : Fin (2 ^ N) → ℂ}
    (hOut : ∀ x y : Fin (2 ^ N), r.AgreeOutside x y → d x = d y) : CommutesWithReg r
    (Matrix.diagonal d) := fun W ↦ (embedMatrix_comm_diagonal_of_outside r W d hOut).symm

theorem CommutesWithReg.of_signedInvolution {m N : ℕ} {r : QRegister m N}
    (π_inv : Equiv.Perm (Fin (2 ^ N))) (ε : Fin (2 ^ N) → ℝ)
    (hInv : ∀ x, π_inv (π_inv x) = x)
    (hSymm : ∀ x, ε (π_inv x) = ε x)
    (hSq : ∀ x, ε x * ε x = 1)
    (hFix : ∀ z, r.extractIndex (π_inv z) = r.extractIndex z)
    (hAg : ∀ x y, r.AgreeOutside x y → r.AgreeOutside (π_inv x) (π_inv y))
    (hEps : ∀ x y, r.AgreeOutside x y → ε x = ε y) :
    CommutesWithReg r (signedInvolutionUnitary π_inv ε hInv hSymm hSq).1 := fun W ↦ by
  ext i j
  change (signedPermMatrix π_inv ε * r.embedMatrix W) i j =
    (r.embedMatrix W * signedPermMatrix π_inv ε) i j
  have hL : (signedPermMatrix π_inv ε * r.embedMatrix W) i j =
      ((ε i : ℝ) : ℂ) * r.embedMatrix W (π_inv i) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (π_inv i)]
    · rw [signedPermMatrix_apply, ite_eq_left (hInv i)]
    · intro k _ hk
      have hne : π_inv k ≠ i := fun h ↦ hk (by rw [← h, hInv k])
      rw [signedPermMatrix_apply, ite_eq_right hne, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hR : (r.embedMatrix W * signedPermMatrix π_inv ε) i j =
      r.embedMatrix W i (π_inv j) * ((ε (π_inv j) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (π_inv j)]
    · rw [signedPermMatrix_apply, ite_eq_left rfl]
    · intro k _ hk
      rw [signedPermMatrix_apply, ite_eq_right (Ne.symm hk), mul_zero]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  rw [hL, hR, QRegister.embedMatrix_apply, QRegister.embedMatrix_apply, hFix i, hFix j]
  have hEnvIff : ((r.basisSplitEquiv (π_inv i)).2 = (r.basisSplitEquiv j).2) ↔
      ((r.basisSplitEquiv i).2 = (r.basisSplitEquiv (π_inv j)).2) := by
    rw [r.basisSplit_environment_eq_iff, r.basisSplit_environment_eq_iff]
    exact ⟨fun h ↦ by simpa only [hInv i] using hAg (π_inv i) j h,
      fun h ↦ by simpa only [hInv j] using hAg i (π_inv j) h⟩
  by_cases hE : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv (π_inv j)).2
  · have hAgIJ : r.AgreeOutside i (π_inv j) := (r.basisSplit_environment_eq_iff _ _).mp hE
    rw [ite_eq_left (hEnvIff.mpr hE), ite_eq_left hE, hEps i (π_inv j) hAgIJ, mul_comm]
  · simp only [ite_eq_right (fun h ↦ hE (hEnvIff.mp h)), ite_eq_right hE, mul_zero, zero_mul]

/-- Involutive wire-permutation transport of `r.embedMatrix` and `CommutesWithReg`. -/
theorem perm_conj_embedMatrix_eq {m N : ℕ} (r : QRegister m N)
    (τ : Equiv.Perm (Wire N)) (hτ : ∀ w, τ (τ w) = w)
    (σ : Equiv.Perm (Fin (2 ^ N)))
    (hBits : ∀ z w, basisBits N (σ z) w = basisBits N z (τ w))
    (W : Operator (2 ^ m)) :
    let r' : QRegister m N := ⟨r.wires.trans τ.toEmbedding⟩
    (Operator.permutationUnitary σ).1 * r.embedMatrix W * (Operator.permutationUnitary σ).1 =
      r'.embedMatrix W := by
  intro r'
  have hσInv : ∀ z, σ (σ z) = z := fun z ↦ by
    apply (basisBitsEquiv N).injective; funext w
    change basisBits N (σ (σ z)) w = basisBits N z w
    rw [hBits, hBits, hτ]
  ext i j
  have hStep1 : ((Operator.permutationUnitary σ).1 * r.embedMatrix W *
      (Operator.permutationUnitary σ).1) i j = r.embedMatrix W (σ i) (σ j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
    · rw [permutationUnitary_entry, ite_eq_left rfl, mul_one,
        Matrix.mul_apply, Finset.sum_eq_single (σ i)]
      · rw [permutationUnitary_entry, ite_eq_left (hσInv i), one_mul]
      · intro k _ hk
        have hne : σ k ≠ i := fun h ↦ hk (by rw [← h, hσInv k])
        rw [permutationUnitary_entry, ite_eq_right hne, zero_mul]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · intro k _ hk
      rw [permutationUnitary_entry, ite_eq_right (Ne.symm hk), mul_zero]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hExt : ∀ z, r.extractIndex (σ z) = r'.extractIndex z := fun z ↦ by
    apply (basisBitsEquiv m).injective; funext idx
    change basisBits m (r.extractIndex (σ z)) idx = basisBits m (r'.extractIndex z) idx
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hBits]
    rfl
  have hEnv : ((r.basisSplitEquiv (σ i)).2 = (r.basisSplitEquiv (σ j)).2) ↔
      ((r'.basisSplitEquiv i).2 = (r'.basisSplitEquiv j).2) := by
    rw [r.basisSplit_environment_eq_iff, r'.basisSplit_environment_eq_iff]
    constructor
    · intro h w hw
      have hw' : τ w ∉ Set.range r.wires := fun ⟨idx, hidx⟩ ↦
        hw ⟨idx, by change τ (r idx) = w; rw [hidx, hτ]⟩
      simpa only [hBits, hτ] using h (τ w) hw'
    · intro h w hw
      have hw' : τ w ∉ Set.range r'.wires := fun ⟨idx, hidx⟩ ↦
        hw ⟨idx, by
          have := congrArg τ hidx;
          simpa only [r', Function.Embedding.trans_apply,
            Equiv.toEmbedding_apply, hτ] using this⟩
      rw [hBits, hBits]; exact h (τ w) hw'
  rw [hStep1, QRegister.embedMatrix_apply, QRegister.embedMatrix_apply, hExt i, hExt j]
  by_cases hE : (r'.basisSplitEquiv i).2 = (r'.basisSplitEquiv j).2
  · rw [ite_eq_left (hEnv.mpr hE), ite_eq_left hE]
  · rw [ite_eq_right (fun h ↦ hE (hEnv.mp h)), ite_eq_right hE]

theorem CommutesWithReg.unitaryConj_wirePerm {m N : ℕ} {r : QRegister m N}
    (τ : Equiv.Perm (Wire N)) (hτ : ∀ w, τ (τ w) = w)
    (σ : Equiv.Perm (Fin (2 ^ N)))
    (hBits : ∀ z w, basisBits N (σ z) w = basisBits N z (τ w))
    {P U : Unitary (2 ^ N)}
    (hP : P.1 = (Operator.permutationUnitary σ).1)
    (hU : CommutesWithReg ⟨r.wires.trans τ.toEmbedding⟩ U.1) :
    CommutesWithReg r (PosMomSelectDynamic.unitaryConj P U).1 := fun W ↦ by
  let r' : QRegister m N := ⟨r.wires.trans τ.toEmbedding⟩
  have hσSq : σ * σ = 1 := by
    apply Equiv.ext; intro z; apply (basisBitsEquiv N).injective; funext w
    change basisBits N (σ (σ z)) w = basisBits N z w
    rw [hBits, hBits, hτ]
  set Q := (Operator.permutationUnitary σ).1
  have hQ2 : Q * Q = 1 := by
    dsimp only [Q]
    rw [← Submonoid.coe_mul, ← OperatorExt.permutationUnitary_mul, hσSq,
      OperatorExt.permutationUnitary_one, OneMemClass.coe_one]
  have hPAdj : P.1ᴴ = Q := by
    have hUGroup := Matrix.mem_unitaryGroup_iff'.mp P.2
    rw [Matrix.star_eq_conjTranspose, hP] at hUGroup
    calc P.1ᴴ = Qᴴ := by rw [hP]
      _ = Qᴴ * (Q * Q) := by rw [hQ2, Matrix.mul_one]
      _ = (Qᴴ * Q) * Q := (Matrix.mul_assoc _ _ _).symm
      _ = Q := by rw [hUGroup, Matrix.one_mul]
  have hConj : Q * r.embedMatrix W * Q = r'.embedMatrix W :=
    perm_conj_embedMatrix_eq r τ hτ σ hBits W
  rw [PosMomSelectDynamic.unitaryConj_val, hPAdj, hP]
  calc (Q * U.1 * Q) * r.embedMatrix W
      = Q * (U.1 * (Q * r.embedMatrix W * Q)) * Q := by
          simp only [Matrix.mul_assoc]
          rw [hQ2, Matrix.mul_one]
    _ = Q * (U.1 * r'.embedMatrix W) * Q := by rw [hConj]
    _ = Q * (r'.embedMatrix W * U.1) * Q := by rw [hU W]
    _ = Q * ((Q * r.embedMatrix W * Q) * U.1) * Q := by rw [← hConj]
    _ = r.embedMatrix W * (Q * U.1 * Q) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q Q _, hQ2, Matrix.one_mul]

/- ## Section 2: `piSwap3Wire`, `uPiSwap3Core`, and `CommutesWithReg rEC80 (uSlot3Swap3Eff
  cfg).1` -/

theorem basisBits_symm_apply {k : ℕ} (f : BitAssignment k) (w : Wire k) : basisBits k
    ((basisBitsEquiv k).symm f) w = f w := congrFun ((basisBitsEquiv k).apply_symm_apply f) w

/-- Involutive wire map swapping `3954 + j <-> 4026 + j` (`j : Fin 3`) on `momCoreWires 80 =
  4034`. -/
def piSwap3WireFun (w : Wire (momCoreWires 80)) : Wire (momCoreWires 80) :=
  if h1 : 3954 ≤ w.val ∧ w.val < 3957 then
    ⟨w.val + 72, by
      dsimp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]
      omega⟩
  else if h2 : 4026 ≤ w.val ∧ w.val < 4029 then
    ⟨w.val - 72, by have := w.isLt; omega⟩
  else w

theorem piSwap3WireFun_involutive (w : Wire (momCoreWires 80)) :
    piSwap3WireFun (piSwap3WireFun w) = w := by
  apply Fin.ext
  by_cases h1 : 3954 ≤ w.val ∧ w.val < 3957
  · have hw1 : piSwap3WireFun w = ⟨w.val + 72, by
        dsimp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩ := dite_eq_left h1
    rw [hw1]
    unfold piSwap3WireFun
    rw [dite_eq_right (by dsimp; omega), dite_eq_left (by dsimp; omega)]
    dsimp; omega
  · by_cases h2 : 4026 ≤ w.val ∧ w.val < 4029
    · have hw2 : piSwap3WireFun w = ⟨w.val - 72, by have := w.isLt; omega⟩ := by
        unfold piSwap3WireFun; rw [dite_eq_right h1, dite_eq_left h2]
      rw [hw2]
      unfold piSwap3WireFun
      rw [dite_eq_left (by dsimp; omega)]
      dsimp; omega
    · have hw3 : piSwap3WireFun w = w := by
        unfold piSwap3WireFun; rw [dite_eq_right h1, dite_eq_right h2]
      rw [hw3, hw3]

/-- Bundled `Equiv.Perm` on `Wire (momCoreWires 80)` swapping `[3954..3957) <-> [4026..4029)`. -/
def piSwap3Wire : Equiv.Perm (Wire (momCoreWires 80)) where
  toFun := piSwap3WireFun
  invFun := piSwap3WireFun
  left_inv := piSwap3WireFun_involutive
  right_inv := piSwap3WireFun_involutive

/-- Basis-index permutation on `Fin (2 ^ (momCoreWires 80))` induced by `piSwap3Wire`. -/
def piSwap3CorePerm : Equiv.Perm (Fin (2 ^ (momCoreWires 80))) where
  toFun z := (basisBitsEquiv (momCoreWires 80)).symm
    (fun w ↦ basisBits (momCoreWires 80) z (piSwap3Wire w))
  invFun z := (basisBitsEquiv (momCoreWires 80)).symm
    (fun w ↦ basisBits (momCoreWires 80) z (piSwap3Wire w))
  left_inv z := by
    apply (basisBitsEquiv (momCoreWires 80)).injective; funext w
    change basisBits _ ((basisBitsEquiv _).symm _) w = basisBits _ z w
    rw [basisBits_symm_apply, basisBits_symm_apply]
    exact congrArg (basisBits _ z) (piSwap3WireFun_involutive w)
  right_inv z := by
    apply (basisBitsEquiv (momCoreWires 80)).injective; funext w
    change basisBits _ ((basisBitsEquiv _).symm _) w = basisBits _ z w
    rw [basisBits_symm_apply, basisBits_symm_apply]
    exact congrArg (basisBits _ z) (piSwap3WireFun_involutive w)

@[simp] theorem basisBits_piSwap3CorePerm (z : Fin (2 ^ (momCoreWires 80)))
    (w : Wire (momCoreWires 80)) : basisBits (momCoreWires 80) (piSwap3CorePerm z) w =
    basisBits (momCoreWires 80) z (piSwap3Wire w) := basisBits_symm_apply _ w

/-- Core `3-SWAP` unitary on `momCoreWires 80 = 4034` vacating `rCosetB1 = [3954..3957)`. -/
def uPiSwap3Core : Unitary (2 ^ (momCoreWires 80)) :=
  Operator.permutationUnitary piSwap3CorePerm

/-- Any unitary `U` whose matrix entries match a basis permutation with bit map `piSwap3Wire`
is equal to `uPiSwap3Core` (zero-dependency adapter for `Slot3Prep273AndSwap3`). -/
theorem uPiSwap3Core_eq_of_perm (U : Unitary (2 ^ (momCoreWires 80)))
    (σ : Equiv.Perm (Fin (2 ^ (momCoreWires 80)))) (hU : U = Operator.permutationUnitary σ)
    (hBits : ∀ z w, basisBits (momCoreWires 80) (σ z) w = basisBits (momCoreWires 80) z
    (piSwap3Wire w)) : U = uPiSwap3Core := by
  have hEq : σ = piSwap3CorePerm := by
    apply Equiv.ext; intro z; apply (basisBitsEquiv (momCoreWires 80)).injective; funext w
    change basisBits _ (σ z) w = basisBits _ (piSwap3CorePerm z) w
    rw [hBits, basisBits_piSwap3CorePerm]
  rw [hU, hEq]; rfl

abbrev rEC80 : QRegister (3924 + 3) (momCoreWires 80) :=
  coreElecCosetB1Block (by decide : 6 ≤ 80)

/-- Image of `rEC80` under `piSwap3Wire`: wires `[0..3924) ∪ [4026..4029)`. -/
def rECPre80 : QRegister (3924 + 3) (momCoreWires 80) :=
  ⟨rEC80.wires.trans piSwap3Wire.toEmbedding⟩

theorem rECPre80_val_cases (idx : Fin (3924 + 3)) :
    (idx.val < 3924 ∧ (rECPre80 idx).val = idx.val) ∨
      (4026 ≤ (rECPre80 idx).val ∧ (rECPre80 idx).val < 4029) := by
  refine Fin.addCases (fun i ↦ Or.inl ?_) (fun j ↦ Or.inr ?_) idx
  · have hi := i.isLt
    refine ⟨hi, ?_⟩
    change (piSwap3WireFun (rEC80 (Fin.castAdd 3 i))).val = i.val
    have hL : (rEC80 (Fin.castAdd 3 i)).val = i.val := by
      dsimp only [rEC80, coreElecCosetB1Block]
      rw [QRegister.concat_apply_left]
      simp [coreElecBlock]
    unfold piSwap3WireFun
    split_ifs <;> dsimp at * <;> omega
  · have hj := j.isLt
    change 4026 ≤ (piSwap3WireFun (rEC80 (Fin.natAdd 3924 j))).val ∧
      (piSwap3WireFun (rEC80 (Fin.natAdd 3924 j))).val < 4029
    have hR : (rEC80 (Fin.natAdd 3924 j)).val = 3954 + j.val := by
      dsimp only [rEC80, coreElecCosetB1Block]
      rw [QRegister.concat_apply_right]
      simp [coreCosetB1Block]
    unfold piSwap3WireFun
    split_ifs <;> dsimp at * <;> omega

theorem not_mem_rECPre80_of_mid {w : Wire (momCoreWires 80)} (hlo : 3924 ≤ w.val)
    (hhi : w.val < 4026) : w ∉ Set.range rECPre80.wires := by
  rintro ⟨idx, hidx⟩
  have hv := congrArg Fin.val hidx
  rcases rECPre80_val_cases idx with ⟨_, h⟩ | ⟨_, _⟩ <;> omega

theorem mem_rECPre80_of_lt_3924 {w : Wire (momCoreWires 80)} (hw : w.val < 3924) :
    w ∈ Set.range rECPre80.wires := by
  refine ⟨Fin.castAdd 3 ⟨w.val, hw⟩, Fin.ext ?_⟩
  rcases rECPre80_val_cases (Fin.castAdd 3 ⟨w.val, hw⟩) with ⟨_, h⟩ | ⟨hge, _⟩
  · exact h
  · exfalso
    have hL : (rEC80 (Fin.castAdd 3 ⟨w.val, hw⟩)).val = w.val := by
      dsimp only [rEC80, coreElecCosetB1Block]
      rw [QRegister.concat_apply_left]; simp [coreElecBlock]
    change 4026 ≤ (piSwap3WireFun (rEC80 (Fin.castAdd 3 ⟨w.val, hw⟩))).val at hge
    unfold piSwap3WireFun at hge
    split_ifs at hge <;> dsimp at * <;> omega

theorem disjoint_rECPre80_of_mid {k : ℕ} (s : QRegister k (momCoreWires 80))
    (hs : ∀ i : Fin k, 3924 ≤ (s i).val ∧ (s i).val < 4026) : rECPre80.DisjointWires s := by
  apply QRegExt.disjointWires_of_finset
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  obtain ⟨i, rfl⟩ := (QRegister.mem_image s w).mp hw2
  obtain ⟨idx, hidx⟩ := (QRegister.mem_image rECPre80 (s i)).mp hw1
  exact not_mem_rECPre80_of_mid (hs i).1 (hs i).2 ⟨idx, hidx⟩

theorem extractIndex_eq_of_agreeOutside_rECPre80 {k : ℕ} (s : QRegister k (momCoreWires 80))
    (hs : ∀ i : Fin k, 3924 ≤ (s i).val ∧ (s i).val < 4026)
    {x y : Fin (2 ^ (momCoreWires 80))} (hAg : rECPre80.AgreeOutside x y) : s.extractIndex x =
    s.extractIndex y := by
  apply (basisBitsEquiv k).injective; funext i
  change basisBits k (s.extractIndex x) i = basisBits k (s.extractIndex y) i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact hAg (s i) (not_mem_rECPre80_of_mid (hs i).1 (hs i).2)

theorem projAxisField_eq_of_agreeOutside_rECPre80 {x y : Fin (2 ^ (momCoreWires 80))}
    (hAg : rECPre80.AgreeOutside x y) (a : Fin 3) : projAxisField
    ((momSysReg 80).extractIndex x) a = projAxisField ((momSysReg 80).extractIndex y) a := by
  apply (basisBitsEquiv 8).injective; funext b
  change basisBits 8 ((proj3Axes a).extractIndex ((momSysReg 80).extractIndex x)) b =
    basisBits 8 ((proj3Axes a).extractIndex ((momSysReg 80).extractIndex y)) b
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  have hwBounds : 3924 ≤ (momSysReg 80 (proj3Axes a b)).val ∧
      (momSysReg 80 (proj3Axes a b)).val < 4026 := by
    have := a.isLt; have := b.isLt
    change 3924 ≤ 0 + (3924 + 8 * a.val + b.val) ∧ 0 + (3924 + 8 * a.val + b.val) < 4026
    omega
  exact hAg _ (not_mem_rECPre80_of_mid hwBounds.1 hwBounds.2)

theorem s3Accept216_and_nuc_eq_of_agreeOutside_rECPre80 {x y : Fin (2 ^ (momCoreWires 80))}
    (hAg : rECPre80.AgreeOutside x y) : s3Accept216 (le_refl 80) x = s3Accept216 (le_refl 80)
    y ∧ s3NucleusIdx216 (le_refl 80) x = s3NucleusIdx216 (le_refl 80) y := by
  have hCoin := extractIndex_eq_of_agreeOutside_rECPre80 (momCoinReg 80)
    (fun i ↦ by have := i.isLt; simp [momCoinReg]; omega) hAg
  have hU22 := extractIndex_eq_of_agreeOutside_rECPre80 (s3U22Core (le_refl 80))
    (fun i ↦ by have := i.isLt; simp [s3U22Core]; omega) hAg
  have hS3 := extractIndex_eq_of_agreeOutside_rECPre80 (s3S3Core (le_refl 80))
    (fun i ↦ by have := i.isLt; simp [s3S3Core]; omega) hAg
  have hC8 := extractIndex_eq_of_agreeOutside_rECPre80 (s3C8Core (le_refl 80))
    (fun i ↦ by have := i.isLt; simp [s3C8Core]; omega) hAg
  have hF30 := extractIndex_eq_of_agreeOutside_rECPre80 (s3Fine30Core (le_refl 80))
    (fun i ↦ by have := i.isLt; simp [s3Fine30Core]; omega) hAg
  have hP0 := projAxisField_eq_of_agreeOutside_rECPre80 hAg 0
  have hP1 := projAxisField_eq_of_agreeOutside_rECPre80 hAg 1
  have hP2 := projAxisField_eq_of_agreeOutside_rECPre80 hAg 2
  have hGrid : s3ProjGridBool ((momSysReg 80).extractIndex x) =
      s3ProjGridBool ((momSysReg 80).extractIndex y) := by
    unfold s3ProjGridBool; rw [hP0, hP1, hP2]
  refine ⟨by unfold s3Accept216; dsimp only; rw [hCoin, hU22, hS3, hC8, hF30, hP0, hP1, hP2, hGrid],
    ?_⟩
  have hBPar : basisBits (momCoreWires 80) x (s3BParCore (le_refl 80)) =
      basisBits (momCoreWires 80) y (s3BParCore (le_refl 80)) :=
    hAg _ (not_mem_rECPre80_of_mid (by simp) (by simp))
  have hU16Bits : ∀ i : Fin 16, i.val < 8 →
      basisBits 16 ((s3U16Core (le_refl 80)).extractIndex x) i =
        basisBits 16 ((s3U16Core (le_refl 80)).extractIndex y) i := fun i hi ↦ by
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    exact hAg _ (not_mem_rECPre80_of_mid
      (by simp [s3U16Core]; omega) (by simp [s3U16Core]; omega))
  have hBitVal : ∀ (u : Fin (2 ^ 16)) (i : Fin 16),
      (basisBits 16 u i).val = u.val / 2 ^ i.val % 2 := fun u i ↦ by
    rw [basisBits_eq_div_mod, ZMod.val_natCast, Nat.mod_mod]
  have hMod4 : ((s3U16Core (le_refl 80)).extractIndex x).val % 4 =
      ((s3U16Core (le_refl 80)).extractIndex y).val % 4 := by
    have b0 := congrArg ZMod.val (hU16Bits 0 (by decide))
    have b1 := congrArg ZMod.val (hU16Bits 1 (by decide))
    rw [hBitVal, hBitVal] at b0 b1
    dsimp at b0 b1; omega
  have hQ27 : s3NucleusQ27 (basisBits 16 ((s3U16Core (le_refl 80)).extractIndex x)) =
      s3NucleusQ27 (basisBits 16 ((s3U16Core (le_refl 80)).extractIndex y)) := by
    unfold s3NucleusQ27
    rw [hU16Bits 2 (by decide), hU16Bits 3 (by decide), hU16Bits 4 (by decide),
      hU16Bits 5 (by decide), hU16Bits 6 (by decide), hU16Bits 7 (by decide)]
  apply Fin.ext
  unfold s3NucleusIdx216; dsimp only
  rw [hMod4, hQ27, hBPar]

theorem coin0Active_false_of_wSlot2_ne_zero {i : Fin (2 ^ (momCoreWires 80))} (hne : basisBits
    (fullSysCoreWires 80) i (NuclearTwistAndXor654Concrete.wSlot2 (QRegExt.idReg _)) ≠ 0) :
    coin0Active (basisBits (fullSysCoreWires 80) i) = false ∧ vepHighNuc
    (by decide : 22 ≤ 80) (basisBits (fullSysCoreWires 80) i) = false := by
  have hc0 : coin0Active (basisBits (fullSysCoreWires 80) i) = false := by
    unfold coin0Active
    exact decide_eq_false fun h ↦ hne h.1
  refine ⟨hc0, ?_⟩
  unfold vepHighNuc
  rw [hc0]; rfl

def uFourSegSelectCat {mPayload B_tot : ℕ} (uPreSeg uTwistSeg uMidSeg uPostSeg :
    SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysBEWires mPayload + B_tot)))
    (c : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (fullSysBEWires mPayload + B_tot)) :=
    uPostSeg c * ((uTwistSeg c)⁻¹ * (uMidSeg c * (uTwistSeg c * uPreSeg c)))

/-- Prefix workspace slice `[0 .. m)` inside a larger workspace `QRegister mMax n`. -/
abbrev workSlice {m mMax n : ℕ} (hm : m ≤ mMax) (rWork : QRegister mMax n) : QRegister m n :=
  rWork.compose (QRegister.block 0 m (FullSysCatSegmentBridge.fullSys_zero_add_le_of_le hm))

theorem intertwinesCat_fourSegs {mPayload B_tot : ℕ} (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle mPayload 48) {uPreSeg uTwistSeg uMidSeg uPostSeg :
    SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysBEWires mPayload + B_tot))} {uPreEff
    uTwistEff uMidEff uPostEff : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires
    mPayload))} (c : SpecsAux.SpecMirror.Configuration) (iPre : IntertwinesCat ((rCatSelLoc mPayload
    B_tot).embedUnitary (U_cat_B_normalized B_tot)).1 ((rCatSelLoc mPayload
    B_tot).basisOutcomeProjector 0) (uPreSeg c).1 (((rBESelLoc mPayload B_tot).compose
    (beCoreBlock mPayload)).embedUnitary (uPreEff c)).1) (iTwist : IntertwinesCat ((rCatSelLoc
    mPayload B_tot).embedUnitary (U_cat_B_normalized B_tot)).1 ((rCatSelLoc mPayload
    B_tot).basisOutcomeProjector 0) (uTwistSeg c).1 (((rBESelLoc mPayload B_tot).compose
    (beCoreBlock mPayload)).embedUnitary (uTwistEff c)).1) (iTwistInv : IntertwinesCat
    ((rCatSelLoc mPayload B_tot).embedUnitary (U_cat_B_normalized B_tot)).1 ((rCatSelLoc
    mPayload B_tot).basisOutcomeProjector 0) ((uTwistSeg c)⁻¹).1 (((rBESelLoc mPayload
    B_tot).compose (beCoreBlock mPayload)).embedUnitary (uTwistEff c)⁻¹).1) (iMid :
    IntertwinesCat ((rCatSelLoc mPayload B_tot).embedUnitary (U_cat_B_normalized B_tot)).1
    ((rCatSelLoc mPayload B_tot).basisOutcomeProjector 0) (uMidSeg c).1 (((rBESelLoc mPayload
    B_tot).compose (beCoreBlock mPayload)).embedUnitary (uMidEff c)).1) (iPost :
    IntertwinesCat ((rCatSelLoc mPayload B_tot).embedUnitary (U_cat_B_normalized B_tot)).1
    ((rCatSelLoc mPayload B_tot).basisOutcomeProjector 0) (uPostSeg c).1 (((rBESelLoc mPayload
    B_tot).compose (beCoreBlock mPayload)).embedUnitary (uPostEff c)).1) (hEffEq : uPostEff c
    * ((uTwistEff c)⁻¹ * (uMidEff c * (uTwistEff c * uPreEff c))) = fullSysSelectEffUnitary
    qft selOra c) : IntertwinesCat ((rCatSelLoc mPayload B_tot).embedUnitary
    (U_cat_B_normalized B_tot)).1 ((rCatSelLoc mPayload B_tot).basisOutcomeProjector 0)
    (uFourSegSelectCat uPreSeg uTwistSeg uMidSeg uPostSeg c).1 ((rBESelLoc mPayload
    B_tot).embedUnitary ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft
    selOra c))).1 := by
  let rCoreLoc := (rBESelLoc mPayload B_tot).compose (beCoreBlock mPayload)
  have i5 := intertwinesCat_mul_gen iPost (intertwinesCat_mul_gen iTwistInv
      (intertwinesCat_mul_gen iMid (intertwinesCat_mul_gen iTwist iPre)))
  have hCat : (uPostSeg c).1 * (((uTwistSeg c)⁻¹).1 * ((uMidSeg c).1 * ((uTwistSeg c).1 *
      (uPreSeg c).1))) = (uFourSegSelectCat uPreSeg uTwistSeg uMidSeg uPostSeg c).1 := by
    simp only [uFourSegSelectCat, Submonoid.coe_mul]
  have hEff : (rCoreLoc.embedUnitary (uPostEff c)).1 * ((rCoreLoc.embedUnitary (uTwistEff
      c)⁻¹).1 * ((rCoreLoc.embedUnitary (uMidEff c)).1 * ((rCoreLoc.embedUnitary (uTwistEff
      c)).1 * (rCoreLoc.embedUnitary (uPreEff c)).1))) = ((rBESelLoc mPayload
      B_tot).embedUnitary ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft
      selOra c))).1 := by
    simp only [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, hEffEq,
      ← QRegister.embedUnitary_compose, rCoreLoc]
  exact intertwinesCat_congr_ops i5 hCat.symm hEff

set_option maxRecDepth 2000
set_option exponentiation.threshold 256

end

end ConfigSlot3StreamUncK35Shift3

end Slot3StreamUncK35Shift3
end
set_option exponentiation.threshold 256
end Slot3StreamUncK35Shift3

section ZeroAncillaUSPS3_aux
local instance (priority := 1000000) instNeZeroTwoPow_ZeroAncillaUSPS3_aux (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩


public section
section ZeroAncillaUSPS3

section ModZeroAncillaUSPS3
set_option exponentiation.threshold 256
public section
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace ZeroAncillaUSPS3
theorem SbmTreeCertW.l1_err_le {m : ℕ} {words : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate}
    {W : Fin (2 ^ m) → ℕ} {S errNat : ℕ}
    (hcert : SbmTreeCertW m words W S errNat) (hS : 0 < S) :
    ∑ j : Fin (2 ^ m), |‖sbmAmp m words j‖ ^ 2 - (W j : ℝ) / (S : ℝ)| ≤
      (errNat : ℝ) / ((S : ℝ) * (2 : ℝ) ^ 48) := by
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hscaled := (hcert.sound hS).2.2
  have hrew : (∑ j : Fin (2 ^ m), |‖sbmAmp m words j‖ ^ 2 - (W j : ℝ) / (S : ℝ)|) =
      (∑ j : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ)|) / (S : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hid : ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ) / (S : ℝ) =
        ((S : ℝ) * ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ)) / (S : ℝ) := by
      field_simp [hSR.ne']
    rw [hid, abs_div, abs_of_pos hSR]
  rw [hrew]
  calc (∑ j : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ)|) / (S : ℝ)
      ≤ ((errNat : ℝ) / (2 : ℝ) ^ 48) / (S : ℝ) := div_le_div_of_nonneg_right hscaled hSR.le
    _ = (errNat : ℝ) / ((S : ℝ) * (2 : ℝ) ^ 48) := by rw [div_div, mul_comm]
set_option exponentiation.threshold 512
set_option maxRecDepth 4096
set_option maxRecDepth 512
set_option exponentiation.threshold 256
end ZeroAncillaUSPS3
end
end ModZeroAncillaUSPS3
end ZeroAncillaUSPS3
end
set_option exponentiation.threshold 256
end ZeroAncillaUSPS3_aux

section PosPostPrep80MergedVepS3_aux
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80MergedVepS3_aux (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩


public section
section PosPostPrep80MergedVepS3

section ModPosPostPrep80MergedVepS3
public section
namespace PosPostPrep80MergedVepS3
section ConfigPosPostPrep80MergedVepS3
set_option backward.isDefEq.respectTransparency true
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open ZeroAncillaUSPS3 hiding ket
set_option maxRecDepth 2000000
set_option exponentiation.threshold 256
section SecJointTailCardAndBridge
set_option exponentiation.threshold 28
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem l1_le_of_good_subprob {ι : Type*} [Fintype ι]
    (μ p : ι → ℝ) (G : Finset ι)
    (hμ_nn : ∀ x, 0 ≤ μ x)
    (hμ_sum : (∑ x : ι, μ x) ≤ 1)
    (hp_out : ∀ x, x ∉ G → p x = 0)
    (hp_sum : (∑ x ∈ G, p x) = 1) :
    (∑ x : ι, |μ x - p x|) ≤ (∑ x ∈ G, |μ x - p x|) + (1 - ∑ x ∈ G, μ x) ∧
    (∑ x : ι, |μ x - p x|) ≤ 2 * (∑ x ∈ G, |μ x - p x|) := by
  classical
  have hG_eq : Finset.univ.filter (fun x ↦ x ∈ G) = G := by
    ext x; simp
  have hpart : ∀ f : ι → ℝ,
      (∑ x : ι, f x) = (∑ x ∈ G, f x) + (∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ G), f x) :=
    fun f ↦ by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x ↦ x ∈ G) f, hG_eq]
  have hbad_eq : (∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ G), |μ x - p x|) =
      ∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ G), μ x := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hxG : x ∉ G := (Finset.mem_filter.mp hx).2
    rw [hp_out x hxG, sub_zero, abs_of_nonneg (hμ_nn x)]
  have hbad_le : (∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ G), μ x) ≤ 1 - ∑ x ∈ G, μ x := by
    have htot := hμ_sum
    rw [hpart μ] at htot
    linarith
  have hfirst : (∑ x : ι, |μ x - p x|) ≤ (∑ x ∈ G, |μ x - p x|) + (1 - ∑ x ∈ G, μ x) := by
    rw [hpart (fun x ↦ |μ x - p x|), hbad_eq]
    linarith
  have hdef_le : 1 - ∑ x ∈ G, μ x ≤ ∑ x ∈ G, |μ x - p x| := by
    calc 1 - ∑ x ∈ G, μ x
        = (∑ x ∈ G, p x) - (∑ x ∈ G, μ x) := by rw [hp_sum]
      _ = ∑ x ∈ G, (p x - μ x) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ x ∈ G, |μ x - p x| := by
          refine Finset.sum_le_sum fun x _ ↦ ?_
          rw [abs_sub_comm]
          exact le_abs_self (p x - μ x)
  exact ⟨hfirst, by linarith⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem bhmt_poly_id (sSq : ℝ) :
    1 - sSq * (3 - 4 * sSq) ^ 2 = (4 * sSq - 1) ^ 2 * (1 - sSq) := by
  ring
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem bhmt_uniform_good_l1_le {ι : Type*} [Fintype ι]
    (μ p : ι → ℝ) (G : Finset ι) (sSq : ℝ)
    (hG : 0 < G.card)
    (hs_le : sSq ≤ 1)
    (hμ_nn : ∀ x, 0 ≤ μ x)
    (hμ_sum : (∑ x : ι, μ x) ≤ 1)
    (hμ_good : ∀ x ∈ G, μ x = (sSq * (3 - 4 * sSq) ^ 2) / (G.card : ℝ))
    (hp_good : ∀ x ∈ G, p x = 1 / (G.card : ℝ))
    (hp_out : ∀ x, x ∉ G → p x = 0) :
    (∑ x : ι, |μ x - p x|) ≤ 2 * (4 * sSq - 1) ^ 2 * (1 - sSq) := by
  have hcard_pos : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hG
  have hcard_ne : (G.card : ℝ) ≠ 0 := hcard_pos.ne'
  have hp_sum : (∑ x ∈ G, p x) = 1 := by
    rw [Finset.sum_congr rfl fun x hx ↦ hp_good x hx, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard_ne]
  have hμG_sum : (∑ x ∈ G, μ x) = sSq * (3 - 4 * sSq) ^ 2 := by
    rw [Finset.sum_congr rfl fun x hx ↦ hμ_good x hx, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard_ne]
  have hdef_nn : 0 ≤ 1 - sSq * (3 - 4 * sSq) ^ 2 := by
    rw [bhmt_poly_id]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have hgood_l1 : (∑ x ∈ G, |μ x - p x|) = (4 * sSq - 1) ^ 2 * (1 - sSq) := by
    have hterm : ∀ x ∈ G, |μ x - p x| = (1 - sSq * (3 - 4 * sSq) ^ 2) / (G.card : ℝ) :=
      fun x hx ↦ by
        rw [hμ_good x hx, hp_good x hx, abs_sub_comm]
        have hsub : 1 / (G.card : ℝ) - sSq * (3 - 4 * sSq) ^ 2 / (G.card : ℝ) =
            (1 - sSq * (3 - 4 * sSq) ^ 2) / (G.card : ℝ) := by ring
        rw [hsub, abs_of_nonneg (div_nonneg hdef_nn hcard_pos.le)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcancel : (G.card : ℝ) * ((1 - sSq * (3 - 4 * sSq) ^ 2) / (G.card : ℝ)) =
        1 - sSq * (3 - 4 * sSq) ^ 2 := by
      field_simp [hcard_ne]
    rw [hcancel, bhmt_poly_id]
  have hsub := (l1_le_of_good_subprob μ p G hμ_nn hμ_sum hp_out hp_sum).1
  rw [hgood_l1, hμG_sum, bhmt_poly_id] at hsub
  linarith
end SecJointTailCardAndBridge
set_option maxRecDepth 2000
end ConfigPosPostPrep80MergedVepS3
end PosPostPrep80MergedVepS3
end
end ModPosPostPrep80MergedVepS3
end PosPostPrep80MergedVepS3
end
set_option exponentiation.threshold 256
end PosPostPrep80MergedVepS3_aux

section PosPostPrep80CertS3_aux
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80CertS3_aux (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩


public section
section PosPostPrep80CertS3

section ModPosPostPrep80CertS3
public section
namespace PosPostPrep80CertS3
section ConfigPosPostPrep80CertS3
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
local instance (priority :=
  1000000) instLoc_PosPostPrep80CertS3_aux_1InstNeZeroTwoPowCer {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.PhaseGradCatalystCore (hadamardAll)
open MeasureBranchHadamardSem (ket ket_H bitSign)
open ZeroAncillaUSPS3 hiding ket
open FullSysPrepare6Slot (coinSelOutcome basisBits_coinSelOutcome_coin
  basisBits_coinSelOutcome_outside)
open FullSysFullPrepareAndTopConcrete (selWiresSym selCoin3Sym coreAncSym corePayloadSym)
open PosSlots24SemanticOracleConcrete80 (ancIdx86 ancIdx86_injective)
open PosPostPrep80MergedVepS3
open PosPostPrep80InnerAmpS3
section Junction
open HermitianMat
open scoped ComplexOrder MatrixOrder
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[local simp] private theorem toff_mkWithTempAndDyn {Var : Type} {n : ℕ}
    (v : Var) (rFull128 : QRegister 128 n) (c₁ c₂ anc : Wire 128) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : DynamicCircuit Var n) :
    (mkWithTempAndDyn v rFull128 c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.TOFF =
    body.count PrimitiveGate.TOFF := by
  simp [mkWithTempAndDyn, DynamicCircuit.count, DynamicCircuit.count_andCompute_toff,
    DynamicCircuit.count_andUncompute_toff]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[local simp] private theorem t_mkWithTempAndDyn {Var : Type} {n : ℕ}
    (v : Var) (rFull128 : QRegister 128 n) (c₁ c₂ anc : Wire 128) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : DynamicCircuit Var n) :
    (mkWithTempAndDyn v rFull128 c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.T = 4 +
    body.count PrimitiveGate.T := by
  simp [mkWithTempAndDyn, DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
    DynamicCircuit.count_andUncompute_t]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def Clean42_128 (β : BitAssignment 128) : Prop := ∀ w : Wire 128, 86 ≤ w.val → β w = 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def Clean39_128 (β : BitAssignment 128) : Prop := (∀ j : Fin 30, β (scr30_128 j) = 0) ∧ β
    wEnHead_128 = 0 ∧ β wEnTail_128 = 0 ∧ β wEnC0Head_128 = 0 ∧ β wEnAnc_128 = 0 ∧ β
    wEnS0Tail_128 = 0 ∧ β wPopT01_128 = 0 ∧ β wPopMaj_128 = 0 ∧ β wPopPar_128 = 0 ∧ β
    wBrTop_128 = 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def OpInv2 (β : BitAssignment 128) : Prop := Clean39_128 β ∧ β wEnPos_128 = β wCoin1_128 * β
    wCoin2_128 ∧ β wEnS0_128 = 0 ∧ β wEnC0_128 = 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def OpInv3 (β : BitAssignment 128) : Prop := Clean39_128 β ∧ β wEnPos_128 = (1 - β wCoin1_128)
    * (1 - β wCoin2_128) ∧ β wEnS0_128 = 0 ∧ β wEnC0_128 = 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def OpInv4 (β : BitAssignment 128) : Prop := Clean39_128 β ∧ β wEnPos_128 = (1 - β wCoin1_128)
    * (1 - β wCoin2_128) ∧ β wEnS0_128 = β wEnPos_128 * β wCoin0_128 ∧ β wEnC0_128 = 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def cFlip12_128 : Circuit 128 :=
  Circuit.X wCoin1_128 ;;ᶜ Circuit.X wCoin2_128
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def cOpenC0_128 : Circuit 128 :=
  cnotIf wEnPos_128 wEnC0_128 ;;ᶜ cnotIf wEnS0_128 wEnC0_128
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def dOpenWrap {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n := mkWithCliffDyn rFull128
    cFlip12_128 (mkWithTempAndDyn v rFull128 wCoin1_128 wCoin2_128 wEnPos_128 (by decide)
    (by decide) (by decide) (mkWithCliffDyn rFull128 cFlip12_128 (mkWithTempAndDyn v rFull128
    wEnPos_128 wCoin0_128 wEnS0_128 (by decide) (by decide) (by decide) (mkWithCliffDyn
    rFull128 cOpenC0_128 body))))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem embedUnitary_inv_eq {m N : ℕ} (r : QRegister m N) (V : Unitary (2 ^ m)) :
    (r.embedUnitary V)⁻¹ = r.embedUnitary V⁻¹ := by
  apply mul_eq_one_iff_inv_eq.mp
  rw [← r.embedUnitary_mul, mul_inv_cancel, r.embedUnitary_one]
end Junction
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev selPayload80 : QRegister 80 (selWiresSym 80) := QRegister.block 6 80 le_rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem coreAncSym_compose_selPayload80 :
    (coreAncSym 80).compose selPayload80 = corePayloadSym 80 := by
  apply PosPostPrep80CertS3Alt.qreg_ext
  intro j
  ext
  dsimp [coreAncSym, selPayload80, corePayloadSym, QRegister.compose, QRegister.compose_apply,
    PosPostPrep80CertS3Alt.qreg_compose_wires, PosPostPrep80CertS3Alt.qreg_whole_wires,
    PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
    PosPostPrep80CertS3Alt.emb_mk_apply, PosPostPrep80CertS3Alt.qreg_block_apply,
    PosPostPrep80CertS3Alt.qreg_block_wires_apply]
  omega
attribute [local irreducible] muActualFactor80
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailReg_mem_range {k n : ℕ} (r : QRegister (k + 1) n) :
    let rTail : QRegister k n := r.compose (QRegister.block 1 k (by omega))
    ∀ (β : BitAssignment n) (b₀ : ZMod 2) (qT : BitAssignment k),
      writeReg (Function.update β (r 0) b₀) rTail qT =
        writeReg β r (Fin.cons b₀ qT) := by
  intro rTail β b₀ qT
  have hTail : ∀ j : Fin k, rTail j = r j.succ := fun j ↦ by
    dsimp [rTail, QRegister.compose, QRegister.compose_apply,
      PosPostPrep80CertS3Alt.qreg_compose_wires, PosPostPrep80CertS3Alt.qreg_whole_wires,
      PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
      PosPostPrep80CertS3Alt.emb_mk_apply, PosPostPrep80CertS3Alt.qreg_block_apply,
      PosPostPrep80CertS3Alt.qreg_block_wires_apply]
    congr 1; ext; dsimp; omega
  funext w
  by_cases hwT : ∃ j : Fin k, rTail j = w
  · obtain ⟨j, rfl⟩ := hwT
    rw [writeReg_apply_reg]
    rw [hTail j, writeReg_apply_reg, Fin.cons_succ]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hwT]
    by_cases hw0 : w = r 0
    · subst hw0
      rw [Function.update_self, writeReg_apply_reg, Fin.cons_zero]
    · rw [Function.update_of_ne hw0]
      have hwR : ¬∃ i : Fin (k + 1), r i = w := by
        rintro ⟨i, rfl⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact hw0 rfl
        · exact hwT ⟨j, hTail j⟩
      rw [writeReg_apply_of_not_mem _ _ _ _ hwR]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem hadamardAll_mulVec_ket_of_zero :
    ∀ {m n : ℕ} (r : QRegister m n) (β : BitAssignment n),
      (∀ i : Fin m, β (r i) = 0) →
      (hadamardAll r).eval.1.mulVec (ket β) =
        ∑ q : BitAssignment m, ((1 / √(2 : ℝ) : ℂ) ^ m) • ket (writeReg β r q)
  | 0, n, r, β, _ => by
      have hseq : hadamardAll r = Circuit.identity := rfl
      have huniq : (Finset.univ : Finset (BitAssignment 0)) = {default} := by
        ext q
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim q default
      have hw : writeReg β r default = β := by
        funext w
        apply writeReg_apply_of_not_mem
        rintro ⟨i, _⟩
        exact Fin.elim0 i
      rw [hseq, Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec,
        huniq, Finset.sum_singleton, pow_zero, one_smul, hw]
  | k + 1, n, r, β, hz => by
      let rTail : QRegister k n := r.compose (QRegister.block 1 k (by omega))
      have hTail : ∀ j : Fin k, rTail j = r j.succ := fun j ↦ by
        dsimp [rTail, QRegister.compose, QRegister.compose_apply,
          PosPostPrep80CertS3Alt.qreg_compose_wires, PosPostPrep80CertS3Alt.qreg_whole_wires,
          PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
          PosPostPrep80CertS3Alt.emb_mk_apply, PosPostPrep80CertS3Alt.qreg_block_apply,
          PosPostPrep80CertS3Alt.qreg_block_wires_apply]
        congr 1; ext; dsimp; omega
      have hList : List.ofFn (fun i : Fin (k + 1) ↦ Circuit.H (r i)) =
          Circuit.H (r 0) :: List.ofFn (fun j : Fin k ↦ Circuit.H (rTail j)) := by
        rw [List.ofFn_succ]
        congr 2
        funext j
        rw [hTail j]
      have hEval : (hadamardAll r).eval = (hadamardAll rTail).eval * (Circuit.H (r 0)).eval := by
        unfold hadamardAll
        rw [hList, Circuit.sequence, Circuit.eval_seq]
      rw [hEval, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      have hH0 : (Circuit.H (r 0)).eval.1.mulVec (ket β) =
          (1 / √(2 : ℝ) : ℂ) • ket (Function.update β (r 0) 0) +
            (1 / √(2 : ℝ) : ℂ) • ket (Function.update β (r 0) 1) := by
        rw [ket_H, hz 0, sqrtHalf_eq_one_div_sqrt2]
        simp only [bitSign, ↓reduceIte, one_smul, smul_add]
      have hzUpd : ∀ (b₀ : ZMod 2) (j : Fin k), Function.update β (r 0) b₀ (rTail j) = 0 := by
        intro b₀ j
        have hne : rTail j ≠ r 0 := by
          rw [hTail j]
          exact fun h ↦ Fin.succ_ne_zero j (r.wires.injective h)
        rw [Function.update_of_ne hne, hTail j, hz j.succ]
      rw[hH0, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          hadamardAll_mulVec_ket_of_zero rTail _ (hzUpd 0),
          hadamardAll_mulVec_ket_of_zero rTail _ (hzUpd 1), Finset.smul_sum, Finset.smul_sum]
      let e : ZMod 2 × BitAssignment k ≃ BitAssignment (k + 1) :=
        { toFun := fun p ↦ Fin.cons p.1 p.2
          invFun := fun q ↦ (q 0, fun j ↦ q j.succ)
          left_inv := fun _ ↦ Prod.ext rfl (funext fun _ ↦ rfl)
          right_inv := fun q ↦ funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      have hZ2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
      have hne01 : (0 : ZMod 2) ≠ 1 := by decide
      rw [hZ2, Finset.sum_pair hne01]
      congr 1 <;>
        (refine Finset.sum_congr rfl fun qT _ ↦ ?_;
         simp only [Equiv.coe_fn_mk, e];
         rw [smul_smul, pow_succ', tailReg_mem_range r β _ qT])
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem selPayload80_coinSelOutcome_zero (c : Fin 8) (j : Fin 80) :
    basisBits 86 (coinSelOutcome (selCoin3Sym 80) c) (selPayload80 j) = 0 := by
  refine basisBits_coinSelOutcome_outside (selCoin3Sym 80) c ?_
  intro hmem
  rcases (QRegister.mem_image (selCoin3Sym 80) (selPayload80 j)).mp hmem with ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  dsimp [selCoin3Sym, selPayload80, PosPostPrep80CertS3Alt.qreg_block_apply,
    PosPostPrep80CertS3Alt.qreg_block_wires_apply, PosPostPrep80CertS3Alt.qreg_whole_wires,
    PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
    PosPostPrep80CertS3Alt.emb_mk_apply] at hv
  omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem writeReg_coinSelOutcome_eq_ancBits86 (s0 : Bool) (q : BitAssignment 80) :
    writeReg (basisBits 86 (coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0)))
      selPayload80 q = ancBits86 s0 q := by
  let c : Fin 8 := if s0 then 1 else 0
  funext w
  by_cases hw6 : w.val < 6
  · have hnotP : ¬∃ j : Fin 80, selPayload80 j = w := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      dsimp [selPayload80, PosPostPrep80CertS3Alt.qreg_block_apply,
        PosPostPrep80CertS3Alt.qreg_block_wires_apply, PosPostPrep80CertS3Alt.qreg_whole_wires,
        PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
        PosPostPrep80CertS3Alt.emb_mk_apply] at hv
      omega
    rw [writeReg_apply_of_not_mem _ _ _ _ hnotP]
    by_cases hw3 : w.val < 3
    · have hwEq : w = (selCoin3Sym 80) ⟨w.val, hw3⟩ :=
        Fin.ext (by
          dsimp [selCoin3Sym, PosPostPrep80CertS3Alt.qreg_block_apply,
            PosPostPrep80CertS3Alt.qreg_block_wires_apply, PosPostPrep80CertS3Alt.qreg_whole_wires,
            PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
            PosPostPrep80CertS3Alt.emb_mk_apply]; omega)
      rw [hwEq, basisBits_coinSelOutcome_coin]
      change basisBits 3 (if s0 then 1 else 0) ⟨w.val, hw3⟩ =
        ancBits86 s0 q ((selCoin3Sym 80) ⟨w.val, hw3⟩)
      generalize (⟨w.val, hw3⟩ : Fin 3) = j3'
      clear w hw6 hnotP hw3 hwEq c
      cases s0 <;> fin_cases j3' <;> rfl
    · have hnotC : w ∉ (selCoin3Sym 80).image := by
        intro hmem
        rcases (QRegister.mem_image (selCoin3Sym 80) w).mp hmem with ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        dsimp [selCoin3Sym, selPayload80, PosPostPrep80CertS3Alt.qreg_block_apply,
          PosPostPrep80CertS3Alt.qreg_block_wires_apply, PosPostPrep80CertS3Alt.qreg_whole_wires,
          PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
          PosPostPrep80CertS3Alt.emb_mk_apply] at hv
        omega
      have hw0 : (w.val == 0) = false := by
        cases hwz : w.val with
        | zero => omega
        | succ _ => rfl
      rw [basisBits_coinSelOutcome_outside (selCoin3Sym 80) c hnotC]
      simp only [ancBits86, hw0, Bool.false_eq_true, ↓reduceIte, hw6, ↓reduceDIte]
  · have hj : w.val - 6 < 80 := by
      have := w.isLt
      change w.val < 86 at this
      omega
    let u : Wire 86 := selPayload80 ⟨w.val - 6, hj⟩
    have hwEq : w = u := by
      ext;
      dsimp [u, selPayload80, PosPostPrep80CertS3Alt.qreg_block_apply,
        PosPostPrep80CertS3Alt.qreg_block_wires_apply, PosPostPrep80CertS3Alt.qreg_whole_wires,
        PosPostPrep80CertS3Alt.emb_trans_apply, PosPostPrep80CertS3Alt.emb_refl_apply,
        PosPostPrep80CertS3Alt.emb_mk_apply]; omega
    have hu0 : (u.val == 0) = false := by
      change ((6 + (w.val - 6)) == 0) = false
      simp
    have hu6 : ¬(u.val < 6) := by
      change ¬(6 + (w.val - 6) < 6)
      omega
    have hAnc : ancBits86 s0 q u = q ⟨w.val - 6, hj⟩ := by
      unfold ancBits86
      simp only [hu0, Bool.false_eq_true, ↓reduceIte, hu6, ↓reduceDIte]
      congr 1
      ext
      change (6 + (w.val - 6)) - 6 = w.val - 6
      omega
    rw [hwEq, writeReg_apply_reg, hAnc]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem col_eq_amp_of_mulVec (M U H : Operator (2 ^ 86)) (amp : BitAssignment 80 → ℂ)
    (s0 : Bool) (hM : M = U * H) (hH : H.mulVec (ket (basisBits 86 (coinSelOutcome
    (selCoin3Sym 80) (if s0 then 1 else 0)))) = ∑ q : BitAssignment 80, ((1 / √(2 : ℝ) : ℂ) ^
    80) • ket (writeReg (basisBits 86 (coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0)))
    selPayload80 q)) (hU : U.mulVec (∑ q : BitAssignment 80, ((1 / √(2 : ℝ) : ℂ) ^ 80) • ket
    (ancBits86 s0 q)) = ∑ p : BitAssignment 80, amp p • ket (ancBits86 s0 p))
    (b : Fin (2 ^ 86)) : M b (coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0)) = ∑ p :
    BitAssignment 80, if b = ancIdx86 s0 p then amp p else 0 := by
  let aCol : Fin (2 ^ 86) := coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0)
  have hSingle : ket (basisBits 86 aCol) = Pi.single aCol (1 : ℂ) := by
    rw [ket_eq_single_local, symm_basisBits_eq aCol]
  have hCol : M b aCol = (M.mulVec (ket (basisBits 86 aCol))) b := by
    rw [hSingle]
    exact (congrFun (Matrix.mulVec_single_one M aCol) b).symm
  have hRew : (∑ q : BitAssignment 80,
      ((1 / √(2 : ℝ) : ℂ) ^ 80) • ket (writeReg (basisBits 86 aCol) selPayload80 q)) =
      ∑ q : BitAssignment 80, ((1 / √(2 : ℝ) : ℂ) ^ 80) • ket (ancBits86 s0 q) := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [writeReg_coinSelOutcome_eq_ancBits86 s0 q]
  rw [hCol, hM, ← Matrix.mulVec_mulVec, hH, hRew, hU, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hIdx : (basisBitsEquiv 86).symm (ancBits86 s0 p) = ancIdx86 s0 p := rfl
  rw [Pi.smul_apply, ket_eq_single_local (ancBits86 s0 p), hIdx]
  by_cases hb : b = ancIdx86 s0 p
  · subst hb; simp only [Pi.single_eq_same, smul_eq_mul, mul_one, ↓reduceIte]
  · simp only [Pi.single_eq_of_ne hb, smul_eq_mul, mul_zero, hb, ↓reduceIte]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem hSupp_of_col_eq (M : Operator (2 ^ (selWiresSym 80))) (amp : BitAssignment 80 → ℂ)
    (s0 : Bool) (aCol : Fin (2 ^ (selWiresSym 80))) (hCol : ∀ b, M b aCol = ∑ p :
    BitAssignment 80, if b = ancIdx86 s0 p then amp p else 0) (b : Fin (2 ^ (selWiresSym 80)))
    (hb : b ∉ Set.range (ancIdx86 s0)) : M b aCol = 0 := by
  rw [hCol b]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  have hne : b ≠ ancIdx86 s0 p := fun h ↦ hb ⟨p, h.symm⟩
  simp only [hne, ↓reduceIte]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem hMu_of_col_eq (M : Operator (2 ^ (selWiresSym 80))) (amp : BitAssignment 80 → ℂ)
    (mu : BitAssignment 80 → ℝ) (s0 : Bool) (aCol : Fin (2 ^ (selWiresSym 80))) (hCol : ∀ b, M
    b aCol = ∑ q : BitAssignment 80, if b = ancIdx86 s0 q then amp q else 0)
    (hSq : ∀ p, ‖amp p‖ ^ 2 = mu p) (p : BitAssignment 80) : ‖M (ancIdx86 s0 p) aCol‖ ^ 2 = mu
    p := by
  rw [hCol (ancIdx86 s0 p), Finset.sum_eq_single p]
  · simp only [↓reduceIte]
    exact hSq p
  · intro q _ hqp
    have hne : ancIdx86 s0 p ≠ ancIdx86 s0 q := fun h ↦ hqp (ancIdx86_injective s0 h).symm
    simp only [hne, ↓reduceIte]
  · intro hp; exact absurd (Finset.mem_univ p) hp
set_option maxRecDepth 2000
end ConfigPosPostPrep80CertS3
end PosPostPrep80CertS3
end
end ModPosPostPrep80CertS3
end PosPostPrep80CertS3
end
set_option exponentiation.threshold 256
end PosPostPrep80CertS3_aux

section PosPostPrep80L1BoundsS3Aux
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80L1BoundsS3 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩


public section
section PosPostPrep80L1BoundsS3

section ModPosPostPrep80L1BoundsS3
public section
namespace PosPostPrep80L1BoundsS3
section Opts
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 262144
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority :=
  1000000) instLoc_PosPostPrep80L1BoundsS3_1InstNeZeroTwoPowPos (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open ZeroAncillaUSPS3
open PosPostPrep80MergedVepS3
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pos80IdealDist_eq_physics : PosPostPrep80MergedVepS3.pos80IdealDist =
    PosSlots24Semantic80Physics.pos80IdealDist := rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ite_pos {α : Type*} {P : Prop} {_h : Decidable P} (hp : P) {a b : α} :
    (if P then a else b) = a := by
  simp [hp]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ite_neg {α : Type*} {P : Prop} {_h : Decidable P} (hp : ¬P) {a b : α} :
    (if P then a else b) = b := by
  simp [hp]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ne_zero_of_ite_zero {α : Type*} [Zero α] {c : Bool} {v : α}
    (h : (if c then v else 0) ≠ 0) : c = true := by
  cases c
  · exact absurd rfl h
  · rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ne_zero_of_dite_zero {α : Type*} [Zero α] {P : Prop} [Decidable P] {v : P → α}
    (h : (if hp : P then v hp else 0) ≠ 0) : ∃ hp : P, v hp ≠ 0 := by
  by_cases hp : P
  · rw [dite_eq_left hp] at h; exact ⟨hp, h⟩
  · rw [dite_eq_right hp] at h; exact absurd rfl h
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem mk_bitsVal_fin_eq {m N : ℕ} (γ : BitAssignment m) (v : Fin N)
    (hlt : Pos24HeadCoordXor80.bitsVal γ < N) (h : Pos24HeadCoordXor80.bitsVal γ = v.val) :
    (⟨Pos24HeadCoordXor80.bitsVal γ, hlt⟩ : Fin N) = v := Fin.ext h
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem zmod2_add_self_cancel (a b : ZMod 2) : a + b + b = a := by
  revert a b; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem zmod2_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem z2BitOfNat_val (x i : ℕ) : (z2BitOfNat x i).val = (x / 2 ^ i) % 2 := by
  unfold z2BitOfNat
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h0 | h1
  · simp [h0]
  · simp [h1]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem bitsVal_z2BitOfNat (m x : ℕ) (hx : x < 2 ^ m) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ z2BitOfNat x j.val) = x := by
  induction m generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst hx0; rfl
  | succ m ih =>
    rw [Pos24HeadCoordXor80.bitsVal, Fin.sum_univ_succ]
    have h0 : (z2BitOfNat x 0).val * 2 ^ (0 : ℕ) = x % 2 := by
      rw [z2BitOfNat_val]; omega
    have hstep : ∀ i : Fin m,
        (z2BitOfNat x i.succ.val).val * 2 ^ i.succ.val =
          2 * ((z2BitOfNat (x / 2) i.val).val * 2 ^ i.val) := fun i ↦ by
      rw [z2BitOfNat_val, z2BitOfNat_val]
      have hdiv : x / 2 ^ (i.val + 1) = (x / 2) / 2 ^ i.val := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul]
      rw [Fin.val_succ, hdiv, pow_succ']
      ring
    simp_rw [hstep, ← Finset.mul_sum]
    change (z2BitOfNat x 0).val * 2 ^ (0 : ℕ) +
      2 * Pos24HeadCoordXor80.bitsVal (fun i : Fin m ↦ z2BitOfNat (x / 2) i.val) = x
    rw [h0, ih (x / 2) (by rw [pow_succ'] at hx; omega)]
    omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem z2BitOfNat_bitsVal {m : ℕ} (γ : BitAssignment m) (i : Fin m) :
    z2BitOfNat (Pos24HeadCoordXor80.bitsVal γ) i.val = γ i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    have hSplit : Pos24HeadCoordXor80.bitsVal γ =
        (γ 0).val + 2 * Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ γ j.succ) := by
      rw [Pos24HeadCoordXor80.bitsVal, Fin.sum_univ_succ]
      have h0 : (γ 0).val * 2 ^ (0 : Fin (m + 1)).val = (γ 0).val := by simp
      have hs : ∀ j : Fin m, (γ j.succ).val * 2 ^ j.succ.val =
          2 * ((γ j.succ).val * 2 ^ j.val) := fun j ↦ by
        rw [Fin.val_succ, pow_succ']; ring
      rw [h0]
      simp_rw [hs, ← Finset.mul_sum]
    have _hb0 : (γ 0).val < 2 := ZMod.val_lt (γ 0)
    refine Fin.cases ?_ ?_ i
    · rw [hSplit]
      rcases zmod2_zero_or_one (γ 0) with h | h <;> simp [z2BitOfNat, h]
    · intro j
      have hdiv : ((γ 0).val + 2 * Pos24HeadCoordXor80.bitsVal (fun k : Fin m ↦ γ k.succ)) /
          2 ^ j.succ.val =
          Pos24HeadCoordXor80.bitsVal (fun k : Fin m ↦ γ k.succ) / 2 ^ j.val := by
        rw [show j.succ.val = j.val + 1 from rfl, pow_succ', ← Nat.div_div_eq_div_mul]
        congr 1; omega
      change z2BitOfNat (Pos24HeadCoordXor80.bitsVal γ) j.succ.val = γ j.succ
      unfold z2BitOfNat
      rw [hSplit, hdiv]
      exact ih (fun k : Fin m ↦ γ k.succ) j
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem flipTailDpScratch80_preserve (p : BitAssignment 80) (q : Fin 80)
    (hq : q.val ≠ 75 ∧ q.val ≠ 76 ∧ q.val ≠ 77) : flipTailDpScratch80 p q = p q := by
  unfold flipTailDpScratch80
  by_cases h30 : (p 30 == 1) = true
  · simp [h30]
  · simp only [h30, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h75 h76 h77
    · exact absurd (beq_iff_eq.mp h75) hq.1
    · exact absurd (beq_iff_eq.mp h76) hq.2.1
    · exact absurd (beq_iff_eq.mp h77) hq.2.2
    · rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem flipTailDpScratch80_eq_outside_scratch16 (p : BitAssignment 80) (j : Fin 80)
    (hj : ¬(63 ≤ j.val ∧ j.val < 79)) : flipTailDpScratch80 p j = p j :=
  flipTailDpScratch80_preserve p j ⟨by omega, by omega, by omega⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem flipTailDpScratch80_involutive : Function.Involutive flipTailDpScratch80 := by
  intro p
  set fp := flipTailDpScratch80 p with hfp_def
  have h30eq : fp 30 = p 30 := flipTailDpScratch80_preserve p 30 (by decide)
  have h0eq : fp 0 = p 0 := flipTailDpScratch80_preserve p 0 (by decide)
  have h1eq : fp 1 = p 1 := flipTailDpScratch80_preserve p 1 (by decide)
  have h2eq : fp 2 = p 2 := flipTailDpScratch80_preserve p 2 (by decide)
  funext q
  unfold flipTailDpScratch80
  rw [h30eq]
  by_cases h30 : (p 30 == 1) = true
  · simp [h30, hfp_def, flipTailDpScratch80]
  · simp only [h30, Bool.false_eq_true, ↓reduceIte]
    have hfp_at : ∀ r : Fin 80, fp r =
        if r.val == 75 then p 75 + p 0
        else if r.val == 76 then p 76 + p 1
        else if r.val == 77 then p 77 + p 2
        else p r := fun r ↦ by
      rw [hfp_def]; unfold flipTailDpScratch80; simp [h30]
    split_ifs with h75 h76 h77
    · rw [hfp_at 75, h0eq]; dsimp; rw [zmod2_add_self_cancel]
      exact congrArg p (Fin.ext (beq_iff_eq.mp h75)).symm
    · rw [hfp_at 76, h1eq]; dsimp; rw [zmod2_add_self_cancel]
      exact congrArg p (Fin.ext (beq_iff_eq.mp h76)).symm
    · rw [hfp_at 77, h2eq]; dsimp; rw [zmod2_add_self_cancel]
      exact congrArg p (Fin.ext (beq_iff_eq.mp h77)).symm
    · rw [hfp_at q]; simp [h75, h76, h77]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p80ClearB0Local_out (p : BitAssignment 80) (j : Fin 80)
    (hj : ¬(3 ≤ j.val ∧ j.val < 6)) : p80ClearB0Local p j = p j := by
  unfold p80ClearB0Local
  simp [hj]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p80ClearB0Local_b0Val (p : BitAssignment 80) : Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 3 ↦ p80ClearB0Local p (pos80SubIdx 3 3 (by decide) j)) = 0 := by
  have hfn : (fun j : Fin 3 ↦ p80ClearB0Local p (pos80SubIdx 3 3 (by decide) j)) =
      fun j : Fin 3 ↦ z2BitOfNat 0 j.val := by
    funext j
    unfold p80ClearB0Local pos80SubIdx z2BitOfNat
    simp [show 3 ≤ 3 + j.val ∧ 3 + j.val < 6 by omega]
  rw [hfn]
  exact bitsVal_z2BitOfNat 3 0 (by decide)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem flipTailDpScratch80_comm_of_disj (S : ℕ → Prop)
    (f : BitAssignment 80 → BitAssignment 80) (p : BitAssignment 80)
    (hDisj : ¬ S 0 ∧ ¬ S 1 ∧ ¬ S 2 ∧ ¬ S 30 ∧ ¬ S 75 ∧ ¬ S 76 ∧ ¬ S 77)
    (hOut : ∀ r (j : Fin 80), ¬ S j.val → f r j = r j)
    (hIn : ∀ j : Fin 80, S j.val → f (flipTailDpScratch80 p) j = f p j) :
    flipTailDpScratch80 (f p) = f (flipTailDpScratch80 p) := by
  rcases hDisj with ⟨hd0, hd1, hd2, hd30, hd75, hd76, hd77⟩
  funext j
  by_cases hj : S j.val
  · rw [flipTailDpScratch80_preserve (f p) j
      ⟨fun h ↦ hd75 (h ▸ hj), fun h ↦ hd76 (h ▸ hj), fun h ↦ hd77 (h ▸ hj)⟩, hIn j hj]
  · rw [hOut (flipTailDpScratch80 p) j hj]
    unfold flipTailDpScratch80
    rw [hOut p 30 hd30]
    by_cases hc : (p 30 == 1) = true
    · simp [hc, hOut p j hj]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, hOut p j hj,
        hOut p 75 hd75, hOut p 76 hd76, hOut p 77 hd77,
        hOut p 0 hd0, hOut p 1 hd1, hOut p 2 hd2]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem flip_clearB0_comm (p : BitAssignment 80) :
    p80ClearB0Local (flipTailDpScratch80 p) = flipTailDpScratch80 (p80ClearB0Local p) :=
  (flipTailDpScratch80_comm_of_disj (fun n ↦ 3 ≤ n ∧ n < 6) p80ClearB0Local p
    (by omega) (fun r j hj ↦ p80ClearB0Local_out r j hj)
    (fun j hj ↦ by
      unfold p80ClearB0Local
      simp [hj])).symm
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p80NucVal_eq_bitsVal (p : BitAssignment 80) : MergedVepTopCoinCollapse.p80NucVal p =
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j)) := rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p80NucVal_flipTailDpScratch80 (p : BitAssignment 80) :
    MergedVepTopCoinCollapse.p80NucVal (flipTailDpScratch80 p) =
      MergedVepTopCoinCollapse.p80NucVal p := by
  rw [p80NucVal_eq_bitsVal, p80NucVal_eq_bitsVal]
  congr 1
  funext j
  exact flipTailDpScratch80_preserve p (pos80SubIdx 6 8 (by decide) j)
    ⟨by
      dsimp [pos80SubIdx]
      omega, by
      dsimp [pos80SubIdx]
      omega, by
      dsimp [pos80SubIdx]
      omega⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem muSlot2Ideal216_eq_zero_of_guard (p : BitAssignment 80)
    (h : ¬(Pos24HeadCoordXor80.bitsVal
        (fun j : Fin 8 ↦ flipTailDpScratch80 p (pos80SubIdx 6 8 (by decide) j)) < 216) ∨
      (Pos24HeadCoordXor80.bitsVal
        (fun j : Fin 3 ↦ flipTailDpScratch80 p (pos80SubIdx 3 3 (by decide) j)) == 0) = false) :
    muSlot2Ideal216 p = 0 := by
  unfold muSlot2Ideal216 pos80IdealDist
  by_cases h62 : (flipTailDpScratch80 p 62 != 0) = true
  · simp [h62]
  · simp only [h62, Bool.false_eq_true, ↓reduceIte]
    rcases h with hnuc | hbFalse
    · by_cases h30 : (flipTailDpScratch80 p 30 == 1) = true
      · simp only [h30, ↓reduceIte, hnuc, decide_false, Bool.false_eq_true,
          Bool.and_false, Bool.false_and]
        split_ifs <;> rfl
      · simp only [h30, Bool.false_eq_true, ↓reduceIte, hnuc, decide_false,
          Bool.and_false, Bool.false_and]
    · by_cases h30 : (flipTailDpScratch80 p 30 == 1) = true
      · simp only [h30, ↓reduceIte, hbFalse, Bool.false_eq_true, decide_false,
          Bool.and_false, Bool.false_and]
        split_ifs <;> rfl
      · simp only [h30, Bool.false_eq_true, ↓reduceIte, hbFalse, Bool.false_and, Bool.and_false]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem muSlot2Ideal216_eq_zero_of_nuc_ge_216 (p : BitAssignment 80)
    (hge : 216 ≤ MergedVepTopCoinCollapse.p80NucVal p) : muSlot2Ideal216 p = 0 :=
  muSlot2Ideal216_eq_zero_of_guard p (.inl (by
    rw [← p80NucVal_eq_bitsVal, p80NucVal_flipTailDpScratch80]
    omega))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem muSlot2Ideal216_eq_zero_of_b0_ne_zero (p : BitAssignment 80)
    (hb0 : MergedVepTopCoinCollapse.p80CosetP3 p ≠ 0) : muSlot2Ideal216 p = 0 := by
  refine muSlot2Ideal216_eq_zero_of_guard p
    (.inr (beq_false_of_ne fun hZero ↦ hb0 (funext fun w ↦ ?_)))
  have hz := z2BitOfNat_bitsVal
    (fun j : Fin 3 ↦ flipTailDpScratch80 p (pos80SubIdx 3 3 (by decide) j)) w
  rw [hZero, flipTailDpScratch80_preserve p (pos80SubIdx 3 3 (by decide) w) ⟨by
    dsimp [pos80SubIdx]
    omega, by
    dsimp [pos80SubIdx]
    omega, by
    dsimp [pos80SubIdx]
    omega⟩] at hz
  dsimp [pos80SubIdx] at hz
  have hv : (p ⟨3 + w.val, by omega⟩).val = 0 := by
    rw [← hz, z2BitOfNat_val]
    simp
  exact Fin.ext hv
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem flip_setCosetAndNuc_comm (l : Fin 256) (p : BitAssignment 80) :
    flipTailDpScratch80 (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l p) =
      MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l (flipTailDpScratch80 p) :=
  flipTailDpScratch80_comm_of_disj (fun n ↦ 3 ≤ n ∧ n < 14)
    (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l) p (by omega)
    (fun r j hj ↦ by
      unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc
      rw [dite_eq_right (by omega), dite_eq_right (by omega)])
    (fun j hj ↦ by
      unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc
      by_cases h36 : 3 ≤ j.val ∧ j.val < 6
      · simp [h36]
      · simp [h36, show 6 ≤ j.val ∧ j.val < 14 by omega])
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p80ClearCosetAndNucLocal_eq_set0 (p : BitAssignment 80) :
    p80ClearCosetAndNucLocal p = MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 0 p := by
  funext q
  unfold p80ClearCosetAndNucLocal MergedVepTopCoinCollapse.p80SetCosetAndNuc
  by_cases h36 : 3 ≤ q.val ∧ q.val < 6
  · have h314 : 3 ≤ q.val ∧ q.val < 14 := ⟨h36.1, by omega⟩
    simp [h36, h314]
  · by_cases h614 : 6 ≤ q.val ∧ q.val < 14
    · have h314 : 3 ≤ q.val ∧ q.val < 14 := ⟨by omega, h614.2⟩
      simp [h614, h314]
    · have h314 : ¬(3 ≤ q.val ∧ q.val < 14) := by omega
      simp [h36, h614, h314]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem natModTwoCast_eq_z2BitOfNat (x i : ℕ) :
    (((x / 2 ^ i) % 2 : ℕ) : ZMod 2) = z2BitOfNat x i := by
  unfold z2BitOfNat
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h
  · simp [h]
  · simp [h]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem p80SetCosetAndNuc_out (m : Fin 256) (q : BitAssignment 80) (j : Fin 80)
    (hj : j.val < 3 ∨ 14 ≤ j.val) :
    MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m q j = q j := by
  unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem p80SetCosetAndNuc_pay_beq_eq (m₁ m₂ : Fin 256) (q : BitAssignment 80)
    (pay : ℕ → BitAssignment 80)
    (h36 : ∀ m (j : Fin 80), ¬(j.val < 3) → j.val < 6 → pay m j = 0)
    (h614 : ∀ m (j : Fin 80), ¬(j.val < 3) → ¬(j.val < 6) → j.val < 14 →
      pay m j = z2BitOfNat m (j.val - 6))
    (hOut : ∀ m (j : Fin 80), (j.val < 3 ∨ 14 ≤ j.val) → pay m j = pay 0 j) :
    (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m₁ q == pay m₁.val) =
      (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m₂ q == pay m₂.val) := by
  have hImp : ∀ (a b : Fin 256),
      MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 a q = pay a.val →
      MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 b q = pay b.val := by
    intro a b hEq
    funext j
    by_cases hj3 : j.val < 3
    · have hj := congrFun hEq j
      rw [p80SetCosetAndNuc_out a q j (.inl hj3)] at hj
      rw [p80SetCosetAndNuc_out b q j (.inl hj3), hj, hOut a.val j (.inl hj3),
        ← hOut b.val j (.inl hj3)]
    · by_cases hj6 : j.val < 6
      · unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc
        rw [dite_eq_left (by omega), h36 b.val j hj3 hj6]
        simp
      · by_cases hj14 : j.val < 14
        · unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc
          rw [dite_eq_right (by omega), dite_eq_left (by omega), h614 b.val j hj3 hj6 hj14]
          exact natModTwoCast_eq_z2BitOfNat b.val (j.val - 6)
        · have hge : j.val < 3 ∨ 14 ≤ j.val := .inr (by omega)
          have hj := congrFun hEq j
          rw [p80SetCosetAndNuc_out a q j hge] at hj
          rw [p80SetCosetAndNuc_out b q j hge, hj, hOut a.val j hge, ← hOut b.val j hge]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨hImp m₁ m₂, hImp m₂ m₁⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pos80IdealDist_false_setCosetAndNuc_eq (l : Fin 256) (hl : l.val < 216)
    (q : BitAssignment 80) :
    pos80IdealDist false (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l q) =
      pos80IdealDist false (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 0 q) := by
  set qL := MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l q with hqL_def
  set q0 := MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 0 q with hq0_def
  have hOutEq : ∀ j : Fin 80, (j.val < 3 ∨ 14 ≤ j.val) → qL j = q0 j := fun j hj ↦
    (p80SetCosetAndNuc_out l q j hj).trans (p80SetCosetAndNuc_out 0 q j hj).symm
  have hB0Gen : ∀ m : Fin 256,
      Pos24HeadCoordXor80.bitsVal
        (fun j : Fin 3 ↦ MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m q
          (pos80SubIdx 3 3 (by decide) j)) = 0 := fun m ↦ by
    have hfn : (fun j : Fin 3 ↦ MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m q
        (pos80SubIdx 3 3 (by decide) j)) = fun j : Fin 3 ↦ z2BitOfNat 0 j.val := by
      funext j
      unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc pos80SubIdx z2BitOfNat
      simp [show 3 ≤ 3 + j.val ∧ 3 + j.val < 6 by omega]
    rw [hfn]
    exact bitsVal_z2BitOfNat 3 0 (by decide)
  have hNucGen : ∀ m : Fin 256,
      Pos24HeadCoordXor80.bitsVal
        (fun j : Fin 8 ↦ MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m q
          (pos80SubIdx 6 8 (by decide) j)) = m.val := fun m ↦ by
    have hfn : (fun j : Fin 8 ↦ MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m q
        (pos80SubIdx 6 8 (by decide) j)) = fun j : Fin 8 ↦ z2BitOfNat m.val j.val := by
      funext j
      unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc pos80SubIdx
      dsimp only
      rw [dite_eq_right (by omega), dite_eq_left (by omega), natModTwoCast_eq_z2BitOfNat]
      exact congrArg (z2BitOfNat m.val) (by omega)
    rw [hfn]
    exact bitsVal_z2BitOfNat 8 m.val m.isLt
  have hEqSlice : ∀ (off a : ℕ) (h : off + a ≤ 80), 14 ≤ off →
      (fun j : Fin a ↦ qL (pos80SubIdx off a h j)) =
      (fun j : Fin a ↦ q0 (pos80SubIdx off a h j)) := fun off a h hoff ↦
    funext fun j ↦ hOutEq _ (.inr (by
      dsimp [pos80SubIdx]
      omega))
  have hHeadEq : ∀ (anc : ℕ) (k : Fin 56) (pid : Fin 6) (sm : Fin 8) (t r : Bool),
      (qL == headWitnessPayload80 0 l.val anc k pid sm t r) =
      (q0 == headWitnessPayload80 0 0 anc k pid sm t r) := fun anc k pid sm t r ↦
    p80SetCosetAndNuc_pay_beq_eq l 0 q
      (fun m ↦ headWitnessPayload80 0 m anc k pid sm t r)
      (fun _ j hj3 hj6 ↦ by simp [headWitnessPayload80, hj3, hj6, z2BitOfNat])
      (fun _ j hj3 hj6 hj14 ↦ by simp [headWitnessPayload80, hj3, hj6, hj14])
      (fun _ j hj ↦ by
        rcases hj with hj3 | hj14
        · simp [headWitnessPayload80, hj3]
        · simp [headWitnessPayload80, show ¬(j.val < 3) by omega,
            show ¬(j.val < 6) by omega, show ¬(j.val < 14) by omega])
  have hTailEq : ∀ (anc part : ℕ) (dp : Fin 8) (keep : ℕ) (t r : Bool),
      (qL == tailWitnessPayload80 0 l.val anc part dp keep t r) =
      (q0 == tailWitnessPayload80 0 0 anc part dp keep t r) := fun anc part dp keep t r ↦
    p80SetCosetAndNuc_pay_beq_eq l 0 q
      (fun m ↦ tailWitnessPayload80 0 m anc part dp keep t r)
      (fun _ j hj3 hj6 ↦ by simp [tailWitnessPayload80, hj3, hj6, z2BitOfNat])
      (fun _ j hj3 hj6 hj14 ↦ by simp [tailWitnessPayload80, hj3, hj6, hj14])
      (fun _ j hj ↦ by
        rcases hj with hj3 | hj14
        · simp [tailWitnessPayload80, hj3]
        · simp [tailWitnessPayload80, show ¬(j.val < 3) by omega,
            show ¬(j.val < 6) by omega, show ¬(j.val < 14) by omega])
  have hScrEq : (∀ j : Fin 12, qL (pos80SubIdx 63 12 (by decide) j) = 0) ↔
      (∀ j : Fin 12, q0 (pos80SubIdx 63 12 (by decide) j) = 0) :=
    forall_congr' fun j ↦ by rw [congrFun (hEqSlice 63 12 (by decide) (by decide)) j]
  change pos80IdealDist false qL = pos80IdealDist false q0
  unfold pos80IdealDist
  dsimp only
  rw [hB0Gen l, hB0Gen 0, hNucGen l, hNucGen 0,
    show (0 : Fin 256).val = 0 from rfl,
    hEqSlice 14 8 (by decide) (by decide),
    hEqSlice 22 8 (by decide) (by decide),
    hEqSlice 32 30 (by decide) (by decide),
    hOutEq 62 (by decide), hOutEq 30 (by decide), hOutEq 31 (by decide),
    hOutEq 75 (by decide), hOutEq 76 (by decide), hOutEq 77 (by decide),
    hOutEq 78 (by decide), hOutEq 79 (by decide)]
  have hl0 : (0 : ℕ) < 216 := by decide
  by_cases hc62 : (q0 62 != 0) = true
  · rw [ite_pos hc62, ite_pos hc62]
  · rw [ite_neg hc62, ite_neg hc62]
    by_cases hc30 : (q0 30 == 1) = true
    · simp only [hc30, ↓reduceIte, Bool.false_eq_true, hl, hl0, decide_true,
        hEqSlice 63 6 (by decide) (by decide), hEqSlice 69 3 (by decide) (by decide),
        hEqSlice 72 3 (by decide) (by decide)]
      by_cases hk :
          Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ q0 (pos80SubIdx 63 6 (by decide) j)) < 56
      · by_cases hp :
            Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q0 (pos80SubIdx 69 3 (by decide) j)) < 6
        · simp only [hk, hp, ↓reduceDIte, hHeadEq]
        · simp only [hk, hp, ↓reduceDIte]
      · simp only [hk, ↓reduceDIte]
    · simp only [hc30, Bool.false_eq_true, ↓reduceIte, hl, hl0, decide_true,
        hScrEq, hEqSlice 75 3 (by decide) (by decide), hTailEq]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen (qRatio : ℝ) (b2 :
    SpecsAux.SpecMirror.Configuration → Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (cfg : SpecsAux.SpecMirror.Configuration) : MergedVepTopCoinCollapse.mMergedBUnitTwosGen qRatio
    b2 cfg = Pos24MergedVepPrepAndStitch.mergedPosSlot2BUnitTwosGen qRatio b2 cfg := by
  have hr : MergedVepTopCoinCollapse.mProj24_sp = PosSlots24MergedVepBound.rProj24_sp := rfl
  have hg : MergedVepTopCoinCollapse.mProjGridEquiv24 = PosSlots24MergedVepBound.projGridEquiv24 :=
    by
    ext x w; rfl
  have hc : ProjZ512QftAndTwist288.cfgProjZ512 = PosSlots24MergedVepBound.cfgProjZ512 := rfl
  have hpg : ProjZ512QftAndTwist288.projGridEquiv24 = PosSlots24MergedVepBound.projGridEquiv24 := by
    ext x w; rfl
  have hpt : ProjZ512QftAndTwist288.projTwosMom3D = PosSlots24MergedVepBound.projTwosMom3D := by
    funext uIdx w
    simp only [ProjZ512QftAndTwist288.projTwosMom3D, PosSlots24MergedVepBound.projTwosMom3D, hpg]
  have hu : ProjZ512QftAndTwist288.uProjPlus512_3D = PosSlots24MergedVepBound.uProjPlus512_3D := by
    funext b; apply Subtype.ext
    rw [ProjZ512QftAndTwist288.uProjPlus512_3D_val]
    change ProjZ512QftAndTwist288.uProjPlus512TwosMat3D b =
      PosSlots24MergedVepBound.uProjPlus512TwosMat3D b
    ext yIdx uIdx
    simp only[ProjZ512QftAndTwist288.uProjPlus512TwosMat3D,
        PosSlots24MergedVepBound.uProjPlus512TwosMat3D, Matrix.of_apply, hpg, hpt]
  have hp : ∀ yIdx,
    MergedVepTopCoinCollapse.mProjBasisGen PosSlots24MergedVepBound.rProj24_sp yIdx =
      PosSlots24MergedVepBound.projBasisGen PosSlots24MergedVepBound.rProj24_sp yIdx := fun _ ↦ rfl
  unfold MergedVepTopCoinCollapse.mMergedBUnitTwosGen MergedVepTopCoinCollapse.mVepFromSlot2TwosOp
    MergedVepTopCoinCollapse.mVepGen Pos24MergedVepPrepAndStitch.mergedPosSlot2BUnitTwosGen
    PosSlots24MergedVepBound.vepFromSlot2TwosOp PosSlots24MergedVepBound.vepGen
  rw [hr, hg, hc, hu]
  simp_rw [hp]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_eq_of_witness_inj {ι : Type*} [Fintype ι]
    (enc : ι → BitAssignment 80) (w : ι → ℝ) (f : BitAssignment 80 → ℝ)
    (hInj : Function.Injective enc) (hOn : ∀ x : ι, f (enc x) = w x)
    (hOff : ∀ p : BitAssignment 80, (∀ x : ι, p ≠ enc x) → f p = 0) :
    (∑ p : BitAssignment 80, f p) = ∑ x : ι, w x := by
  have hSub : (Finset.univ.image enc) ⊆ (Finset.univ : Finset (BitAssignment 80)) :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hSub (fun p _ hp ↦ hOff p
      (fun x hx ↦ hp (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx.symm⟩))),
    Finset.sum_image (fun _ _ _ _ hxy ↦ hInj hxy)]
  exact Finset.sum_congr rfl fun x _ ↦ hOn x
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_prod_eq_mul {α β : Type*} [Fintype α] [Fintype β] (a₁ : α → ℝ) (a₂ : β → ℝ) :
    (∑ p : α × β, a₁ p.1 * a₂ p.2) = (∑ x, a₁ x) * (∑ y, a₂ y) := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_prod_eq_one {α β : Type*} [Fintype α] [Fintype β] (a₁ : α → ℝ) (a₂ : β → ℝ)
    (h₁ : ∑ x, a₁ x = 1) (h₂ : ∑ y, a₂ y = 1) : (∑ p : α × β, a₁ p.1 * a₂ p.2) = 1 := by
  rw [sum_prod_eq_mul a₁ a₂, h₁, h₂, mul_one]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_cond_eq_one {α β : Type*} [Fintype α] [Fintype β] (a₁ : α → ℝ) (a₂ : α → β → ℝ)
    (h₁ : ∑ x, a₁ x = 1) (h₂ : ∀ x, ∑ y, a₂ x y = 1) : (∑ p : α × β, a₁ p.1 * a₂ p.1 p.2) = 1
    := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, h₂, mul_one]
  exact h₁
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_prod_abs_sub_le {α β : Type*} [Fintype α] [Fintype β]
    (a₁ b₁ : α → ℝ) (a₂ b₂ : β → ℝ)
    (ha₁ : ∀ x, 0 ≤ a₁ x) (hSumA₁ : ∑ x, a₁ x = 1)
    (hb₂ : ∀ y, 0 ≤ b₂ y) (hSumB₂ : ∑ y, b₂ y = 1) :
    (∑ p : α × β, |a₁ p.1 * a₂ p.2 - b₁ p.1 * b₂ p.2|) ≤
      (∑ x, |a₁ x - b₁ x|) + (∑ y, |a₂ y - b₂ y|) := by
  rw [Fintype.sum_prod_type]
  have hPt : ∀ x y, |a₁ x * a₂ y - b₁ x * b₂ y| ≤
      a₁ x * |a₂ y - b₂ y| + |a₁ x - b₁ x| * b₂ y := fun x y ↦ by
    have hId : a₁ x * a₂ y - b₁ x * b₂ y =
        a₁ x * (a₂ y - b₂ y) + (a₁ x - b₁ x) * b₂ y := by ring
    rw [hId]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul, abs_of_nonneg (ha₁ x), abs_of_nonneg (hb₂ y)])
  calc ∑ x, ∑ y, |a₁ x * a₂ y - b₁ x * b₂ y|
      ≤ ∑ x, ∑ y, (a₁ x * |a₂ y - b₂ y| + |a₁ x - b₁ x| * b₂ y) :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦ hPt x y
    _ = (∑ x, a₁ x) * (∑ y, |a₂ y - b₂ y|) +
        (∑ x, |a₁ x - b₁ x|) * (∑ y, b₂ y) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = (∑ x, |a₁ x - b₁ x|) + (∑ y, |a₂ y - b₂ y|) := by
        rw [hSumA₁, hSumB₂]; ring
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem split_mixture_abs_sub_le {H T : Type*} [Fintype H] [Fintype T]
    (pH pT qH qT : ℝ) (aH bH : H → ℝ) (aT bT : T → ℝ) (eP eH eT : ℝ)
    (hqH : 0 ≤ qH) (hqT : 0 ≤ qT)
    (hpSum : pH + pT = 1) (hqSum : qH + qT = 1)
    (haH : ∀ x, 0 ≤ aH x) (hSumAH : ∑ x, aH x = 1)
    (haT : ∀ y, 0 ≤ aT y) (hSumAT : ∑ y, aT y = 1)
    (hSplit : |pT - qT| ≤ eP)
    (hHead : (∑ x, |aH x - bH x|) ≤ eH)
    (hTail : (∑ y, |aT y - bT y|) ≤ eT) :
    (∑ x : H, |pH * aH x - qH * bH x|) + (∑ y : T, |pT * aT y - qT * bT y|) ≤
      2 * eP + qH * eH + qT * eT := by
  have hpHqH : |pH - qH| ≤ eP := by
    have hneg : pH - qH = -(pT - qT) := by linarith
    rw [hneg, abs_neg]; exact hSplit
  have h1 : (∑ x : H, |pH * aH x - qH * bH x|) ≤ eP + qH * eH := by
    have hPt : ∀ x, |pH * aH x - qH * bH x| ≤
        |pH - qH| * aH x + qH * |aH x - bH x| := fun x ↦ by
      have hId : pH * aH x - qH * bH x = (pH - qH) * aH x + qH * (aH x - bH x) := by ring
      rw [hId]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul, abs_mul, abs_of_nonneg (haH x), abs_of_nonneg hqH])
    calc ∑ x : H, |pH * aH x - qH * bH x|
        ≤ ∑ x : H, (|pH - qH| * aH x + qH * |aH x - bH x|) :=
          Finset.sum_le_sum fun x _ ↦ hPt x
      _ = |pH - qH| * (∑ x, aH x) + qH * (∑ x, |aH x - bH x|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ eP + qH * eH := by
          rw [hSumAH, mul_one]
          exact add_le_add hpHqH (mul_le_mul_of_nonneg_left hHead hqH)
  have h2 : (∑ y : T, |pT * aT y - qT * bT y|) ≤ eP + qT * eT := by
    have hPt : ∀ y, |pT * aT y - qT * bT y| ≤
        |pT - qT| * aT y + qT * |aT y - bT y| := fun y ↦ by
      have hId : pT * aT y - qT * bT y = (pT - qT) * aT y + qT * (aT y - bT y) := by ring
      rw [hId]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul, abs_mul, abs_of_nonneg (haT y), abs_of_nonneg hqT])
    calc ∑ y : T, |pT * aT y - qT * bT y|
        ≤ ∑ y : T, (|pT - qT| * aT y + qT * |aT y - bT y|) :=
          Finset.sum_le_sum fun y _ ↦ hPt y
      _ = |pT - qT| * (∑ y, aT y) + qT * (∑ y, |aT y - bT y|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ eP + qT * eT := by
          rw [hSumAT, mul_one]
          exact add_le_add hSplit (mul_le_mul_of_nonneg_left hTail hqT)
  linarith
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headShell64Weights_eq_pos24 (k : Fin 56) : headShell64Weights
    ⟨k.val, lt_trans k.isLt (by decide)⟩ = PosSlots24SemanticBridge.pos24HeadWeight56 k := by
  revert k; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headShell64Weights_zero_ge56 (j : Fin (2 ^ 6)) (hj : 56 ≤ j.val) :
    headShell64Weights j = 0 := by
  revert j; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_pos24HeadWeight56_eq :
    (∑ k : Fin 56, (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) / (727884457843 : ℝ)) = 1 :=
      by
  rw [← Finset.sum_div]
  have hNat : (∑ k : Fin 56, PosSlots24SemanticBridge.pos24HeadWeight56 k) = 727884457843 := by
    decide
  have hReal : (∑ k : Fin 56, (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ)) =
      ((∑ k : Fin 56, PosSlots24SemanticBridge.pos24HeadWeight56 k : ℕ) : ℝ) := by
    push_cast; rfl
  rw [hReal, hNat]
  norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailSpan_eq_tailDp8Weights (dp : Fin (2 ^ 3)) :
    tailKeepSpanOfDp dp = tailDp8Weights dp := by
  revert dp; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailSpan_eq_pos24TailSpan8 (dp : Fin (2 ^ 3)) :
    tailKeepSpanOfDp dp = PosSlots24SemanticBridge.pos24TailSpan8 dp := by
  revert dp; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailSpan_bounds (dp : Fin (2 ^ 3)) :
    1 ≤ tailKeepSpanOfDp dp ∧ tailKeepSpanOfDp dp ≤ 2 ^ 30 := by
  fin_cases dp <;> dsimp [tailKeepSpanOfDp] <;> norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev NucB0Idx := Fin (2 ^ 8) × Fin (2 ^ 3)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev HeadRestIdx := Fin (2 ^ 8) × Fin 56 × Fin (2 ^ 3) × Fin (2 ^ 3) × (Bool × Bool)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev HeadIdx := NucB0Idx × HeadRestIdx
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev DpKeepIdx := Fin (2 ^ 3) × Fin (2 ^ 30)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev TailRestIdx := Fin (2 ^ 8) × Fin (2 ^ 8) × DpKeepIdx × (Bool × Bool)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev TailIdx := NucB0Idx × TailRestIdx
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def writeB0Raw (b0 : Fin (2 ^ 3)) (q : BitAssignment 80) : BitAssignment 80 :=
  fun i ↦ if 3 ≤ i.val ∧ i.val < 6 then z2BitOfNat b0.val (i.val - 3) else q i
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem writeB0Raw_out (b0 : Fin (2 ^ 3)) (q : BitAssignment 80) (i : Fin 80)
    (hi : ¬(3 ≤ i.val ∧ i.val < 6)) : writeB0Raw b0 q i = q i := by
  unfold writeB0Raw
  simp [hi]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem writeB0Raw_b0Val (b0 : Fin (2 ^ 3)) (q : BitAssignment 80) :
    Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ writeB0Raw b0 q (pos80SubIdx 3 3 (by decide) j)) = b0.val := by
  have hfn : (fun j : Fin 3 ↦ writeB0Raw b0 q (pos80SubIdx 3 3 (by decide) j)) =
      fun j : Fin 3 ↦ z2BitOfNat b0.val j.val := by
    funext j
    unfold writeB0Raw pos80SubIdx
    rw [itePosLocal (show 3 ≤ 3 + j.val ∧ 3 + j.val < 6 by omega)]
    exact congrArg (z2BitOfNat b0.val) (by dsimp; omega)
  rw [hfn]
  exact bitsVal_z2BitOfNat 3 b0.val b0.isLt
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem clearB0_writeB0Raw (b0 : Fin (2 ^ 3)) (q : BitAssignment 80)
    (hq0 : ∀ i : Fin 80, 3 ≤ i.val ∧ i.val < 6 → q i = 0) :
    p80ClearB0Local (writeB0Raw b0 q) = q := by
  funext i
  unfold p80ClearB0Local writeB0Raw
  by_cases hi : 3 ≤ i.val ∧ i.val < 6
  · simp [hi, hq0 i hi]
  · simp [hi]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem writeB0Raw_clearB0_self (p : BitAssignment 80) :
    writeB0Raw ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)),
        bitsVal_lt_two_pow_local _⟩ (p80ClearB0Local p) = p := by
  funext i
  by_cases hi : 3 ≤ i.val ∧ i.val < 6
  · unfold writeB0Raw
    rw [itePosLocal hi]
    let j : Fin 3 := ⟨i.val - 3, by omega⟩
    have hz := z2BitOfNat_bitsVal (fun w : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) w)) j
    have hij : pos80SubIdx 3 3 (by decide) j = i := Fin.ext (by dsimp [pos80SubIdx, j]; omega)
    simpa [j, hij] using hz
  · rw [writeB0Raw_out _ _ i hi, p80ClearB0Local_out p i hi]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def encHead (s0 : Bool) (x : HeadIdx) : BitAssignment 80 :=
  let nb := x.1
  let r := x.2
  if s0 then
    headGeneralPayload80 nb.2.val nb.1.val r.1.val r.2.1 r.2.2.1.val r.2.2.2.1
      r.2.2.2.2.1 r.2.2.2.2.2
  else
    writeB0Raw nb.2 (headGeneralPayload80 0 nb.1.val r.1.val r.2.1 r.2.2.1.val r.2.2.2.1
      r.2.2.2.2.1 r.2.2.2.2.2)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def encTail (s0 : Bool) (y : TailIdx) : BitAssignment 80 :=
  let nb := y.1
  let r := y.2
  if s0 then
    tailWitnessPayload80 nb.2.val nb.1.val r.1.val r.2.1.val r.2.2.1.1 r.2.2.1.2.val
      r.2.2.2.1 r.2.2.2.2
  else
    writeB0Raw nb.2 (tailWitnessPayload80 0 nb.1.val r.1.val r.2.1.val r.2.2.1.1 r.2.2.1.2.val
      r.2.2.2.1 r.2.2.2.2)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def encAll (s0 : Bool) : HeadIdx ⊕ TailIdx → BitAssignment 80 :=
  Sum.elim (encHead s0) (encTail s0)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem z2BitOfNat_zero_local (m : ℕ) : z2BitOfNat 0 m = 0 := by
  unfold z2BitOfNat; simp
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_eq (b0Val nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (thresh rej0 : Bool) :
    headGeneralPayload80 b0Val nuc anc k pidVal sm thresh rej0 =
      if hp : pidVal < 6 then
        headWitnessPayload80 b0Val nuc anc k ⟨pidVal, hp⟩ sm thresh rej0
      else
        fun q ↦
          let i := q.val
          if i < 3 then z2BitOfNat b0Val i
          else if i < 6 then z2BitOfNat b0Val (i - 3)
          else if i < 14 then z2BitOfNat nuc (i - 6)
          else if i < 22 then z2BitOfNat anc (i - 14)
          else if i < 30 then 0
          else if i == 30 then 1
          else if i == 31 then (if thresh then 1 else 0)
          else if i < 62 then 0
          else if i == 62 then 0
          else if i < 69 then z2BitOfNat k.val (i - 63)
          else if i < 72 then z2BitOfNat pidVal (i - 69)
          else if i < 75 then z2BitOfNat sm.val (i - 72)
          else if i < 79 then 0
          else (if rej0 then 1 else 0) := by
  funext q
  unfold headGeneralPayload80 headJointPayload80
  by_cases hp : pidVal < 6
  · simp only [hp, ↓reduceDIte]
    by_cases h22 : 22 ≤ q.val ∧ q.val < 30
    · rw [ite_pos h22, z2BitOfNat_zero_local]
      unfold headWitnessPayload80
      simp [show ¬(q.val < 3) by omega, show ¬(q.val < 6) by omega,
        show ¬(q.val < 14) by omega, show ¬(q.val < 22) by omega, h22.2]
    · rw [ite_neg h22]
  · simp only [hp, ↓reduceDIte, z2BitOfNat_zero_local]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_b0_zero (nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (t r : Bool) (i : Fin 80) (hi : 3 ≤ i.val ∧ i.val < 6) :
    headGeneralPayload80 0 nuc anc k pidVal sm t r i = 0 := by
  have hi3 : ¬(i.val < 3) := by omega
  have hi6 : i.val < 6 := hi.2
  rw [headGeneralPayload80_eq]
  by_cases hp : pidVal < 6 <;> simp [hp, headWitnessPayload80, hi3, hi6, z2BitOfNat]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailWitnessPayload80_b0_zero (nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ)
    (t r : Bool) (i : Fin 80) (hi : 3 ≤ i.val ∧ i.val < 6) :
    tailWitnessPayload80 0 nuc anc part dp keep t r i = 0 := by
  have hi3 : ¬(i.val < 3) := by omega
  have hi6 : i.val < 6 := hi.2
  simp [tailWitnessPayload80, hi3, hi6, z2BitOfNat]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_at30 (b0 nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (t r : Bool) : headGeneralPayload80 b0 nuc anc k pidVal sm t r 30 = 1 := by
  rw [headGeneralPayload80_eq]
  by_cases hp : pidVal < 6 <;> simp only [hp, ↓reduceDIte] <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_at62 (b0 nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (t r : Bool) : headGeneralPayload80 b0 nuc anc k pidVal sm t r 62 = 0 := by
  rw [headGeneralPayload80_eq]
  by_cases hp : pidVal < 6 <;> simp only [hp, ↓reduceDIte] <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_remZero (b0 nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (t r : Bool) : ((headGeneralPayload80 b0 nuc anc k pidVal sm t r 75 == 0) &&
    (headGeneralPayload80 b0 nuc anc k pidVal sm t r 76 == 0) && (headGeneralPayload80 b0 nuc
    anc k pidVal sm t r 77 == 0) && (headGeneralPayload80 b0 nuc anc k pidVal sm t r 78 == 0))
    = true := by
  rw [headGeneralPayload80_eq]
  by_cases hp : pidVal < 6 <;> simp only [hp, ↓reduceDIte] <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_at31 (b0 nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (t r : Bool) : (headGeneralPayload80 b0 nuc anc k pidVal sm t r 31 == 1) = t := by
  rw [headGeneralPayload80_eq]
  by_cases hp : pidVal < 6 <;> cases t <;> simp only [hp, ↓reduceDIte] <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_at79 (b0 nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (t r : Bool) : (headGeneralPayload80 b0 nuc anc k pidVal sm t r 79 == 1) = r := by
  rw [headGeneralPayload80_eq]
  by_cases hp : pidVal < 6 <;> cases r <;> simp only [hp, ↓reduceDIte] <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem headGeneralPayload80_slices
    (b0 : ℕ) (hb0 : b0 < 2 ^ 3) (nuc : Fin (2 ^ 8)) (anc : Fin (2 ^ 8))
    (k : Fin 56) (pid : Fin (2 ^ 3)) (sm : Fin (2 ^ 3)) (t r : Bool) :
    let q := headGeneralPayload80 b0 nuc.val anc.val k pid.val sm t r
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) = b0 ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j)) = nuc.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j)) = anc.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) = 0 ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ q (pos80SubIdx 63 6 (by decide) j)) = k.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 69 3 (by decide) j)) = pid.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 72 3 (by decide) j)) = sm.val := by
  intro q
  have hB0 : (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) =
      fun j : Fin 3 ↦ z2BitOfNat b0 j.val := by
    funext j; dsimp only [q]
    rw [headGeneralPayload80_eq]
    unfold headWitnessPayload80 pos80SubIdx
    by_cases hp : pid.val < 6 <;> simp only [hp, ↓reduceDIte,
      show ¬(3 + j.val < 3) by omega, show 3 + j.val < 6 by omega, ↓reduceIte] <;>
      exact congrArg (z2BitOfNat b0) (by omega)
  have hNuc : (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat nuc.val j.val := by
    funext j; dsimp only [q]
    rw [headGeneralPayload80_eq]
    unfold headWitnessPayload80 pos80SubIdx
    by_cases hp : pid.val < 6 <;> simp only [hp, ↓reduceDIte,
      show ¬(6 + j.val < 3) by omega, show ¬(6 + j.val < 6) by omega,
      show 6 + j.val < 14 by omega, ↓reduceIte] <;>
      exact congrArg (z2BitOfNat nuc.val) (by omega)
  have hAnc : (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat anc.val j.val := by
    funext j; dsimp only [q]
    rw [headGeneralPayload80_eq]
    unfold headWitnessPayload80 pos80SubIdx
    by_cases hp : pid.val < 6 <;> simp only [hp, ↓reduceDIte,
      show ¬(14 + j.val < 3) by omega, show ¬(14 + j.val < 6) by omega,
      show ¬(14 + j.val < 14) by omega, show 14 + j.val < 22 by omega, ↓reduceIte] <;>
      exact congrArg (z2BitOfNat anc.val) (by omega)
  have hPart : (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat 0 j.val := by
    funext j; dsimp only [q]
    rw [headGeneralPayload80_eq]
    unfold headWitnessPayload80 pos80SubIdx z2BitOfNat
    by_cases hp : pid.val < 6 <;> simp [hp, show ¬(22 + j.val < 3) by omega,
      show ¬(22 + j.val < 6) by omega, show ¬(22 + j.val < 14) by omega,
      show ¬(22 + j.val < 22) by omega, show 22 + j.val < 30 by omega]
  have hK : (fun j : Fin 6 ↦ q (pos80SubIdx 63 6 (by decide) j)) =
      fun j : Fin 6 ↦ z2BitOfNat k.val j.val := by
    funext j; dsimp only [q]
    rw [headGeneralPayload80_eq]
    unfold headWitnessPayload80 pos80SubIdx
    by_cases hp : pid.val < 6 <;> simp only [hp, ↓reduceDIte,
      show ¬(63 + j.val < 3) by omega, show ¬(63 + j.val < 6) by omega,
      show ¬(63 + j.val < 14) by omega, show ¬(63 + j.val < 22) by omega,
      show ¬(63 + j.val < 30) by omega, beq_false_of_ne (by omega : 63 + j.val ≠ 30),
      beq_false_of_ne (by omega : 63 + j.val ≠ 31), show ¬(63 + j.val < 62) by omega,
      beq_false_of_ne (by omega : 63 + j.val ≠ 62), show 63 + j.val < 69 by omega,
      Bool.false_eq_true, ↓reduceIte] <;>
      exact congrArg (z2BitOfNat k.val) (by omega)
  have hPid : (fun j : Fin 3 ↦ q (pos80SubIdx 69 3 (by decide) j)) =
      fun j : Fin 3 ↦ z2BitOfNat pid.val j.val := by
    funext j; dsimp only [q]
    rw [headGeneralPayload80_eq]
    unfold headWitnessPayload80 pos80SubIdx
    by_cases hp : pid.val < 6 <;> simp only [hp, ↓reduceDIte,
      show ¬(69 + j.val < 3) by omega, show ¬(69 + j.val < 6) by omega,
      show ¬(69 + j.val < 14) by omega, show ¬(69 + j.val < 22) by omega,
      show ¬(69 + j.val < 30) by omega, beq_false_of_ne (by omega : 69 + j.val ≠ 30),
      beq_false_of_ne (by omega : 69 + j.val ≠ 31), show ¬(69 + j.val < 62) by omega,
      beq_false_of_ne (by omega : 69 + j.val ≠ 62), show ¬(69 + j.val < 69) by omega,
      show 69 + j.val < 72 by omega, Bool.false_eq_true, ↓reduceIte] <;>
      exact congrArg (z2BitOfNat pid.val) (by omega)
  have hSm : (fun j : Fin 3 ↦ q (pos80SubIdx 72 3 (by decide) j)) =
      fun j : Fin 3 ↦ z2BitOfNat sm.val j.val := by
    funext j; dsimp only [q]
    rw [headGeneralPayload80_eq]
    unfold headWitnessPayload80 pos80SubIdx
    by_cases hp : pid.val < 6 <;> simp only [hp, ↓reduceDIte,
      show ¬(72 + j.val < 3) by omega, show ¬(72 + j.val < 6) by omega,
      show ¬(72 + j.val < 14) by omega, show ¬(72 + j.val < 22) by omega,
      show ¬(72 + j.val < 30) by omega, beq_false_of_ne (by omega : 72 + j.val ≠ 30),
      beq_false_of_ne (by omega : 72 + j.val ≠ 31), show ¬(72 + j.val < 62) by omega,
      beq_false_of_ne (by omega : 72 + j.val ≠ 62), show ¬(72 + j.val < 69) by omega,
      show ¬(72 + j.val < 72) by omega, show 72 + j.val < 75 by omega,
      Bool.false_eq_true, ↓reduceIte] <;>
      exact congrArg (z2BitOfNat sm.val) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB0]; exact bitsVal_z2BitOfNat 3 b0 hb0
  · rw [hNuc]; exact bitsVal_z2BitOfNat 8 nuc.val nuc.isLt
  · rw [hAnc]; exact bitsVal_z2BitOfNat 8 anc.val anc.isLt
  · rw [hPart]; exact bitsVal_z2BitOfNat 8 0 (by decide)
  · rw [hK]; exact bitsVal_z2BitOfNat 6 k.val (lt_trans k.isLt (by decide))
  · rw [hPid]; exact bitsVal_z2BitOfNat 3 pid.val pid.isLt
  · rw [hSm]; exact bitsVal_z2BitOfNat 3 sm.val sm.isLt
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailWitnessPayload80_at30 (b0 nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ) (t r : Bool) :
    tailWitnessPayload80 b0 nuc anc part dp keep t r 30 = 0 := rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailWitnessPayload80_at62 (b0 nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ) (t r : Bool) :
    tailWitnessPayload80 b0 nuc anc part dp keep t r 62 = 0 := rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailWitnessPayload80_scratchZero (b0 nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ)
    (t r : Bool) : (decide (∀ j : Fin 12, tailWitnessPayload80 b0 nuc anc part dp keep t r
    (pos80SubIdx 63 12 (by decide) j) = 0) && (tailWitnessPayload80 b0 nuc anc part dp keep t
    r 78 == 0)) = true := by
  have hall : ∀ j : Fin 12,
      tailWitnessPayload80 b0 nuc anc part dp keep t r (pos80SubIdx 63 12 (by decide) j) = 0 :=
    fun j ↦ by
      unfold tailWitnessPayload80 pos80SubIdx
      simp [show ¬(63 + j.val < 3) by omega, show ¬(63 + j.val < 6) by omega,
        show ¬(63 + j.val < 14) by omega, show ¬(63 + j.val < 22) by omega,
        show ¬(63 + j.val < 30) by omega, beq_false_of_ne (by omega : 63 + j.val ≠ 30),
        beq_false_of_ne (by omega : 63 + j.val ≠ 31), show ¬(63 + j.val < 62) by omega,
        beq_false_of_ne (by omega : 63 + j.val ≠ 62), show 63 + j.val < 75 by omega]
  have h78 : tailWitnessPayload80 b0 nuc anc part dp keep t r 78 = 0 := rfl
  simp [hall, h78]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailWitnessPayload80_at31 (b0 nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ) (t r : Bool) :
    (tailWitnessPayload80 b0 nuc anc part dp keep t r 31 == 1) = t := by
  unfold tailWitnessPayload80
  cases t <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailWitnessPayload80_at79 (b0 nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ) (t r : Bool) :
    (tailWitnessPayload80 b0 nuc anc part dp keep t r 79 == 1) = r := by
  unfold tailWitnessPayload80
  cases r <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem bitsVal_subIdx_eq_of_at (q : BitAssignment 80) (off a v : ℕ)
    (hOff : off + a ≤ 80) (hv : v < 2 ^ a)
    (hAt : ∀ j : Fin a, q (pos80SubIdx off a hOff j) = z2BitOfNat v j.val) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin a ↦ q (pos80SubIdx off a hOff j)) = v := by
  rw [show (fun j : Fin a ↦ q (pos80SubIdx off a hOff j)) =
      fun j : Fin a ↦ z2BitOfNat v j.val from funext hAt]
  exact bitsVal_z2BitOfNat a v hv
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tailWitnessPayload80_slices
    (b0 : ℕ) (hb0 : b0 < 2 ^ 3) (nuc anc part : Fin (2 ^ 8))
    (dp : Fin (2 ^ 3)) (keep : Fin (2 ^ 30)) (t r : Bool) :
    let q := tailWitnessPayload80 b0 nuc.val anc.val part.val dp keep.val t r
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) = b0 ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j)) = nuc.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j)) = anc.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) = part.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ q (pos80SubIdx 32 30 (by decide) j)) = keep.val ∧
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 75 3 (by decide) j)) = dp.val := by
  intro q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bitsVal_subIdx_eq_of_at q 3 3 b0 (by decide) hb0 fun j ↦ by
      dsimp only [q, tailWitnessPayload80, pos80SubIdx]
      simp only [show ¬(3 + j.val < 3) by omega, show 3 + j.val < 6 by omega,
        Nat.add_sub_cancel_left, ↓reduceIte]
  · exact bitsVal_subIdx_eq_of_at q 6 8 nuc.val (by decide) nuc.isLt fun j ↦ by
      dsimp only [q, tailWitnessPayload80, pos80SubIdx]
      simp only [show ¬(6 + j.val < 3) by omega, show ¬(6 + j.val < 6) by omega,
        show 6 + j.val < 14 by omega, Nat.add_sub_cancel_left, ↓reduceIte]
  · exact bitsVal_subIdx_eq_of_at q 14 8 anc.val (by decide) anc.isLt fun j ↦ by
      dsimp only [q, tailWitnessPayload80, pos80SubIdx]
      simp only [show ¬(14 + j.val < 3) by omega, show ¬(14 + j.val < 6) by omega,
        show ¬(14 + j.val < 14) by omega, show 14 + j.val < 22 by omega,
        Nat.add_sub_cancel_left, ↓reduceIte]
  · exact bitsVal_subIdx_eq_of_at q 22 8 part.val (by decide) part.isLt fun j ↦ by
      dsimp only [q, tailWitnessPayload80, pos80SubIdx]
      simp only [show ¬(22 + j.val < 3) by omega, show ¬(22 + j.val < 6) by omega,
        show ¬(22 + j.val < 14) by omega, show ¬(22 + j.val < 22) by omega,
        show 22 + j.val < 30 by omega, Nat.add_sub_cancel_left, ↓reduceIte]
  · exact bitsVal_subIdx_eq_of_at q 32 30 keep.val (by decide) keep.isLt fun j ↦ by
      dsimp only [q, tailWitnessPayload80, pos80SubIdx]
      simp only [show ¬(32 + j.val < 3) by omega, show ¬(32 + j.val < 6) by omega,
        show ¬(32 + j.val < 14) by omega, show ¬(32 + j.val < 22) by omega,
        show ¬(32 + j.val < 30) by omega, beq_false_of_ne (by omega : 32 + j.val ≠ 30),
        beq_false_of_ne (by omega : 32 + j.val ≠ 31), show 32 + j.val < 62 by omega,
        Bool.false_eq_true, Nat.add_sub_cancel_left, ↓reduceIte]
  · exact bitsVal_subIdx_eq_of_at q 75 3 dp.val (by decide) dp.isLt fun j ↦ by
      dsimp only [q, tailWitnessPayload80, pos80SubIdx]
      simp only [show ¬(75 + j.val < 3) by omega, show ¬(75 + j.val < 6) by omega,
        show ¬(75 + j.val < 14) by omega, show ¬(75 + j.val < 22) by omega,
        show ¬(75 + j.val < 30) by omega, beq_false_of_ne (by omega : 75 + j.val ≠ 30),
        beq_false_of_ne (by omega : 75 + j.val ≠ 31), show ¬(75 + j.val < 62) by omega,
        beq_false_of_ne (by omega : 75 + j.val ≠ 62), show ¬(75 + j.val < 75) by omega,
        show 75 + j.val < 78 by omega, Bool.false_eq_true, Nat.add_sub_cancel_left, ↓reduceIte]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encHead_at30 (s0 : Bool) (x : HeadIdx) : encHead s0 x 30 = 1 := by
  unfold encHead
  cases s0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [writeB0Raw_out _ _ 30 (by decide)]
    exact headGeneralPayload80_at30 _ _ _ _ _ _ _ _
  · simp only [↓reduceIte]
    exact headGeneralPayload80_at30 _ _ _ _ _ _ _ _
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTail_at30 (s0 : Bool) (y : TailIdx) : encTail s0 y 30 = 0 := by
  unfold encTail
  cases s0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [writeB0Raw_out _ _ 30 (by decide)]
    rfl
  · rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encHead_at62 (s0 : Bool) (x : HeadIdx) : encHead s0 x 62 = 0 := by
  unfold encHead
  cases s0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [writeB0Raw_out _ _ 62 (by decide)]
    exact headGeneralPayload80_at62 _ _ _ _ _ _ _ _
  · simp only [↓reduceIte]
    exact headGeneralPayload80_at62 _ _ _ _ _ _ _ _
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTail_at62 (s0 : Bool) (y : TailIdx) : encTail s0 y 62 = 0 := by
  unfold encTail
  cases s0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [writeB0Raw_out _ _ 62 (by decide)]
    rfl
  · rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encHead_q_eq (s0 : Bool) (x : HeadIdx) :
    (if !s0 then p80ClearB0Local (encHead s0 x) else encHead s0 x) =
      headGeneralPayload80 (if s0 then x.1.2.val else 0) x.1.1.val x.2.1.val
        x.2.2.1 x.2.2.2.1.val x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 := by
  cases s0
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, encHead]
    exact clearB0_writeB0Raw x.1.2 _ (headGeneralPayload80_b0_zero _ _ _ _ _ _ _)
  · rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTail_q_eq (s0 : Bool) (y : TailIdx) :
    (if !s0 then p80ClearB0Local (encTail s0 y) else encTail s0 y) =
      tailWitnessPayload80 (if s0 then y.1.2.val else 0) y.1.1.val y.2.1.val
        y.2.2.1.val y.2.2.2.1.1 y.2.2.2.1.2.val y.2.2.2.2.1 y.2.2.2.2.2 := by
  cases s0
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, encTail]
    exact clearB0_writeB0Raw y.1.2 _ (tailWitnessPayload80_b0_zero _ _ _ _ _ _ _)
  · rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encHead_b0Raw (s0 : Bool) (x : HeadIdx) : Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 3 ↦ encHead s0 x (pos80SubIdx 3 3 (by decide) j)) = x.1.2.val := by
  cases s0
  · unfold encHead
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact writeB0Raw_b0Val _ _
  · unfold encHead
    simp only [↓reduceIte]
    exact (headGeneralPayload80_slices x.1.2.val x.1.2.isLt x.1.1 x.2.1
      x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2).1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTail_b0Raw (s0 : Bool) (y : TailIdx) : Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 3 ↦ encTail s0 y (pos80SubIdx 3 3 (by decide) j)) = y.1.2.val := by
  cases s0
  · unfold encTail
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact writeB0Raw_b0Val _ _
  · unfold encTail
    simp only [↓reduceIte]
    exact (tailWitnessPayload80_slices y.1.2.val y.1.2.isLt y.1.1 y.2.1 y.2.2.1
      y.2.2.2.1.1 y.2.2.2.1.2 y.2.2.2.2.1 y.2.2.2.2.2).1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem ite_b0_lt8 (s0 : Bool) (b : Fin (2 ^ 3)) :
    (if s0 then b.val else 0) < 2 ^ 3 := by
  cases s0 <;> simp
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encHead_injective (s0 : Bool) : Function.Injective (encHead s0) := by
  rintro ⟨⟨n1, b1⟩, a1, k1, p1, sm1, t1, r1⟩ ⟨⟨n2, b2⟩, a2, k2, p2, sm2, t2, r2⟩ h
  have hb : b1 = b2 := Fin.ext (by
    rw [← encHead_b0Raw s0 ((n1, b1), a1, k1, p1, sm1, t1, r1),
      ← encHead_b0Raw s0 ((n2, b2), a2, k2, p2, sm2, t2, r2), h])
  have hq : headGeneralPayload80 (if s0 then b1.val else 0) n1.val a1.val k1 p1.val sm1 t1 r1 =
      headGeneralPayload80 (if s0 then b2.val else 0) n2.val a2.val k2 p2.val sm2 t2 r2 := by
    rw [← encHead_q_eq s0 ((n1, b1), a1, k1, p1, sm1, t1, r1),
      ← encHead_q_eq s0 ((n2, b2), a2, k2, p2, sm2, t2, r2), h]
  have hs1 := headGeneralPayload80_slices _ (ite_b0_lt8 s0 b1) n1 a1 k1 p1 sm1 t1 r1
  have hs2 := headGeneralPayload80_slices _ (ite_b0_lt8 s0 b2) n2 a2 k2 p2 sm2 t2 r2
  dsimp only at hs1 hs2
  subst hb
  obtain rfl : n1 = n2 := Fin.ext (hs1.2.1.symm.trans (hq ▸ hs2.2.1))
  obtain rfl : a1 = a2 := Fin.ext (hs1.2.2.1.symm.trans (hq ▸ hs2.2.2.1))
  obtain rfl : k1 = k2 := Fin.ext (hs1.2.2.2.2.1.symm.trans (hq ▸ hs2.2.2.2.2.1))
  obtain rfl : p1 = p2 := Fin.ext (hs1.2.2.2.2.2.1.symm.trans (hq ▸ hs2.2.2.2.2.2.1))
  obtain rfl : sm1 = sm2 := Fin.ext (hs1.2.2.2.2.2.2.symm.trans (hq ▸ hs2.2.2.2.2.2.2))
  obtain rfl : t1 = t2 := by
    rw [← headGeneralPayload80_at31 (if s0 then b1.val else 0) n1.val a1.val k1 p1.val sm1 t1 r1,
      hq, headGeneralPayload80_at31]
  obtain rfl : r1 = r2 := by
    rw [← headGeneralPayload80_at79 (if s0 then b1.val else 0) n1.val a1.val k1 p1.val sm1 t1 r1,
      hq, headGeneralPayload80_at79]
  rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTail_injective (s0 : Bool) : Function.Injective (encTail s0) := by
  rintro ⟨⟨n1, b1⟩, a1, pt1, ⟨dp1, kp1⟩, t1, r1⟩ ⟨⟨n2, b2⟩, a2, pt2, ⟨dp2, kp2⟩, t2, r2⟩ h
  have hb : b1 = b2 := Fin.ext (by
    rw [← encTail_b0Raw s0 ((n1, b1), a1, pt1, (dp1, kp1), t1, r1),
      ← encTail_b0Raw s0 ((n2, b2), a2, pt2, (dp2, kp2), t2, r2), h])
  have hq :
      tailWitnessPayload80 (if s0 then b1.val else 0) n1.val a1.val pt1.val dp1 kp1.val t1 r1 =
      tailWitnessPayload80 (if s0 then b2.val else 0) n2.val a2.val pt2.val dp2 kp2.val t2 r2 := by
    rw [← encTail_q_eq s0 ((n1, b1), a1, pt1, (dp1, kp1), t1, r1),
      ← encTail_q_eq s0 ((n2, b2), a2, pt2, (dp2, kp2), t2, r2), h]
  have hs1 := tailWitnessPayload80_slices _ (ite_b0_lt8 s0 b1) n1 a1 pt1 dp1 kp1 t1 r1
  have hs2 := tailWitnessPayload80_slices _ (ite_b0_lt8 s0 b2) n2 a2 pt2 dp2 kp2 t2 r2
  dsimp only at hs1 hs2
  subst hb
  obtain rfl : n1 = n2 := Fin.ext (hs1.2.1.symm.trans (hq ▸ hs2.2.1))
  obtain rfl : a1 = a2 := Fin.ext (hs1.2.2.1.symm.trans (hq ▸ hs2.2.2.1))
  obtain rfl : pt1 = pt2 := Fin.ext (hs1.2.2.2.1.symm.trans (hq ▸ hs2.2.2.2.1))
  obtain rfl : kp1 = kp2 := Fin.ext (hs1.2.2.2.2.1.symm.trans (hq ▸ hs2.2.2.2.2.1))
  obtain rfl : dp1 = dp2 := Fin.ext (hs1.2.2.2.2.2.symm.trans (hq ▸ hs2.2.2.2.2.2))
  obtain rfl : t1 = t2 := by
    rw [← tailWitnessPayload80_at31
        (if s0 then b1.val else 0) n1.val a1.val pt1.val dp1 kp1.val t1 r1,
      hq, tailWitnessPayload80_at31]
  obtain rfl : r1 = r2 := by
    rw [← tailWitnessPayload80_at79
        (if s0 then b1.val else 0) n1.val a1.val pt1.val dp1 kp1.val t1 r1,
      hq, tailWitnessPayload80_at79]
  rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encAll_injective (s0 : Bool) : Function.Injective (encAll s0) := by
  intro z1 z2 h
  rcases z1 with x1 | y1
  · rcases z2 with x2 | y2
    · exact congrArg Sum.inl (encHead_injective s0 h)
    · have h30 : encHead s0 x1 30 = encTail s0 y2 30 := congrFun h 30
      rw [encHead_at30, encTail_at30] at h30
      exact absurd h30 (by decide)
  · rcases z2 with x2 | y2
    · have h30 : encTail s0 y1 30 = encHead s0 x2 30 := congrFun h 30
      rw [encTail_at30, encHead_at30] at h30
      exact absurd h30 (by decide)
    · exact congrArg Sum.inr (encTail_injective s0 h)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def encWitness (isMerged218 s0 : Bool) (z : HeadIdx ⊕ TailIdx) : BitAssignment 80 :=
  if !s0 && isMerged218 then flipTailDpScratch80 (encAll false z) else encAll s0 z
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encWitness_injective (isMerged218 s0 : Bool) :
    Function.Injective (encWitness isMerged218 s0) := by
  unfold encWitness
  cases s0
  · cases isMerged218
    · exact encAll_injective false
    · exact flipTailDpScratch80_involutive.injective.comp (encAll_injective false)
  · exact encAll_injective true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem flip_writeB0Raw_comm (b0 : Fin (2 ^ 3)) (q : BitAssignment 80) :
    flipTailDpScratch80 (writeB0Raw b0 q) = writeB0Raw b0 (flipTailDpScratch80 q) :=
  flipTailDpScratch80_comm_of_disj (fun n ↦ 3 ≤ n ∧ n < 6) (writeB0Raw b0) q (by omega)
    (fun r j hj ↦ writeB0Raw_out b0 r j hj)
    (fun j hj ↦ by
      unfold writeB0Raw
      simp [hj])
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem writeB0Raw_of_val_zero (b0 : Fin (2 ^ 3)) (hb0 : b0.val = 0) (q : BitAssignment 80)
    (hq0 : ∀ i : Fin 80, 3 ≤ i.val ∧ i.val < 6 → q i = 0) : writeB0Raw b0 q = q := by
  funext i
  unfold writeB0Raw
  by_cases hi : 3 ≤ i.val ∧ i.val < 6
  · rw [ite_eq_left hi, hb0, z2BitOfNat_zero_local, hq0 i hi]
  · simp [hi]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem flip_b0Slice_eq (r : BitAssignment 80) :
    (fun j : Fin 3 ↦ flipTailDpScratch80 r (pos80SubIdx 3 3 (by decide) j)) =
      fun j : Fin 3 ↦ r (pos80SubIdx 3 3 (by decide) j) :=
  funext fun j ↦ flipTailDpScratch80_preserve r _ ⟨by
    dsimp [pos80SubIdx]
    omega, by
    dsimp [pos80SubIdx]
    omega, by
    dsimp [pos80SubIdx]
    omega⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem encAll_b0Raw (s0 : Bool) (z : HeadIdx ⊕ TailIdx) :
    Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ encAll s0 z (pos80SubIdx 3 3 (by decide) j)) =
      Sum.elim (fun x : HeadIdx ↦ x.1.2.val) (fun y : TailIdx ↦ y.1.2.val) z := by
  rcases z with x | y
  · exact encHead_b0Raw s0 x
  · exact encTail_b0Raw s0 y
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encWitness_b0Raw (isMerged218 s0 : Bool) (z : HeadIdx ⊕ TailIdx) :
    Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ encWitness isMerged218 s0 z (pos80SubIdx 3 3 (by decide) j)) =
      Sum.elim (fun x : HeadIdx ↦ x.1.2.val) (fun y : TailIdx ↦ y.1.2.val) z := by
  unfold encWitness
  cases s0 <;> cases isMerged218 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, flip_b0Slice_eq, encAll_b0Raw]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encWitness_q_eq (isMerged218 s0 : Bool) (z : HeadIdx ⊕ TailIdx) : (if !s0 then (if
    isMerged218 then flipTailDpScratch80 (p80ClearB0Local (encWitness isMerged218 s0 z)) else
    p80ClearB0Local (encWitness isMerged218 s0 z)) else encWitness isMerged218 s0 z) =
    (if !s0 then p80ClearB0Local (encAll s0 z) else encAll s0 z) := by
  unfold encWitness
  cases s0 <;> cases isMerged218 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [flip_clearB0_comm, flipTailDpScratch80_involutive]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem recover_p_from_q (isMerged218 s0 : Bool) (p : BitAssignment 80) :
    let b0Raw : Fin (2 ^ 3) := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3
        3 (by decide) j)), bitsVal_lt_two_pow_local _⟩
    let q := if !s0 then (if isMerged218 then flipTailDpScratch80 (p80ClearB0Local p) else
        p80ClearB0Local p) else p
    (if !s0 && isMerged218 then flipTailDpScratch80 (writeB0Raw b0Raw q)
     else if s0 then q else writeB0Raw b0Raw q) = p := by
  cases s0 <;> cases isMerged218 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · exact writeB0Raw_clearB0_self p
  · rw [flip_writeB0Raw_comm, flipTailDpScratch80_involutive]
    exact writeB0Raw_clearB0_self p
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem q_b0Val_eq (isMerged218 s0 : Bool) (p : BitAssignment 80) :
    let q := if !s0 then (if isMerged218 then flipTailDpScratch80 (p80ClearB0Local p) else
        p80ClearB0Local p) else p
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) =
      if s0 then Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j))
      else 0 := by
  cases s0 <;> cases isMerged218 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, flip_b0Slice_eq, p80ClearB0Local_b0Val]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def qSplitHead (s0 : Bool) : ℝ := if s0 then (727884457843 : ℝ) /
    (PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat : ℝ) else (727884457843 : ℝ) /
    (PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat : ℝ)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def qSplitTail (s0 : Bool) : ℝ := if s0 then (1386279409375 : ℝ) /
    (PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat : ℝ) else (1392667793750 : ℝ) /
    (PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat : ℝ)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealNucB0 (isMerged218 s0 : Bool) (nb : NucB0Idx) : ℝ := if s0 then
    (if nb.1.val == 0 then (1 : ℝ) else 0) * (1 / 8 : ℝ) else if isMerged218 then
    (if nb.1.val < 218 then (1 : ℝ) / (218 : ℝ) else 0) * (if (nb.1.val &&& 216) == 216 then
    (1 / 8 : ℝ) else if nb.2.val == 0 then 1 else 0) else
    (if nb.1.val < 216 then (1 : ℝ) / (216 : ℝ) else 0) * (if nb.2.val == 0 then 1 else 0)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealHeadRest (s0 : Bool) (r : HeadRestIdx) : ℝ := (if s0 then (if r.1.val <
    218 then (1 : ℝ) / (218 : ℝ) else 0) else if r.1.val == 0 then (1 : ℝ) else 0) *
    (((PosSlots24SemanticBridge.pos24HeadWeight56 r.2.1 : ℝ) / (727884457843 : ℝ)) * ((if
    r.2.2.1.val < 6 then (1 : ℝ) / (6 : ℝ) else 0) * ((1 / 8 : ℝ) * (1 / 4 : ℝ))))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealTailRest (s0 : Bool) (r : TailRestIdx) : ℝ :=
    (if r.1.val < 218 then (1 : ℝ) / (218 : ℝ) else 0) * ((if s0 then (if r.2.1.val < 217 then
    (1 : ℝ) / (217 : ℝ) else 0) else if r.2.1.val == 0 then (1 : ℝ) else 0) *
    (((tailDp8Weights r.2.2.1.1 : ℝ) / (6388384375 : ℝ) * (if r.2.2.1.2.val < tailKeepSpanOfDp
    r.2.2.1.1 then (1 : ℝ) / (tailKeepSpanOfDp r.2.2.1.1 : ℝ) else 0)) * (1 / 4 : ℝ)))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealWitnessWeight (isMerged218 s0 : Bool) : HeadIdx ⊕ TailIdx → ℝ
  | .inl x => qSplitHead s0 * (idealNucB0 isMerged218 s0 x.1 * idealHeadRest s0 x.2)
  | .inr y => qSplitTail s0 * (idealNucB0 isMerged218 s0 y.1 * idealTailRest s0 y.2)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def encTailSub1 (isMerged218 s0 : Bool) (y : TailIdx) : BitAssignment 80 :=
  Function.update (encWitness isMerged218 s0 (.inr y)) (62 : Fin 80) 1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encAll_at62 (s0 : Bool) (z : HeadIdx ⊕ TailIdx) : encAll s0 z 62 = 0 := by
  rcases z with x | y
  · exact encHead_at62 s0 x
  · exact encTail_at62 s0 y
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encWitness_at62 (isMerged218 s0 : Bool) (z : HeadIdx ⊕ TailIdx) :
    encWitness isMerged218 s0 z 62 = 0 := by
  unfold encWitness
  split_ifs
  · rw [flipTailDpScratch80_preserve _ 62 (by decide)]
    exact encAll_at62 false z
  · exact encAll_at62 s0 z
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTailSub1_at62 (isMerged218 s0 : Bool) (y : TailIdx) :
    encTailSub1 isMerged218 s0 y 62 = 1 := by
  unfold encTailSub1
  exact Function.update_self 62 1 _
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem update_encTailSub1_62_zero (isMerged218 s0 : Bool) (y : TailIdx) : Function.update
    (encTailSub1 isMerged218 s0 y) 62 0 = encWitness isMerged218 s0 (.inr y) := by
  funext i
  by_cases hi : i = 62
  · subst hi
    rw [Function.update_self, encWitness_at62]
  · simp [encTailSub1, hi]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTailSub1_injective (isMerged218 s0 : Bool) :
    Function.Injective (encTailSub1 isMerged218 s0) := by
  intro y1 y2 h
  have h0 : Function.update (encTailSub1 isMerged218 s0 y1) 62 0 = Function.update
      (encTailSub1 isMerged218 s0 y2) 62 0 := congrArg (fun f ↦ Function.update f 62 0) h
  rw [update_encTailSub1_62_zero, update_encTailSub1_62_zero] at h0
  exact Sum.inr.inj (encWitness_injective isMerged218 s0 h0)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTailSub1_ne_encWitness (isMerged218 s0 : Bool) (y : TailIdx) (z : HeadIdx ⊕ TailIdx) :
    encTailSub1 isMerged218 s0 y ≠ encWitness isMerged218 s0 z := fun h ↦ by
  have h62 : encTailSub1 isMerged218 s0 y 62 = encWitness isMerged218 s0 z 62 := congrFun h 62
  rw [encTailSub1_at62, encWitness_at62] at h62
  exact absurd h62 (by decide)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTailSub1_ne_encAll (isMerged218 s0 : Bool) (y : TailIdx) (z : HeadIdx ⊕ TailIdx) :
    encTailSub1 isMerged218 s0 y ≠ encAll s0 z := fun h ↦ by
  have h62 : encTailSub1 isMerged218 s0 y 62 = encAll s0 z 62 := congrFun h 62
  rw [encTailSub1_at62, encAll_at62] at h62
  exact absurd h62 (by decide)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p80ClearB0Local_update62 (p : BitAssignment 80) (v : ZMod 2) :
    p80ClearB0Local (Function.update p 62 v) = Function.update (p80ClearB0Local p) 62 v := by
  funext i
  by_cases hi : i = 62
  · subst hi
    rw [Function.update_self, p80ClearB0Local_out _ 62 (by decide), Function.update_self]
  · rw [Function.update_of_ne hi]
    unfold p80ClearB0Local
    split_ifs <;> simp [hi]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem writeB0Raw_update62 (b0 : Fin (2 ^ 3)) (p : BitAssignment 80) (v : ZMod 2) :
    writeB0Raw b0 (Function.update p 62 v) = Function.update (writeB0Raw b0 p) 62 v := by
  funext i
  by_cases hi : i = 62
  · subst hi
    rw [writeB0Raw_out _ _ 62 (by decide), Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hi]
    unfold writeB0Raw
    split_ifs <;> simp [hi]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem flipTailDpScratch80_update62 (p : BitAssignment 80) (v : ZMod 2) :
    flipTailDpScratch80 (Function.update p 62 v) = Function.update (flipTailDpScratch80 p) 62 v :=
  flipTailDpScratch80_comm_of_disj (fun n ↦ n = 62) (fun r ↦ Function.update r 62 v) p (by omega)
    (fun r j hj ↦ by
      rw [Function.update_of_ne fun h ↦ hj (congrArg Fin.val h)])
    (fun j hj ↦ by
      rw [show j = (62 : Fin 80) from Fin.ext hj, Function.update_self, Function.update_self])
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTailSub1_b0Raw (isMerged218 s0 : Bool) (y : TailIdx) : Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 3 ↦ encTailSub1 isMerged218 s0 y (pos80SubIdx 3 3 (by decide) j)) = y.1.2.val
    := by
  have hfn : (fun j : Fin 3 ↦ encTailSub1 isMerged218 s0 y (pos80SubIdx 3 3 (by decide) j)) =
      fun j : Fin 3 ↦ encWitness isMerged218 s0 (.inr y) (pos80SubIdx 3 3 (by decide) j) := by
    funext j
    unfold encTailSub1
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    dsimp [pos80SubIdx] at hv
    omega
  rw [hfn]
  simpa using encWitness_b0Raw isMerged218 s0 (.inr y)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTailSub1_q_eq (isMerged218 s0 : Bool) (y : TailIdx) : (if !s0 then (if isMerged218
    then flipTailDpScratch80 (p80ClearB0Local (encTailSub1 isMerged218 s0 y)) else
    p80ClearB0Local (encTailSub1 isMerged218 s0 y)) else encTailSub1 isMerged218 s0 y) =
    Function.update (tailWitnessPayload80 (if s0 then y.1.2.val else 0) y.1.1.val y.2.1.val
    y.2.2.1.val y.2.2.2.1.1 y.2.2.2.1.2.val y.2.2.2.2.1 y.2.2.2.2.2) (62 : Fin 80) 1 := by
  unfold encTailSub1
  have h1 : (if !s0 then (if isMerged218 then flipTailDpScratch80 (p80ClearB0Local
      (Function.update (encWitness isMerged218 s0 (.inr y)) (62 : Fin 80) 1)) else
      p80ClearB0Local (Function.update (encWitness isMerged218 s0 (.inr y)) (62 : Fin 80) 1))
      else Function.update (encWitness isMerged218 s0 (.inr y)) (62 : Fin 80) 1) =
      Function.update (if !s0 then (if isMerged218 then flipTailDpScratch80 (p80ClearB0Local
      (encWitness isMerged218 s0 (.inr y))) else p80ClearB0Local (encWitness isMerged218 s0
      (.inr y))) else encWitness isMerged218 s0 (.inr y)) (62 : Fin 80) 1 := by
    cases s0 <;> cases isMerged218 <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        p80ClearB0Local_update62, flipTailDpScratch80_update62]
  rw [h1, encWitness_q_eq]
  dsimp only [encAll, Sum.elim_inr]
  rw [encTail_q_eq]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem mk_bitsVal3_eq (γ : BitAssignment 3) (v : Fin 8)
    (h : Pos24HeadCoordXor80.bitsVal γ = v.val) : (⟨Pos24HeadCoordXor80.bitsVal γ,
    Pos24HeadCoordXor80.bitsVal3_lt8 γ⟩ : Fin 8) = v := Fin.ext h
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem update62_subSlice_eq (q : BitAssignment 80) (v : ZMod 2) (off len : ℕ)
    (h : off + len ≤ 80) (hOut : 62 < off ∨ off + len ≤ 62) :
    (fun j : Fin len ↦ Function.update q (62 : Fin 80) v (pos80SubIdx off len h j)) =
      fun j : Fin len ↦ q (pos80SubIdx off len h j) := by
  funext j
  apply Function.update_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  dsimp [pos80SubIdx] at hv
  omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pos80Slot2TotNat_val :
    (PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat : ℝ) = (2120552251593 : ℝ) := by
  unfold PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat
    PosSlots24SemanticOracleConcrete80.pos80HeadWeightNat
    PosSlots24SemanticOracleConcrete80.pos80TailWeightNat
  norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pos80Slot4TotNat_val :
    (PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat : ℝ) = (2114163867218 : ℝ) := by
  unfold PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat
    PosSlots24SemanticOracleConcrete80.pos80HeadWeightNat
    PosSlots24SemanticOracleConcrete80.pos80TailWeightNat
  norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pos80IdealDist_on (s0 : Bool) (z : HeadIdx ⊕ TailIdx) :
    pos80IdealDist s0 (encAll s0 z) = idealWitnessWeight false s0 z := by
  rcases z with x | y
  · dsimp only [encAll, Sum.elim_inl, idealWitnessWeight]
    cases s0
    · by_cases hb0 : x.1.2.val = 0
      · have hEnc : encHead false x = headGeneralPayload80 0 x.1.1.val x.2.1.val x.2.2.1
          x.2.2.2.1.val x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 := by
          unfold encHead
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact writeB0Raw_of_val_zero x.1.2 hb0 _ (headGeneralPayload80_b0_zero _ _ _ _ _ _ _)
        rw [hEnc]
        have hs := headGeneralPayload80_slices 0 (by decide) x.1.1 x.2.1
          x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2
        dsimp only at hs
        unfold pos80IdealDist
        dsimp only
        rw [ite_neg (by rw [headGeneralPayload80_at62]; decide),
          ite_pos (by rw [headGeneralPayload80_at30]; decide),
          dite_eq_left (by rw [hs.2.2.2.2.1]; exact x.2.2.1.isLt),
          mk_bitsVal_fin_eq _ x.2.2.1 _ hs.2.2.2.2.1]
        by_cases hp : x.2.2.2.1.val < 6
        · have hgp : headGeneralPayload80 0 x.1.1.val x.2.1.val x.2.2.1 x.2.2.2.1.val
              x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 =
              headWitnessPayload80 0 x.1.1.val x.2.1.val x.2.2.1 ⟨x.2.2.2.1.val, hp⟩
                x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 := by
            rw [headGeneralPayload80_eq]; simp [hp]
          rw [dite_eq_left (by rw [hs.2.2.2.2.2.1]; exact hp),
            mk_bitsVal_fin_eq _ ⟨x.2.2.2.1.val, hp⟩ _ hs.2.2.2.2.2.1,
            mk_bitsVal3_eq _ x.2.2.2.2.1 hs.2.2.2.2.2.2,
            hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
            headGeneralPayload80_remZero, headGeneralPayload80_at31, headGeneralPayload80_at79]
          unfold qSplitHead idealNucB0 idealHeadRest
          simp only [Bool.false_eq_true, ↓reduceIte, hb0, beq_self_eq_true, decide_true,
            Bool.true_and, Bool.and_true, hp, hgp]
          rw [pos80Slot2TotNat_val]
          by_cases hn : x.1.1.val < 216 <;> by_cases ha : x.2.1.val = 0
          · simp [hn, ha]; ring
          · simp [hn, ha]
          · simp [hn, ha]
          · simp [hn, ha]
        · rw [dite_eq_right (by rw [hs.2.2.2.2.2.1]; exact hp)]
          unfold qSplitHead idealNucB0 idealHeadRest
          simp [hp]
      · have hbRaw := encHead_b0Raw false x
        have hbn : (x.1.2.val == 0) = false := beq_false_of_ne hb0
        unfold pos80IdealDist
        dsimp only
        rw [ite_neg (by rw [encHead_at62]; decide),
          ite_pos (by rw [encHead_at30]; decide), hbRaw]
        unfold qSplitHead idealNucB0 idealHeadRest
        simp only [Bool.false_eq_true, ↓reduceIte, hbn, decide_false,
          Bool.false_and, Bool.and_false]
        split_ifs <;> ring
    · have hEnc : encHead true x = headGeneralPayload80 x.1.2.val x.1.1.val x.2.1.val x.2.2.1
        x.2.2.2.1.val x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 := rfl
      rw [hEnc]
      have hs := headGeneralPayload80_slices x.1.2.val x.1.2.isLt x.1.1 x.2.1
        x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2
      dsimp only at hs
      unfold pos80IdealDist
      dsimp only
      rw [ite_neg (by rw [headGeneralPayload80_at62]; decide),
        ite_pos (by rw [headGeneralPayload80_at30]; decide),
        dite_eq_left (by rw [hs.2.2.2.2.1]; exact x.2.2.1.isLt),
        mk_bitsVal_fin_eq _ x.2.2.1 _ hs.2.2.2.2.1]
      by_cases hp : x.2.2.2.1.val < 6
      · have hgp : headGeneralPayload80 x.1.2.val x.1.1.val x.2.1.val x.2.2.1 x.2.2.2.1.val
          x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 = headWitnessPayload80 x.1.2.val x.1.1.val
          x.2.1.val x.2.2.1 ⟨x.2.2.2.1.val, hp⟩ x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 := by
          rw [headGeneralPayload80_eq]; simp [hp]
        rw [dite_eq_left (by rw [hs.2.2.2.2.2.1]; exact hp),
          mk_bitsVal_fin_eq _ ⟨x.2.2.2.1.val, hp⟩ _ hs.2.2.2.2.2.1,
          mk_bitsVal3_eq _ x.2.2.2.2.1 hs.2.2.2.2.2.2,
          hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
          headGeneralPayload80_remZero, headGeneralPayload80_at31, headGeneralPayload80_at79]
        unfold qSplitHead idealNucB0 idealHeadRest
        simp only [↓reduceIte, beq_self_eq_true, Bool.true_and, Bool.and_true, hp, hgp]
        rw [pos80Slot4TotNat_val]
        by_cases hn : x.1.1.val = 0 <;> by_cases ha : x.2.1.val < 218
        · simp [hn, ha]; ring
        · simp [hn, ha]
        · simp [hn, ha]
        · simp [hn, ha]
      · rw [dite_eq_right (by rw [hs.2.2.2.2.2.1]; exact hp)]
        unfold qSplitHead idealNucB0 idealHeadRest
        simp [hp]
  · dsimp only [encAll, Sum.elim_inr, idealWitnessWeight]
    cases s0
    · by_cases hb0 : y.1.2.val = 0
      · have hEnc : encTail false y = tailWitnessPayload80 0 y.1.1.val y.2.1.val y.2.2.1.val
          y.2.2.2.1.1 y.2.2.2.1.2.val y.2.2.2.2.1 y.2.2.2.2.2 := by
          unfold encTail
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact writeB0Raw_of_val_zero y.1.2 hb0 _ (tailWitnessPayload80_b0_zero _ _ _ _ _ _ _)
        rw [hEnc]
        have hs := tailWitnessPayload80_slices 0 (by decide) y.1.1 y.2.1 y.2.2.1
          y.2.2.2.1.1 y.2.2.2.1.2 y.2.2.2.2.1 y.2.2.2.2.2
        dsimp only at hs
        unfold pos80IdealDist
        dsimp only
        rw [ite_neg (by rw [tailWitnessPayload80_at62]; decide),
          ite_neg (by rw [tailWitnessPayload80_at30]; decide),
          mk_bitsVal3_eq _ y.2.2.2.1.1 hs.2.2.2.2.2,
          hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
          tailWitnessPayload80_scratchZero, tailWitnessPayload80_at31, tailWitnessPayload80_at79]
        simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Bool.true_and, Bool.and_true]
        unfold qSplitTail idealNucB0 idealTailRest
        rw [← tailSpan_eq_pos24TailSpan8 y.2.2.2.1.1, ← tailSpan_eq_tailDp8Weights y.2.2.2.1.1,
          pos80Slot2TotNat_val]
        have hspPos : (tailKeepSpanOfDp y.2.2.2.1.1 : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (tailSpan_bounds y.2.2.2.1.1).1)
        simp only [Bool.false_eq_true, ↓reduceIte, hb0, beq_self_eq_true]
        by_cases hn : y.1.1.val < 216 <;> by_cases ha : y.2.1.val < 218 <;>
          by_cases hpt : y.2.2.1.val = 0 <;>
          by_cases hkp : y.2.2.2.1.2.val < tailKeepSpanOfDp y.2.2.2.1.1 <;>
          simp [hn, ha, hpt, hkp]
        field_simp [hspPos]
        norm_num
      · have hbRaw := encTail_b0Raw false y
        have hbn : (y.1.2.val == 0) = false := beq_false_of_ne hb0
        unfold pos80IdealDist
        dsimp only
        rw [ite_neg (by rw [encTail_at62]; decide),
          ite_neg (by rw [encTail_at30]; decide), hbRaw]
        unfold qSplitTail idealNucB0 idealTailRest
        simp only [Bool.false_eq_true, ↓reduceIte, hbn, Bool.false_and, Bool.and_false]
        split_ifs <;> ring
    · have hEnc : encTail true y = tailWitnessPayload80 y.1.2.val y.1.1.val y.2.1.val
        y.2.2.1.val y.2.2.2.1.1 y.2.2.2.1.2.val y.2.2.2.2.1 y.2.2.2.2.2 := rfl
      rw [hEnc]
      have hs := tailWitnessPayload80_slices y.1.2.val y.1.2.isLt y.1.1 y.2.1 y.2.2.1
        y.2.2.2.1.1 y.2.2.2.1.2 y.2.2.2.2.1 y.2.2.2.2.2
      dsimp only at hs
      unfold pos80IdealDist
      dsimp only
      rw [ite_neg (by rw [tailWitnessPayload80_at62]; decide),
        ite_neg (by rw [tailWitnessPayload80_at30]; decide),
        mk_bitsVal3_eq _ y.2.2.2.1.1 hs.2.2.2.2.2,
        hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
        tailWitnessPayload80_scratchZero, tailWitnessPayload80_at31, tailWitnessPayload80_at79]
      simp only [↓reduceIte, beq_self_eq_true, Bool.true_and, Bool.and_true]
      unfold qSplitTail idealNucB0 idealTailRest
      rw [← tailSpan_eq_pos24TailSpan8 y.2.2.2.1.1, ← tailSpan_eq_tailDp8Weights y.2.2.2.1.1,
        pos80Slot4TotNat_val]
      have hspPos : (tailKeepSpanOfDp y.2.2.2.1.1 : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (tailSpan_bounds y.2.2.2.1.1).1)
      simp only [↓reduceIte]
      by_cases hn : y.1.1.val = 0 <;> by_cases ha : y.2.1.val < 218 <;>
        by_cases hpt : y.2.2.1.val < 217 <;>
        by_cases hkp : y.2.2.2.1.2.val < tailKeepSpanOfDp y.2.2.2.1.1 <;>
        simp [hn, ha, hpt, hkp]
      field_simp [hspPos]
      norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pos80IdealDist_off (s0 : Bool) (p : BitAssignment 80)
    (hOff : ∀ z : HeadIdx ⊕ TailIdx, p ≠ encAll s0 z) : pos80IdealDist s0 p = 0 := by
  by_contra hNe
  set b0Raw : Fin (2 ^ 3) :=
    ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)),
      bitsVal_lt_two_pow_local _⟩
  unfold pos80IdealDist at hNe
  dsimp only at hNe
  by_cases h62 : (p 62 != 0) = true
  · rw [ite_pos h62] at hNe
    exact hNe rfl
  · rw [ite_neg h62] at hNe
    by_cases h30 : (p 30 == 1) = true
    · rw [ite_pos h30] at hNe
      rcases ne_zero_of_dite_zero hNe with ⟨hk, hNe⟩
      rcases ne_zero_of_dite_zero hNe with ⟨hp, hNe⟩
      have hCond := ne_zero_of_ite_zero hNe
      simp only [Bool.and_eq_true, beq_iff_eq] at hCond
      have hpEq := hCond.2
      let x : HeadIdx := ((⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8
          (by decide) j)), bitsVal_lt_two_pow_local _⟩, b0Raw), (⟨Pos24HeadCoordXor80.bitsVal
          (fun j : Fin 8 ↦ p (pos80SubIdx 14 8 (by decide) j)), bitsVal_lt_two_pow_local _⟩,
          ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ p (pos80SubIdx 63 6 (by decide) j)),
          hk⟩, ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 69 3 (by decide)
          j)), bitsVal_lt_two_pow_local _⟩, ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p
          (pos80SubIdx 72 3 (by decide) j)), Pos24HeadCoordXor80.bitsVal3_lt8 _⟩, (p 31 == 1,
          p 79 == 1)))
      have hGenEq : headGeneralPayload80 b0Raw.val x.1.1.val x.2.1.val x.2.2.1 x.2.2.2.1.val
          x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 = headWitnessPayload80 b0Raw.val x.1.1.val
          x.2.1.val x.2.2.1 ⟨x.2.2.2.1.val, hp⟩ x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 := by
        have hxp : x.2.2.2.1.val < 6 := hp
        rw [headGeneralPayload80_eq]
        simp only [hxp, ↓reduceDIte]
      apply hOff (.inl x)
      unfold encAll Sum.elim encHead
      cases s0
      · have hb0 : b0Raw.val = 0 := by
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq] at hCond
          exact hCond.1.1.2.1.1
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [writeB0Raw_of_val_zero b0Raw hb0 _ (headGeneralPayload80_b0_zero _ _ _ _ _ _ _),
          ← hb0, hGenEq, ← hpEq]
      · simp only [↓reduceIte]
        rw [hGenEq, ← hpEq]
    · rw [ite_neg h30] at hNe
      have hCond := ne_zero_of_ite_zero hNe
      simp only [Bool.and_eq_true, beq_iff_eq] at hCond
      have hpEq := hCond.2
      let y : TailIdx := ((⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8
          (by decide) j)), bitsVal_lt_two_pow_local _⟩, b0Raw), (⟨Pos24HeadCoordXor80.bitsVal
          (fun j : Fin 8 ↦ p (pos80SubIdx 14 8 (by decide) j)), bitsVal_lt_two_pow_local _⟩,
          ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 22 8 (by decide) j)),
          bitsVal_lt_two_pow_local _⟩, (⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p
          (pos80SubIdx 75 3 (by decide) j)), Pos24HeadCoordXor80.bitsVal3_lt8 _⟩,
          ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ p (pos80SubIdx 32 30 (by decide) j)),
          bitsVal_lt_two_pow_local _⟩), (p 31 == 1, p 79 == 1)))
      apply hOff (.inr y)
      unfold encAll Sum.elim encTail
      cases s0
      · have hb0 : b0Raw.val = 0 := by
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hCond
          exact hCond.1.1.2.1.1.1
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [writeB0Raw_of_val_zero b0Raw hb0 _ (tailWitnessPayload80_b0_zero _ _ _ _ _ _ _),
          ← hb0, ← hpEq]
      · simp only [↓reduceIte]
        rw [← hpEq]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem nuc_and216_of_lt216 (nuc : Fin (2 ^ 8)) (h : nuc.val < 216) :
    ((nuc.val &&& 216) == 216) = false := by
  revert nuc; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem nuc_and216_of_216_218 (nuc : Fin (2 ^ 8)) (h1 : 216 ≤ nuc.val) (h2 : nuc.val < 218) :
    ((nuc.val &&& 216) == 216) = true := by
  revert nuc; decide
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def setWitnessNucB0 (nb : NucB0Idx) : HeadIdx ⊕ TailIdx → HeadIdx ⊕ TailIdx
  | .inl x => .inl (nb, x.2)
  | .inr y => .inr (nb, y.2)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem encAll_false_setWitnessNucB0_apply (nb : NucB0Idx) (z : HeadIdx ⊕ TailIdx)
    (i : Fin 80) :
    encAll false (setWitnessNucB0 nb z) i =
      if 3 ≤ i.val ∧ i.val < 6 then z2BitOfNat nb.2.val (i.val - 3)
      else if 6 ≤ i.val ∧ i.val < 14 then z2BitOfNat nb.1.val (i.val - 6)
      else encAll false z i := by
  by_cases h36 : 3 ≤ i.val ∧ i.val < 6
  · rcases z with x | y
    · unfold encAll Sum.elim setWitnessNucB0 encHead writeB0Raw
      simp [h36]
    · unfold encAll Sum.elim setWitnessNucB0 encTail writeB0Raw
      simp [h36]
  · by_cases h614 : 6 ≤ i.val ∧ i.val < 14
    · have hi3 : ¬(i.val < 3) := by omega
      have hi6 : ¬(i.val < 6) := by omega
      rcases z with x | y
      · unfold encAll Sum.elim setWitnessNucB0 encHead writeB0Raw
        simp only [Bool.false_eq_true, ↓reduceIte, h36, h614]
        rw [headGeneralPayload80_eq]
        unfold headWitnessPayload80
        by_cases hp : x.2.2.2.1.val < 6
        · simp [hp, hi3, hi6, h614.2]
        · simp [hp, hi3, hi6, h614.2]
      · unfold encAll Sum.elim setWitnessNucB0 encTail writeB0Raw
        simp only [Bool.false_eq_true, ↓reduceIte, h36, h614]
        unfold tailWitnessPayload80
        simp [hi3, hi6, h614.2]
    · rcases z with x | y
      · unfold encAll Sum.elim setWitnessNucB0 encHead writeB0Raw
        simp only [Bool.false_eq_true, ↓reduceIte, h36, h614]
        rw [headGeneralPayload80_eq, headGeneralPayload80_eq]
        unfold headWitnessPayload80
        by_cases hp : x.2.2.2.1.val < 6
        · simp only [hp, ↓reduceDIte]
          by_cases hi3 : i.val < 3
          · simp [hi3]
          · simp [hi3, show ¬(i.val < 6) by omega, show ¬(i.val < 14) by omega]
        · simp only [hp, ↓reduceDIte]
          by_cases hi3 : i.val < 3
          · simp [hi3]
          · simp [hi3, show ¬(i.val < 6) by omega, show ¬(i.val < 14) by omega]
      · unfold encAll Sum.elim setWitnessNucB0 encTail writeB0Raw
        simp only [Bool.false_eq_true, ↓reduceIte, h36, h614]
        unfold tailWitnessPayload80
        by_cases hi3 : i.val < 3
        · simp [hi3]
        · simp [hi3, show ¬(i.val < 6) by omega, show ¬(i.val < 14) by omega]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p80ClearCosetAndNucLocal_encAll_false (z : HeadIdx ⊕ TailIdx) :
    p80ClearCosetAndNucLocal (encAll false z) = encAll false (setWitnessNucB0 (0, 0) z) := by
  funext i
  rw [encAll_false_setWitnessNucB0_apply (0, 0) z i]
  unfold p80ClearCosetAndNucLocal
  by_cases h36 : 3 ≤ i.val ∧ i.val < 6
  · simp [h36, show 3 ≤ i.val ∧ i.val < 14 from ⟨h36.1, by omega⟩, z2BitOfNat_zero_local]
  · by_cases h614 : 6 ≤ i.val ∧ i.val < 14
    · simp [h614, show 3 ≤ i.val ∧ i.val < 14 from ⟨by omega, h614.2⟩, z2BitOfNat_zero_local]
    · simp [h36, h614, show ¬(3 ≤ i.val ∧ i.val < 14) by omega]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encAll_false_setWitnessNucB0_of_clear (r : BitAssignment 80) (z₀ : HeadIdx ⊕ TailIdx)
    (hClear : p80ClearCosetAndNucLocal r = encAll false z₀) : r = encAll false
    (setWitnessNucB0 (⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ r (pos80SubIdx 6 8
    (by decide) j)), bitsVal_lt_two_pow_local _⟩, ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3
    ↦ r (pos80SubIdx 3 3 (by decide) j)), bitsVal_lt_two_pow_local _⟩) z₀) := by
  funext i
  rw [encAll_false_setWitnessNucB0_apply _ z₀ i]
  by_cases h36 : 3 ≤ i.val ∧ i.val < 6
  · let j : Fin 3 := ⟨i.val - 3, by omega⟩
    have hz := z2BitOfNat_bitsVal (fun w : Fin 3 ↦ r (pos80SubIdx 3 3 (by decide) w)) j
    rw [show pos80SubIdx 3 3 (by decide) j = i from Fin.ext (by
      dsimp [pos80SubIdx, j]
      omega)] at hz
    dsimp only [j] at hz
    simp [h36, hz.symm]
  · by_cases h614 : 6 ≤ i.val ∧ i.val < 14
    · let j : Fin 8 := ⟨i.val - 6, by omega⟩
      have hz := z2BitOfNat_bitsVal (fun w : Fin 8 ↦ r (pos80SubIdx 6 8 (by decide) w)) j
      rw [show pos80SubIdx 6 8 (by decide) j = i from Fin.ext (by
        dsimp [pos80SubIdx, j]
        omega)] at hz
      dsimp only [j] at hz
      simp [h36, h614, hz.symm]
    · simp only [h36, h614, ↓reduceIte, ← hClear]
      unfold p80ClearCosetAndNucLocal
      simp [show ¬(3 ≤ i.val ∧ i.val < 14) by omega]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encAll_false_nucVal (z : HeadIdx ⊕ TailIdx) : Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 8 ↦ encAll false z (pos80SubIdx 6 8 (by decide) j)) = Sum.elim
    (fun x : HeadIdx ↦ x.1.1.val) (fun y : TailIdx ↦ y.1.1.val) z := by
  rcases z with x | y
  · dsimp only [encAll, Sum.elim_inl]
    have hfn : (fun j : Fin 8 ↦ encHead false x (pos80SubIdx 6 8 (by decide) j)) = fun j : Fin
        8 ↦ headGeneralPayload80 0 x.1.1.val x.2.1.val x.2.2.1 x.2.2.2.1.val x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2 (pos80SubIdx 6 8 (by decide) j) := by
      funext j
      unfold encHead
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact writeB0Raw_out x.1.2 _ _ (by dsimp [pos80SubIdx]; omega)
    rw [hfn]
    exact (headGeneralPayload80_slices 0 (by decide) x.1.1 x.2.1
      x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2).2.1
  · dsimp only [encAll, Sum.elim_inr]
    have hfn : (fun j : Fin 8 ↦ encTail false y (pos80SubIdx 6 8 (by decide) j)) = fun j : Fin
        8 ↦ tailWitnessPayload80 0 y.1.1.val y.2.1.val y.2.2.1.val y.2.2.2.1.1 y.2.2.2.1.2.val
        y.2.2.2.2.1 y.2.2.2.2.2 (pos80SubIdx 6 8 (by decide) j) := by
      funext j
      unfold encTail
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact writeB0Raw_out y.1.2 _ _ (by dsimp [pos80SubIdx]; omega)
    rw [hfn]
    exact (tailWitnessPayload80_slices 0 (by decide) y.1.1 y.2.1 y.2.2.1
      y.2.2.2.1.1 y.2.2.2.1.2 y.2.2.2.2.1 y.2.2.2.2.2).2.1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem muSlot2Ideal218_on (z : HeadIdx ⊕ TailIdx) :
    muSlot2Ideal218 (encWitness true false z) = idealWitnessWeight true false z := by
  have hEnc : encWitness true false z = flipTailDpScratch80 (encAll false z) := rfl
  rw [hEnc]
  unfold muSlot2Ideal218
  have hNucFlip : Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ flipTailDpScratch80 (encAll
      false z) (pos80SubIdx 6 8 (by decide) j)) = Sum.elim (fun x : HeadIdx ↦ x.1.1.val)
      (fun y : TailIdx ↦ y.1.1.val) z := by
    rw [← p80NucVal_eq_bitsVal, p80NucVal_flipTailDpScratch80, p80NucVal_eq_bitsVal,
      encAll_false_nucVal]
  rw [hNucFlip]
  set nb : NucB0Idx := Sum.elim Prod.fst Prod.fst z
  have hnb : Sum.elim (fun x : HeadIdx ↦ x.1.1.val) (fun y : TailIdx ↦ y.1.1.val) z = nb.1.val := by
    rcases z with x | y <;> rfl
  rw [hnb]
  by_cases h216 : nb.1.val < 216
  · have hlt218 : nb.1.val < 218 := by omega
    have hand : ((nb.1.val &&& 216) == 216) = false := nuc_and216_of_lt216 nb.1 h216
    simp only [h216, ↓reduceIte, muSlot2Ideal216, flipTailDpScratch80_involutive,
      pos80IdealDist_on false z]
    rcases z with x | y <;>
      dsimp only [nb, Sum.elim_inl, Sum.elim_inr] at h216 hlt218 hand <;>
      unfold idealWitnessWeight idealNucB0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte, h216, hlt218, hand] <;>
      ring
  · simp only [h216, ↓reduceIte]
    by_cases h218 : nb.1.val < 218
    · have hge : 216 ≤ nb.1.val := Nat.le_of_not_lt h216
      have hand : ((nb.1.val &&& 216) == 216) = true := nuc_and216_of_216_218 nb.1 hge h218
      have hComm :
          muSlot2Ideal216 (p80ClearCosetAndNucLocal (flipTailDpScratch80 (encAll false z))) =
            pos80IdealDist false (encAll false (setWitnessNucB0 (0, 0) z)) := by
        unfold muSlot2Ideal216
        rw [p80ClearCosetAndNucLocal_eq_set0, flip_setCosetAndNuc_comm,
          flipTailDpScratch80_involutive, ← p80ClearCosetAndNucLocal_eq_set0,
          p80ClearCosetAndNucLocal_encAll_false]
      simp only [h218, ↓reduceIte, hComm, pos80IdealDist_on false (setWitnessNucB0 (0, 0) z)]
      have h0lt : (0 : Fin (2 ^ 8)).val < 216 := by decide
      have h0eq : ((0 : Fin (2 ^ 3)).val == 0) = true := rfl
      rcases z with x | y <;>
        dsimp only [nb, Sum.elim_inl, Sum.elim_inr] at h218 hand <;>
        unfold setWitnessNucB0 idealWitnessWeight idealNucB0 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, h218, hand, h0lt, h0eq] <;>
        ring
    · simp only [h218, ↓reduceIte]
      rcases z with x | y <;>
        dsimp only [nb, Sum.elim_inl, Sum.elim_inr] at h218 <;>
        unfold idealWitnessWeight idealNucB0 <;>
        simp [h218]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem muSlot2Ideal218_off (p : BitAssignment 80)
    (hOff : ∀ z : HeadIdx ⊕ TailIdx, p ≠ encWitness true false z) :
    muSlot2Ideal218 p = 0 := by
  by_contra hNe
  unfold muSlot2Ideal218 at hNe
  dsimp only at hNe
  by_cases h216 : Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
    p (pos80SubIdx 6 8 (by decide) j)) < 216
  · rw [ite_pos h216] at hNe
    have hPos : pos80IdealDist false (flipTailDpScratch80 p) ≠ 0 := fun h0 ↦ by
      unfold muSlot2Ideal216 at hNe
      rw [h0, mul_zero] at hNe
      exact hNe rfl
    have hEx : ∃ z, flipTailDpScratch80 p = encAll false z := by
      by_contra hNo
      exact hPos (pos80IdealDist_off false (flipTailDpScratch80 p) fun z hz ↦ hNo ⟨z, hz⟩)
    rcases hEx with ⟨z, hz⟩
    apply hOff z
    unfold encWitness
    simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
    rw [← hz, flipTailDpScratch80_involutive]
  · rw [ite_neg h216] at hNe
    by_cases h218 : Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
      p (pos80SubIdx 6 8 (by decide) j)) < 218
    · rw [ite_pos h218] at hNe
      have hPos : pos80IdealDist false (p80ClearCosetAndNucLocal (flipTailDpScratch80 p)) ≠ 0 :=
        fun h0 ↦ by
          unfold muSlot2Ideal216 at hNe
          rw [p80ClearCosetAndNucLocal_eq_set0, flip_setCosetAndNuc_comm,
            ← p80ClearCosetAndNucLocal_eq_set0, h0, mul_zero] at hNe
          exact hNe rfl
      have hEx : ∃ z₀, p80ClearCosetAndNucLocal (flipTailDpScratch80 p) = encAll false z₀ := by
        by_contra hNo
        exact hPos (pos80IdealDist_off false _ fun z₀ hz₀ ↦ hNo ⟨z₀, hz₀⟩)
      rcases hEx with ⟨z₀, hz₀⟩
      have hr := encAll_false_setWitnessNucB0_of_clear (flipTailDpScratch80 p) z₀ hz₀
      apply hOff
      · unfold encWitness
        simp only [Bool.not_false, Bool.true_and, ↓reduceIte]
        rw [← hr, flipTailDpScratch80_involutive]
    · rw [ite_neg h218] at hNe
      exact hNe rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_fin_beq_zero (m : ℕ) :
    (∑ i : Fin (2 ^ m), (if i.val == 0 then (1 : ℝ) else 0)) = 1 := by
  have hEq : (fun i : Fin (2 ^ m) ↦ if i.val == 0 then (1 : ℝ) else 0) =
      fun i : Fin (2 ^ m) ↦ if i = (0 : Fin (2 ^ m)) then (1 : ℝ) else 0 := by
    funext i
    have h0val : (0 : Fin (2 ^ m)).val = 0 := Fin.val_zero (2 ^ m)
    by_cases hi : i = (0 : Fin (2 ^ m))
    · subst hi; simp
    · have hne : i.val ≠ 0 := fun hv ↦ hi (Fin.ext (hv.trans h0val.symm))
      rw [beq_false_of_ne hne, ite_neg hi]
      rfl
  rw [hEq]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_fin8_eighth : (∑ _ : Fin (2 ^ 3), (1 / 8 : ℝ)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_bool_prod_quarter : (∑ _ : Bool × Bool, (1 / 4 : ℝ)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
  norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem qSplitHead_nonneg (s0 : Bool) : 0 ≤ qSplitHead s0 := by
  unfold qSplitHead
  cases s0 <;> simp only [Bool.false_eq_true, ↓reduceIte,
    pos80Slot2TotNat_val, pos80Slot4TotNat_val] <;> norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem qSplitTail_nonneg (s0 : Bool) : 0 ≤ qSplitTail s0 := by
  unfold qSplitTail
  cases s0 <;> simp only [Bool.false_eq_true, ↓reduceIte,
    pos80Slot2TotNat_val, pos80Slot4TotNat_val] <;> norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem qSplit_sum_eq_one (s0 : Bool) : qSplitHead s0 + qSplitTail s0 = 1 := by
  unfold qSplitHead qSplitTail
  cases s0 <;> simp only [Bool.false_eq_true, ↓reduceIte,
    pos80Slot2TotNat_val, pos80Slot4TotNat_val] <;> norm_num
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_b0_cond_merged (nuc : Fin (2 ^ 8)) : (∑ b0 : Fin (2 ^ 3), (if (nuc.val &&& 216) ==
    216 then (1 / 8 : ℝ) else if b0.val == 0 then 1 else 0)) = 1 := by
  by_cases h : ((nuc.val &&& 216) == 216) = true
  · simp only [h, ↓reduceIte]
    exact sum_fin8_eighth
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact sum_fin_beq_zero 3
section TailBhmtBounds
set_option exponentiation.threshold 64
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def goodDpKeepSet : Finset DpKeepIdx :=
  Finset.univ.filter (fun dk : DpKeepIdx ↦ dk.2.val < tailKeepSpanOfDp dk.1)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem card_goodDpKeepSet : goodDpKeepSet.card = 6388384375 := by
  unfold goodDpKeepSet
  have hc := card_prod_lt (α := Fin (2 ^ 3)) (N := 2 ^ 30) tailKeepSpanOfDp
    (fun dp ↦ (tailSpan_bounds dp).2)
  rw [hc]
  change (∑ dp : Fin 8, tailKeepSpanOfDp dp) = 6388384375
  rw [Fin.sum_univ_eight]
  decide
end TailBhmtBounds
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev FullWitnessIdx := (HeadIdx × Bool) ⊕ (TailIdx × Bool)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encWitness_head_at30 (isMerged218 s0 : Bool) (x : HeadIdx) :
    encWitness isMerged218 s0 (.inl x) (30 : Fin 80) = 1 := by
  unfold encWitness
  split_ifs
  · rw [flipTailDpScratch80_preserve _ 30 (by decide)]
    exact encHead_at30 false x
  · exact encHead_at30 s0 x
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encWitness_tail_at30 (isMerged218 s0 : Bool) (y : TailIdx) :
    encWitness isMerged218 s0 (.inr y) (30 : Fin 80) = 0 := by
  unfold encWitness
  split_ifs
  · rw [flipTailDpScratch80_preserve _ 30 (by decide)]
    exact encTail_at30 false y
  · exact encTail_at30 s0 y
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem encTailSub1_at30 (isMerged218 s0 : Bool) (y : TailIdx) :
    encTailSub1 isMerged218 s0 y (30 : Fin 80) = 0 := by
  unfold encTailSub1
  rw [Function.update_of_ne (by decide : (30 : Fin 80) ≠ 62)]
  exact encWitness_tail_at30 isMerged218 s0 y
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def pB0Weight (isMerged218 s0 : Bool) (nb : NucB0Idx) : ℝ := if s0 then
    (1 / 8 : ℝ) else if isMerged218 then if (nb.1.val &&& 216) == 216 then (1 / 8 : ℝ) else if
    nb.2.val == 0 then 1 else 0 else if nb.2.val == 0 then 1 else 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealHeadCond (isMerged218 s0 : Bool) (xb : HeadIdx × Bool) : ℝ :=
  if !xb.2 then idealNucB0 isMerged218 s0 xb.1.1 * idealHeadRest s0 xb.1.2 else 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealTailCond (isMerged218 s0 : Bool) (yb : TailIdx × Bool) : ℝ :=
  if !yb.2 then idealNucB0 isMerged218 s0 yb.1.1 * idealTailRest s0 yb.1.2 else 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealFullWeight (isMerged218 s0 : Bool) : FullWitnessIdx → ℝ
  | .inl xb => qSplitHead s0 * idealHeadCond isMerged218 s0 xb
  | .inr yb => qSplitTail s0 * idealTailCond isMerged218 s0 yb
section Joint16BhmtBounds
set_option exponentiation.threshold 64
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem card_prod_bool_false {ι : Type*} [Fintype ι] (P : ι → Bool) :
    (Finset.univ.filter (fun x : ι × Bool ↦ (!x.2 && P x.1) = true)).card =
      (Finset.univ.filter (fun u : ι ↦ P u = true)).card := by
  let emb : ι ↪ ι × Bool := ⟨fun u ↦ (u, false), fun _ _ h ↦ congrArg Prod.fst h⟩
  have hSet : Finset.univ.filter (fun x : ι × Bool ↦ (!x.2 && P x.1) = true) =
      (Finset.univ.filter (fun u : ι ↦ P u = true)).map emb := by
    ext ⟨u, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, emb,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    cases b <;> simp
  rw [hSet, Finset.card_map]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem card_fin_prod_lt {N₁ N₂ M₁ M₂ : ℕ} (h₁ : M₁ ≤ N₁) (h₂ : M₂ ≤ N₂) :
    (Finset.univ.filter (fun u : Fin N₁ × Fin N₂ ↦
      (decide (u.1.val < M₁) && decide (u.2.val < M₂)) = true)).card = M₁ * M₂ := by
  let emb : Fin M₁ × Fin M₂ ↪ Fin N₁ × Fin N₂ :=
    ⟨fun p ↦ (⟨p.1.val, lt_of_lt_of_le p.1.isLt h₁⟩, ⟨p.2.val, lt_of_lt_of_le p.2.isLt h₂⟩),
     by
       intro p1 p2 h
       simp only [Prod.mk.injEq, Fin.ext_iff] at h
       exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)⟩
  have hSet : Finset.univ.filter (fun u : Fin N₁ × Fin N₂ ↦ (decide (u.1.val < M₁) && decide
      (u.2.val < M₂)) = true) = Finset.univ.map emb := by
    ext ⟨u1, u2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, emb,
      Function.Embedding.coeFn_mk, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hu1, hu2⟩
      exact ⟨(⟨u1.val, hu1⟩, ⟨u2.val, hu2⟩), rfl⟩
    · rintro ⟨⟨i1, i2⟩, hEq⟩
      cases hEq
      exact ⟨i1.isLt, i2.isLt⟩
  rw [hSet, Finset.card_map, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def jointBhmtGen {ι : Type*} (P : ι → Bool) (cardG N : ℝ) (pGood pBad : ℝ)
    (x : ι × Bool) : ℝ :=
  let sSq := (cardG / N) * pGood
  if !x.2 then
    if P x.1 then
      (sSq * (3 - 4 * sSq) ^ 2) / cardG
    else
      ((1 - 4 * sSq) ^ 2 * pGood) / N
  else
    ((1 - 4 * sSq) ^ 2 * pBad) / N
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem jointBhmtGen_nonneg {ι : Type*} (P : ι → Bool) (cardG N pGood pBad : ℝ)
    (hG : 0 < cardG) (hN : 0 < N) (hpG : 0 ≤ pGood) (hpB : 0 ≤ pBad) (x : ι × Bool) : 0 ≤
    jointBhmtGen P cardG N pGood pBad x := by
  unfold jointBhmtGen
  dsimp only
  have hs0 : 0 ≤ (cardG / N) * pGood := mul_nonneg (div_nonneg hG.le hN.le) hpG
  split_ifs
  · exact div_nonneg (mul_nonneg hs0 (sq_nonneg _)) hG.le
  · exact div_nonneg (mul_nonneg (sq_nonneg _) hpG) hN.le
  · exact div_nonneg (mul_nonneg (sq_nonneg _) hpB) hN.le
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_jointBhmtGen_eq_one {ι : Type*} [Fintype ι] (P : ι → Bool)
    (cardG : ℕ) (pGood pBad : ℝ)
    (hCard : (Finset.univ.filter (fun u : ι ↦ P u = true)).card = cardG) (hG : 0 < cardG)
    (hN : 0 < Fintype.card ι) (hpSum : pGood + pBad = 1) : (∑ x : ι × Bool, jointBhmtGen P
    (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad x) = 1 := by
  rw [Fintype.sum_prod_type]
  have hBool : ∀ u : ι, (∑ b : Bool, jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood
      pBad (u, b)) = jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad (u, false) +
      jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad (u, true) :=
    fun u ↦ by rw [Fintype.sum_bool, add_comm]
  simp_rw [hBool]
  rw [Finset.sum_add_distrib]
  have hTrue : (∑ u : ι, jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad (u, true)) =
      (1 - 4 * (((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood)) ^ 2 * pBad := by
    unfold jointBhmtGen
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hNne : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    field_simp [hNne]
  rw [hTrue, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : ι ↦ P u = true)]
  have hGood : (∑ u ∈ Finset.univ.filter (fun u : ι ↦ P u = true),
      jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad (u, false)) =
      (((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood) *
        (3 - 4 * (((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood)) ^ 2 := by
    have hCong : ∀ u ∈ Finset.univ.filter (fun u : ι ↦ P u = true),
        jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad (u, false) =
          ((((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood) *
            (3 - 4 * (((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood)) ^ 2) / (cardG : ℝ) :=
      fun u hu ↦ by
        have hpu := (Finset.mem_filter.mp hu).2
        unfold jointBhmtGen
        simp [hpu]
    rw [Finset.sum_congr rfl hCong, Finset.sum_const, hCard, nsmul_eq_mul]
    have hGne : (cardG : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hG)
    field_simp [hGne]
  have hCardAdd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (p := fun u : ι ↦ P u = true)
  rw [Finset.card_univ, hCard] at hCardAdd
  have hBadCard : ((Finset.univ.filter (fun u : ι ↦ ¬(P u = true))).card : ℝ) =
      (Fintype.card ι : ℝ) - (cardG : ℝ) := by
    have hCast : (cardG : ℝ) + ((Finset.univ.filter (fun u : ι ↦ ¬(P u = true))).card : ℝ) =
        (Fintype.card ι : ℝ) := by exact_mod_cast hCardAdd
    linarith
  have hBad : (∑ u ∈ Finset.univ.filter (fun u : ι ↦ ¬(P u = true)), jointBhmtGen P (cardG :
      ℝ) (Fintype.card ι : ℝ) pGood pBad (u, false)) = ((Fintype.card ι : ℝ) - (cardG : ℝ)) *
      (((1 - 4 * (((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood)) ^ 2 * pGood) / (Fintype.card
      ι : ℝ)) := by
    have hCong : ∀ u ∈ Finset.univ.filter (fun u : ι ↦ ¬(P u = true)), jointBhmtGen P
        (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad (u, false) = ((1 - 4 * (((cardG : ℝ) /
        (Fintype.card ι : ℝ)) * pGood)) ^ 2 * pGood) / (Fintype.card ι : ℝ) :=
      fun u hu ↦ by
        have hpu := (Finset.mem_filter.mp hu).2
        unfold jointBhmtGen
        simp [hpu]
    rw [Finset.sum_congr rfl hCong, Finset.sum_const, nsmul_eq_mul, hBadCard]
  rw [hGood, hBad]
  have hpBadEq : pBad = 1 - pGood := by linarith
  have hNne : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [hpBadEq]
  field_simp [hNne]
  ring
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem jointBhmtGen_l1_le {ι : Type*} [Fintype ι]
    (P : ι → Bool) (cardG : ℕ) (pGood pBad : ℝ)
    (ideal : ι × Bool → ℝ)
    (hCard : (Finset.univ.filter (fun u : ι ↦ P u = true)).card = cardG)
    (hG : 0 < cardG) (hN : 0 < Fintype.card ι)
    (hpG : 0 ≤ pGood) (hpB : 0 ≤ pBad) (hpSum : pGood + pBad = 1)
    (hs : ((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood ≤ 1)
    (hIdealGood : ∀ x : ι × Bool, (!x.2 && P x.1) = true → ideal x = 1 / (cardG : ℝ))
    (hIdealOut : ∀ x : ι × Bool, ¬((!x.2 && P x.1) = true) → ideal x = 0) :
    let sSq := ((cardG : ℝ) / (Fintype.card ι : ℝ)) * pGood
    (∑ x : ι × Bool,
      |jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad x - ideal x|) ≤
      2 * (4 * sSq - 1) ^ 2 * (1 - sSq) := by
  intro sSq
  let G : Finset (ι × Bool) := Finset.univ.filter (fun x : ι × Bool ↦ (!x.2 && P x.1) = true)
  have hGCard : G.card = cardG := (card_prod_bool_false P).trans hCard
  exact bhmt_uniform_good_l1_le
    (jointBhmtGen P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad) ideal G sSq
    (by rw [hGCard]; exact hG)
    hs
    (jointBhmtGen_nonneg P (cardG : ℝ) (Fintype.card ι : ℝ) pGood pBad
      (by exact_mod_cast hG) (by exact_mod_cast hN) hpG hpB)
    (sum_jointBhmtGen_eq_one P cardG pGood pBad hCard hG hN hpSum).le
    (fun x hx ↦ by
      have hm := (Finset.mem_filter.mp hx).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
      unfold jointBhmtGen
      rw [hGCard, hm.1, hm.2]
      rfl)
    (fun x hx ↦ by
      rw [hGCard]
      exact hIdealGood x (Finset.mem_filter.mp hx).2)
    (fun x hx ↦ hIdealOut x (fun hm ↦ hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hm⟩)))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev JointHeadCore := (Fin (2 ^ 8) × Fin (2 ^ 3)) × Bool
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev HeadShellDom := Fin 56 × Fin (2 ^ 3) × (Bool × Bool)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def idealShellSmTr (z : HeadShellDom) : ℝ :=
  ((PosSlots24SemanticBridge.pos24HeadWeight56 z.1 : ℝ) / (727884457843 : ℝ)) *
    ((1 / 8 : ℝ) * (1 / 4 : ℝ))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem idealShellSmTr_nonneg (z : HeadShellDom) : 0 ≤ idealShellSmTr z :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (by norm_num)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_idealShellSmTr_eq_one : (∑ z : HeadShellDom, idealShellSmTr z) = 1 := by
  unfold idealShellSmTr
  rw [sum_prod_eq_mul
    (fun k : Fin 56 ↦ (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) / (727884457843 : ℝ))
    (fun _ : Fin (2 ^ 3) × (Bool × Bool) ↦ (1 / 8 : ℝ) * (1 / 4 : ℝ)),
    sum_prod_eq_mul (fun _ : Fin (2 ^ 3) ↦ (1 / 8 : ℝ)) (fun _ : Bool × Bool ↦ (1 / 4 : ℝ)),
    sum_pos24HeadWeight56_eq, sum_fin8_eighth, sum_bool_prod_quarter, mul_one, mul_one]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def headSlot2Equiv : (HeadIdx × Bool) ≃ Fin (2 ^ 8) × ((JointHeadCore × Fin (2 ^ 3)) × HeadShellDom)
    where
  toFun xb :=
    (xb.1.2.1, ((((xb.1.1.1, xb.1.2.2.2.1), xb.2), xb.1.1.2),
      (xb.1.2.2.1, xb.1.2.2.2.2.1, xb.1.2.2.2.2.2)))
  invFun z :=
    (((z.2.1.1.1.1, z.2.1.2), (z.1, z.2.2.1, z.2.1.1.1.2, z.2.2.2.1, z.2.2.2.2)), z.2.1.1.2)
  left_inv := by rintro ⟨⟨⟨nuc, b0⟩, anc, k, pid, sm, tr⟩, bAux⟩; rfl
  right_inv := by rintro ⟨anc, ⟨⟨⟨nuc, pid⟩, bAux⟩, b0⟩, k, sm, tr⟩; rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def headSlot4Equiv : (HeadIdx × Bool) ≃ Fin (2 ^ 8) × (Fin (2 ^ 3) × (JointHeadCore × HeadShellDom))
    where
  toFun xb :=
    (xb.1.1.1, (xb.1.1.2, (((xb.1.2.1, xb.1.2.2.2.1), xb.2),
      (xb.1.2.2.1, xb.1.2.2.2.2.1, xb.1.2.2.2.2.2))))
  invFun z :=
    (((z.1, z.2.1), (z.2.2.1.1.1, z.2.2.2.1, z.2.2.1.1.2, z.2.2.2.2.1, z.2.2.2.2.2)), z.2.2.1.2)
  left_inv := by rintro ⟨⟨⟨nuc, b0⟩, anc, k, pid, sm, tr⟩, bAux⟩; rfl
  right_inv := by rintro ⟨nuc, b0, ⟨⟨anc, pid⟩, bAux⟩, k, sm, tr⟩; rfl
end Joint16BhmtBounds
end Opts
set_option maxRecDepth 2000
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
end PosPostPrep80L1BoundsS3
end
end ModPosPostPrep80L1BoundsS3
end PosPostPrep80L1BoundsS3
end
set_option exponentiation.threshold 256
end PosPostPrep80L1BoundsS3Aux

section Aux_Coin3PerHorizon5799Aux
local instance (priority := 1000000) instNeZeroTwoPow_Aux_Coin3PerHorizon5799 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩


public section
section Aux_Coin3PerHorizon5799

section ModCoin3PerHorizon5799
public section
namespace Coin3PerHorizon5799
section ConfigCoin3PerHorizon5799
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 256
local instance (priority :=
  1000000) instLoc_Aux_Coin3PerHorizon5799_1InstNeZeroTwoPowM1 {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open _root_.QuantumComputation.Specs.StoppingPowerSolution (DynProgS2)
open MeasureBranchHadamardSem (ket ket_X ket_CNOT ket_TOFF toffoli_eval_sq bit_cases)
open ZeroAncillaUSP hiding ket
open SegmentAndTopClosure (cleanZeroEmbedIdx cleanZeroEmbedIdx_extract_act
  cleanZeroEmbedIdx_extract_subW)
open ZeroSubwireCoinPrep80 (toMatrix_entry00 toMatrix_entry10 coinHwa wCoin0 wCoin1 wCoin2 wCoinAnc)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def PreservesWire {N : ℕ} (w : Wire N) (A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) : Prop :=
  ∀ i j : Fin (2 ^ N), A i j ≠ 0 → basisBits N i w = basisBits N j w
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem zmod2_eq_of_eq_zero_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · rfl
  · exact absurd (h.mp rfl) one_ne_zero
  · exact absurd (h.mpr rfl) one_ne_zero
  · rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem preservesWire_iff_comm_cleanSetProj {N : ℕ} (w : Wire N)
    (A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) : PreservesWire w A ↔ A * cleanSetProj
    ({w} : Finset (Wire N)) = cleanSetProj ({w} : Finset (Wire N)) * A := by
  constructor
  · intro h
    ext i j
    rw [cleanSetProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hA : A i j = 0
    · simp [hA]
    · have hw := h i j hA
      simp [hw, mul_comm]
  · intro hcomm i j hA
    have hij := congrFun (congrFun hcomm i) j
    rw [cleanSetProj, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
    simp only [Finset.mem_singleton, forall_eq, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero] at hij
    apply zmod2_eq_of_eq_zero_iff
    constructor
    · intro hiw
      by_contra hjw
      rw [ite_eq_right hjw, ite_eq_left hiw] at hij
      exact hA hij.symm
    · intro hjw
      by_contra hiw
      rw [ite_eq_left hjw, ite_eq_right hiw] at hij
      exact hA hij
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.comm_cleanSetProj_finset {N : ℕ} {S : Finset (Wire N)}
    {A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ} (h : ∀ w ∈ S, PreservesWire w A) : A *
    cleanSetProj S = cleanSetProj S * A := by
  ext i j
  rw [cleanSetProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hA : A i j = 0
  · simp [hA]
  · have hiff : (∀ w ∈ S, basisBits N i w = 0) ↔ (∀ w ∈ S, basisBits N j w = 0) :=
      ⟨fun hi w hw ↦ (h w hw i j hA).symm.trans (hi w hw),
       fun hj w hw ↦ (h w hw i j hA).trans (hj w hw)⟩
    by_cases hj : ∀ w ∈ S, basisBits N j w = 0
    · rw [ite_eq_left hj, ite_eq_left (hiff.mpr hj), mul_one, one_mul]
    · rw [ite_eq_right hj, ite_eq_right (mt hiff.mp hj), mul_zero, zero_mul]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.preservesCleanSet_singleton {N : ℕ} {w : Wire N}
    {A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ} (h : PreservesWire w A) :
    PreservesCleanSet ({w} : Finset (Wire N)) A :=
  PreservesCleanSet.of_comm ((preservesWire_iff_comm_cleanSetProj w A).mp h)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.preservesCleanSet_finset {N : ℕ} {S : Finset (Wire N)}
    {A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ} (h : ∀ w ∈ S, PreservesWire w A) :
    PreservesCleanSet S A :=
  PreservesCleanSet.of_comm (PreservesWire.comm_cleanSetProj_finset h)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.one {N : ℕ} (w : Wire N) :
    PreservesWire w (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) := by
  intro i j hij
  by_cases h : i = j
  · subst h; rfl
  · simp [Matrix.one_apply_ne h] at hij
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.mul {N : ℕ} {w : Wire N} {A B : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ}
    (hA : PreservesWire w A) (hB : PreservesWire w B) : PreservesWire w (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  have hAk : A i k ≠ 0 := left_ne_zero_of_mul hk
  have hBk : B k j ≠ 0 := right_ne_zero_of_mul hk
  exact (hA i k hAk).trans (hB k j hBk)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.conjTranspose {N : ℕ} {w : Wire N}
    {A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ} (hA : PreservesWire w A) : PreservesWire w Aᴴ
    := by
  intro i j hij
  rw [Matrix.conjTranspose_apply, star_ne_zero] at hij
  exact (hA j i hij).symm
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.of_not_mem_support {N : ℕ} {w : Wire N} {c : Circuit N}
    (hw : w ∉ c.support) : PreservesWire w c.eval.1 :=
    (preservesWire_iff_comm_cleanSetProj w c.eval.1).mpr (eval_comm_cleanSetProj_of_disjoint c
    {w} (Finset.disjoint_singleton_right.mpr hw))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ket_basisBits_eq_single {N : ℕ} (j : Fin (2 ^ N)) :
    ket (basisBits N j) = (Pi.single j (1 : ℂ) : Fin (2 ^ N) → ℂ) := by
  simp [ket, MeasureBranchHadamardSem.ket, basisState]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem mulVec_ket_apply_eq {N : ℕ} (A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ)
    (β : BitAssignment N) (i : Fin (2 ^ N)) :
    (A.mulVec (ket β)) i = A i ((basisBitsEquiv N).symm β) := by
  have hk : ket β = (Pi.single ((basisBitsEquiv N).symm β) (1 : ℂ) : Fin (2 ^ N) → ℂ) := by
    simp [ket, MeasureBranchHadamardSem.ket, basisState]
  rw [hk]
  exact congrFun (Matrix.mulVec_single_one A ((basisBitsEquiv N).symm β)) i
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ket_apply_ne_zero_imp {N : ℕ} {γ : BitAssignment N} {i : Fin (2 ^ N)}
    (h : ket γ i ≠ 0) : basisBits N i = γ := by
  have hk : ket γ = (Pi.single ((basisBitsEquiv N).symm γ) (1 : ℂ) : Fin (2 ^ N) → ℂ) := by
    simp [ket, MeasureBranchHadamardSem.ket, basisState]
  rw [hk] at h
  by_cases hi : i = (basisBitsEquiv N).symm γ
  · subst hi; exact (basisBitsEquiv N).apply_symm_apply γ
  · simp [Pi.single_eq_of_ne hi] at h
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.of_mulVec_ket {N : ℕ} {w : Wire N}
    {A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ} (h : ∀ (β : BitAssignment N) (i : Fin (2 ^ N)),
    (A.mulVec (ket β)) i ≠ 0 → basisBits N i w = β w) : PreservesWire w A := by
  intro i j hA
  refine h (basisBits N j) i ?_
  have hsymm : (basisBitsEquiv N).symm (basisBits N j) = j :=
    (basisBitsEquiv N).symm_apply_apply j
  rwa [mulVec_ket_apply_eq, hsymm]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.cnot_of_ne {N : ℕ} {w c t : Wire N} (hct : c ≠ t) (hw : w ≠ t) :
    PreservesWire w (Circuit.CNOT c t hct).eval.1 := by
  apply PreservesWire.of_mulVec_ket
  intro β i hi
  rw [ket_CNOT] at hi
  have hEq := ket_apply_ne_zero_imp hi
  rw [hEq, Function.update_of_ne hw]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem support_hstGateCircuit_subset {N : ℕ} (g : HSTGate) (q : Wire N) :
    (hstGateCircuit g q).support ⊆ {q} := by
  cases g <;> simp [hstGateCircuit]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem support_hstWordCircuit_subset {N : ℕ} (word : List HSTGate) (q : Wire N) :
    (hstWordCircuit word q).support ⊆ {q} := by
  induction word with
  | nil => simp [hstWordCircuit]
  | cons g gs ih =>
      simp only [hstWordCircuit, Circuit.support_seq, Finset.union_subset_iff]
      exact ⟨support_hstGateCircuit_subset g q, ih⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem support_inverse_subset {N : ℕ} (c : Circuit N) : c.inverse.support ⊆ c.support := by
  induction c with
  | identity => simp
  | gate g r =>
      cases g <;>
        simp [Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.inverse_seq, Circuit.support_seq]
      intro w hw
      rcases Finset.mem_union.mp hw with h₂ | h₁
      · exact Finset.mem_union_right _ (ih₂ h₂)
      · exact Finset.mem_union_left _ (ih₁ h₁)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem vec_eq_sum_ket {N : ℕ} (v : Fin (2 ^ N) → ℂ) :
    v = ∑ k : Fin (2 ^ N), v k • ket (basisBits N k) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, ket_basisBits_eq_single, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki; simp [Pi.single_eq_of_ne (Ne.symm hki)]
  · intro hi; exact absurd (Finset.mem_univ i) hi
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem PreservesWire.toff_sandwich_target {N : ℕ} {c₁ c₂ anc : Wire N} (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) {L : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ}
    (h₁ : PreservesWire c₁ L) (h₂ : PreservesWire c₂ L) (ha : PreservesWire anc L) :
    PreservesWire anc ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * L * (Circuit.TOFF c₁ c₂
    anc h₁₂ h₁a h₂a).eval.1) := by
  apply PreservesWire.of_mulVec_ket
  intro β i hi
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_TOFF] at hi
  let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
  rw [vec_eq_sum_ket (L.mulVec (ket β₁)), Matrix.mulVec_sum] at hi
  simp only [Matrix.mulVec_smul, ket_TOFF, Finset.sum_apply, Pi.smul_apply] at hi
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hLk : (L.mulVec (ket β₁)) k ≠ 0 := left_ne_zero_of_smul hk
  have hket : ket (Function.update (basisBits N k) anc (basisBits N k anc + basisBits N k c₁ *
      basisBits N k c₂)) i ≠ 0 := right_ne_zero_of_smul hk
  rw [mulVec_ket_apply_eq] at hLk
  have hkc₁ : basisBits N k c₁ = β c₁ := by
    have h := h₁ k ((basisBitsEquiv N).symm β₁) hLk
    simpa [β₁, (basisBitsEquiv N).apply_symm_apply, Function.update_of_ne h₁a] using h
  have hkc₂ : basisBits N k c₂ = β c₂ := by
    have h := h₂ k ((basisBitsEquiv N).symm β₁) hLk
    simpa [β₁, (basisBitsEquiv N).apply_symm_apply, Function.update_of_ne h₂a] using h
  have hka : basisBits N k anc = β anc + β c₁ * β c₂ := by
    have h := ha k ((basisBitsEquiv N).symm β₁) hLk
    simpa [β₁, (basisBitsEquiv N).apply_symm_apply] using h
  have hEq := ket_apply_ne_zero_imp hket
  rw [hEq, Function.update_self, hka, hkc₁, hkc₂, add_assoc, CharTwo.add_self_eq_zero, add_zero]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
inductive CleanPrepProg (N : ℕ) where
  | circ (c : Circuit N)
  | seq (p₁ p₂ : CleanPrepProg N)
  | tempAnd (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : CleanPrepProg N)
namespace CleanPrepProg
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def toCircuit {N : ℕ} : CleanPrepProg N → Circuit N
  | .circ c => c
  | .seq p₁ p₂ => p₁.toCircuit ;;ᶜ p₂.toCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def inv {N : ℕ} : CleanPrepProg N → CleanPrepProg N
  | .circ c => .circ c.inverse
  | .seq p₁ p₂ => .seq p₂.inv p₁.inv
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body.inv
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def tBound {N : ℕ} : CleanPrepProg N → ℕ
  | .circ c => c.count PrimitiveGate.T + 4 * c.count PrimitiveGate.TOFF
  | .seq p₁ p₂ => p₁.tBound + p₂.tBound
  | .tempAnd _ _ _ _ _ _ body => 4 + body.tBound
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem count_t_inverse_eq {N : ℕ} (c : Circuit N) :
    c.inverse.count PrimitiveGate.T = c.count PrimitiveGate.T := by
  induction c with
  | identity => rfl
  | gate g r =>
      cases g <;> simp [Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.inverse_seq, Circuit.count_seq, ih₁, ih₂, add_comm]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem count_toff_inverse_eq {N : ℕ} (c : Circuit N) :
    c.inverse.count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF := by
  induction c with
  | identity => rfl
  | gate g r =>
      cases g <;> simp [Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.inverse_seq, Circuit.count_seq, ih₁, ih₂, add_comm]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem tBound_inv {N : ℕ} (p : CleanPrepProg N) :
    p.inv.tBound = p.tBound := by
  induction p with
  | circ c => rw [inv, tBound, count_t_inverse_eq, count_toff_inverse_eq]; rfl
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, tBound, ih₁, ih₂, add_comm]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih => simp [inv, tBound, ih]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem eval_inv_toCircuit {N : ℕ} (p : CleanPrepProg N) :
    p.inv.toCircuit.eval = (p.toCircuit.eval)⁻¹ := by
  induction p with
  | circ c => exact Circuit.eval_inverse c
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [inv, toCircuit, Circuit.eval_seq, ih₁, ih₂, _root_.mul_inv_rev]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      simp only [inv, toCircuit, Circuit.eval_seq, ih]
      let T := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right (toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a)
      change T * (body.toCircuit.eval)⁻¹ * T = (T * body.toCircuit.eval * T)⁻¹
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hTinv, mul_assoc]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def toDyn {Var : Type} {N n : ℕ} (r : QRegister N n) : CleanPrepProg N → DynProgS2 Var n
  | .circ c => .circ (Circuit.onRegister r c)
  | .seq p₁ p₂ => .seq (p₁.toDyn r) (p₂.toDyn r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd (r c₁) (r c₂) (r anc)
        (fun h ↦ h₁₂ (r.wires.injective h))
        (fun h ↦ h₁a (r.wires.injective h))
        (fun h ↦ h₂a (r.wires.injective h))
        (body.toDyn r)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem toDyn_toCircuit {Var : Type} {N n : ℕ} (r : QRegister N n) (p : CleanPrepProg N) :
    (p.toDyn (Var := Var) r).toCircuit = Circuit.onRegister r p.toCircuit := by
  induction p with
  | circ c => rfl
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [toDyn, toCircuit, DynProgS2.toCircuit, Circuit.onRegister, ih₁, ih₂]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      simp only [toDyn, toCircuit, DynProgS2.toCircuit, ih]
      have hT : Circuit.TOFF (r c₁) (r c₂) (r anc) (fun h ↦ h₁₂ (r.wires.injective h))
          (fun h ↦ h₁a (r.wires.injective h)) (fun h ↦ h₂a (r.wires.injective h)) =
          Circuit.onRegister r (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a) := by
        simp only [Circuit.TOFF, compat_primGate_TOFF_eq, Circuit.onRegister]
        congr 1
        ext i
        fin_cases i <;> rfl
      rw [hT]
      rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp]
theorem count_compile_toDyn_toff {Var : Type} {N n : ℕ} (v : Var) (qToff : Wire n)
    (r : QRegister N n) (p : CleanPrepProg N) :
    ((p.toDyn r).compile v qToff).count PrimitiveGate.TOFF = 0 := by
  induction p with
  | circ c => exact count_substCircuit_toff v qToff (Circuit.onRegister r c)
  | seq p₁ p₂ ih₁ ih₂ => simp [toDyn, DynProgS2.compile, ih₁, ih₂]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      simp [toDyn, DynProgS2.compile, DynamicCircuit.andCompute, DynamicCircuit.andUncompute,
        Circuit.count_andCompute_toff, Circuit.andUncomputeFixup, ih]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem count_compile_toDyn_t_le {Var : Type} {N n : ℕ} (v : Var) (qToff : Wire n)
    (r : QRegister N n) (p : CleanPrepProg N) :
    ((p.toDyn r).compile v qToff).count PrimitiveGate.T ≤ p.tBound := by
  induction p with
  | circ c =>
      refine (count_substCircuit_t_le v qToff (Circuit.onRegister r c)).trans ?_
      simp [Circuit.count_onRegister, tBound]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [toDyn, DynProgS2.compile, DynamicCircuit.count, tBound]
      omega
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      have hcomp : (DynamicCircuit.andCompute (Var := Var) (r c₁) (r c₂) (r anc)
          (fun h ↦ h₁a (r.wires.injective h))
          (fun h ↦ h₂a (r.wires.injective h))).count PrimitiveGate.T = 4 := by
        simp [DynamicCircuit.andCompute, Circuit.count_andCompute_t]
      have huncomp : (DynamicCircuit.andUncompute v (r c₁) (r c₂) (r anc)
          (fun h ↦ h₁₂ (r.wires.injective h))).count PrimitiveGate.T = 0 := by
        simp [DynamicCircuit.andUncompute, Circuit.andUncomputeFixup]
      simp only [toDyn, DynProgS2.compile, DynamicCircuit.count, tBound, hcomp, huncomp]
      omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def ValidDyn {N : ℕ} : Finset (Wire N) → CleanPrepProg N → Prop
  | S, .circ c => Disjoint c.support S
  | S, .seq p₁ p₂ => ValidDyn S p₁ ∧ ValidDyn S p₂
  | S, .tempAnd c₁ c₂ anc _ _ _ body =>
      anc ∈ S ∧
      ValidDyn (S.erase anc) body ∧
      PreservesWire c₁ body.toCircuit.eval.1 ∧
      PreservesWire c₂ body.toCircuit.eval.1 ∧
      PreservesWire anc body.toCircuit.eval.1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ValidDyn.inv {N : ℕ} {S : Finset (Wire N)} {p : CleanPrepProg N} (hv : ValidDyn S p) :
    ValidDyn S p.inv := by
  induction p generalizing S with
  | circ c =>
      exact Disjoint.mono_left (support_inverse_subset c) hv
  | seq p₁ p₂ ih₁ ih₂ =>
      exact ⟨ih₂ hv.2, ih₁ hv.1⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      rcases hv with ⟨hanc, hbody, hc₁, hc₂, ha⟩
      have hEvalInv : body.inv.toCircuit.eval.1 = (body.toCircuit.eval.1)ᴴ := by
        rw [eval_inv_toCircuit]
        rfl
      refine ⟨hanc, ih hbody, ?_, ?_, ?_⟩ <;> rw [hEvalInv]
      · exact hc₁.conjTranspose
      · exact hc₂.conjTranspose
      · exact ha.conjTranspose
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem support_onRegister_subset {N n : ℕ} (r : QRegister N n) (c : Circuit N) :
    (Circuit.onRegister r c).support ⊆ c.support.image r.wires := by
  induction c with
  | identity => simp [Circuit.onRegister]
  | gate g reg =>
      intro w hw
      simp only [Circuit.onRegister, Circuit.support_gate, QRegister.mem_image] at hw ⊢
      obtain ⟨i, rfl⟩ := hw
      exact Finset.mem_image.mpr ⟨reg i, QRegister.mem_image reg (reg i) |>.mpr ⟨i, rfl⟩, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ =>
      intro w hw
      simp only [Circuit.onRegister, Circuit.support_seq, Finset.mem_union] at hw
      rw [Circuit.support_seq, Finset.image_union]
      exact hw.elim (fun h ↦ Finset.mem_union_left _ (ih₁ h))
        (fun h ↦ Finset.mem_union_right _ (ih₂ h))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem embedMatrix_cleanSetProj_singleton {N n : ℕ} (r : QRegister N n) (anc : Wire N) :
    r.embedMatrix (cleanSetProj ({anc} : Finset (Wire N))) =
      cleanSetProj ({r anc} : Finset (Wire n)) := by
  have hcomp : r.compose (QRegister.singleton anc) = QRegister.singleton (r anc) := by
    ext i; fin_cases i; rfl
  rw[cleanSetProj_singleton, cleanSetProj_singleton, QRegister.basisOutcomeProjector,
      QRegister.basisOutcomeProjector, ← hcomp, QRegister.embedMatrix_compose]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem ValidDyn.toSemValid {Var : Type} [Fintype Var] [DecidableEq Var] {N n : ℕ}
    [NeZero (2 ^ n)] {S : Finset (Wire N)} {p : CleanPrepProg N} (hv : ValidDyn S p)
    (rFull : QRegister N n) (v : Var) (qToff : Wire n) (hq : qToff ∉ rFull.image) :
    (p.toDyn rFull).SemValid v qToff (insert qToff (S.image rFull.wires)) := by
  induction p generalizing S with
  | circ c =>
      refine ⟨Finset.mem_insert_self _ _, Finset.disjoint_left.mpr fun w hw hmem ↦ ?_⟩
      obtain ⟨u, hu_supp, rfl⟩ := Finset.mem_image.mp (support_onRegister_subset rFull c hw)
      rcases Finset.mem_insert.mp hmem with hEq | hImg
      · exact hq (QRegister.mem_image rFull _ |>.mpr ⟨u, hEq⟩)
      · obtain ⟨u', hu'S, hu'Eq⟩ := Finset.mem_image.mp hImg
        cases rFull.wires.injective hu'Eq
        exact Finset.disjoint_left.mp hv hu_supp hu'S
  | seq p₁ p₂ ih₁ ih₂ =>
      exact ⟨ih₁ hv.1, ih₂ hv.2⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      rcases hv with ⟨hanc, hbody, hc₁, hc₂, ha⟩
      have hanc_mem : rFull anc ∈ insert qToff (S.image rFull.wires) :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem rFull.wires hanc)
      have hanc_ne_q : rFull anc ≠ qToff :=
        fun h ↦ hq (QRegister.mem_image rFull qToff |>.mpr ⟨anc, h⟩)
      have rotAux : (insert qToff (S.image rFull.wires)).erase (rFull anc) =
          insert qToff ((S.erase anc).image rFull.wires) := by
        ext w
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_image]
        constructor
        · rintro ⟨hne, rfl | ⟨u, huS, rfl⟩⟩
          · exact Or.inl rfl
          · refine Or.inr ⟨u, ⟨fun hu ↦ hne (congrArg rFull.wires hu), huS⟩, rfl⟩
        · rintro (rfl | ⟨u, ⟨hu_ne, huS⟩, rfl⟩)
          · exact ⟨hanc_ne_q.symm, Or.inl rfl⟩
          · exact ⟨fun h ↦ hu_ne (rFull.wires.injective h), Or.inr ⟨u, huS, rfl⟩⟩
      have hLocalPres : PreservesCleanSet ({anc} : Finset (Wire N))
          (CleanPrepProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toCircuit.eval.1 := by
        simp only [CleanPrepProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul]
        exact (PreservesWire.toff_sandwich_target h₁₂ h₁a h₂a hc₁ hc₂
          ha).preservesCleanSet_singleton
      have hGlobPres : PreservesCleanSet ({rFull anc} : Finset (Wire n))
          ((CleanPrepProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toDyn (Var :=
            Var) rFull).toCircuit.eval.1 := by
        rw [toDyn_toCircuit, Circuit.eval_onRegister, QRegister.embedUnitary_val]
        unfold PreservesCleanSet at hLocalPres ⊢
        rw [← embedMatrix_cleanSetProj_singleton rFull anc, ← rFull.embedMatrix_mul,
          ← rFull.embedMatrix_mul, hLocalPres, rFull.embedMatrix_mul]
      refine ⟨hanc_mem, ?_, hGlobPres⟩
      rw [rotAux]
      exact ih hbody
end CleanPrepProg
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem basisOutcomeProjector_zero_eq_cleanSetProj {m n : ℕ} (r : QRegister m n) :
    r.basisOutcomeProjector 0 = cleanSetProj r.image := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, cleanSetProj]
  congr 1
  funext g
  have hiff : r.extractIndex g = 0 ↔ ∀ w ∈ r.image, basisBits n g w = 0 := by
    constructor
    · intro h w hw
      obtain ⟨j, rfl⟩ := QRegister.mem_image r w |>.mp hw
      have h0 : basisBits m (r.extractIndex g) j = 0 := by
        rw [h]; simp [-Nat.reducePow, basisBits_eq_div_mod]
      simpa only [QRegister.basisBits_extractIndex] using h0
    · intro h
      apply (basisBitsEquiv m).injective
      funext j
      change basisBits m (r.extractIndex g) j = basisBits m 0 j
      rw [QRegister.basisBits_extractIndex, h (r j) (QRegister.mem_image r _ |>.mpr ⟨j, rfl⟩)]
      simp [-Nat.reducePow, basisBits_eq_div_mod]
  by_cases h : r.extractIndex g = 0
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem preservesCleanSubW_of_preservesWire {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (A : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ)
    (hPres : ∀ w : Wire N, k_act ≤ w.val → PreservesWire w A) :
    (QRegister.block k_act k_w (by omega) : QRegister k_w N).basisOutcomeProjector 0 * A *
      (QRegister.block k_act k_w (by omega) : QRegister k_w N).basisOutcomeProjector 0 =
    A * (QRegister.block k_act k_w (by omega) : QRegister k_w N).basisOutcomeProjector 0 := by
  let rSub : QRegister k_w N := QRegister.block k_act k_w (by omega)
  change rSub.basisOutcomeProjector 0 * A * rSub.basisOutcomeProjector 0 =
    A * rSub.basisOutcomeProjector 0
  rw [basisOutcomeProjector_zero_eq_cleanSetProj]
  refine PreservesWire.preservesCleanSet_finset fun w hw ↦ hPres w ?_
  obtain ⟨j, rfl⟩ := QRegister.mem_image rSub w |>.mp hw
  change k_act ≤ k_act + j.val
  omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def castRegLenLocal {M N n : ℕ} (h : M = N) (r : QRegister M n) : QRegister N n := h ▸ r
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def dCleanSubDynProg {Var : Type} {k_act k_w N mWork n : ℕ} (hN : k_act + k_w = N)
    (hm : 1 + k_w ≤ mWork) (v : Var) (rAct : QRegister k_act n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) (p : CleanPrepProg N) : DynamicCircuit Var n :=
  let rSubW : QRegister k_w n := rWork.slice 1 k_w hm
  have hActSub : rAct.DisjointWires rSubW := hDisj.compose_right _
  (p.toDyn (castRegLenLocal hN (rAct.concat rSubW hActSub))).compile v (rWork ⟨0, by omega⟩)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem dCleanSubDynProg_count_TOFF {Var : Type} {k_act k_w N mWork n : ℕ}
    (hN : k_act + k_w = N) (hm : 1 + k_w ≤ mWork) (v : Var) (rAct : QRegister k_act n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) (p : CleanPrepProg N) :
    (dCleanSubDynProg hN hm v rAct rWork hDisj p).count PrimitiveGate.TOFF = 0 :=
    CleanPrepProg.count_compile_toDyn_toff _ _ _ _
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem dCleanSubDynProg_count_T_le {Var : Type} {k_act k_w N mWork n : ℕ}
    (hN : k_act + k_w = N) (hm : 1 + k_w ≤ mWork) (v : Var) (rAct : QRegister k_act n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) (p : CleanPrepProg N) :
    (dCleanSubDynProg hN hm v rAct rWork hDisj p).count PrimitiveGate.T ≤ p.tBound :=
    CleanPrepProg.count_compile_toDyn_t_le _ _ _ _
open Classical in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem realizesCleanWorkspace_dCleanSubDynProg {Var : Type} [Finite Var] [DecidableEq Var]
    {k_act k_w N mWork n : ℕ} [NeZero (2 ^ n)] (hN : k_act + k_w = N) (hm : 1 + k_w ≤ mWork)
    (v : Var) (rAct : QRegister k_act n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) (S : Finset (Wire N)) (hS : ∀ w ∈ S, k_act ≤ w.val)
    (p : CleanPrepProg N) (hv : CleanPrepProg.ValidDyn S p) (U_eff : Unitary (2 ^ k_act))
    (hMulProj : p.toCircuit.eval.1 * (QRegister.block k_act k_w (by omega) : QRegister k_w
    N).basisOutcomeProjector 0 = ((QRegister.block 0 k_act (by omega) : QRegister k_act
    N).embedUnitary U_eff).1 * (QRegister.block k_act k_w (by omega) : QRegister k_w
    N).basisOutcomeProjector 0) : ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
      wp
    (dCleanSubDynProg hN hm v rAct rWork hDisj p).compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    rWork.basisOutcomeProjector 0 * M'.1.1 * rWork.basisOutcomeProjector 0 =
    rWork.basisOutcomeProjector 0 *
    ((rAct.embedUnitary U_eff).1ᴴ * M.1.1 * (rAct.embedUnitary U_eff).1) *
    rWork.basisOutcomeProjector 0 := by
  let _ : Fintype Var := Fintype.ofFinite Var
  subst hN
  let rSubW : QRegister k_w n := rWork.slice 1 k_w hm
  have hActSub : rAct.DisjointWires rSubW := hDisj.compose_right _
  let rFull : QRegister (k_act + k_w) n := rAct.concat rSubW hActSub
  let qToff : Wire n := rWork ⟨0, by omega⟩
  have hqNotMem : qToff ∉ rFull.image := by
    intro hmem
    obtain ⟨u, hu⟩ := (QRegister.mem_image rFull qToff).mp hmem
    revert hu
    refine Fin.addCases (fun i hi ↦ ?_) (fun j hj ↦ ?_) u
    · rw [QRegister.concat_apply_left] at hi
      exact hDisj.ne i ⟨0, by omega⟩ hi
    · rw [QRegister.concat_apply_right, QRegister.slice_apply] at hj
      have hval := congrArg Fin.val (rWork.wires.injective hj)
      dsimp at hval; omega
  let S_glob : Finset (Wire n) := insert qToff (S.image rFull.wires)
  have hSem : (p.toDyn (Var := Var) rFull).SemValid v qToff S_glob :=
    hv.toSemValid rFull v qToff hqNotMem
  have hsub : ∀ w ∈ S_glob, ∃ j : Fin mWork, rWork j = w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hImg
    · exact ⟨⟨0, by omega⟩, rfl⟩
    · obtain ⟨u, huS, rfl⟩ := Finset.mem_image.mp hImg
      have hge : k_act ≤ u.val := hS u huS
      let idx : Fin k_w := ⟨u.val - k_act, by omega⟩
      have huEq : u = Fin.natAdd k_act idx := by
        ext; dsimp [idx]; omega
      refine ⟨⟨1 + idx.val, by omega⟩, ?_⟩
      have h1 : rFull u = rFull (Fin.natAdd k_act idx) := congrArg rFull.wires huEq
      rw [h1, QRegister.concat_apply_right, QRegister.slice_apply]
  have hSubAbsorb : rSubW.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 := by
    have hR : rWork.basisOutcomeProjector 0 * cleanSetProj rSubW.image =
        rWork.basisOutcomeProjector 0 := by
      refine basisOutcomeProjector_zero_mul_cleanSetProj rWork rSubW.image fun w hw ↦ ?_
      obtain ⟨j, rfl⟩ := QRegister.mem_image rSubW w |>.mp hw
      exact ⟨⟨1 + j.val, by omega⟩, (QRegister.slice_apply rWork 1 k_w hm j).symm⟩
    have hAdj := congrArg conjTranspose hR
    rw [conjTranspose_mul, cleanSetProj_conjTranspose,
      QRegister.basisOutcomeProjector_conjTranspose,
      ← basisOutcomeProjector_zero_eq_cleanSetProj] at hAdj
    exact hAdj
  let rAct0 : QRegister k_act (k_act + k_w) := QRegister.block 0 k_act (by omega)
  let rSub0 : QRegister k_w (k_act + k_w) := QRegister.block k_act k_w (by omega)
  have hCompAct : rFull.compose rAct0 = rAct := by
    ext i
    have hi : rAct0 i = Fin.castAdd k_w i := by ext; change 0 + i.val = i.val; omega
    change (rFull (rAct0 i)).val = (rAct i).val
    rw [hi, QRegister.concat_apply_left]
  have hCompSub : rFull.compose rSub0 = rSubW := by
    ext i
    have hi : rSub0 i = Fin.natAdd k_act i := by ext; rfl
    change (rFull (rSub0 i)).val = (rSubW i).val
    rw [hi, QRegister.concat_apply_right]
  have hFullMul : (rFull.embedUnitary p.toCircuit.eval).1 * rSubW.basisOutcomeProjector 0 =
      (rAct.embedUnitary U_eff).1 * rSubW.basisOutcomeProjector 0 := by
    have hPS : rSubW.basisOutcomeProjector 0 = rFull.embedMatrix (rSub0.basisOutcomeProjector 0) :=
      by
      rw [QRegister.basisOutcomeProjector, ← hCompSub, QRegister.embedMatrix_compose,
        ← QRegister.basisOutcomeProjector]
    have hUA : (rAct.embedUnitary U_eff).1 = rFull.embedMatrix (rAct0.embedUnitary U_eff).1 := by
      rw [QRegister.embedUnitary_val, ← hCompAct, QRegister.embedMatrix_compose,
        ← QRegister.embedUnitary_val]
    rw [QRegister.embedUnitary_val, hPS, hUA, ← rFull.embedMatrix_mul, ← rFull.embedMatrix_mul]
    exact congrArg rFull.embedMatrix hMulProj
  have hXP : (rFull.embedUnitary p.toCircuit.eval).1 * rWork.basisOutcomeProjector 0 =
      (rAct.embedUnitary U_eff).1 * rWork.basisOutcomeProjector 0 := by
    calc (rFull.embedUnitary p.toCircuit.eval).1 * rWork.basisOutcomeProjector 0
        = ((rFull.embedUnitary p.toCircuit.eval).1 * rSubW.basisOutcomeProjector 0) *
            rWork.basisOutcomeProjector 0 := by rw [Matrix.mul_assoc, hSubAbsorb]
      _ = ((rAct.embedUnitary U_eff).1 * rSubW.basisOutcomeProjector 0) *
            rWork.basisOutcomeProjector 0 := by rw [hFullMul]
      _ = (rAct.embedUnitary U_eff).1 * rWork.basisOutcomeProjector 0 := by
            rw [Matrix.mul_assoc, hSubAbsorb]
  have hEvalDyn : (p.toDyn (Var := Var) rFull).toCircuit.eval =
      rFull.embedUnitary p.toCircuit.eval := by
    rw [CleanPrepProg.toDyn_toCircuit, Circuit.eval_onRegister]
  have hSpec := DynProgS2.wp_compile_clean_workspace_spec hSem rFull rWork hsub
    p.toCircuit.eval hEvalDyn
  intro M
  obtain ⟨M', hwp, heq⟩ := hSpec M
  refine ⟨M', hwp, ?_⟩
  rw [heq]
  set PW := rWork.basisOutcomeProjector 0
  have hPWh : PWᴴ = PW := QRegister.basisOutcomeProjector_conjTranspose rWork 0
  calc PW * ((rFull.embedUnitary p.toCircuit.eval).1ᴴ * M.1.1 *
          (rFull.embedUnitary p.toCircuit.eval).1) * PW
      = ((rFull.embedUnitary p.toCircuit.eval).1 * PW)ᴴ * M.1.1 *
          ((rFull.embedUnitary p.toCircuit.eval).1 * PW) := by
            rw [conjTranspose_mul, hPWh]; simp only [Matrix.mul_assoc]
    _ = ((rAct.embedUnitary U_eff).1 * PW)ᴴ * M.1.1 *
          ((rAct.embedUnitary U_eff).1 * PW) := by rw [hXP]
    _ = PW * ((rAct.embedUnitary U_eff).1ᴴ * M.1.1 * (rAct.embedUnitary U_eff).1) * PW := by
          rw [conjTranspose_mul, hPWh]; simp only [Matrix.mul_assoc]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def stepX (m : Mat2Zw) : Mat2Zw := ⟨m.m10, m.m11, m.m00, m.m01, m.h⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def stepToggleBool (d : Bool) (m : Mat2Zw) : Mat2Zw := if d then stepX m else m
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def matPlus : Mat2Zw := evalList [.H] matId
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
structure AffineLayer2 where
  c0 : Bool
  x0 : Bool
  c1 : Bool
  x1 : Bool
  deriving DecidableEq, Repr
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def toggleBool2 (c x b0 : Bool) : Bool := xor c (x && b0)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def stepMux2Layer (l : AffineLayer2) (b0 : Bool) (m : Mat2Zw) : Mat2Zw :=
  let d0 := toggleBool2 l.c0 l.x0 b0
  let d1 := toggleBool2 l.c1 l.x1 b0
  stepToggleBool d1 (evalList [.H] (stepToggleBool d0 (evalList [.T] (stepToggleBool d0 m))))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def evalMux2Layers : List AffineLayer2 → Bool → Mat2Zw → Mat2Zw
  | [], _, m => m
  | l :: ls, b0, m => evalMux2Layers ls b0 (stepMux2Layer l b0 m)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem evalMux2Layers_append (u v : List AffineLayer2) (b0 : Bool)
    (m m1 : Mat2Zw) (h1 : evalMux2Layers u b0 m = m1) :
    evalMux2Layers (u ++ v) b0 m = evalMux2Layers v b0 m1 := by
  induction u generalizing m with
  | nil =>
      dsimp only [evalMux2Layers] at h1
      subst h1
      rfl
  | cons l ls ih =>
      exact ih (stepMux2Layer l b0 m) h1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
structure AnfLayer3 where
  c0 : Bool
  x0 : Bool
  y0 : Bool
  z0 : Bool
  c1 : Bool
  x1 : Bool
  y1 : Bool
  z1 : Bool
  deriving DecidableEq, Repr
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def toggleBoolAnf3 (c x y z b0 b1 : Bool) : Bool :=
  xor (xor (xor c (x && b0)) (y && b1)) (z && (b0 && b1))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def stepAnf3Layer (l : AnfLayer3) (b0 b1 : Bool) (m : Mat2Zw) : Mat2Zw :=
  let d0 := toggleBoolAnf3 l.c0 l.x0 l.y0 l.z0 b0 b1
  let d1 := toggleBoolAnf3 l.c1 l.x1 l.y1 l.z1 b0 b1
  stepToggleBool d1 (evalList [.H] (stepToggleBool d0 (evalList [.T] (stepToggleBool d0 m))))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def evalAnf3Layers : List AnfLayer3 → Bool → Bool → Mat2Zw → Mat2Zw
  | [], _, _, m => m
  | l :: ls, b0, b1, m => evalAnf3Layers ls b0 b1 (stepAnf3Layer l b0 b1 m)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem evalAnf3Layers_append (u v : List AnfLayer3) (b0 b1 : Bool)
    (m m1 : Mat2Zw) (h1 : evalAnf3Layers u b0 b1 m = m1) :
    evalAnf3Layers (u ++ v) b0 b1 m = evalAnf3Layers v b0 b1 m1 := by
  induction u generalizing m with
  | nil =>
      dsimp only [evalAnf3Layers] at h1
      subst h1
      rfl
  | cons l ls ih =>
      exact ih (stepAnf3Layer l b0 b1 m) h1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cToggleCoin1 (c x : Bool) : Circuit 4 :=
  (if c then Circuit.X wCoin1 else Circuit.identity) ;;ᶜ
  (if x then Circuit.CNOT wCoin0 wCoin1 (by decide) else Circuit.identity)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cMux2Layer (l : AffineLayer2) : Circuit 4 :=
  cToggleCoin1 l.c0 l.x0 ;;ᶜ
  hstGateCircuit .T wCoin1 ;;ᶜ
  cToggleCoin1 l.c0 l.x0 ;;ᶜ
  hstGateCircuit .H wCoin1 ;;ᶜ
  cToggleCoin1 l.c1 l.x1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cAffineMux2 : List AffineLayer2 → Circuit 4
  | [] => Circuit.identity
  | l :: ls => cMux2Layer l ;;ᶜ cAffineMux2 ls
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cToggleCoin2Anf (c x y z : Bool) : Circuit 4 :=
  (if c then Circuit.X wCoin2 else Circuit.identity) ;;ᶜ
  (if x then Circuit.CNOT wCoin0 wCoin2 (by decide) else Circuit.identity) ;;ᶜ
  (if y then Circuit.CNOT wCoin1 wCoin2 (by decide) else Circuit.identity) ;;ᶜ
  (if z then Circuit.CNOT wCoinAnc wCoin2 (by decide) else Circuit.identity)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cAnf3Layer (l : AnfLayer3) : Circuit 4 :=
  cToggleCoin2Anf l.c0 l.x0 l.y0 l.z0 ;;ᶜ
  hstGateCircuit .T wCoin2 ;;ᶜ
  cToggleCoin2Anf l.c0 l.x0 l.y0 l.z0 ;;ᶜ
  hstGateCircuit .H wCoin2 ;;ᶜ
  cToggleCoin2Anf l.c1 l.x1 l.y1 l.z1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cAnfMux3 : List AnfLayer3 → Circuit 4
  | [] => Circuit.identity
  | l :: ls => cAnf3Layer l ;;ᶜ cAnfMux3 ls
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cStage2Gen (ls2 : List AffineLayer2) : Circuit 4 :=
  hstGateCircuit .H wCoin1 ;;ᶜ cAffineMux2 ls2
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def cStages1To2HGen (w0 : List HSTGate) (ls2 : List AffineLayer2) : Circuit 4 :=
  hstWordCircuit w0 wCoin0 ;;ᶜ
  cStage2Gen ls2 ;;ᶜ
  hstGateCircuit .H wCoin2
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def pStage3Gen (ls3 : List AnfLayer3) : CleanPrepProg 4 := .tempAnd wCoin0
    wCoin1 wCoinAnc (by decide) (by decide) (by decide) (.circ (cAnfMux3 ls3))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def pCoinPrepGen (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    : CleanPrepProg 4 :=
  CleanPrepProg.seq (.circ (cStages1To2HGen w0 ls2)) (pStage3Gen ls3)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_toff_cToggleCoin1 (c x : Bool) :
    (cToggleCoin1 c x).count PrimitiveGate.TOFF = 0 := by
  cases c <;> cases x <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_t_cToggleCoin1 (c x : Bool) :
    (cToggleCoin1 c x).count PrimitiveGate.T = 0 := by
  cases c <;> cases x <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_toff_cMux2Layer (l : AffineLayer2) :
    (cMux2Layer l).count PrimitiveGate.TOFF = 0 := by
  simp [cMux2Layer, hstGateCircuit]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_t_cMux2Layer (l : AffineLayer2) :
    (cMux2Layer l).count PrimitiveGate.T = 1 := by
  simp [cMux2Layer, hstGateCircuit]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_toff_cAffineMux2 (ls : List AffineLayer2) :
    (cAffineMux2 ls).count PrimitiveGate.TOFF = 0 := by
  induction ls with
  | nil => rfl
  | cons l rest ih => simp [cAffineMux2, ih]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_t_cAffineMux2 (ls : List AffineLayer2) :
    (cAffineMux2 ls).count PrimitiveGate.T = ls.length := by
  induction ls with
  | nil => rfl
  | cons l rest ih =>
      simp only [cAffineMux2, Circuit.count_seq, count_t_cMux2Layer, ih, List.length_cons]
      omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_toff_cToggleCoin2Anf (c x y z : Bool) :
    (cToggleCoin2Anf c x y z).count PrimitiveGate.TOFF = 0 := by
  cases c <;> cases x <;> cases y <;> cases z <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_t_cToggleCoin2Anf (c x y z : Bool) :
    (cToggleCoin2Anf c x y z).count PrimitiveGate.T = 0 := by
  cases c <;> cases x <;> cases y <;> cases z <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_toff_cAnf3Layer (l : AnfLayer3) :
    (cAnf3Layer l).count PrimitiveGate.TOFF = 0 := by
  simp [cAnf3Layer, hstGateCircuit]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_t_cAnf3Layer (l : AnfLayer3) :
    (cAnf3Layer l).count PrimitiveGate.T = 1 := by
  simp [cAnf3Layer, hstGateCircuit]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_toff_cAnfMux3 (ls : List AnfLayer3) :
    (cAnfMux3 ls).count PrimitiveGate.TOFF = 0 := by
  induction ls with
  | nil => rfl
  | cons l rest ih => simp [cAnfMux3, ih]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem count_t_cAnfMux3 (ls : List AnfLayer3) :
    (cAnfMux3 ls).count PrimitiveGate.T = ls.length := by
  induction ls with
  | nil => rfl
  | cons l rest ih =>
      simp only [cAnfMux3, Circuit.count_seq, count_t_cAnf3Layer, ih, List.length_cons]
      omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp]
theorem count_toff_cStages1To2HGen (w0 : List HSTGate) (ls2 : List AffineLayer2) :
    (cStages1To2HGen w0 ls2).count PrimitiveGate.TOFF = 0 := by
  simp [cStages1To2HGen, cStage2Gen, hstGateCircuit]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem count_t_cStages1To2HGen (w0 : List HSTGate) (ls2 : List AffineLayer2) :
    (cStages1To2HGen w0 ls2).count PrimitiveGate.T = hstWordTCount w0 + ls2.length := by
  have hH1 : (hstGateCircuit .H wCoin1).count PrimitiveGate.T = 0 := rfl
  have hH2 : (hstGateCircuit .H wCoin2).count PrimitiveGate.T = 0 := rfl
  simp only [cStages1To2HGen, cStage2Gen, Circuit.count_seq, count_t_hstWordCircuit,
    count_t_cAffineMux2, hH1, hH2]
  omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tBound_pStage3Gen (ls3 : List AnfLayer3) :
    (pStage3Gen ls3).tBound = 4 + ls3.length := by
  simp [pStage3Gen, CleanPrepProg.tBound, count_t_cAnfMux3, count_toff_cAnfMux3]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tBound_pCoinPrepGen_eq (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    :
    (pCoinPrepGen w0 ls2 ls3).tBound = (hstWordTCount w0 + ls2.length) + (4 + ls3.length) := by
  simp [pCoinPrepGen, CleanPrepProg.tBound, tBound_pStage3Gen,
    count_t_cStages1To2HGen, count_toff_cStages1To2HGen]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_seq_local {N : ℕ} {w : Wire N} {c₁ c₂ : Circuit N}
    (h₁ : w ∉ c₁.support) (h₂ : w ∉ c₂.support) :
    w ∉ (c₁ ;;ᶜ c₂).support := by
  rw [Circuit.support_seq, Finset.mem_union]
  rintro (h | h)
  · exact h₁ h
  · exact h₂ h
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_x_of_ne {N : ℕ} {w q : Wire N} (hw : w ≠ q) :
    w ∉ (Circuit.X q).support := by
  simp [Circuit.X, hw]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_cnot_of_ne {N : ℕ} {w c t : Wire N} (hct : c ≠ t) (hwc : w ≠ c)
    (hwt : w ≠ t) : w ∉ (Circuit.CNOT c t hct).support := by
  intro hmem
  simp only [Circuit.CNOT, compat_primGate_CNOT_eq, Circuit.support_gate,
    QRegister.mem_image] at hmem
  obtain ⟨i, hi⟩ := hmem
  fin_cases i
  · exact hwc hi.symm
  · exact hwt hi.symm
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_hstGate_of_ne {N : ℕ} (g : HSTGate) {w q : Wire N} (hw : w ≠ q) :
    w ∉ (hstGateCircuit g q).support :=
  fun hm ↦ hw (Finset.mem_singleton.mp (support_hstGateCircuit_subset g q hm))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_hstWord_of_ne {N : ℕ} (word : List HSTGate) {w q : Wire N} (hw : w ≠ q) :
    w ∉ (hstWordCircuit word q).support :=
  fun hm ↦ hw (Finset.mem_singleton.mp (support_hstWordCircuit_subset word q hm))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_cToggleCoin1 (c x : Bool) :
    wCoinAnc ∉ (cToggleCoin1 c x).support := by
  dsimp only [cToggleCoin1]
  refine not_mem_support_seq_local ?_ ?_
  · cases c
    · simp
    · exact not_mem_support_x_of_ne (by decide)
  · cases x
    · simp
    · exact not_mem_support_cnot_of_ne _ (by decide) (by decide)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_cMux2Layer (l : AffineLayer2) : wCoinAnc ∉ (cMux2Layer l).support :=
    not_mem_support_seq_local (not_mem_support_cToggleCoin1 _ _) (not_mem_support_seq_local
    (not_mem_support_hstGate_of_ne .T (by decide)) (not_mem_support_seq_local
    (not_mem_support_cToggleCoin1 _ _) (not_mem_support_seq_local
    (not_mem_support_hstGate_of_ne .H (by decide)) (not_mem_support_cToggleCoin1 _ _))))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_cAffineMux2 (ls : List AffineLayer2) :
    wCoinAnc ∉ (cAffineMux2 ls).support := by
  induction ls with
  | nil => simp [cAffineMux2]
  | cons l rest ih => exact not_mem_support_seq_local (not_mem_support_cMux2Layer l) ih
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem not_mem_support_cStages1To2HGen (w0 : List HSTGate) (ls2 : List AffineLayer2) :
    wCoinAnc ∉ (cStages1To2HGen w0 ls2).support := not_mem_support_seq_local
    (not_mem_support_hstWord_of_ne _ (by decide)) (not_mem_support_seq_local
    (not_mem_support_seq_local (not_mem_support_hstGate_of_ne .H (by decide))
    (not_mem_support_cAffineMux2 _)) (not_mem_support_hstGate_of_ne .H (by decide)))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem preservesWire_seq_local {N : ℕ} {w : Wire N} {c₁ c₂ : Circuit N}
    (h₁ : PreservesWire w c₁.eval.1) (h₂ : PreservesWire w c₂.eval.1) :
    PreservesWire w (c₁ ;;ᶜ c₂).eval.1 := by
  rw [Circuit.eval_seq, Submonoid.coe_mul]
  exact h₂.mul h₁
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem preservesWire_cToggleCoin2Anf_of_ne (c x y z : Bool) {w : Wire 4} (hw : w ≠ wCoin2) :
    PreservesWire w (cToggleCoin2Anf c x y z).eval.1 := by
  dsimp only [cToggleCoin2Anf]
  refine preservesWire_seq_local ?_ (preservesWire_seq_local ?_ (preservesWire_seq_local ?_ ?_))
  · cases c
    · exact PreservesWire.of_not_mem_support (by simp)
    · exact PreservesWire.of_not_mem_support (not_mem_support_x_of_ne hw)
  · cases x
    · exact PreservesWire.of_not_mem_support (by simp)
    · exact PreservesWire.cnot_of_ne _ hw
  · cases y
    · exact PreservesWire.of_not_mem_support (by simp)
    · exact PreservesWire.cnot_of_ne _ hw
  · cases z
    · exact PreservesWire.of_not_mem_support (by simp)
    · exact PreservesWire.cnot_of_ne _ hw
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem preservesWire_cAnf3Layer_of_ne (l : AnfLayer3) {w : Wire 4} (hw : w ≠ wCoin2) :
    PreservesWire w (cAnf3Layer l).eval.1 :=
  preservesWire_seq_local (preservesWire_cToggleCoin2Anf_of_ne _ _ _ _ hw)
    (preservesWire_seq_local (PreservesWire.of_not_mem_support (not_mem_support_hstGate_of_ne .T
      hw))
      (preservesWire_seq_local (preservesWire_cToggleCoin2Anf_of_ne _ _ _ _ hw)
        (preservesWire_seq_local (PreservesWire.of_not_mem_support (not_mem_support_hstGate_of_ne .H
          hw))
          (preservesWire_cToggleCoin2Anf_of_ne _ _ _ _ hw))))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem preservesWire_cAnfMux3_of_ne (ls : List AnfLayer3) {w : Wire 4} (hw : w ≠ wCoin2) :
    PreservesWire w (cAnfMux3 ls).eval.1 := by
  induction ls with
  | nil => exact PreservesWire.of_not_mem_support (by simp [cAnfMux3])
  | cons l rest ih => exact preservesWire_seq_local (preservesWire_cAnf3Layer_of_ne l hw) ih
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def sCoinAnc4 : Finset (Wire 4) := {wCoinAnc}
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem validDyn_pCoinPrepGen (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) :
    CleanPrepProg.ValidDyn sCoinAnc4 (pCoinPrepGen w0 ls2 ls3) := by
  refine ⟨Finset.disjoint_singleton_right.mpr (not_mem_support_cStages1To2HGen w0 ls2), ?_⟩
  refine ⟨Finset.mem_singleton_self wCoinAnc, ?_, preservesWire_cAnfMux3_of_ne _ (by decide),
    preservesWire_cAnfMux3_of_ne _ (by decide), preservesWire_cAnfMux3_of_ne _ (by decide)⟩
  change Disjoint _ (({wCoinAnc} : Finset (Wire 4)).erase wCoinAnc)
  simp
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def bits4 (b0 b1 b2 b3 : ZMod 2) : BitAssignment 4 := fun q ↦ if q.val = 0 then b0 else if
    q.val = 1 then b1 else if q.val = 2 then b2 else b3
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem bits4_0 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoin0 = b0 := rfl
@[scoped simp] theorem bits4_1 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoin1 = b1 := rfl
@[scoped simp] theorem bits4_2 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoin2 = b2 := rfl
@[scoped simp] theorem bits4_3 (b0 b1 b2 b3 : ZMod 2) : bits4 b0 b1 b2 b3 wCoinAnc = b3 := rfl
@[scoped simp] theorem upd_bits4_0 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoin0 v = bits4 v b1 b2 b3 := by
  funext q; fin_cases q <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem upd_bits4_1 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoin1 v = bits4 b0 v b2 b3 := by
  funext q; fin_cases q <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem upd_bits4_2 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoin2 v = bits4 b0 b1 v b3 := by
  funext q; fin_cases q <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem upd_bits4_3 (b0 b1 b2 b3 v : ZMod 2) :
    Function.update (bits4 b0 b1 b2 b3) wCoinAnc v = bits4 b0 b1 b2 v := by
  funext q; fin_cases q <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
def zmodOfBool (b : Bool) : ZMod 2 := if b then 1 else 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[scoped simp] theorem zmodOfBool_false : zmodOfBool false = 0 := rfl
@[scoped simp] theorem zmodOfBool_true : zmodOfBool true = 1 := rfl
theorem cToggle1StepC_mulVec_ket (c b0 b1 : Bool) :
    (if c then Circuit.X wCoin1 else Circuit.identity).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0)) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool (xor b1 c)) 0 0) := by
  cases c
  · change (Circuit.identity : Circuit 4).eval.1.mulVec _ = _
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    cases b1 <;> rfl
  · change (Circuit.X wCoin1).eval.1.mulVec _ = _
    rw [ket_X, bits4_1, upd_bits4_1]
    cases b1 <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cToggle1StepX_mulVec_ket (x b0 b1 : Bool) :
    (if x then Circuit.CNOT wCoin0 wCoin1 (by decide) else Circuit.identity).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0)) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool (xor b1 (x && b0))) 0 0) := by
  cases x
  · change (Circuit.identity : Circuit 4).eval.1.mulVec _ = _
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    cases b1 <;> rfl
  · change (Circuit.CNOT wCoin0 wCoin1 (by decide)).eval.1.mulVec _ = _
    rw [ket_CNOT, bits4_0, bits4_1, upd_bits4_1]
    cases b0 <;> cases b1 <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cToggleCoin1_mulVec_ket_bool (c x b0 b1 : Bool) : (cToggleCoin1 c x).eval.1.mulVec
    (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0)) = ket (bits4 (zmodOfBool b0) (zmodOfBool
    (xor b1 (toggleBool2 c x b0))) 0 0) := by
  simp only [cToggleCoin1, MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [cToggle1StepC_mulVec_ket, cToggle1StepX_mulVec_ket]
  have hbool : xor (xor b1 c) (x && b0) = xor b1 (toggleBool2 c x b0) := by
    cases c <;> cases x <;> cases b0 <;> cases b1 <;> rfl
  rw [hbool]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cToggleCoin1_mulVec_pair (c x b0 : Bool) (m : Mat2Zw) :
    (cToggleCoin1 c x).eval.1.mulVec (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0 0) +
    m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0)) =
    (stepToggleBool (toggleBool2 c x b0) m).toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0 0) +
    (stepToggleBool (toggleBool2 c x b0) m).toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0)
    := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have h0 := cToggleCoin1_mulVec_ket_bool c x b0 false
  have h1 := cToggleCoin1_mulVec_ket_bool c x b0 true
  rw [zmodOfBool_false] at h0
  rw [zmodOfBool_true] at h1
  rw [h0, h1]
  cases hd : toggleBool2 c x b0
  · rfl
  · have ht0 : (stepToggleBool true m).toMatrix 0 0 = m.toMatrix 1 0 := by
      rw [toMatrix_entry00, toMatrix_entry10]; rfl
    have ht1 : (stepToggleBool true m).toMatrix 1 0 = m.toMatrix 0 0 := by
      rw [toMatrix_entry10, toMatrix_entry00]; rfl
    have hz1 : zmodOfBool (xor false true) = 1 := rfl
    have hz0 : zmodOfBool (xor true true) = 0 := rfl
    rw [hz1, hz0, ht0, ht1]
    exact add_comm _ _
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem hstGateCircuit_wCoin1_mulVec_pair (g : HSTGate) (b0 : Bool) (m : Mat2Zw) :
    (hstGateCircuit g wCoin1).eval.1.mulVec (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0
    0) + m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0)) = (evalList [g] m).toMatrix 0 0 •
    ket (bits4 (zmodOfBool b0) 0 0 0) + (evalList [g] m).toMatrix 1 0 • ket
    (bits4 (zmodOfBool b0) 1 0 0) := by
  have hne10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  rw [hstGate_eval_eq g wCoin1, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    singleton_embedMatrix_mulVec_ket, singleton_embedMatrix_mulVec_ket]
  simp only [bits4_1, ↓reduceIte, hne10, upd_bits4_1]
  have hmul : (evalList [g] m).toMatrix = wordMatrix2 [g] * m.toMatrix := by
    rw [wordMatrix2, evalList_mul_right]
  ext idx
  simp only [hmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cMux2Layer_mulVec_pair (l : AffineLayer2) (b0 : Bool) (m : Mat2Zw) :
    (cMux2Layer l).eval.1.mulVec (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0 0) +
    m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0)) = (stepMux2Layer l b0 m).toMatrix 0 0
    • ket (bits4 (zmodOfBool b0) 0 0 0) + (stepMux2Layer l b0 m).toMatrix 1 0 • ket
    (bits4 (zmodOfBool b0) 1 0 0) := by
  dsimp only [cMux2Layer, stepMux2Layer]
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw[cToggleCoin1_mulVec_pair, hstGateCircuit_wCoin1_mulVec_pair, cToggleCoin1_mulVec_pair,
      hstGateCircuit_wCoin1_mulVec_pair, cToggleCoin1_mulVec_pair]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cAffineMux2_mulVec_pair (ls : List AffineLayer2) (b0 : Bool) (m : Mat2Zw) :
    (cAffineMux2 ls).eval.1.mulVec (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0 0) +
    m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0)) = (evalMux2Layers ls b0 m).toMatrix 0
    0 • ket (bits4 (zmodOfBool b0) 0 0 0) + (evalMux2Layers ls b0 m).toMatrix 1 0 • ket
    (bits4 (zmodOfBool b0) 1 0 0) := by
  induction ls generalizing m with
  | nil => simp [cAffineMux2, evalMux2Layers]
  | cons l rest ih =>
      simp only [cAffineMux2, evalMux2Layers, MeasureBranchHadamardSem.eval_seq_mulVec]
      rw [cMux2Layer_mulVec_pair, ih]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cStage2Gen_mulVec_ket (ls2 : List AffineLayer2) (b0 : Bool) :
    (cStage2Gen ls2).eval.1.mulVec (ket (bits4 (zmodOfBool b0) 0 0 0)) =
    (evalMux2Layers ls2 b0 matPlus).toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0 0) +
    (evalMux2Layers ls2 b0 matPlus).toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0) := by
  have hid : ket (bits4 (zmodOfBool b0) 0 0 0) =
      matId.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0 0) +
        matId.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0) := by
    have h00 : matId.toMatrix 0 0 = 1 := by simp [matId, Mat2Zw.toMatrix, Zw.toComplex]
    have h10 : matId.toMatrix 1 0 = 0 := by simp [matId, Mat2Zw.toMatrix, Zw.toComplex]
    rw [h00, h10, one_smul, zero_smul, add_zero]
  have hH : (hstGateCircuit .H wCoin1).eval.1.mulVec (ket (bits4 (zmodOfBool b0) 0 0 0)) =
      matPlus.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) 0 0 0) +
        matPlus.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) 1 0 0) := by
    conv_lhs => rw [hid]
    exact hstGateCircuit_wCoin1_mulVec_pair .H b0 matId
  dsimp only [cStage2Gen]
  rw [MeasureBranchHadamardSem.eval_seq_mulVec, hH]
  exact cAffineMux2_mulVec_pair ls2 b0 matPlus
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem toff013_mulVec_ket_in (b0 b1 : Bool) (b2 : ZMod 2) :
    (Circuit.TOFF wCoin0 wCoin1 wCoinAnc (by decide) (by decide) (by decide)).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) b2 0)) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool b1) b2 (zmodOfBool (b0 && b1))) := by
  rw [ket_TOFF, bits4_0, bits4_1, bits4_3, upd_bits4_3]
  have hand : (0 : ZMod 2) + zmodOfBool b0 * zmodOfBool b1 = zmodOfBool (b0 && b1) := by
    cases b0 <;> cases b1 <;> rfl
  rw [hand]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem toff013_mulVec_ket_out (b0 b1 : Bool) (b2 : ZMod 2) :
    (Circuit.TOFF wCoin0 wCoin1 wCoinAnc (by decide) (by decide) (by decide)).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) b2 (zmodOfBool (b0 && b1)))) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool b1) b2 0) := by
  rw [ket_TOFF, bits4_0, bits4_1, bits4_3, upd_bits4_3]
  have hand : zmodOfBool (b0 && b1) + zmodOfBool b0 * zmodOfBool b1 = 0 := by
    cases b0 <;> cases b1 <;> rfl
  rw [hand]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cAnfStepC_mulVec_ket (c b0 b1 b2 b3 : Bool) :
    (if c then Circuit.X wCoin2 else Circuit.identity).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool b2) (zmodOfBool b3))) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool (xor b2 c)) (zmodOfBool b3)) := by
  cases c
  · change (Circuit.identity : Circuit 4).eval.1.mulVec _ = _
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    cases b2 <;> rfl
  · change (Circuit.X wCoin2).eval.1.mulVec _ = _
    rw [ket_X, bits4_2, upd_bits4_2]
    cases b2 <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cAnfStepX_mulVec_ket (x b0 b1 b2 b3 : Bool) :
    (if x then Circuit.CNOT wCoin0 wCoin2 (by decide) else Circuit.identity).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool b2) (zmodOfBool b3))) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool (xor b2 (x && b0))) (zmodOfBool b3)) :=
        by
  cases x
  · change (Circuit.identity : Circuit 4).eval.1.mulVec _ = _
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    cases b2 <;> rfl
  · change (Circuit.CNOT wCoin0 wCoin2 (by decide)).eval.1.mulVec _ = _
    rw [ket_CNOT, bits4_0, bits4_2, upd_bits4_2]
    cases b0 <;> cases b2 <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cAnfStepY_mulVec_ket (y b0 b1 b2 b3 : Bool) :
    (if y then Circuit.CNOT wCoin1 wCoin2 (by decide) else Circuit.identity).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool b2) (zmodOfBool b3))) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool (xor b2 (y && b1))) (zmodOfBool b3)) :=
        by
  cases y
  · change (Circuit.identity : Circuit 4).eval.1.mulVec _ = _
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    cases b2 <;> rfl
  · change (Circuit.CNOT wCoin1 wCoin2 (by decide)).eval.1.mulVec _ = _
    rw [ket_CNOT, bits4_1, bits4_2, upd_bits4_2]
    cases b1 <;> cases b2 <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cAnfStepZ_mulVec_ket (z b0 b1 b2 b3 : Bool) :
    (if z then Circuit.CNOT wCoinAnc wCoin2 (by decide) else Circuit.identity).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool b2) (zmodOfBool b3))) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool (xor b2 (z && b3))) (zmodOfBool b3)) :=
        by
  cases z
  · change (Circuit.identity : Circuit 4).eval.1.mulVec _ = _
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    cases b2 <;> rfl
  · change (Circuit.CNOT wCoinAnc wCoin2 (by decide)).eval.1.mulVec _ = _
    rw [ket_CNOT, bits4_3, bits4_2, upd_bits4_2]
    cases b3 <;> cases b2 <;> rfl
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cToggleCoin2Anf_mulVec_ket_bool (c x y z b0 b1 b2 : Bool) :
    (cToggleCoin2Anf c x y z).eval.1.mulVec (ket (bits4 (zmodOfBool b0) (zmodOfBool b1)
    (zmodOfBool b2) (zmodOfBool (b0 && b1)))) = ket (bits4 (zmodOfBool b0) (zmodOfBool b1)
    (zmodOfBool (xor b2 (toggleBoolAnf3 c x y z b0 b1))) (zmodOfBool (b0 && b1))) := by
  simp only [cToggleCoin2Anf, MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [cAnfStepC_mulVec_ket, cAnfStepX_mulVec_ket, cAnfStepY_mulVec_ket, cAnfStepZ_mulVec_ket]
  have hbool : xor (xor (xor (xor b2 c) (x && b0)) (y && b1)) (z && (b0 && b1)) =
      xor b2 (toggleBoolAnf3 c x y z b0 b1) := by
    cases c <;> cases x <;> cases y <;> cases z <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl
  rw [hbool]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cToggleCoin2Anf_mulVec_pair (c x y z b0 b1 : Bool) (m : Mat2Zw) :
    (cToggleCoin2Anf c x y z).eval.1.mulVec
        (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 (zmodOfBool (b0 && b1))) +
          m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 (zmodOfBool (b0 && b1)))) =
      (stepToggleBool (toggleBoolAnf3 c x y z b0 b1) m).toMatrix 0 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 (zmodOfBool (b0 && b1))) +
        (stepToggleBool (toggleBoolAnf3 c x y z b0 b1) m).toMatrix 1 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 (zmodOfBool (b0 && b1))) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have h0 := cToggleCoin2Anf_mulVec_ket_bool c x y z b0 b1 false
  have h1 := cToggleCoin2Anf_mulVec_ket_bool c x y z b0 b1 true
  rw [zmodOfBool_false] at h0
  rw [zmodOfBool_true] at h1
  rw [h0, h1]
  cases hd : toggleBoolAnf3 c x y z b0 b1
  · rfl
  · have ht0 : (stepToggleBool true m).toMatrix 0 0 = m.toMatrix 1 0 := by
      rw [toMatrix_entry00, toMatrix_entry10]; rfl
    have ht1 : (stepToggleBool true m).toMatrix 1 0 = m.toMatrix 0 0 := by
      rw [toMatrix_entry10, toMatrix_entry00]; rfl
    have hz1 : zmodOfBool (xor false true) = 1 := rfl
    have hz0 : zmodOfBool (xor true true) = 0 := rfl
    rw [hz1, hz0, ht0, ht1]
    exact add_comm _ _
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem hstGateCircuit_wCoin2_anf_mulVec_pair (g : HSTGate) (b0 b1 : Bool) (b3 : ZMod 2) (m :
    Mat2Zw) :
    (hstGateCircuit g wCoin2).eval.1.mulVec
        (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 b3) +
          m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 b3)) =
      (evalList [g] m).toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 b3) +
        (evalList [g] m).toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 b3) := by
  have hne10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  rw [hstGate_eval_eq g wCoin2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    singleton_embedMatrix_mulVec_ket, singleton_embedMatrix_mulVec_ket]
  simp only [bits4_2, ↓reduceIte, hne10, upd_bits4_2]
  have hmul : (evalList [g] m).toMatrix = wordMatrix2 [g] * m.toMatrix := by
    rw [wordMatrix2, evalList_mul_right]
  ext idx
  simp only [hmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cAnf3Layer_mulVec_pair (l : AnfLayer3) (b0 b1 : Bool) (m : Mat2Zw) :
    (cAnf3Layer l).eval.1.mulVec (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1)
    0 (zmodOfBool (b0 && b1))) + m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1
    (zmodOfBool (b0 && b1)))) = (stepAnf3Layer l b0 b1 m).toMatrix 0 0 • ket
    (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 (zmodOfBool (b0 && b1))) +
    (stepAnf3Layer l b0 b1 m).toMatrix 1 0 • ket
    (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 (zmodOfBool (b0 && b1))) := by
  dsimp only [cAnf3Layer, stepAnf3Layer]
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [cToggleCoin2Anf_mulVec_pair, hstGateCircuit_wCoin2_anf_mulVec_pair,
    cToggleCoin2Anf_mulVec_pair, hstGateCircuit_wCoin2_anf_mulVec_pair,
    cToggleCoin2Anf_mulVec_pair]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cAnfMux3_mulVec_pair (ls : List AnfLayer3) (b0 b1 : Bool) (m : Mat2Zw) :
    (cAnfMux3 ls).eval.1.mulVec (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0
    (zmodOfBool (b0 && b1))) + m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1
    (zmodOfBool (b0 && b1)))) = (evalAnf3Layers ls b0 b1 m).toMatrix 0 0 • ket
    (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 (zmodOfBool (b0 && b1))) +
    (evalAnf3Layers ls b0 b1 m).toMatrix 1 0 • ket
    (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 (zmodOfBool (b0 && b1))) := by
  induction ls generalizing m with
  | nil => simp [cAnfMux3, evalAnf3Layers]
  | cons l rest ih =>
      simp only [cAnfMux3, evalAnf3Layers, MeasureBranchHadamardSem.eval_seq_mulVec]
      rw [cAnf3Layer_mulVec_pair, ih]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem h_then_pStage3Gen_mulVec_ket (ls3 : List AnfLayer3) (b0 b1 : Bool) :
    (hstGateCircuit .H wCoin2 ;;ᶜ (pStage3Gen ls3).toCircuit).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0)) =
      (evalAnf3Layers ls3 b0 b1 matPlus).toMatrix 0 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        (evalAnf3Layers ls3 b0 b1 matPlus).toMatrix 1 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
  have hid : ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) =
      matId.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        matId.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
    have h00 : matId.toMatrix 0 0 = 1 := by simp [matId, Mat2Zw.toMatrix, Zw.toComplex]
    have h10 : matId.toMatrix 1 0 = 0 := by simp [matId, Mat2Zw.toMatrix, Zw.toComplex]
    rw [h00, h10, one_smul, zero_smul, add_zero]
  have hH : (hstGateCircuit .H wCoin2).eval.1.mulVec
      (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0)) =
      matPlus.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        matPlus.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
    conv_lhs => rw [hid]
    exact hstGateCircuit_wCoin2_anf_mulVec_pair .H b0 b1 0 matId
  dsimp only [pStage3Gen, CleanPrepProg.toCircuit]
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw[hH, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      toff013_mulVec_ket_in b0 b1 0, toff013_mulVec_ket_in b0 b1 1,
      cAnfMux3_mulVec_pair ls3 b0 b1 matPlus, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, toff013_mulVec_ket_out b0 b1 0, toff013_mulVec_ket_out b0 b1 1]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def coin3Col0AmpGen (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List
    AnfLayer3) :
    Fin 8 → ℂ
  | ⟨0, _⟩ =>
      wordMatrix2 w0 0 0 *
        (evalMux2Layers ls2 false matPlus).toMatrix 0 0 *
        (evalAnf3Layers ls3 false false matPlus).toMatrix 0 0
  | ⟨1, _⟩ =>
      wordMatrix2 w0 1 0 *
        (evalMux2Layers ls2 true matPlus).toMatrix 0 0 *
        (evalAnf3Layers ls3 true false matPlus).toMatrix 0 0
  | ⟨2, _⟩ =>
      wordMatrix2 w0 0 0 *
        (evalMux2Layers ls2 false matPlus).toMatrix 1 0 *
        (evalAnf3Layers ls3 false true matPlus).toMatrix 0 0
  | ⟨3, _⟩ =>
      wordMatrix2 w0 1 0 *
        (evalMux2Layers ls2 true matPlus).toMatrix 1 0 *
        (evalAnf3Layers ls3 true true matPlus).toMatrix 0 0
  | ⟨4, _⟩ =>
      wordMatrix2 w0 0 0 *
        (evalMux2Layers ls2 false matPlus).toMatrix 0 0 *
        (evalAnf3Layers ls3 false false matPlus).toMatrix 1 0
  | ⟨5, _⟩ =>
      wordMatrix2 w0 1 0 *
        (evalMux2Layers ls2 true matPlus).toMatrix 0 0 *
        (evalAnf3Layers ls3 true false matPlus).toMatrix 1 0
  | ⟨6, _⟩ =>
      wordMatrix2 w0 0 0 *
        (evalMux2Layers ls2 false matPlus).toMatrix 1 0 *
        (evalAnf3Layers ls3 false true matPlus).toMatrix 1 0
  | ⟨7, _⟩ =>
      wordMatrix2 w0 1 0 *
        (evalMux2Layers ls2 true matPlus).toMatrix 1 0 *
        (evalAnf3Layers ls3 true true matPlus).toMatrix 1 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pCoinPrepGen_mulVec_zero (w0 : List HSTGate) (ls2 : List AffineLayer2)
    (ls3 : List AnfLayer3) : (pCoinPrepGen w0 ls2 ls3).toCircuit.eval.1.mulVec
    (ket (bits4 0 0 0 0)) = coin3Col0AmpGen w0 ls2 ls3 0 • ket (bits4 0 0 0 0) +
    coin3Col0AmpGen w0 ls2 ls3 1 • ket (bits4 1 0 0 0) + coin3Col0AmpGen w0 ls2 ls3 2 • ket
    (bits4 0 1 0 0) + coin3Col0AmpGen w0 ls2 ls3 3 • ket (bits4 1 1 0 0) + coin3Col0AmpGen w0
    ls2 ls3 4 • ket (bits4 0 0 1 0) + coin3Col0AmpGen w0 ls2 ls3 5 • ket (bits4 1 0 1 0) +
    coin3Col0AmpGen w0 ls2 ls3 6 • ket (bits4 0 1 1 0) + coin3Col0AmpGen w0 ls2 ls3 7 • ket
    (bits4 1 1 1 0) := by
  have hne10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  have hSplit : (pCoinPrepGen w0 ls2 ls3).toCircuit.eval.1 =
      (hstGateCircuit .H wCoin2 ;;ᶜ (pStage3Gen ls3).toCircuit).eval.1 *
      ((cStage2Gen ls2).eval.1 *
      (hstWordCircuit w0 wCoin0).eval.1) := by
    simp only [pCoinPrepGen, cStages1To2HGen, CleanPrepProg.toCircuit,
      Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hSplit]
  simp only [← Matrix.mulVec_mulVec]
  rw [hstWordCircuit_eval_eq_embedMatrix, singleton_embedMatrix_mulVec_ket]
  simp only [bits4_0, ↓reduceIte, upd_bits4_0]
  have hs0 := cStage2Gen_mulVec_ket ls2 false
  have hs1 := cStage2Gen_mulVec_ket ls2 true
  rw [zmodOfBool_false] at hs0
  rw [zmodOfBool_true] at hs1
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hs0, hs1]
  have hp00 := h_then_pStage3Gen_mulVec_ket ls3 false false
  have hp01 := h_then_pStage3Gen_mulVec_ket ls3 false true
  have hp10 := h_then_pStage3Gen_mulVec_ket ls3 true false
  have hp11 := h_then_pStage3Gen_mulVec_ket ls3 true true
  rw [zmodOfBool_false] at hp00
  rw [zmodOfBool_false, zmodOfBool_true] at hp01
  rw [zmodOfBool_true, zmodOfBool_false] at hp10
  rw [zmodOfBool_true] at hp11
  simp only [hp00, hp01, hp10, hp11]
  ext idx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coin3Col0AmpGen]
  ring
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cleanZeroEmbedIdx_coin4_eq_local (c : Fin 8) :
    cleanZeroEmbedIdx coinHwa c =
      (basisBitsEquiv 4).symm
        (bits4 (basisBits 3 c ⟨0, by decide⟩)
               (basisBits 3 c ⟨1, by decide⟩)
               (basisBits 3 c ⟨2, by decide⟩) 0) := by
  apply (basisBitsEquiv 4).injective
  funext q
  rw [(basisBitsEquiv 4).apply_symm_apply]
  have hAct := congrArg (basisBits 3) (cleanZeroEmbedIdx_extract_act coinHwa c)
  have hSub := congrArg (basisBits 1) (cleanZeroEmbedIdx_extract_subW coinHwa c)
  fin_cases q
  · have hq := congrFun hAct ⟨0, by decide⟩
    rw [QRegister.basisBits_extractIndex] at hq
    exact hq
  · have hq := congrFun hAct ⟨1, by decide⟩
    rw [QRegister.basisBits_extractIndex] at hq
    exact hq
  · have hq := congrFun hAct ⟨2, by decide⟩
    rw [QRegister.basisBits_extractIndex] at hq
    exact hq
  · have hq := congrFun hSub ⟨0, by decide⟩
    rw [QRegister.basisBits_extractIndex] at hq
    have hb0 : basisBits 1 0 ⟨0, by decide⟩ = 0 := by decide
    exact hq.trans hb0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cleanZeroEmbedIdx_coin4_zero_local :
    cleanZeroEmbedIdx coinHwa 0 = (basisBitsEquiv 4).symm (bits4 0 0 0 0) := by
  rw [cleanZeroEmbedIdx_coin4_eq_local 0]
  have h0 : basisBits 3 0 ⟨0, by decide⟩ = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
  have h1 : basisBits 3 0 ⟨1, by decide⟩ = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
  have h2 : basisBits 3 0 ⟨2, by decide⟩ = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
  rw [h0, h1, h2]
end ConfigCoin3PerHorizon5799
end Coin3PerHorizon5799
end
end ModCoin3PerHorizon5799
end Aux_Coin3PerHorizon5799
end
set_option exponentiation.threshold 256
end Aux_Coin3PerHorizon5799Aux

section Pos24Slot2FermionicBridge
local instance (priority := 1000000) instNeZeroTwoPow_Pos24Slot2FermionicBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Coherent 80-Wire `Slot 2 + V_ep` Fermionic Semantic Bridge (`Pos24Slot2FermionicBridge`)

Closes the ideal coherent `80`-wire `Slot 2` (`s0 = false`, electron-nuclear channel `U_en`) and
merged `218`-center `Slot 2 + V_ep` (`tierBB2Id`) semantic obligations directly on
`StoppingPower.fermionicProjector spinUp` with **zero bosonic `hPermSm2` hypothesis**:

1. `pos80IdealDist_nonneg`, `sum_abs_pos80IdealDist_eq_one`, `coherentSysOp80_slot2_norm_le_one`,
   `tierBB2RawId_norm_le_one`, `tierBB2RawId_comm_rProj24`, and `tierBB2Id_norm_le_one`.
2. Per-payload `s0 = false` slice factorization (`sysBlockAtPayloadGen_pos24ConjCore80_factor`,
   `offsetSysUnitary_eq_fwdPerm`, `sysBlockAtPayloadGen_uTwist_slot2_eq`) and global-phase
   cancellation via `NuclearTwistRealizes.slot2_shiftDiag_conj_eq_sysNucDiag48`.
3. Exact witness summation over `Pos80SupportIdx false`, BCH `GF(2^8)` Pauli-cap cancellation on
   `fermionicProjector spinUp`, and pure-electron `elecFermionicProjector` transport across `V_ep`.
4. Sharp `≤ 1 / 1000000` `48`-bit nuclear twist bound + `47088 / 2 ^ 30` `Q30` bound
   (`pos80EpsIntr2`), standalone `coherentSysOp80_slot2_agreesOnFermionicSector`,
   schedule-polymorphic `tierBB2Id_slot2wEff_agreesOnFermionicSector`, and `pos24Slot2LeafData`.
-/

public section

namespace Pos24Slot2FermionicBridge
open SpecsAux.SpecMirror
set_option maxRecDepth 4096

open Operator QProg Matrix Real
open SpecsAux.BridgeFermionicComm.SpecInner (permElectron)
open SpecsAux.DyadicSubgridToeplitz128
  (NyqFine3D128 NyqGrid3D64 NyqParity3D kHead128 kHead128_add_kTail128 kTail128
   nyq128Equiv3D oneElectronPhase shiftedFin64ToInt
   shiftedMom3D)
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open Dyadic128CoulombMath (canonTriple128 orbitParityWeight)
open Dyadic128CoulombMath (subGridWeight128_eq_orbit tetRank65)
open Dyadic128CoulombMath (tetUnrank65)
open Dyadic128OrbitTableCert
  (nyqParityToBool orbitMultNat subGridParityWeight3 w128DualQ30 w128OrbitQ30Real_shell_cert
    w128OrbitQ30Real_zero_eq)
open NuclearTwistAndXor654Concrete
  (nuclearM48_phase_diff_le oneElecNucDiag48 oneElecNucDiagExact oneElectronPhase48
   uenSubGridKet48)
open PosSlots24MergedVepBound (projSector_guard_diff_eq)
open PosSlots24SemanticBridge (fin56ToOrbit pos24CutNyq pos24CutQb
   pos24HeadCoords56_eq pos24HeadU56 pos24HeadV56 pos24HeadW56 pos24HeadWeight56
   pos24HeadWeight56_eq pos24IteNeg pos24ItePos
   pos24_kHead128_eq_zero_of_idx_ge_56 pos24_shell_cert
   subGridParityWeight3_nyqParityToBool subGridWeight128_eq_nyqParity)
open SingleAnchorFermionicPauliCap (nSub_sp nTot_sp op_sp rEl_sp)
open SixSlotEndpointJunctionBridge
  (commute_fermionicProjector_of_inGridPerm)
open Slot2SingleElecTwistBound (norm_unitary_conj_sub_le_gen)
open Slot2Slot4QuantizedChannelBridge (elecOffsetGridEquiv18
   norm_sum_op_sp_le_of_orthonormal
   uenSubGridKet uenSubGridRaw
   veeSubGridKet veeSubGridKet_complete veeSubGridKet_orthonormal)
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

section ConfigPos24Slot2FermionicBridge
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512
set_option exponentiation.threshold 256

theorem pos24Head_mult_pos (k : Fin 56) :
    0 < orbitMultNat (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) := by
  fin_cases k <;> decide

theorem pos24Head_weight_le_17_half_mult {k : Fin 56} (hk : k ≠ 0) : 2 * pos24HeadWeight56 k ≤
    18253611008 * orbitMultNat (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) := by
  fin_cases k
  · exact absurd rfl hk
  all_goals decide

theorem pos24CutNyq_le_three_div_two (b : NyqParity3D) : pos24CutNyq b ≤ (3 : ℝ) / 2 := by
  unfold pos24CutNyq
  set wt := subGridParityWeight3 (nyqParityToBool b)
  rcases wt with ⟨_ | _ | _ | _ | _, hwt⟩
  · norm_num [pos24CutQb]
  · norm_num [pos24CutQb]
  · norm_num [pos24CutQb]
  · norm_num [pos24CutQb]
  · omega

theorem pos24_kHead128_le_17_div_2_of_idx_ne_zero {d : NyqFine3D128}
    (hne : tetRank65 (canonTriple128 d) ≠ 0) :
    kHead128 w128DualQ30 pos24CutNyq d ≤ (17 : ℝ) / 2 := by
  by_cases hlt : (tetRank65 (canonTriple128 d)).val < 56
  · let k : Fin 56 := ⟨(tetRank65 (canonTriple128 d)).val, hlt⟩
    have hidx : fin56ToOrbit k = tetRank65 (canonTriple128 d) := Fin.ext rfl
    have hk_ne : k ≠ 0 := fun hk0 ↦ hne (by
      apply Fin.ext
      change k.val = 0
      exact congrArg Fin.val hk0)
    have hcanon : canonTriple128 d = tetUnrank65 (fin56ToOrbit k) := by
      rw [hidx]
      exact (tetRank65.symm_apply_apply (canonTriple128 d)).symm
    obtain ⟨hu, hv, hw⟩ := pos24HeadCoords56_eq k
    have hshell := (pos24_shell_cert d).2
    rw [← hidx, ← pos24HeadWeight56_eq k, hcanon, hu, hv, hw] at hshell
    set m := orbitMultNat (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k)
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (pos24Head_mult_pos k)
    have hnat : ((2 * pos24HeadWeight56 k : ℕ) : ℝ) ≤ ((18253611008 * m : ℕ) : ℝ) :=
      Nat.cast_le.mpr (pos24Head_weight_le_17_half_mult hk_ne)
    push_cast at hnat
    have h17 : (18253611008 : ℝ) = 17 * (2 ^ 30 : ℝ) := by norm_num
    rw [h17] at hnat
    have h2 : (2 : ℝ) * ((m : ℝ) * kHead128 w128DualQ30 pos24CutNyq d) ≤ 17 * (m : ℝ) := by
      have heq : (2 : ℝ) * ((m : ℝ) * kHead128 w128DualQ30 pos24CutNyq d) =
          (2 * (pos24HeadWeight56 k : ℝ)) / 2 ^ 30 := by
        rw [hshell]
        ring
      rw [heq]
      have hdiv : (2 * (pos24HeadWeight56 k : ℝ)) / 2 ^ 30 ≤ (17 * (2 ^ 30 : ℝ) * (m : ℝ)) / 2
          ^ 30 := div_le_div_of_nonneg_right hnat (by positivity)
      exact hdiv.trans_eq (by ring)
    nlinarith
  · have hge : 56 ≤ (tetRank65 (canonTriple128 d)).val := Nat.le_of_not_lt hlt
    rw [pos24_kHead128_eq_zero_of_idx_ge_56 d hge]
    norm_num

theorem nyq_idx_ne_zero_of_parity_ne_zero {b : NyqParity3D} (hb : b ≠ 0) (y : NyqGrid3D64) :
    tetRank65 (canonTriple128 (nyq128Equiv3D (y, b))) ≠ 0 := by
  intro h0
  set d := nyq128Equiv3D (y, b)
  have hw_eq : orbitParityWeight (tetRank65 (canonTriple128 d)) =
      subGridParityWeight3 (nyqParityToBool (nyq128Equiv3D.symm d).2) :=
    (subGridWeight128_eq_orbit d).symm.trans (subGridWeight128_eq_nyqParity d)
  rw [h0, Equiv.symm_apply_apply] at hw_eq
  have hw0 : (orbitParityWeight 0).val = 0 := by decide
  have hsum : (b 0).val + (b 1).val + (b 2).val = 0 := by
    rw [← subGridParityWeight3_nyqParityToBool b, ← congrArg Fin.val hw_eq, hw0]
  have hb0 : (b 0).val = 0 := by omega
  have hb1 : (b 1).val = 0 := by omega
  have hb2 : (b 2).val = 0 := by omega
  apply hb
  funext i
  fin_cases i
  · exact Fin.ext hb0
  · exact Fin.ext hb1
  · exact Fin.ext hb2

/-- Entrywise bound on `w128DualQ30 - 5`: `≤ 18` on `b = 0` (`idx = 0` included) and `≤ 6` on all
`7` nonzero Nyquist parities `b ≠ 0` (`∑_b cap_b = 18 + 7 * 6 = 60`). -/
theorem w128DualQ30_nyq_sub_five_abs_le (b : NyqParity3D) (y : NyqGrid3D64) :
    |w128DualQ30 (nyq128Equiv3D (y, b)) - 5| ≤ if b = 0 then (18 : ℝ) else 6 := by
  set d := nyq128Equiv3D (y, b)
  have hlo_raw := (w128OrbitQ30Real_shell_cert (tetRank65 (canonTriple128 d))).2.1
  have hlo : (-1 : ℝ) ≤ w128DualQ30 d := by
    unfold w128DualQ30
    linarith
  have hhi_ne : tetRank65 (canonTriple128 d) ≠ 0 → w128DualQ30 d ≤ 10 := fun hne ↦ by
    have hsum := kHead128_add_kTail128 w128DualQ30 pos24CutNyq d
    have hhead := pos24_kHead128_le_17_div_2_of_idx_ne_zero hne
    have htail : kTail128 w128DualQ30 pos24CutNyq d ≤ (3 : ℝ) / 2 := by
      unfold kTail128
      exact (min_le_right _ _).trans (pos24CutNyq_le_three_div_two _)
    linarith
  by_cases hb : b = 0
  · rw [pos24ItePos hb]
    by_cases h0 : tetRank65 (canonTriple128 d) = 0
    · have hhi0 : w128DualQ30 d ≤ 23 := by
        unfold w128DualQ30
        rw [h0, w128OrbitQ30Real_zero_eq]
        norm_num
      rw [abs_le]
      constructor <;> linarith
    · have hhi := hhi_ne h0
      rw [abs_le]
      constructor <;> linarith
  · rw [pos24IteNeg hb]
    have hhi := hhi_ne (nyq_idx_ne_zero_of_parity_ne_zero hb y)
    rw [abs_le]
    constructor <;> linarith

theorem norm_embed_oneElecNucDiag48_sub_exact_le (c : Configuration) (l : Fin 216)
    (e : Fin numElectrons) : ‖((rEl_sp e).embedUnitary (oneElecNucDiag48 c l)).1 -
    ((rEl_sp e).embedUnitary (oneElecNucDiagExact c l)).1‖ ≤ (302 : ℝ) / 2 ^ 48 := by
  have hdiag_e : ((rEl_sp e).embedUnitary (oneElecNucDiag48 c l)).1 -
      ((rEl_sp e).embedUnitary (oneElecNucDiagExact c l)).1 = Matrix.diagonal (fun x : Fin (2
      ^ systemQubits) ↦ oneElectronPhase48 c l (shiftedMom3D (elecOffsetGridEquiv18 ((rEl_sp
      e).extractIndex x))) - oneElectronPhase (c.nuclei l) (shiftedMom3D
      (elecOffsetGridEquiv18 ((rEl_sp e).extractIndex x)))) := by
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    dsimp only [oneElecNucDiag48, oneElecNucDiagExact]
    rw [QRegister.embedMatrix_diagonal, QRegister.embedMatrix_diagonal]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hdiag_e, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x ↦ ?_
  exact nuclearM48_phase_diff_le c l _ fun w ↦ by
    unfold shiftedMom3D shiftedFin64ToInt
    have := (elecOffsetGridEquiv18 ((rEl_sp e).extractIndex x) w).isLt
    rw [abs_le]
    constructor <;> omega

/-- Sharp single-electron `-5` constant-shift `48`-bit nuclear twist approximation bound:
`‖uenSubGridRaw48 c w128DualQ30 - uenSubGridRaw c w128DualQ30‖ ≤ 213308640 / 2 ^ 48 ≤ 1 / 1000000`.
-/
theorem norm_uenSubGridRaw48_sub_exact_le (c : Configuration) :
    ‖uenSubGridRaw48 c w128DualQ30 - uenSubGridRaw c w128DualQ30‖ ≤ (1 : ℝ) / 1000000 := by
  let V₁ : Fin 216 → Fin numElectrons → Unitary (2 ^ systemQubits) :=
    fun l e ↦ (rEl_sp e).embedUnitary (oneElecNucDiag48 c l)
  let V₂ : Fin 216 → Fin numElectrons → Unitary (2 ^ systemQubits) :=
    fun l e ↦ (rEl_sp e).embedUnitary (oneElecNucDiagExact c l)
  let M_sh : NyqParity3D → Fin numElectrons → Operator (2 ^ systemQubits) :=
    fun b e ↦ ∑ y : NyqGrid3D64,
      ((w128DualQ30 (nyq128Equiv3D (y, b)) - 5 : ℝ) : ℂ) • op_sp (veeSubGridKet b y) e
  have hconj : ∀ (U : Unitary (2 ^ 18)) (d k : Fin (2 ^ 18) → ℂ) (hU : U.1 = Matrix.diagonal d)
      (b : NyqParity3D) (y : NyqGrid3D64) (hk : (fun u ↦ d u * veeSubGridKet b y u) = k)
      (e : Fin numElectrons),
      ((rEl_sp e).embedUnitary U).1 * op_sp (veeSubGridKet b y) e *
        ((rEl_sp e).embedUnitary U).1ᴴ = op_sp k e := fun U d k hU b y hk e ↦ by
    dsimp only [op_sp]
    rw [QRegister.embedUnitary_val, ← (rEl_sp e).embedMatrix_conjTranspose,
      ← (rEl_sp e).embedMatrix_mul, ← (rEl_sp e).embedMatrix_mul, hU, diagonal_conj_rk1_sp, hk]
  have hblock_eq : ∀ (l : Fin 216) (b : NyqParity3D) (e : Fin numElectrons),
      (∑ y : NyqGrid3D64,
        (w128DualQ30 (nyq128Equiv3D (y, b)) : ℂ) • op_sp (uenSubGridKet48 c l b y) e) -
      (∑ y : NyqGrid3D64,
        (w128DualQ30 (nyq128Equiv3D (y, b)) : ℂ) • op_sp (uenSubGridKet c l b y) e) =
      (V₁ l e).1 * M_sh b e * (V₁ l e).1ᴴ - (V₂ l e).1 * M_sh b e * (V₂ l e).1ᴴ := by
    intro l b e
    have hsplit : ∀ U : Unitary (2 ^ systemQubits), U.1 * M_sh b e * U.1ᴴ =
        (∑ y : NyqGrid3D64,
          (w128DualQ30 (nyq128Equiv3D (y, b)) : ℂ) • (U.1 * op_sp (veeSubGridKet b y) e * U.1ᴴ)) -
        (5 : ℂ) • (1 : Operator (2 ^ systemQubits)) := fun U ↦ by
      dsimp only [M_sh]
      simp_rw [Complex.ofReal_sub, Complex.ofReal_ofNat, sub_smul, Finset.sum_sub_distrib,
        ← Finset.smul_sum, sum_op_sp_veeSubGridKet_eq_one b e]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        show U.1 * U.1ᴴ = 1 from U.2.2, Matrix.mul_sum, Finset.sum_mul]
      refine congrArg (· - (5 : ℂ) • (1 : Operator (2 ^ systemQubits)))
        (Finset.sum_congr rfl fun y _ ↦ by rw [Matrix.mul_smul, Matrix.smul_mul])
    have hc1 := fun y ↦ hconj (oneElecNucDiag48 c l)
      (fun u ↦ oneElectronPhase48 c l (shiftedMom3D (elecOffsetGridEquiv18 u)))
      (uenSubGridKet48 c l b y) rfl b y rfl e
    have hc2 := fun y ↦ hconj (oneElecNucDiagExact c l)
      (fun u ↦ oneElectronPhase (c.nuclei l) (shiftedMom3D (elecOffsetGridEquiv18 u)))
      (uenSubGridKet c l b y) rfl b y rfl e
    rw [hsplit (V₁ l e), hsplit (V₂ l e)]
    dsimp only [V₁, V₂]
    simp_rw [hc1, hc2]
    abel
  have hdiff : uenSubGridRaw48 c w128DualQ30 - uenSubGridRaw c w128DualQ30 =
      (-((1 / 8 : ℝ) : ℂ)) • ∑ l : Fin 216, ∑ b : NyqParity3D, ∑ e : Fin numElectrons,
        ((V₁ l e).1 * M_sh b e * (V₁ l e).1ᴴ - (V₂ l e).1 * M_sh b e * (V₂ l e).1ᴴ) := by
    unfold uenSubGridRaw48 uenSubGridRaw nTot_sp nSub_sp
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun l _ ↦ ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [sum_smul_sum_sub_comm (fun y : NyqGrid3D64 ↦ (w128DualQ30 (nyq128Equiv3D (y, b)) : ℂ))
      (fun y e ↦ op_sp (uenSubGridKet48 c l b y) e) (fun y e ↦ op_sp (uenSubGridKet c l b y) e)]
    exact Finset.sum_congr rfl fun e _ ↦ hblock_eq l b e
  have hper_lbe : ∀ (l : Fin 216) (b : NyqParity3D) (e : Fin numElectrons),
      ‖(V₁ l e).1 * M_sh b e * (V₁ l e).1ᴴ - (V₂ l e).1 * M_sh b e * (V₂ l e).1ᴴ‖ ≤
        2 * (if b = 0 then (18 : ℝ) else 6) * ((302 : ℝ) / 2 ^ 48) := fun l b e ↦ by
    have h1 := norm_unitary_conj_sub_le_gen (V₁ l e) (V₂ l e) (M_sh b e)
    have hM := norm_sum_op_sp_le_of_orthonormal elecOffsetGridEquiv18 (veeSubGridKet b)
      (veeSubGridKet_orthonormal b) (veeSubGridKet_complete b) e
      (fun y ↦ w128DualQ30 (nyq128Equiv3D (y, b)) - 5) (by split_ifs <;> positivity)
      (w128DualQ30_nyq_sub_five_abs_le b)
    have hprod := mul_le_mul hM (norm_embed_oneElecNucDiag48_sub_exact_le c l e) (norm_nonneg _)
      (by split_ifs <;> positivity)
    linarith
  have hsum_b : (∑ b : NyqParity3D, (if b = 0 then (18 : ℝ) else 6)) = 60 := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun b : NyqParity3D ↦ if b = 0 then (18 : ℝ) else 6) (Finset.mem_univ 0),
      ite_eq_left rfl, Finset.sum_congr rfl fun b hb ↦ pos24IteNeg (Finset.mem_erase.mp hb).1 18 6,
      Finset.sum_const, show (Finset.univ.erase (0 : NyqParity3D)).card = 7 by decide,
      nsmul_eq_mul]
    norm_num
  rw [hdiff, norm_smul, show ‖(-((1 / 8 : ℝ) : ℂ))‖ = (1 / 8 : ℝ) by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]]
  have htot : ‖∑ l : Fin 216, ∑ b : NyqParity3D, ∑ e : Fin numElectrons,
      ((V₁ l e).1 * M_sh b e * (V₁ l e).1ᴴ - (V₂ l e).1 * M_sh b e * (V₂ l e).1ᴴ)‖ ≤
      (216 : ℝ) * (60 * (218 * (2 * ((302 : ℝ) / 2 ^ 48)))) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun l _ ↦
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ ↦
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ ↦ hper_lbe l b e))).trans_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numElectrons, nsmul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum, hsum_b]
    ring
  linarith

/-! ## Section 5: Standalone `Slot 2` & Merged `Slot 2 + V_ep` Fermionic Sector Closures
  (`Pos24Slot2LeafData`) -/

/-- Guarded `AgreesOnFermionicSector` certificate for the symmetric `48`-bit proxy `B_mod`. -/
theorem agreesOnFermionicSector_gridSandwich_slot2Mod
    (B_mod : Configuration → Operator (2 ^ systemQubits))
    (e2Const : ℝ) {eps2 : ℝ}
    (hPermMod : ∀ (c : Configuration) (g : Equiv.Perm (Fin numElectrons))
        (a b : Fin (2 ^ systemQubits)),
      IsGridState a → IsGridState b →
        B_mod c (permElectron g a) (permElectron g b) = B_mod c a b)
    (hErrMod : ∀ (c : Configuration) (spinUp0 : Finset (Fin numElectrons)),
      let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then e2Const else 0
      ‖fermionicProjector spinUp0 * (B_mod c - sixChannelShifted c E2only 2) *
        fermionicProjector spinUp0‖ ≤ eps2)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (E : Fin 6 → ℝ) (hE2 : E 2 = e2Const) :
    AgreesOnFermionicSector spinUp
      (SpecsAux.gridProjector * B_mod cfg *
        SpecsAux.gridProjector)
      (sixChannelShifted cfg E 2)
      eps2 := by
  refine ⟨commute_fermionicProjector_of_inGridPerm (B_mod cfg) (hPermMod cfg) spinUp, ?_⟩
  rw [projSector_guard_diff_eq (fermionicProjector spinUp)
    SpecsAux.gridProjector (B_mod cfg) (sixChannelShifted cfg E 2)
    ⟨SpecsAux.fermionicProjector_mul_gridProjector spinUp,
      SpecsAux.gridProjector_mul_fermionicProjector spinUp⟩]
  have hEq2 : sixChannelShifted cfg E 2 =
      sixChannelShifted cfg (fun q : Fin 6 ↦ if q = 2 then e2Const else 0) 2 := by
    unfold sixChannelShifted
    rw [hE2]
    rfl
  rw [hEq2]
  exact hErrMod cfg spinUp

end ConfigPos24Slot2FermionicBridge

end Pos24Slot2FermionicBridge
end
set_option exponentiation.threshold 256
end Pos24Slot2FermionicBridge

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
