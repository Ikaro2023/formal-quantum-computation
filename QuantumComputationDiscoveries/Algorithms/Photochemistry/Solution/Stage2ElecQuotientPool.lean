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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.UpperSelectAlwaysLoW338

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

/-!
# `q2`-Aligned 2-Batch Phase-1 `cHi` Gadget (`Stage2ElecQuotientPool`)

Provides clean, `wPool`-parameterized Phase-1 electronic `cHi` circuits disjoint from `rHA`
(`buf96[48..71]`) and `wBufStash4` (`buf96[92..95]`):
- `pCHi2Batch338` (`S = 44`, `45` clean scratch wires incl. `rCtrlLo[0]`, `338 T`, `0 .TOFF`),
  covering `K = 214` (`wWork = 314`).
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecQuotient
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
open Operator QProg Matrix Circuit Qubit HermitianMat
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.Stage2QromMux
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.WStateRouterPrim
  PhotochemistrySolution.HalfBellCollapse
open PhotochemistrySolution.Stage2ElecOptA
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ProviderCore (cw_1 cw_cnot)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_of_circuit subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (CircWires)
local instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩

/-! ### 1. Wire Pool Layout (`51 + S` Wires) & Disjointness -/

/-- `24` quotient wires `wPool[0..23]` holding the 1-hot `idxHi5_2` indicator (`rRawHas2`). -/
abbrev poolB {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (b : Fin 24) : Wire n :=
  wPool ⟨b.val, by
      have := b.isLt
      omega⟩

/-- `24` Round-0 odd-leaf scratch wires `wPool[24..47]`. -/
abbrev poolOdd0 {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (b : Fin 24) : Wire n :=
  wPool ⟨24 + b.val, by
      have := b.isLt
      omega⟩

/-- `S + 1` clean scratch wires for Round-1 cohorts (`wPool[48..]` ++ `rCtrlLo[0]`). -/
def poolClean {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (k : Fin (S + 1)) : Wire n :=
  if hk : k.val < S then wPool ⟨48 + k.val, by omega⟩ else rCtrlLo r ⟨0, by decide⟩

/-- Dummy root wire `wPool[48 + S]`. -/
abbrev poolRDum {S n : ℕ} (wPool : Fin (51 + S) → Wire n) : Wire n :=
  wPool ⟨48 + S, by omega⟩

/-- Dummy leaf wire `wPool[49 + S]`. -/
abbrev poolWDum {S n : ℕ} (wPool : Fin (51 + S) → Wire n) : Wire n :=
  wPool ⟨49 + S, by omega⟩

/-- Phase-encoding ancilla wire `wPool[50 + S]`. -/
abbrev poolQEnc {S n : ℕ} (wPool : Fin (51 + S) → Wire n) : Wire n :=
  wPool ⟨50 + S, by omega⟩

/-- Minimal 3-field disjointness contract on `wPool : Fin (51 + S) → Wire n`. -/
structure CHiPoolDisj {S n : ℕ} (r : RouterReg 187 8 n) (wPool : Fin (51 + S) → Wire n) : Prop where
  inj : Function.Injective wPool
  ne_pub18 : ∀ (i : Fin (51 + S)) (u : Fin (routerWidth 187 8)), u.val < 18 → wPool i ≠ r u
  ne_ctrlLo : ∀ (i : Fin (51 + S)) (p : Fin 187), wPool i ≠ rCtrlLo r p

theorem cohW5_pub18_ne_ctrlLo {n : ℕ} (r : RouterReg 187 8 n)
    {u : Fin (routerWidth 187 8)} (hu : u.val < 18) (p : Fin 187) :
    r u ≠ rCtrlLo r p := by
  have := p.isLt
  exact rr_ne r (by
    dsimp [rCtrlLo]
    rw [bp187_eq]
    omega)

theorem cohW5_apply_ite {α β : Type*} (f : α → β) (c : Prop) [Decidable c] (x y : α) :
    (if c then f x else f y) = f (if c then x else y) := by
  split_ifs <;> rfl

/-- Convenience constructor for `CHiPoolDisj` when `wPool i = r (idxFn i)`. -/
theorem chiPoolDisj_of_idx {S n : ℕ} (r : RouterReg 187 8 n)
    (idxFn : Fin (51 + S) → Fin (routerWidth 187 8))
    (hInj : ∀ i j, (idxFn i).val = (idxFn j).val → i = j)
    (hSafe : ∀ i, (18 ≤ (idxFn i).val ∧ (idxFn i).val < 4624) ∨ 4811 ≤ (idxFn i).val) :
    CHiPoolDisj r (fun i ↦ r (idxFn i)) where
  inj i j heq := hInj i j (congrArg Fin.val (r.wires.injective heq))
  ne_pub18 i u hu := by
    have := hSafe i
    exact rr_ne r (by omega)
  ne_ctrlLo i p := by
    have := hSafe i
    have := p.isLt
    exact rr_ne r (by
        dsimp [rCtrlLo]
        rw [bp187_eq]
        omega)

theorem wPool_ne {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) {i j : Fin (51 + S)} (h : i.val ≠ j.val) :
    wPool i ≠ wPool j := fun e ↦ h (congrArg Fin.val (hP.inj e))

theorem wPool_ne_rRawHas2 {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (i : Fin (51 + S)) : wPool i ≠ rRawHas2 r :=
  rRawHas2_eq_r1 r ▸ hP.ne_pub18 i ⟨1, rw187_lt_1⟩ (by decide)

theorem wPool_ne_idxLo3_2 {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (i : Fin (51 + S)) (d : Fin 3) : wPool i ≠ idxLo3_2 r d :=
  hP.ne_pub18 i _ (by
    have := d.isLt
    dsimp [idxLo3_2, rIdx2]
    omega)

theorem wPool_ne_idxHi5_2 {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (i : Fin (51 + S)) (d : Fin 5) : wPool i ≠ idxHi5_2 r d :=
  hP.ne_pub18 i _ (by
    have := d.isLt
    dsimp [idxHi5_2, rIdx2]
    omega)

theorem poolClean_inj {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) : Function.Injective (poolClean wPool r) := by
  intro k₁ k₂ heq
  have hk₁ := k₁.isLt
  have hk₂ := k₂.isLt
  dsimp only [poolClean] at heq
  split_ifs at heq
  · have hv := congrArg Fin.val (hP.inj heq)
    dsimp at hv
    exact Fin.ext (by omega)
  · exact absurd heq (hP.ne_ctrlLo _ _)
  · exact absurd heq.symm (hP.ne_ctrlLo _ _)
  · exact Fin.ext (by omega)

theorem poolClean_ne_wPool_ge {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (k : Fin (S + 1)) (i : Fin (51 + S)) (hi : 48 + S ≤ i.val) :
    poolClean wPool r k ≠ wPool i := by
  dsimp only [poolClean]
  split_ifs with hk
  · exact wPool_ne hP (by omega : 48 + k.val ≠ i.val)
  · exact (hP.ne_ctrlLo i _).symm

theorem poolClean_ne_ctrlLo_nz {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (k : Fin (S + 1)) (p : Fin 187) (hp : p.val ≠ 0) :
    poolClean wPool r k ≠ rCtrlLo r p := by
  dsimp only [poolClean]
  split_ifs with hk
  · exact hP.ne_ctrlLo _ p
  · exact rCtrlLo_inj_ne r ⟨0, by decide⟩ p (fun e ↦ hp (congrArg Fin.val e).symm)

theorem poolClean_ne_pub18 {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (k : Fin (S + 1)) (u : Fin (routerWidth 187 8)) (hu : u.val < 18) :
    poolClean wPool r k ≠ r u := by
  dsimp only [poolClean]
  split_ifs with hk
  · exact hP.ne_pub18 _ u hu
  · exact (cohW5_pub18_ne_ctrlLo r hu _).symm

/-! ### 2. Input Predicates & Intermediate State Maps -/

/-- Pre-`pCHi` input support predicate on `R_mid` (before `(uXorPubLo r).1 * R_mid`). -/
def ValidCHiPoolIn {S n : ℕ} (r : RouterReg 187 8 n) (wPool : Fin (51 + S) → Wire n)
    (α : BitAssignment n) : Prop :=
  idxValD (rIdx1 r) α < 187 ∧
  (α (rHas1 r) = 0 → idxValD (rIdx1 r) α = 0) ∧
  idxValD (rIdx2 r) α < 187 ∧
  (α (rRawHas2 r) = 0 → idxValD (rIdx2 r) α = 0) ∧
  (α (rRawHas2 r) = 1 → idxValD (rIdx2 r) α ≠ 0) ∧
  (∀ p : Fin 187, α (rCtrlLo r p) = 0) ∧
  (∀ b : Fin 24, α (poolB wPool b) = if idxValD (idxHi5_2 r) α = b.val then α (rRawHas2 r) else 0) ∧
  (∀ k : Fin (27 + S), α (wPool ⟨24 + k.val, by
      have := k.isLt
      omega⟩) = 0)

/-- Internal post-`cScrubCtrlLo0` support predicate (`rCtrlLo[0] = 0`). -/
def ValidCHiPoolCtrl0 {S n : ℕ} (r : RouterReg 187 8 n) (wPool : Fin (51 + S) → Wire n)
    (γ : BitAssignment n) : Prop :=
  idxValD (rIdx2 r) γ < 187 ∧
  (γ (rRawHas2 r) = 0 → idxValD (rIdx2 r) γ = 0) ∧
  (γ (rRawHas2 r) = 1 → idxValD (rIdx2 r) γ ≠ 0) ∧
  (∀ b : Fin 24, γ (poolB wPool b) = if idxValD (idxHi5_2 r) γ = b.val then γ (rRawHas2 r) else 0) ∧
  (∀ k : Fin (27 + S), γ (wPool ⟨24 + k.val, by
      have := k.isLt
      omega⟩) = 0) ∧
  γ (rCtrlLo r ⟨0, by decide⟩) = 0

theorem cohW5_pub18_congr {n : ℕ} (r : RouterReg 187 8 n) {α β : BitAssignment n}
    (h : ∀ u : Fin (routerWidth 187 8), u.val < 18 → α (r u) = β (r u)) :
    α (rHas1 r) = β (rHas1 r) ∧
    α (rRawHas2 r) = β (rRawHas2 r) ∧
    idxValD (rIdx1 r) α = idxValD (rIdx1 r) β ∧
    idxValD (rIdx2 r) α = idxValD (rIdx2 r) β ∧
    idxValD (idxHi5_2 r) α = idxValD (idxHi5_2 r) β ∧
    idxValPrefix (uBit0_2 r) α 1 le_rfl = idxValPrefix (uBit0_2 r) β 1 le_rfl ∧
    idxValPrefix (uBit1_2 r) α 1 le_rfl = idxValPrefix (uBit1_2 r) β 1 le_rfl ∧
    idxValPrefix (uBit2_2 r) α 1 le_rfl = idxValPrefix (uBit2_2 r) β 1 le_rfl ∧
    tStar95 r α = tStar95 r β := by
  have h1 (d : Fin 8) : α (rIdx1 r d) = β (rIdx1 r d) := h _ (by
    have := d.isLt
    dsimp [rIdx1]
    omega)
  have h2 (d : Fin 8) : α (rIdx2 r d) = β (rIdx2 r d) := h _ (by
    have := d.isLt
    dsimp [rIdx2]
    omega)
  have hHi : idxValD (idxHi5_2 r) α = idxValD (idxHi5_2 r) β :=
    idxValPrefix_congr (idxHi5_2 r) α β (fun _ ↦ h2 _) 5 le_rfl
  refine ⟨h ⟨0, rw_lt0 187 8⟩ (by decide), rRawHas2_eq_r1 r ▸ h ⟨1, rw187_lt_1⟩ (by decide),
    idxValPrefix_congr _ _ _ h1 8 le_rfl, idxValPrefix_congr _ _ _ h2 8 le_rfl, hHi,
    idxValPrefix_congr _ _ _ (fun _ ↦ h2 _) 1 le_rfl,
    idxValPrefix_congr _ _ _ (fun _ ↦ h2 _) 1 le_rfl,
    idxValPrefix_congr _ _ _ (fun _ ↦ h2 _) 1 le_rfl, Fin.ext ?_⟩
  dsimp only [tStar95]
  rw [hHi, idxValPrefix_congr (uLo2_2 r) α β (fun _ ↦ h2 _) 2 le_rfl]

theorem validPoolCtrl0_vecToggle {S n : ℕ} (r : RouterReg 187 8 n)
    (wPool : Fin (51 + S) → Wire n) (hP : CHiPoolDisj r wPool)
    (f : BitAssignment n → Fin 187 → ZMod 2)
    (hf0 : ∀ γ, ValidCHiPoolCtrl0 r wPool γ → f γ ⟨0, by decide⟩ = 0)
    {γ : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) :
    ValidCHiPoolCtrl0 r wPool (vecToggleBits (rCtrlLo r) f γ) := by
  have hOth (u : Wire n) (hu : ∀ p : Fin 187, u ≠ rCtrlLo r p) :
      vecToggleBits (rCtrlLo r) f γ u = γ u :=
    (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f γ).2 u hu
  obtain ⟨_, hHas2, _, hIdx2, hHi2, _, _, _, _⟩ :=
    cohW5_pub18_congr r fun u hu ↦ hOth _ (cohW5_pub18_ne_ctrlLo r hu)
  refine ⟨hIdx2 ▸ hγ.1, fun h0 ↦ hIdx2.trans (hγ.2.1 (hHas2.symm.trans h0)),
    fun h1 ↦ hIdx2 ▸ hγ.2.2.1 (hHas2.symm.trans h1),
    fun b ↦ by rw [hOth _ (hP.ne_ctrlLo _), hHi2, hHas2, hγ.2.2.2.1 b],
    fun k ↦ (hOth _ (hP.ne_ctrlLo _)).trans (hγ.2.2.2.2.1 k),
    by rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f γ).1 ⟨0, by decide⟩,
         hγ.2.2.2.2.2, hf0 γ hγ, add_zero]⟩

theorem supportedOn_validPoolCtrl0_uVecToggle {S n : ℕ} (r : RouterReg 187 8 n)
    (wPool : Fin (51 + S) → Wire n) (hP : CHiPoolDisj r wPool)
    (f : BitAssignment n → Fin 187 → ZMod 2)
    (hfIndep : ∀ α β, (∀ w, (∀ p : Fin 187, w ≠ rCtrlLo r p) → α w = β w) → f α = f β)
    (hf0 : ∀ γ, ValidCHiPoolCtrl0 r wPool γ → f γ ⟨0, by decide⟩ = 0)
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    SupportedOn (ValidCHiPoolCtrl0 r wPool)
      ((uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r) f hfIndep).1 * G) :=
  supportedOn_ketMap (uVecToggle_mulVec_ket (rCtrlLo r) (rCtrlLo_inj_ne r) f hfIndep)
    (fun _ hγ ↦ validPoolCtrl0_vecToggle r wPool hP f hf0 hγ) hG

/-- Clear `poolB[q2]` on `γ` (leaving all `wPool` wires at `0`). -/
def cleanPoolB {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (γ : BitAssignment n) : BitAssignment n :=
  Function.update γ (poolB wPool ⟨min (idxValD (idxHi5_2 r) γ) 23, by omega⟩) 0

/-- Round-0 `24 × 2` wire map `(b, 0) ↦ poolB[b]`, `(b, 1) ↦ poolOdd0[b]`. -/
def wR0Pool {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (b : Fin 24) (p : Fin (2 ^ 1)) : Wire n :=
  if p.val = 0 then poolB wPool b else poolOdd0 wPool b

/-- Round-1 `47` root wires `m < 47`: even `m ↦ poolB[m/2]`, odd `m ↦ poolOdd0[m/2]`. -/
def r1RootPool {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (m : Fin 47) : Wire n :=
  if m.val % 2 = 0 then poolB wPool ⟨m.val / 2, by
      have := m.isLt
      omega⟩
  else poolOdd0 wPool ⟨m.val / 2, by
      have := m.isLt
      omega⟩

/-- Post-Round-0 ket map (`wR0Pool[q2][u0] = rRawHas2`, all `0` when `rRawHas2 = 0`). -/
def r0Map {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (γ : BitAssignment n) : BitAssignment n :=
  Function.update (cleanPoolB wPool r γ)
    (wR0Pool wPool ⟨min (idxValD (idxHi5_2 r) γ) 23, by omega⟩
      ⟨idxValPrefix (uBit0_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩)
    (γ (rRawHas2 r))

/-- Linear operator `mkVecOp (ket ∘ r0Map) * X`. -/
def opR0 {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (X : Operator (2 ^ n)) : Operator (2 ^ n) :=
  mkVecOp (fun γ ↦ ket (r0Map wPool r γ)) * X

/-- Round-1 batch `M × 2` pair map for `[mOff, mOff + M)` (`M ≤ S`). -/
def pairsCohR1 {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (k : Fin M) (p : Fin (2 ^ 1)) : Wire n :=
  if p.val = 0 then r1RootPool wPool ⟨mOff + k.val, by
      have := k.isLt
      omega⟩
  else wPool ⟨48 + k.val, by
      have := k.isLt
      omega⟩

/-- Round-0 combined index `2 * q2 + u0`. -/
def mValCoh {n : ℕ} (r : RouterReg 187 8 n) (γ : BitAssignment n) : ℕ :=
  2 * idxValD (idxHi5_2 r) γ + idxValPrefix (uBit0_2 r) γ 1 le_rfl

/-- Active predicate for Round-1 batch `[mOff, mOff + M)`. -/
def actCohPred {n : ℕ} (mOff M : ℕ) (r : RouterReg 187 8 n) (γ : BitAssignment n) : Prop :=
  γ (rRawHas2 r) = 1 ∧ mOff ≤ mValCoh r γ ∧ mValCoh r γ < mOff + M

instance {n : ℕ} (mOff M : ℕ) (r : RouterReg 187 8 n) : DecidablePred (actCohPred mOff M r) :=
  fun γ ↦ by
      unfold actCohPred
      infer_instance

/-- Post-Round-1 batch ket map (with `rDum = 0` scrubbed on all basis kets). -/
def cohMap {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (γ : BitAssignment n) : BitAssignment n :=
  if h : actCohPred mOff M r γ then
    Function.update (cleanPoolB wPool r γ)
      (pairsCohR1 mOff M hm hMS wPool ⟨mValCoh r γ - mOff, by
          have := h.2
          omega⟩
        ⟨idxValPrefix (uBit1_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩) 1
  else r0Map wPool r γ

/-- Linear operator `mkVecOp (ket ∘ cohMap) * X`. -/
def opCoh {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (X : Operator (2 ^ n)) : Operator (2 ^ n) :=
  mkVecOp (fun γ ↦ ket (cohMap mOff M hm hMS wPool r γ)) * X

/-- Batch node wire for `t : Fin 95` whose `m = 2*(t/4) + t%2` lies in `[mOff, mOff + M)`. -/
def wCohNode {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (t : Fin 95)
    (ht : mOff ≤ 2 * (t.val / 4) + t.val % 2 ∧ 2 * (t.val / 4) + t.val % 2 < mOff + M) : Wire n :=
  pairsCohR1 mOff M hm hMS wPool ⟨2 * (t.val / 4) + t.val % 2 - mOff, by omega⟩
    ⟨(t.val % 4) / 2, by omega⟩

/-! ### 3. Pool Index & Ket-Map Lemmas -/

theorem pairsCohR1_idx {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (k : Fin M) (p : Fin (2 ^ 1)) :
    ∃ idx : Fin (51 + S), idx.val < 48 + M ∧ pairsCohR1 mOff M hm hMS wPool k p = wPool idx := by
  have hk := k.isLt
  dsimp only [pairsCohR1, r1RootPool]
  split_ifs
  · exact ⟨⟨(mOff + k.val) / 2, by omega⟩, (by omega : (mOff + k.val) / 2 < 48 + M), rfl⟩
  · exact ⟨⟨24 + (mOff + k.val) / 2, by omega⟩, (by omega : 24 + (mOff + k.val) / 2 < 48 + M), rfl⟩
  · exact ⟨⟨48 + k.val, by omega⟩, (by omega : 48 + k.val < 48 + M), rfl⟩

theorem wInj_wR0Pool {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) : WInj (wR0Pool wPool) := by
  intro b₁ p₁ b₂ p₂ heq
  have hp₁ := p₁.isLt
  have hp₂ := p₂.isLt
  have hb₁ := b₁.isLt
  have hb₂ := b₂.isLt
  dsimp only [wR0Pool, poolB, poolOdd0] at heq
  simp only [cohW5_apply_ite wPool] at heq
  have hv := congrArg Fin.val (hP.inj heq)
  simp only [← cohW5_apply_ite (@Fin.val (51 + S))] at hv
  dsimp at hv
  exact ⟨Fin.ext (by split_ifs at hv <;> omega), Fin.ext (by split_ifs at hv <;> omega)⟩

theorem wInj_pairsCohR1 {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) :
    WInj (pairsCohR1 mOff M hm hMS wPool) := by
  intro k₁ p₁ k₂ p₂ heq
  have hp₁ := p₁.isLt
  have hp₂ := p₂.isLt
  have hk₁ := k₁.isLt
  have hk₂ := k₂.isLt
  dsimp only [pairsCohR1, r1RootPool, poolB, poolOdd0] at heq
  simp only [cohW5_apply_ite wPool] at heq
  have hv := congrArg Fin.val (hP.inj heq)
  simp only [← cohW5_apply_ite (@Fin.val (51 + S))] at hv
  dsimp at hv
  exact ⟨Fin.ext (by split_ifs at hv <;> omega), Fin.ext (by split_ifs at hv <;> omega)⟩

theorem cohW5_mk_wOptInj {S n R : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (uLo : Fin 1 → Wire n)
    (huLo : ∀ i : Fin (51 + S), ∀ d : Fin 1, wPool i ≠ uLo d)
    (w : Fin R → Fin (2 ^ 1) → Wire n) (hwInj : WInj w)
    (huW : ∀ d k p, uLo d ≠ w k p)
    (hwGe : ∀ (i : Fin (51 + S)), 48 + S ≤ i.val → ∀ k p, w k p ≠ wPool i) :
    WOptInj R 1 uLo w (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) :=
  ⟨hwInj, huW, fun d ↦ (huLo _ d).symm, fun d ↦ (huLo _ d).symm, fun d ↦ (huLo _ d).symm,
    hwGe _ le_rfl, hwGe _ (by omega : 48 + S ≤ 49 + S), hwGe _ (by omega : 48 + S ≤ 50 + S),
    wPool_ne hP (by omega : 48 + S ≠ 49 + S), wPool_ne hP (by omega : 48 + S ≠ 50 + S),
    wPool_ne hP (by omega : 49 + S ≠ 50 + S)⟩

theorem wOptInj_pairsCohR1 {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) :
    WOptInj M 1 (uBit1_2 r) (pairsCohR1 mOff M hm hMS wPool)
      (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) :=
  cohW5_mk_wOptInj hP (uBit1_2 r) (fun i _ ↦ wPool_ne_idxLo3_2 hP i _)
    (pairsCohR1 mOff M hm hMS wPool) (wInj_pairsCohR1 hP mOff M hm hMS)
    (fun _ k p ↦ by
      obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool k p
      exact hEq ▸ (wPool_ne_idxLo3_2 hP idx _).symm)
    (fun _ hi k p ↦ by
      obtain ⟨idx, hlt, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool k p
      exact hEq ▸ wPool_ne hP (by omega))

theorem wCohNode_inj {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    {t₁ t₂ : Fin 95}
    {ht₁ : mOff ≤ 2 * (t₁.val / 4) + t₁.val % 2 ∧ 2 * (t₁.val / 4) + t₁.val % 2 < mOff + M}
    {ht₂ : mOff ≤ 2 * (t₂.val / 4) + t₂.val % 2 ∧ 2 * (t₂.val / 4) + t₂.val % 2 < mOff + M}
    (heq : wCohNode mOff M hm hMS wPool t₁ ht₁ = wCohNode mOff M hm hMS wPool t₂ ht₂) :
    t₁ = t₂ := by
  obtain ⟨hk, hp⟩ := wInj_pairsCohR1 hP mOff M hm hMS _ _ _ _ heq
  have hkv := congrArg Fin.val hk
  have hpv := congrArg Fin.val hp
  exact Fin.ext (by
      dsimp at hkv hpv
      omega)

theorem cohW5_wCohNode_idx {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (t : Fin 95)
    (ht : mOff ≤ 2 * (t.val / 4) + t.val % 2 ∧ 2 * (t.val / 4) + t.val % 2 < mOff + M) :
    ∃ idx : Fin (51 + S), idx.val < 48 + M ∧ wCohNode mOff M hm hMS wPool t ht = wPool idx :=
  pairsCohR1_idx mOff M hm hMS wPool ⟨2 * (t.val / 4) + t.val % 2 - mOff, by omega⟩
    ⟨(t.val % 4) / 2, by omega⟩

theorem wCohNode_ne_poolClean_ge {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) (t : Fin 95)
    (ht : mOff ≤ 2 * (t.val / 4) + t.val % 2 ∧ 2 * (t.val / 4) + t.val % 2 < mOff + M)
    (k : Fin (S + 1)) (hk : M ≤ k.val) :
    wCohNode mOff M hm hMS wPool t ht ≠ poolClean wPool r k := by
  obtain ⟨idx, hlt, hEq⟩ := cohW5_wCohNode_idx mOff M hm hMS wPool t ht
  rw [hEq]
  dsimp only [poolClean]
  split_ifs with hkS
  · exact wPool_ne hP (by omega : idx.val ≠ 48 + k.val)
  · exact hP.ne_ctrlLo idx _

theorem cleanPoolB_wPool_zero {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    {γ : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) (i : Fin (51 + S)) :
    cleanPoolB wPool r γ (wPool i) = 0 := by
  have hq24 := idxHi5_2_lt24_of_lt187 r hγ.1
  have hiLt := i.isLt
  dsimp only [cleanPoolB, poolB]
  by_cases hEq : i.val = min (idxValD (idxHi5_2 r) γ) 23
  · exact (Fin.ext hEq : i = ⟨min (idxValD (idxHi5_2 r) γ) 23, by omega⟩) ▸
      Function.update_self _ 0 γ
  · rw [Function.update_of_ne (wPool_ne hP (hEq : i.val ≠ min (idxValD (idxHi5_2 r) γ) 23))]
    by_cases hi24 : i.val < 24
    · exact (hγ.2.2.2.1 ⟨i.val, hi24⟩).trans (ite_eq_right (by
        dsimp
        omega))
    · exact (congrArg (fun idx ↦ γ (wPool idx))
        (Fin.ext (by omega : i.val = 24 + (i.val - 24)))).trans
          (hγ.2.2.2.2.1 ⟨i.val - 24, by omega⟩)

theorem cleanPoolB_eq_of_has2_zero {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (h0 : γ (rRawHas2 r) = 0) :
    cleanPoolB wPool r γ = γ :=
  update_eq_self_of_zero (by rw [hγ.2.2.2.1 _, h0, ite_self])

theorem r0Map_eq_of_has2_zero {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool) {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (h0 : γ (rRawHas2 r) = 0) :
    r0Map wPool r γ = γ := by
  dsimp only [r0Map]
  have hcl := cleanPoolB_eq_of_has2_zero hγ h0
  rw [hcl, h0]
  refine update_eq_self_of_zero ?_
  rw [← hcl]
  dsimp only [wR0Pool, poolB, poolOdd0]
  split_ifs <;> exact cleanPoolB_wPool_zero hP hγ _

theorem r0Map_wPool_ge48_zero {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool) {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (i : Fin (51 + S)) (hi : 48 ≤ i.val) :
    r0Map wPool r γ (wPool i) = 0 := by
  have hne : wPool i ≠ wR0Pool wPool ⟨min (idxValD (idxHi5_2 r) γ) 23, by omega⟩
      ⟨idxValPrefix (uBit0_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩ := by
    dsimp only [wR0Pool, poolB, poolOdd0]
    split_ifs
    · exact wPool_ne hP (by omega : i.val ≠ min (idxValD (idxHi5_2 r) γ) 23)
    · exact wPool_ne hP (by omega : i.val ≠ 24 + min (idxValD (idxHi5_2 r) γ) 23)
  exact (Function.update_of_ne hne _ _).trans (cleanPoolB_wPool_zero hP hγ i)

theorem r1RootPool_eq_wR0Pool {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (m : Fin 47) :
    r1RootPool wPool m =
      wR0Pool wPool ⟨m.val / 2, by
        have := m.isLt
        omega⟩ ⟨m.val % 2, by omega⟩ := rfl

theorem r0Map_r1RootPool {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool) {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (m : Fin 47) :
    r0Map wPool r γ (r1RootPool wPool m) =
      if m.val = mValCoh r γ then γ (rRawHas2 r) else 0 := by
  have hZ : cleanPoolB wPool r γ (r1RootPool wPool m) = 0 := by
    dsimp only [r1RootPool, poolB, poolOdd0]
    split_ifs <;> exact cleanPoolB_wPool_zero hP hγ _
  rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
  · rw [r0Map_eq_of_has2_zero hP hγ hH0, hH0, ite_self, ← cleanPoolB_eq_of_has2_zero hγ hH0]
    exact hZ
  · have hq24 := idxHi5_2_lt24_of_lt187 r hγ.1
    have hu0Lt := idxValPrefix_lt_two_pow (uBit0_2 r) γ 1 le_rfl
    have hmLt := m.isLt
    have hIff : m.val = mValCoh r γ ↔
        (⟨m.val / 2, by omega⟩ : Fin 24) = ⟨min (idxValD (idxHi5_2 r) γ) 23, by omega⟩ ∧
        (⟨m.val % 2, by omega⟩ : Fin (2 ^ 1)) = ⟨idxValPrefix (uBit0_2 r) γ 1 le_rfl, hu0Lt⟩ := by
      rw [Fin.ext_iff, Fin.ext_iff]
      dsimp [mValCoh]
      omega
    dsimp only [r0Map]
    rw [r1RootPool_eq_wR0Pool, hH1]
    by_cases hmEq : m.val = mValCoh r γ
    · rw [ite_eq_left hmEq, ← (hIff.mp hmEq).1, ← (hIff.mp hmEq).2, Function.update_self]
    · rw [ite_eq_right hmEq,
          Function.update_of_ne fun e ↦ hmEq (hIff.mpr (wInj_wR0Pool hP _ _ _ _ e))]
      exact hZ

theorem idxLo2_decomp_coh {n : ℕ} (r : RouterReg 187 8 n) (γ : BitAssignment n) :
    idxValPrefix (uLo2_2 r) γ 2 le_rfl =
      2 * idxValPrefix (uBit1_2 r) γ 1 le_rfl + idxValPrefix (uBit0_2 r) γ 1 le_rfl := by
  dsimp only [idxValPrefix, uLo2_2, uBit1_2, uBit0_2, idxLo3_2]
  split_ifs <;> omega

theorem idxLo3_decomp_coh {n : ℕ} (r : RouterReg 187 8 n) (γ : BitAssignment n) :
    idxValD (idxLo3_2 r) γ =
      4 * idxValPrefix (uBit2_2 r) γ 1 le_rfl + idxValPrefix (uLo2_2 r) γ 2 le_rfl := by
  dsimp only [idxValD, idxValPrefix, uLo2_2, uBit2_2, idxLo3_2]
  split_ifs <;> omega

theorem idx2_eq_of_tStar95_coh {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx2 r) γ < 187) :
    idxValD (rIdx2 r) γ =
      8 * ((tStar95 r γ).val / 4) + (tStar95 r γ).val % 4 +
        4 * idxValPrefix (uBit2_2 r) γ 1 le_rfl := by
  have hsp : idxValD (rIdx2 r) γ = 8 * idxValD (idxHi5_2 r) γ + idxValD (idxLo3_2 r) γ :=
    idxValD_8_split35 (rIdx2 r) γ
  have hlo2 : idxValPrefix (uLo2_2 r) γ 2 le_rfl < 4 := idxValPrefix_lt_two_pow _ γ 2 le_rfl
  have ht := tStar95_val_eq r hlt
  rw [hsp, idxLo3_decomp_coh r γ]
  omega

theorem tOfIdx187_of_eq_idx2_coh {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx2 r) γ < 187) {p : Fin 187} (hp : p.val = idxValD (rIdx2 r) γ) :
    tOfIdx187 p = (tStar95 r γ).val := by
  have hu2 : idxValPrefix (uBit2_2 r) γ 1 le_rfl < 2 := idxValPrefix_lt_two_pow _ γ 1 le_rfl
  have h2 := idx2_eq_of_tStar95_coh r hlt
  dsimp only [tOfIdx187]
  omega

theorem cohMap_eq_of_has2_zero {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (h0 : γ (rRawHas2 r) = 0) :
    cohMap mOff M hm hMS wPool r γ = γ := by
  dsimp only [cohMap]
  rw [dite_eq_right (fun h ↦ absurd (h0.symm.trans h.1) (by decide))]
  exact r0Map_eq_of_has2_zero hP hγ h0

theorem cohW5_tStar95_parts {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx2 r) γ < 187) :
    (tStar95 r γ).val =
      4 * idxValD (idxHi5_2 r) γ + 2 * idxValPrefix (uBit1_2 r) γ 1 le_rfl +
        idxValPrefix (uBit0_2 r) γ 1 le_rfl ∧
    2 * ((tStar95 r γ).val / 4) + (tStar95 r γ).val % 2 = mValCoh r γ ∧
    ((tStar95 r γ).val % 4) / 2 = idxValPrefix (uBit1_2 r) γ 1 le_rfl := by
  have htVal : (tStar95 r γ).val =
      4 * idxValD (idxHi5_2 r) γ + 2 * idxValPrefix (uBit1_2 r) γ 1 le_rfl +
        idxValPrefix (uBit0_2 r) γ 1 le_rfl := by
    rw [tStar95_val_eq r hlt, idxLo2_decomp_coh r γ]
    omega
  have hu0Lt := idxValPrefix_lt_two_pow (uBit0_2 r) γ 1 le_rfl
  have hu1Lt := idxValPrefix_lt_two_pow (uBit1_2 r) γ 1 le_rfl
  exact ⟨htVal, by
    dsimp only [mValCoh]
    omega, by omega⟩

theorem cohMap_wCohNode {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (t : Fin 95)
    (ht : mOff ≤ 2 * (t.val / 4) + t.val % 2 ∧ 2 * (t.val / 4) + t.val % 2 < mOff + M) :
    cohMap mOff M hm hMS wPool r γ (wCohNode mOff M hm hMS wPool t ht) =
      if t = tStar95 r γ then γ (rRawHas2 r) else 0 := by
  have hClNode : cleanPoolB wPool r γ (wCohNode mOff M hm hMS wPool t ht) = 0 := by
    obtain ⟨idx, _, hEq⟩ := cohW5_wCohNode_idx mOff M hm hMS wPool t ht
    exact hEq ▸ cleanPoolB_wPool_zero hP hγ idx
  rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
  · rw [cohMap_eq_of_has2_zero hP mOff M hm hMS hγ hH0, hH0, ite_self,
        ← cleanPoolB_eq_of_has2_zero hγ hH0]
    exact hClNode
  · obtain ⟨_, hmStar, hpStar⟩ := cohW5_tStar95_parts r hγ.1
    dsimp only [cohMap]
    rw [hH1]
    by_cases hAct : actCohPred mOff M r γ
    · have hAct2 := hAct.2
      rw [dite_eq_left hAct,
          show pairsCohR1 mOff M hm hMS wPool ⟨mValCoh r γ - mOff, by omega⟩
                ⟨idxValPrefix (uBit1_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩ =
              wCohNode mOff M hm hMS wPool (tStar95 r γ) (hmStar ▸ hAct2) from
            congrArg₂ (pairsCohR1 mOff M hm hMS wPool)
              (Fin.ext (congrArg (· - mOff) hmStar.symm)) (Fin.ext hpStar.symm)]
      by_cases htEq : t = tStar95 r γ
      · subst htEq
        rw [ite_eq_left rfl, Function.update_self]
      · rw [ite_eq_right htEq, Function.update_of_ne fun e ↦ htEq (wCohNode_inj hP mOff M hm hMS e)]
        exact hClNode
    · have hmNe : 2 * (t.val / 4) + t.val % 2 ≠ mValCoh r γ :=
        fun e ↦ hAct ⟨hH1, e ▸ ht.1, e ▸ ht.2⟩
      rw [dite_eq_right hAct, ite_eq_right (fun e : t = tStar95 r γ ↦ hmNe (e ▸ hmStar))]
      dsimp only [wCohNode, pairsCohR1]
      split_ifs with hp0
      · exact (r0Map_r1RootPool hP hγ _).trans (ite_eq_right (by
          dsimp
          omega))
      · exact r0Map_wPool_ge48_zero hP hγ _ (Nat.le_add_right 48 _)

theorem cohMap_poolClean_ge_zero {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (k : Fin (S + 1)) (hk : M ≤ k.val) :
    cohMap mOff M hm hMS wPool r γ (poolClean wPool r k) = 0 := by
  dsimp only [cohMap, poolClean]
  by_cases hAct : actCohPred mOff M r γ
  · have hAct2 := hAct.2
    obtain ⟨idx, hlt, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool ⟨mValCoh r γ - mOff, by omega⟩
      ⟨idxValPrefix (uBit1_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩
    rw [dite_eq_left hAct, hEq]
    split_ifs with hkS
    · exact (Function.update_of_ne (wPool_ne hP (by omega : 48 + k.val ≠ idx.val)) _ _).trans
        (cleanPoolB_wPool_zero hP hγ _)
    · exact (Function.update_of_ne (hP.ne_ctrlLo idx _).symm _ _).trans
        ((Function.update_of_ne (hP.ne_ctrlLo _ _).symm _ _).trans hγ.2.2.2.2.2)
  · rw [dite_eq_right hAct]
    split_ifs with hkS
    · exact r0Map_wPool_ge48_zero hP hγ _ (Nat.le_add_right 48 k.val)
    · dsimp only [r0Map, cleanPoolB, wR0Pool, poolB, poolOdd0]
      split_ifs <;>
        exact (Function.update_of_ne (hP.ne_ctrlLo _ _).symm _ _).trans
          ((Function.update_of_ne (hP.ne_ctrlLo _ _).symm _ _).trans hγ.2.2.2.2.2)

theorem cohMap_wPool_ge48S_zero {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) (i : Fin (51 + S)) (hi : 48 + S ≤ i.val) :
    cohMap mOff M hm hMS wPool r γ (wPool i) = 0 := by
  dsimp only [cohMap]
  split_ifs with hAct
  · have hAct2 := hAct.2
    obtain ⟨idx, hlt, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool
      ⟨mValCoh r γ - mOff, by omega⟩
      ⟨idxValPrefix (uBit1_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩
    rw [hEq, Function.update_of_ne (wPool_ne hP (by omega))]
    exact cleanPoolB_wPool_zero hP hγ i
  · exact r0Map_wPool_ge48_zero hP hγ i (by omega)

/-! ### 4. Generic `vecToggle` Commutation, `uXorPubHiPred`, Mini-Pass & Singletons -/

theorem pubCtrlSet_ne_wPool {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    {w : Wire n} (hw : PubCtrlSet r w) (i : Fin (51 + S)) : w ≠ wPool i := by
  rcases hw with ⟨u, hu, rfl⟩
  exact (hP.ne_pub18 i u (by omega)).symm

theorem cohW5_ctrlLo_ext {n : ℕ} (r : RouterReg 187 8 n) {α β : BitAssignment n}
    (hL : ∀ p : Fin 187, α (rCtrlLo r p) = β (rCtrlLo r p))
    (hOth : ∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → α u = β u) : α = β := by
  funext u
  by_cases h : ∃ p : Fin 187, u = rCtrlLo r p
  · obtain ⟨p, rfl⟩ := h
    exact hL p
  · exact hOth u fun p e ↦ h ⟨p, e⟩

theorem cohW5_upd_congr_at {n : ℕ} {α β : BitAssignment n} (w u : Wire n) (v : ZMod 2)
    (h : α u = β u) : Function.update α w v u = Function.update β w v u := by
  rcases eq_or_ne u w with rfl | hu <;> simp [*, Function.update_of_ne]

theorem cohW5_upd_eq_vecToggle {n : ℕ} (r : RouterReg 187 8 n)
    (δ η : BitAssignment n) (p₀ : Fin 187) (v : ZMod 2)
    (f : BitAssignment n → Fin 187 → ZMod 2)
    (hAt : v = η (rCtrlLo r p₀) + f η p₀)
    (hNe : ∀ p : Fin 187, p ≠ p₀ → δ (rCtrlLo r p) = η (rCtrlLo r p) + f η p)
    (hOth : ∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → δ u = η u) :
    Function.update δ (rCtrlLo r p₀) v = vecToggleBits (rCtrlLo r) f η :=
  cohW5_ctrlLo_ext r
    (fun p ↦ by
      rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f η).1 p]
      by_cases hp : p = p₀
      · subst hp
        rw [Function.update_self, hAt]
      · rw [Function.update_of_ne (rCtrlLo_inj_ne r p p₀ hp)]
        exact hNe p hp)
    (fun u hu ↦ (Function.update_of_ne (hu p₀) v δ).trans
      ((hOth u hu).trans
        ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f η).2 u hu).symm))

theorem cohW5_supp_eq {n : ℕ} {P : BitAssignment n → Prop} {G L R : Operator (2 ^ n)}
    (hG : SupportedOn P G) (h : ∀ γ, P γ → L.mulVec (ket γ) = R.mulVec (ket γ)) :
    L * G = R * G :=
  hG L R fun γ hγ ↦ h γ hγ

theorem wPoolMap_vecToggle {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (F : BitAssignment n → BitAssignment n)
    (hF_other : ∀ γ u, (∀ i : Fin (51 + S), u ≠ wPool i) → F γ u = γ u)
    (hF_pool : ∀ α β, (∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → α u = β u) →
      ∀ i : Fin (51 + S), F α (wPool i) = F β (wPool i))
    (f : BitAssignment n → Fin 187 → ZMod 2)
    (hfPub : ∀ α β, (∀ w, PubCtrlSet r w → α w = β w) → f α = f β)
    (γ : BitAssignment n) :
    F (vecToggleBits (rCtrlLo r) f γ) = vecToggleBits (rCtrlLo r) f (F γ) := by
  let γ' := vecToggleBits (rCtrlLo r) f γ
  have hOth (u : Wire n) (hu : ∀ p : Fin 187, u ≠ rCtrlLo r p) : γ' u = γ u :=
    (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f γ).2 u hu
  have hfEq : f (F γ) = f γ :=
    hfPub _ _ fun w hw ↦ hF_other γ w (pubCtrlSet_ne_wPool hP hw)
  refine cohW5_ctrlLo_ext r (fun p ↦ ?_) (fun u nL ↦ ?_)
  · have hnP : ∀ i : Fin (51 + S), rCtrlLo r p ≠ wPool i := fun i ↦ (hP.ne_ctrlLo i p).symm
    rw [hF_other γ' _ hnP, (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f (F γ)).1 p,
        hfEq, hF_other γ _ hnP]
    exact (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f γ).1 p
  · rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f (F γ)).2 u nL]
    by_cases hW : ∃ i : Fin (51 + S), u = wPool i
    · obtain ⟨i, rfl⟩ := hW
      exact hF_pool γ' γ hOth i
    · have nW : ∀ i : Fin (51 + S), u ≠ wPool i := fun i e ↦ hW ⟨i, e⟩
      rw [hF_other γ' u nW, hF_other γ u nW, hOth u nL]

theorem not_ctrlLo_pub_eq {n : ℕ} (r : RouterReg 187 8 n) {α β : BitAssignment n}
    (h : ∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → α u = β u) :
    α (rRawHas2 r) = β (rRawHas2 r) ∧
    idxValD (idxHi5_2 r) α = idxValD (idxHi5_2 r) β ∧
    idxValPrefix (uBit0_2 r) α 1 le_rfl = idxValPrefix (uBit0_2 r) β 1 le_rfl ∧
    idxValPrefix (uBit1_2 r) α 1 le_rfl = idxValPrefix (uBit1_2 r) β 1 le_rfl ∧
    tStar95 r α = tStar95 r β := by
  obtain ⟨_, hHas2, _, _, hHi, hu0, hu1, _, htS⟩ :=
    cohW5_pub18_congr r fun u hu ↦ h _ (cohW5_pub18_ne_ctrlLo r hu)
  exact ⟨hHas2, hHi, hu0, hu1, htS⟩

theorem cleanPoolB_other {S n : ℕ} (wPool : Fin (51 + S) → Wire n)
    (r : RouterReg 187 8 n) (γ : BitAssignment n) (u : Wire n)
    (hu : ∀ i : Fin (51 + S), u ≠ wPool i) : cleanPoolB wPool r γ u = γ u :=
  Function.update_of_ne (hu _) 0 γ

theorem cleanPoolB_pool_congr {S n : ℕ} (wPool : Fin (51 + S) → Wire n)
    (r : RouterReg 187 8 n) {α β : BitAssignment n}
    (h : ∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → α u = β u)
    (hP : CHiPoolDisj r wPool) (i : Fin (51 + S)) :
    cleanPoolB wPool r α (wPool i) = cleanPoolB wPool r β (wPool i) := by
  obtain ⟨_, hHi, _, _, _⟩ := not_ctrlLo_pub_eq r h
  dsimp only [cleanPoolB, poolB]
  rw [show (⟨min (idxValD (idxHi5_2 r) α) 23, by omega⟩ : Fin (51 + S)) =
      ⟨min (idxValD (idxHi5_2 r) β) 23, by omega⟩ from Fin.ext (congrArg (min · 23) hHi)]
  exact cohW5_upd_congr_at _ _ 0 (h _ (hP.ne_ctrlLo i))

theorem r0Map_other {S n : ℕ} (wPool : Fin (51 + S) → Wire n)
    (r : RouterReg 187 8 n) (γ : BitAssignment n) (u : Wire n)
    (hu : ∀ i : Fin (51 + S), u ≠ wPool i) : r0Map wPool r γ u = γ u := by
  dsimp only [r0Map, wR0Pool, poolB, poolOdd0]
  split_ifs <;> exact (Function.update_of_ne (hu _) _ _).trans (cleanPoolB_other wPool r γ u hu)

theorem r0Map_pool_congr {S n : ℕ} (wPool : Fin (51 + S) → Wire n)
    (r : RouterReg 187 8 n) {α β : BitAssignment n}
    (h : ∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → α u = β u)
    (hP : CHiPoolDisj r wPool) (i : Fin (51 + S)) :
    r0Map wPool r α (wPool i) = r0Map wPool r β (wPool i) := by
  obtain ⟨hHas, hHi, hu0, _, _⟩ := not_ctrlLo_pub_eq r h
  dsimp only [r0Map]
  rw [show wR0Pool wPool _ _ = wR0Pool wPool ⟨min (idxValD (idxHi5_2 r) β) 23, by omega⟩
          ⟨_, idxValPrefix_lt_two_pow _ β 1 le_rfl⟩ from
        congrArg₂ _ (Fin.ext (congrArg (min · 23) hHi)) (Fin.ext hu0), hHas]
  exact cohW5_upd_congr_at _ _ _ (cleanPoolB_pool_congr wPool r h hP i)

theorem cohMap_other {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n) (γ : BitAssignment n)
    (u : Wire n) (hu : ∀ i : Fin (51 + S), u ≠ wPool i) :
    cohMap mOff M hm hMS wPool r γ u = γ u := by
  dsimp only [cohMap]
  split_ifs with hAct
  · have hAct2 := hAct.2
    obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool
      ⟨mValCoh r γ - mOff, by omega⟩
      ⟨idxValPrefix (uBit1_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩
    rw [hEq, Function.update_of_ne (hu idx)]
    exact cleanPoolB_other wPool r γ u hu
  · exact r0Map_other wPool r γ u hu

theorem cohMap_pool_congr {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n) {α β : BitAssignment n}
    (h : ∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → α u = β u)
    (hP : CHiPoolDisj r wPool) (i : Fin (51 + S)) :
    cohMap mOff M hm hMS wPool r α (wPool i) = cohMap mOff M hm hMS wPool r β (wPool i) := by
  obtain ⟨hHas, hHi, hu0, hu1, _⟩ := not_ctrlLo_pub_eq r h
  have hmEq : mValCoh r α = mValCoh r β := by
    dsimp [mValCoh]
    rw [hHi, hu0]
  have hActIff : actCohPred mOff M r α ↔ actCohPred mOff M r β := by
    unfold actCohPred
    rw [hHas, hmEq]
  dsimp only [cohMap]
  by_cases hAct : actCohPred mOff M r β
  · have hActA := hActIff.mpr hAct
    have hA2 := hActA.2
    have hB2 := hAct.2
    rw [dite_eq_left hActA, dite_eq_left hAct,
        show pairsCohR1 mOff M hm hMS wPool _ _ =
            pairsCohR1 mOff M hm hMS wPool ⟨mValCoh r β - mOff, by omega⟩
              ⟨_, idxValPrefix_lt_two_pow _ β 1 le_rfl⟩ from
          congrArg₂ _ (Fin.ext (congrArg (· - mOff) hmEq)) (Fin.ext hu1)]
    exact cohW5_upd_congr_at _ _ 1 (cleanPoolB_pool_congr wPool r h hP i)
  · rw [dite_eq_right (fun hc ↦ hAct (hActIff.mp hc)), dite_eq_right hAct]
    exact r0Map_pool_congr wPool r h hP i

/-- Toggle `rCtrlLo` on `p : Fin 187` whose `tOfIdx187 p` satisfies `P`. -/
def pubCtrlHiPred {n : ℕ} (P : ℕ → Bool) (r : RouterReg 187 8 n)
    (α : BitAssignment n) (p : Fin 187) : ZMod 2 :=
  if P (tOfIdx187 p) = true then pubCtrlHi r α p else 0

theorem pubCtrlHiPred_pub_congr {n : ℕ} (P : ℕ → Bool) (r : RouterReg 187 8 n)
    {α β : BitAssignment n} (hEq : ∀ w, PubCtrlSet r w → α w = β w) :
    pubCtrlHiPred P r α = pubCtrlHiPred P r β :=
  funext fun p ↦ by
    dsimp only [pubCtrlHiPred]
    rw [congrFun (pubCtrl_congr r hEq).2 p]

/-- Unitary toggling `rCtrlLo` by `pubCtrlHiPred P r`. -/
def uXorPubHiPred {n : ℕ} (P : ℕ → Bool) (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
  uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r) (pubCtrlHiPred P r)
    (fun _ _ hEq ↦ pubCtrlHiPred_pub_congr P r fun w ⟨u, hu, hw⟩ ↦ hw ▸
      hEq (r u) fun q ↦ rr_ne r (by
          have := q.isLt
          dsimp [rCtrlLo]
          rw [bp187_eq]
          omega))

theorem pubCtrlHiPred_zero_at_zero {S n : ℕ} (P : ℕ → Bool) (r : RouterReg 187 8 n)
    {wPool : Fin (51 + S) → Wire n} {γ : BitAssignment n}
    (hγ : ValidCHiPoolCtrl0 r wPool γ) :
    pubCtrlHiPred P r γ ⟨0, by decide⟩ = 0 := by
  dsimp only [pubCtrlHiPred, pubCtrlHi]
  split_ifs with hP
  · rw [cond_nat_beq]
    rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with h0 | h1
    · simp [h0]
    · rw [h1, ite_eq_right (Ne.symm (hγ.2.2.1 h1))]
  · rfl

theorem mul_uXorPubHiPred {n : ℕ} (P₁ P₂ : ℕ → Bool) (r : RouterReg 187 8 n)
    (hDisj : ∀ t < 95, ¬ (P₁ t = true ∧ P₂ t = true)) :
    (uXorPubHiPred P₂ r).1 * (uXorPubHiPred P₁ r).1 =
      (uXorPubHiPred (fun t ↦ P₁ t || P₂ t) r).1 := by
  refine PhotochemistrySolution.SplitRouterSeqBell26k.matrix_ext_ket fun α ↦ ?_
  let g₁ := vecToggleBits (rCtrlLo r) (pubCtrlHiPred P₁ r) α
  have hPub₁ : ∀ w, PubCtrlSet r w → g₁ w = α w := fun w ⟨u, hu, hw⟩ ↦ hw ▸
    (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 _ (cohW5_pub18_ne_ctrlLo r (by omega))
  simp only [← Matrix.mulVec_mulVec]
  dsimp only [uXorPubHiPred]
  rw [uVecToggle_mulVec_ket, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket]
  refine congrArg PhotochemistrySolution.SplitRouterSeqBell26k.ket
    (cohW5_ctrlLo_ext r (fun p ↦ ?_) (fun u nL ↦ ?_))
  · have hpLt := p.isLt
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ g₁).1 p,
        (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).1 p,
        congrFun (pubCtrlHiPred_pub_congr P₂ r hPub₁) p]
    dsimp only [g₁]
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).1 p]
    have hd := hDisj (tOfIdx187 p) (by
      dsimp [tOfIdx187]
      omega)
    dsimp only [pubCtrlHiPred]
    by_cases h1 : P₁ (tOfIdx187 p) = true <;> by_cases h2 : P₂ (tOfIdx187 p) = true <;>
      simp_all
  · rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ g₁).2 u nL,
        (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 u nL]
    exact (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 u nL

theorem uXorPubHiPred_full {n : ℕ} (P : ℕ → Bool) (r : RouterReg 187 8 n)
    (hAll : ∀ t < 95, P t = true) :
    (uXorPubHiPred P r).1 = (uXorPubHiFull r).1 := by
  refine PhotochemistrySolution.SplitRouterSeqBell26k.matrix_ext_ket fun α ↦ ?_
  dsimp only [uXorPubHiPred, uXorPubHiFull]
  rw [uVecToggle_mulVec_ket, uVecToggle_mulVec_ket,
      show pubCtrlHiPred P r = pubCtrlHi r from funext fun β ↦ funext fun p ↦
        ite_eq_left (hAll _ (by
          have := p.isLt
          dsimp [tOfIdx187]
          omega))]

/-- Round-0 singleton CNOT `poolOdd0[23] → rCtrlLo[185]` covering `t = 93` (`m = 47`). -/
def cR0Sing93 {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) : Circuit n :=
  Circuit.CNOT (poolOdd0 wPool ⟨23, by decide⟩) (rCtrlLo r ⟨185, by decide⟩) (hP.ne_ctrlLo _ _)

theorem subspaceStep_cR0Sing93 {Var : Type} [Fintype Var] [DecidableEq Var] {S n : ℕ}
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    SubspaceStep (Var := Var)
      (opR0 wPool r G)
      (opR0 wPool r ((uXorPubHiPred (fun t ↦ decide (t = 93)) r).1 * G))
      (.circuit (cR0Sing93 hP)) := by
  refine subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_
  dsimp only [opR0, uXorPubHiPred]
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hG fun γ hγ ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  rw [mkVecOp_mulVec_ket, uVecToggle_mulVec_ket, mkVecOp_mulVec_ket,
      wPoolMap_vecToggle hP (r0Map wPool r) (r0Map_other wPool r)
        (fun _ _ h ↦ r0Map_pool_congr wPool r h hP) _ (fun _ _ ↦ pubCtrlHiPred_pub_congr _ r) γ]
  dsimp only [cR0Sing93]
  rw [ket_CNOT]
  have hPubR0 : pubCtrlHiPred (fun t ↦ decide (t = 93)) r (r0Map wPool r γ) =
      pubCtrlHiPred (fun t ↦ decide (t = 93)) r γ :=
    pubCtrlHiPred_pub_congr _ r fun w hw ↦ r0Map_other wPool r γ w (pubCtrlSet_ne_wPool hP hw)
  have hOdd23 : r0Map wPool r γ (poolOdd0 wPool ⟨23, by decide⟩) =
      if idxValD (rIdx2 r) γ = 185 then γ (rRawHas2 r) else 0 := by
    rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
    · rw [r0Map_eq_of_has2_zero hP hγ hH0, hH0, ite_self, ← cleanPoolB_eq_of_has2_zero hγ hH0]
      exact cleanPoolB_wPool_zero hP hγ _
    · have hlt2 := hγ.1
      have hq24 := idxHi5_2_lt24_of_lt187 r hlt2
      have hu0Lt := idxValPrefix_lt_two_pow (uBit0_2 r) γ 1 le_rfl
      have hu1Lt := idxValPrefix_lt_two_pow (uBit1_2 r) γ 1 le_rfl
      have hu2Lt := idxValPrefix_lt_two_pow (uBit2_2 r) γ 1 le_rfl
      have hsp : idxValD (rIdx2 r) γ = 8 * idxValD (idxHi5_2 r) γ + idxValD (idxLo3_2 r) γ :=
        idxValD_8_split35 (rIdx2 r) γ
      rw [idxLo3_decomp_coh r γ, idxLo2_decomp_coh r γ] at hsp
      have h185 : idxValD (rIdx2 r) γ = 185 ↔
          (⟨23, by decide⟩ : Fin 24) = ⟨min (idxValD (idxHi5_2 r) γ) 23, by omega⟩ ∧
          (⟨1, by decide⟩ : Fin (2 ^ 1)) = ⟨idxValPrefix (uBit0_2 r) γ 1 le_rfl, hu0Lt⟩ := by
        rw [Fin.ext_iff, Fin.ext_iff]
        dsimp
        omega
      dsimp only [r0Map]
      rw [hH1]
      change Function.update (cleanPoolB wPool r γ) _ 1
        (wR0Pool wPool ⟨23, by decide⟩ ⟨1, by decide⟩) = _
      by_cases hi185 : idxValD (rIdx2 r) γ = 185
      · rw [ite_eq_left hi185, ← (h185.mp hi185).1, ← (h185.mp hi185).2, Function.update_self]
      · rw [ite_eq_right hi185,
            Function.update_of_ne fun e ↦ hi185 (h185.mpr (wInj_wR0Pool hP _ _ _ _ e))]
        exact cleanPoolB_wPool_zero hP hγ _
  refine congrArg ket (cohW5_upd_eq_vecToggle r _ _ ⟨185, by decide⟩ _ _ ?_ ?_ fun _ _ ↦ rfl)
  · rw [hPubR0, hOdd23]
    dsimp only [pubCtrlHiPred, pubCtrlHi]
    rw [ite_eq_left (rfl : decide (tOfIdx187 ⟨185, by decide⟩ = 93) = true), cond_nat_beq,
        if_congr eq_comm rfl rfl]
  · intro p hp185
    have hpv : p.val ≠ 185 := fun e ↦ hp185 (Fin.ext e)
    have hpLt := p.isLt
    simp [pubCtrlHiPred, show tOfIdx187 p ≠ 93 by
      dsimp only [tOfIdx187]
      omega]

/-- Batch singleton CNOT `wCohNode[tSing] → rCtrlLo[pSing]` covering `t ∈ {0, 92, 94}`. -/
def cCohSing {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tSing : Fin 95) (pSing : Fin 187)
    (ht : mOff ≤ 2 * (tSing.val / 4) + tSing.val % 2 ∧
          2 * (tSing.val / 4) + tSing.val % 2 < mOff + M) : Circuit n :=
  Circuit.CNOT (wCohNode mOff M hm hMS wPool tSing ht) (rCtrlLo r pSing) (by
    obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool
      ⟨2 * (tSing.val / 4) + tSing.val % 2 - mOff, by omega⟩ ⟨(tSing.val % 4) / 2, by omega⟩
    change pairsCohR1 _ _ _ _ _ _ _ ≠ _
    rw [hEq]
    exact hP.ne_ctrlLo idx pSing)

theorem cohSing_iff {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    {γ : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) (h1 : γ (rRawHas2 r) = 1)
    (tSing : Fin 95) (pSing : Fin 187)
    (hPair : (tSing.val = 0 ∧ pSing.val = 4) ∨
             (tSing.val = 92 ∧ pSing.val = 184) ∨
             (tSing.val = 94 ∧ pSing.val = 186))
    (p : Fin 187) :
    (tOfIdx187 p = tSing.val ∧ p.val = idxValD (rIdx2 r) γ) ↔
      (p = pSing ∧ tSing = tStar95 r γ) := by
  have hlt := hγ.1
  have hnz := hγ.2.2.1 h1
  have hu2Lt : idxValPrefix (uBit2_2 r) γ 1 le_rfl < 2 := idxValPrefix_lt_two_pow _ γ 1 le_rfl
  have h2 := idx2_eq_of_tStar95_coh r hlt
  have hpLt := p.isLt
  have htSLt := (tStar95 r γ).isLt
  rw [Fin.ext_iff, Fin.ext_iff]
  dsimp only [tOfIdx187]
  rcases hPair with ⟨ht0, hp0⟩ | ⟨ht0, hp0⟩ | ⟨ht0, hp0⟩ <;> omega

theorem subspaceStep_cCohSing {Var : Type} [Fintype Var] [DecidableEq Var] {S n : ℕ}
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tSing : Fin 95) (pSing : Fin 187)
    (ht : mOff ≤ 2 * (tSing.val / 4) + tSing.val % 2 ∧
          2 * (tSing.val / 4) + tSing.val % 2 < mOff + M)
    (hPair : (tSing.val = 0 ∧ pSing.val = 4) ∨
             (tSing.val = 92 ∧ pSing.val = 184) ∨
             (tSing.val = 94 ∧ pSing.val = 186))
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    SubspaceStep (Var := Var)
      (opCoh mOff M hm hMS wPool r G)
      (opCoh mOff M hm hMS wPool r
        ((uXorPubHiPred (fun t ↦ decide (t = tSing.val)) r).1 * G))
      (.circuit (cCohSing hP mOff M hm hMS tSing pSing ht)) := by
  refine subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_
  dsimp only [opCoh, uXorPubHiPred]
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hG fun γ hγ ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  rw [mkVecOp_mulVec_ket, uVecToggle_mulVec_ket, mkVecOp_mulVec_ket,
      wPoolMap_vecToggle hP (cohMap mOff M hm hMS wPool r) (cohMap_other mOff M hm hMS wPool r)
        (fun _ _ h ↦ cohMap_pool_congr mOff M hm hMS wPool r h hP)
        _ (fun _ _ ↦ pubCtrlHiPred_pub_congr _ r) γ]
  dsimp only [cCohSing]
  rw [ket_CNOT, cohMap_wCohNode hP mOff M hm hMS hγ tSing ht]
  have hPubCoh : pubCtrlHiPred (fun t ↦ decide (t = tSing.val)) r
        (cohMap mOff M hm hMS wPool r γ) =
      pubCtrlHiPred (fun t ↦ decide (t = tSing.val)) r γ :=
    pubCtrlHiPred_pub_congr _ r fun w hw ↦
      cohMap_other mOff M hm hMS wPool r γ w (pubCtrlSet_ne_wPool hP hw)
  have hVal (p : Fin 187) :
      pubCtrlHiPred (fun t ↦ decide (t = tSing.val)) r γ p =
        if p = pSing ∧ tSing = tStar95 r γ then γ (rRawHas2 r) else 0 := by
    dsimp only [pubCtrlHiPred, pubCtrlHi]
    rw [cond_nat_beq]
    rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
    · rw [hH0]
      split_ifs <;> rfl
    · have hIff := cohSing_iff hγ hH1 tSing pSing hPair p
      rw [hH1]
      split_ifs <;> simp_all
  refine congrArg ket (cohW5_upd_eq_vecToggle r _ _ pSing _ _ ?_ ?_ fun _ _ ↦ rfl)
  · rw [hPubCoh, hVal pSing, if_congr (and_iff_right rfl) rfl rfl]
  · intro p hpEq
    rw [hPubCoh, hVal p, ite_eq_right (fun h ↦ hpEq h.1), add_zero]

/-! ### 5. Batch Round-2 Mini-Pass (`pCohMiniPass`, `2 * R + 2` `T`, `0 .TOFF`) -/

def actPoolDum {S n : ℕ} (wPool : Fin (51 + S) → Wire n) (δ : BitAssignment n) : Prop :=
  δ (poolRDum wPool) = 0

instance {S n : ℕ} (wPool : Fin (51 + S) → Wire n) : DecidablePred (actPoolDum wPool) :=
  fun δ ↦ inferInstanceAs (Decidable (δ (poolRDum wPool) = 0))

def actRangeCoh {n : ℕ} (tOff R : ℕ) (r : RouterReg 187 8 n) (γ : BitAssignment n) : Prop :=
  γ (rRawHas2 r) = 1 ∧ tOff ≤ (tStar95 r γ).val ∧ (tStar95 r γ).val < tOff + R

instance {n : ℕ} (tOff R : ℕ) (r : RouterReg 187 8 n) :
    DecidablePred (actRangeCoh tOff R r) :=
  fun γ ↦ by
      unfold actRangeCoh
      infer_instance

def bStarCohMini {n : ℕ} (tOff R : ℕ) (hR : 0 < R) (r : RouterReg 187 8 n)
    (δ : BitAssignment n) : Fin R :=
  ⟨min ((tStar95 r δ).val - tOff) (R - 1), by omega⟩

def pairsCohMini {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (k : Fin R) (p : Fin (2 ^ 1)) : Wire n :=
  if p.val = 0 then
    wCohNode mOff M hm hMS wPool ⟨k.val + tOff, by
        have := k.isLt
        omega⟩ (hRange k)
  else
    poolClean wPool r ⟨M + k.val, by
        have := k.isLt
        omega⟩

theorem cohW5_miniNode_idx {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    (wPool : Fin (51 + S) → Wire n) (k : Fin R) :
    ∃ idx : Fin (51 + S), idx.val < 48 + M ∧
      wCohNode mOff M hm hMS wPool ⟨k.val + tOff, by
        have := k.isLt
        omega⟩ (hRange k) = wPool idx :=
  cohW5_wCohNode_idx mOff M hm hMS wPool ⟨k.val + tOff, by
    have := k.isLt
    omega⟩ (hRange k)

theorem wOptInj_pairsCohMini {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M) :
    WOptInj R 1 (uBit2_2 r) (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r)
      (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) :=
  cohW5_mk_wOptInj hP (uBit2_2 r) (fun i _ ↦ wPool_ne_idxLo3_2 hP i _)
    (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r)
    (fun k₁ p₁ k₂ p₂ heq ↦ by
      have hp₁ := p₁.isLt
      have hp₂ := p₂.isLt
      have hMis (a b : Fin R) : wCohNode mOff M hm hMS wPool ⟨a.val + tOff, by
          have := a.isLt
          omega⟩ (hRange a) ≠ poolClean wPool r ⟨M + b.val, by
          have := b.isLt
          omega⟩ := wCohNode_ne_poolClean_ge hP mOff M hm hMS _ _ _ (Nat.le_add_right M b.val)
      dsimp only [pairsCohMini] at heq
      split_ifs at heq with h1 h2 h2
      · have hv := congrArg Fin.val (wCohNode_inj hP mOff M hm hMS heq)
        dsimp at hv
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact absurd heq (hMis k₁ k₂)
      · exact absurd heq.symm (hMis k₂ k₁)
      · have hv := congrArg Fin.val (poolClean_inj hP heq)
        dsimp at hv
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
    (fun _ k p ↦ by
      dsimp only [pairsCohMini]
      split_ifs
      · obtain ⟨idx, _, hEq⟩ := cohW5_miniNode_idx mOff M hm hMS tOff R ht hRange wPool k
        exact hEq ▸ (wPool_ne_idxLo3_2 hP idx _).symm
      · exact (poolClean_ne_pub18 hP _ _ (by
          dsimp [uBit2_2, idxLo3_2, rIdx2]
          omega)).symm)
    (fun i hi k p ↦ by
      dsimp only [pairsCohMini]
      split_ifs
      · obtain ⟨idx, hlt, hEq⟩ := cohW5_miniNode_idx mOff M hm hMS tOff R ht hRange wPool k
        exact hEq ▸ wPool_ne hP (by omega)
      · exact poolClean_ne_wPool_ge hP _ i hi)

theorem wCohNode_ne_rDum {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    (k : Fin R) :
    wCohNode mOff M hm hMS wPool ⟨k.val + tOff, by
        have := k.isLt
        omega⟩ (hRange k) ≠ poolRDum wPool :=
  (wOptInj_pairsCohMini hP mOff M hm hMS tOff R ht hClean hRange).w_ne_rDum k ⟨0, by decide⟩

def cGatCohMiniIn {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M) : Circuit n :=
  Circuit.seq (Circuit.X (poolRDum wPool))
    (seqGatherParity R
      (fun k ↦ wCohNode mOff M hm hMS wPool ⟨k.val + tOff, by
          have := k.isLt
          omega⟩ (hRange k))
      (poolRDum wPool)
      (wCohNode_ne_rDum hP mOff M hm hMS tOff R ht hClean hRange))

def cGatCohMiniOut {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M) : Circuit n :=
  Circuit.seq
    (seqGatherParity R
      (fun k ↦ wCohNode mOff M hm hMS wPool ⟨k.val + tOff, by
          have := k.isLt
          omega⟩ (hRange k))
      (poolRDum wPool)
      (wCohNode_ne_rDum hP mOff M hm hMS tOff R ht hClean hRange))
    (Circuit.X (poolRDum wPool))

def cCopyCohMini {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M) : Circuit n :=
  Circuit.seq
    (seqCnotVec R
      (fun k ↦ wCohNode mOff M hm hMS wPool ⟨k.val + tOff, by
          have := k.isLt
          omega⟩ (hRange k))
      (fun k ↦ rCtrlLo r (pLoMini tOff R ht k))
      (fun k ↦ by
        obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool
          ⟨2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 - mOff, by
              have := hRange k
              omega⟩
          ⟨((k.val + tOff) % 4) / 2, by omega⟩
        change pairsCohR1 _ _ _ _ _ _ _ ≠ _
        rw [hEq]
        exact hP.ne_ctrlLo idx _))
    (seqCnotVec R
      (fun k ↦ poolClean wPool r ⟨M + k.val, by
          have := k.isLt
          omega⟩)
      (fun k ↦ rCtrlLo r (pHiMini tOff R ht k))
      (fun k ↦ poolClean_ne_ctrlLo_nz hP _ _ (by
          dsimp [pHiMini]
          omega)))

/-- Batch Round-2 mini-pass over `[tOff, tOff + R)` (`2 * R + 2` `.T`, `0 .TOFF`). -/
def pCohMiniPass {Var : Type} {S n : ℕ} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M) : DynamicCircuit Var n :=
  let hOpt := wOptInj_pairsCohMini hP mOff M hm hMS tOff R ht hClean hRange
  .seq (.circuit (cGatCohMiniIn hP mOff M hm hMS tOff R ht hClean hRange))
    (.seq (wLastSplitShiftDyn v R 0 (uBit2_2 r)
        (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r)
        (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) hOpt)
      (.seq (.circuit (cCopyCohMini hP mOff M hm hMS tOff R ht hClean hRange))
        (.seq (wUncompTreeDyn v R 1 (uBit2_2 r)
            (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r)
            hOpt.w_inj hOpt.uLo_ne_w (.circuit .identity) 1 le_rfl)
          (.circuit (cGatCohMiniOut hP mOff M hm hMS tOff R ht hClean hRange)))))

theorem count_pCohMiniPass {Var : Type} {S n : ℕ} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M) :
    (pCohMiniPass v hP mOff M hm hMS tOff R ht hClean hRange).count .T = 2 * R + 2 ∧
    (pCohMiniPass v hP mOff M hm hMS tOff R ht hClean hRange).count .TOFF = 0 := by
  let hOpt := wOptInj_pairsCohMini hP mOff M hm hMS tOff R ht hClean hRange
  let pairs := pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r
  obtain ⟨tl, fl⟩ := count_wLastSplitShiftDyn v R 0 (uBit2_2 r) pairs
    (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) hOpt
  obtain ⟨tu, fu⟩ := count_wUncompTreeDyn_opt v R 1 (uBit2_2 r) pairs
    hOpt.w_inj hOpt.uLo_ne_w (.circuit .identity) 1 le_rfl
  unfold pCohMiniPass
  dsimp only [DynamicCircuit.count]
  rw [tl, fl, tu, fu]
  constructor <;> simp [cGatCohMiniIn, cGatCohMiniOut, cCopyCohMini, DynamicCircuit.count,
    Circuit.count_seq, Circuit.X, count_seqGatherParity_t, count_seqGatherParity_toff,
    count_seqCnotVec_t, count_seqCnotVec_toff]

theorem dynWires_pCohMiniPass {Var : Type} {S n : ℕ} {Sw : Wire n → Prop} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    (hI3 : ∀ d : Fin 3, Sw (idxLo3_2 r d))
    (hPool : ∀ i : Fin (51 + S), Sw (wPool i))
    (hCLo : ∀ p : Fin 187, Sw (rCtrlLo r p)) :
    DynWires Sw (pCohMiniPass v hP mOff M hm hMS tOff R ht hClean hRange) := by
  have hwPar (k : Fin R) : Sw (wCohNode mOff M hm hMS wPool ⟨k.val + tOff, by
      have := k.isLt
      omega⟩ (hRange k)) := by
    obtain ⟨idx, _, hEq⟩ := cohW5_miniNode_idx mOff M hm hMS tOff R ht hRange wPool k
    exact hEq ▸ hPool idx
  have hwCh (k : Fin R) : Sw (poolClean wPool r ⟨M + k.val, by
      have := k.isLt
      omega⟩) := by
    dsimp only [poolClean]
    split_ifs
    · exact hPool _
    · exact hCLo _
  have hwPairs (k : Fin R) (p : Fin (2 ^ 1)) :
      Sw (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r k p) := by
    dsimp only [pairsCohMini]
    split_ifs
    · exact hwPar k
    · exact hwCh k
  exact ⟨⟨cw_1 (hPool _), cw_seqGatherParity R _ _ _ hwPar (hPool _)⟩,
    dw_wLastSplitShiftDyn v R 0 _ _ _ _ _ _ (fun _ ↦ hI3 _) hwPairs (hPool _) (hPool _) (hPool _),
    ⟨cw_seqCnotVec R _ _ _ hwPar (fun _ ↦ hCLo _),
      cw_seqCnotVec R _ _ _ hwCh (fun _ ↦ hCLo _)⟩,
    dw_wUncompTreeDyn_opt v R 1 _ _ _ _ (fun _ ↦ hI3 _) hwPairs
      (rest := .circuit .identity) trivial 1 le_rfl,
    ⟨cw_seqGatherParity R _ _ _ hwPar (hPool _), cw_1 (hPool _)⟩⟩

def baseCohMiniMap {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (γ : BitAssignment n) : BitAssignment n :=
  if actRangeCoh tOff R r γ then cleanPoolB wPool r γ
  else Function.update (cohMap mOff M hm hMS wPool r γ) (poolRDum wPool) 1

def baseCohMiniOp {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (X : Operator (2 ^ n)) : Operator (2 ^ n) :=
  mkVecOp (fun γ ↦ ket (baseCohMiniMap mOff M hm hMS tOff R wPool r γ)) * X

theorem baseCohMiniMap_other {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    (γ : BitAssignment n) (u : Wire n) (hu : ∀ i : Fin (51 + S), u ≠ wPool i) :
    baseCohMiniMap mOff M hm hMS tOff R wPool r γ u = γ u := by
  dsimp only [baseCohMiniMap]
  split_ifs
  · exact cleanPoolB_other wPool r γ u hu
  · exact (Function.update_of_ne (hu _) 1 _).trans (cohMap_other mOff M hm hMS wPool r γ u hu)

theorem baseCohMiniMap_pool_congr {S n : ℕ} (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (wPool : Fin (51 + S) → Wire n) (r : RouterReg 187 8 n)
    {α β : BitAssignment n} (h : ∀ u, (∀ p : Fin 187, u ≠ rCtrlLo r p) → α u = β u)
    (hP : CHiPoolDisj r wPool) (i : Fin (51 + S)) :
    baseCohMiniMap mOff M hm hMS tOff R wPool r α (wPool i) =
      baseCohMiniMap mOff M hm hMS tOff R wPool r β (wPool i) := by
  obtain ⟨hHas, _, _, _, htEq⟩ := not_ctrlLo_pub_eq r h
  have hActIff : actRangeCoh tOff R r α ↔ actRangeCoh tOff R r β := by
    unfold actRangeCoh
    rw [hHas, htEq]
  dsimp only [baseCohMiniMap]
  by_cases hAct : actRangeCoh tOff R r β
  · rw [ite_eq_left (hActIff.mpr hAct), ite_eq_left hAct]
    exact cleanPoolB_pool_congr wPool r h hP i
  · rw [ite_eq_right (fun hc ↦ hAct (hActIff.mp hc)), ite_eq_right hAct]
    exact cohW5_upd_congr_at _ _ 1 (cohMap_pool_congr mOff M hm hMS wPool r h hP i)

theorem cohW5_actPoolDum_props {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    {γ δ β : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) (P : Prop) [Decidable P]
    (hβ : β = if P then cleanPoolB wPool r γ else Function.update δ (poolRDum wPool) 1)
    (hδGe : ∀ i : Fin (51 + S), 48 + S < i.val → δ (wPool i) = 0) :
    (actPoolDum wPool β ↔ P) ∧ β (poolWDum wPool) = 0 ∧ β (poolQEnc wPool) = 0 := by
  have hRD : β (poolRDum wPool) = if P then 0 else 1 := by
    rw [hβ]
    split_ifs
    · exact cleanPoolB_wPool_zero hP hγ _
    · exact Function.update_self _ 1 _
  have hGe (i : Fin (51 + S)) (hi : 48 + S < i.val) : β (wPool i) = 0 := by
    rw [hβ]
    split_ifs
    · exact cleanPoolB_wPool_zero hP hγ _
    · exact (Function.update_of_ne (wPool_ne hP (by omega : i.val ≠ 48 + S)) 1 _).trans (hδGe i hi)
  refine ⟨?_, hGe _ (by omega : 48 + S < 49 + S), hGe _ (by omega : 48 + S < 50 + S)⟩
  unfold actPoolDum
  rw [hRD]
  split_ifs with h <;> simp [h]

theorem baseCohMiniMap_props {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (hR : 0 < R) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    {γ : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) :
    let β := baseCohMiniMap mOff M hm hMS tOff R wPool r γ
    (actPoolDum wPool β ↔ actRangeCoh tOff R r γ) ∧
    bStarCohMini tOff R hR r β = bStarCohMini tOff R hR r γ ∧
    idxValPrefix (uBit2_2 r) β 1 le_rfl = idxValPrefix (uBit2_2 r) γ 1 le_rfl ∧
    β (poolWDum wPool) = 0 ∧
    β (poolQEnc wPool) = 0 ∧
    (∀ k p, β (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r k p) = 0) := by
  intro β
  obtain ⟨_, _, _, _, _, _, _, hu2, htEq⟩ := cohW5_pub18_congr r fun u hu ↦
    baseCohMiniMap_other mOff M hm hMS tOff R wPool r γ _ (pubCtrlSet_ne_wPool hP ⟨u, hu, rfl⟩)
  obtain ⟨hActIff, hWD, hQE⟩ := cohW5_actPoolDum_props hP hγ (actRangeCoh tOff R r γ) rfl
    fun i hi ↦ cohMap_wPool_ge48S_zero hP mOff M hm hMS hγ i (by omega)
  refine ⟨hActIff, Fin.ext (by
    dsimp [bStarCohMini]
    rw [htEq]), hu2, hWD, hQE, fun k p ↦ ?_⟩
  have hOpt := wOptInj_pairsCohMini hP mOff M hm hMS tOff R ht hClean hRange
  have hkLt := k.isLt
  dsimp only [β, baseCohMiniMap]
  split_ifs with hAct
  · dsimp only [pairsCohMini, poolClean]
    split_ifs
    · obtain ⟨idx, _, hEq⟩ := cohW5_miniNode_idx mOff M hm hMS tOff R ht hRange wPool k
      exact hEq ▸ cleanPoolB_wPool_zero hP hγ idx
    · exact cleanPoolB_wPool_zero hP hγ _
    · exact (Function.update_of_ne (hP.ne_ctrlLo _ _).symm 0 γ).trans hγ.2.2.2.2.2
  · rw [Function.update_of_ne (hOpt.w_ne_rDum k p)]
    dsimp only [pairsCohMini]
    split_ifs with hp0
    · rw [cohMap_wCohNode hP mOff M hm hMS hγ]
      split_ifs with htEqK
      · rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
        · exact hH0
        · have hv := congrArg Fin.val htEqK
          dsimp at hv
          exact absurd ⟨hH1, by omega, by omega⟩ hAct
      · rfl
    · exact cohMap_poolClean_ge_zero hP mOff M hm hMS hγ _ (Nat.le_add_right M k.val)

theorem cohW5_gatIn_ket {S n K : ℕ} {wPool : Fin (51 + S) → Wire n}
    (wSrc : Fin K → Wire n) (hne : ∀ k, wSrc k ≠ poolRDum wPool)
    (bStar : BitAssignment n → Fin K) (uLo : Fin 1 → Wire n)
    (pairs : Fin K → Fin (2 ^ 1) → Wire n)
    (δ cl β : BitAssignment n) (P : Prop) [Decidable P]
    (hβ : β = if P then cl else Function.update δ (poolRDum wPool) 1)
    (hδRD : δ (poolRDum wPool) = 0)
    (hClRD : cl (poolRDum wPool) = 0)
    (hWD : β (poolWDum wPool) = 0) (hQE : β (poolQEnc wPool) = 0)
    (hPairsZ : ∀ k p, β (pairs k p) = 0)
    (hAct : P → ∃ kStar : Fin K, bStar β = kStar ∧
      (∀ k, δ (wSrc k) = if k = kStar then 1 else 0) ∧
      δ = Function.update cl (pairs kStar ⟨0, by decide⟩) 1)
    (hInact : ¬ P → ∀ k, δ (wSrc k) = 0) :
    (Circuit.seq (Circuit.X (poolRDum wPool))
      (seqGatherParity K wSrc (poolRDum wPool) hne)).eval.1.mulVec (ket δ) =
    oneHotOptPreVec (OptBasePred pTrueChi (poolWDum wPool) (poolQEnc wPool))
      (actPoolDum wPool) bStar uLo pairs β 0 (Nat.zero_le 1) := by
  rw [oneHotOptPreVec, ite_eq_left ⟨⟨trivial, hWD, hQE⟩, hPairsZ⟩, eval_seq_mulVec, ket_X, hδRD,
      zero_add]
  set δ₁ := Function.update δ (poolRDum wPool) 1
  by_cases hp : P
  · obtain ⟨kStar, hbEq, h1, hδEq⟩ := hAct hp
    have hβCl : β = cl := hβ.trans (ite_eq_left hp)
    rw [ite_eq_left (show actPoolDum wPool β from hβCl.symm ▸ hClRD), hbEq, hβCl,
        seqGatherParity_mulVec_oneHot K wSrc _ hne δ₁ kStar
          (fun k ↦ (Function.update_of_ne (hne k) 1 δ).trans (h1 k))]
    dsimp only [δ₁]
    rw [Function.update_idem, Function.update_self, CharTwo.add_self_eq_zero,
        update_eq_self_of_zero hδRD, hδEq]
    exact congrArg (fun p ↦ ket (Function.update cl (pairs kStar p) 1)) (Fin.ext rfl)
  · have hβUpd : β = δ₁ := hβ.trans (ite_eq_right hp)
    rw [ite_eq_right (by simp [actPoolDum, hβUpd, δ₁]), hβUpd]
    exact seqGatherParity_mulVec_zero K wSrc _ hne δ₁
      (fun k ↦ (Function.update_of_ne (hne k) 1 δ).trans (hInact hp k))

theorem cGatCohMiniIn_opCoh {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (hR : 0 < R) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    (cGatCohMiniIn hP mOff M hm hMS tOff R ht hClean hRange).eval.1 *
        opCoh mOff M hm hMS wPool r G =
      oneHotOptPreOp (OptBasePred pTrueChi (poolWDum wPool) (poolQEnc wPool))
        (actPoolDum wPool) (bStarCohMini tOff R hR r) (uBit2_2 r)
        (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r) 0 (Nat.zero_le 1) *
        baseCohMiniOp mOff M hm hMS tOff R wPool r G := by
  dsimp only [opCoh, baseCohMiniOp]
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hG fun γ hγ ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  rw [mkVecOp_mulVec_ket, mkVecOp_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket]
  obtain ⟨_, hbEq, _, hWD, hQE, hPairsZ⟩ :=
    baseCohMiniMap_props hP mOff M hm hMS tOff R hR ht hClean hRange hγ
  dsimp only [cGatCohMiniIn]
  refine cohW5_gatIn_ket _ (wCohNode_ne_rDum hP mOff M hm hMS tOff R ht hClean hRange)
    (bStarCohMini tOff R hR r) (uBit2_2 r)
    (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r)
    (cohMap mOff M hm hMS wPool r γ) (cleanPoolB wPool r γ)
    (baseCohMiniMap mOff M hm hMS tOff R wPool r γ) (actRangeCoh tOff R r γ) rfl
    (cohMap_wPool_ge48S_zero hP mOff M hm hMS hγ _ le_rfl)
    (cleanPoolB_wPool_zero hP hγ _) hWD hQE hPairsZ (fun hAct ↦ ?_) (fun hAct k ↦ ?_)
  · have hAct2 := hAct.2
    let kStar : Fin R := ⟨(tStar95 r γ).val - tOff, by omega⟩
    refine ⟨kStar, hbEq.trans (Fin.ext (by
      dsimp [bStarCohMini, kStar]
      omega)), fun k ↦ ?_, ?_⟩
    · rw [cohMap_wCohNode hP mOff M hm hMS hγ, hAct.1]
      refine if_congr ?_ rfl rfl
      rw [Fin.ext_iff, Fin.ext_iff]
      dsimp [kStar]
      omega
    · obtain ⟨_, hmStar, hpStar⟩ := cohW5_tStar95_parts r hγ.1
      have := hRange kStar
      have hkT : kStar.val + tOff = (tStar95 r γ).val := by
        dsimp [kStar]
        omega
      dsimp only [cohMap, pairsCohMini, wCohNode]
      rw [dite_eq_left ⟨hAct.1, by omega, by omega⟩, ite_eq_left rfl]
      refine congrArg (fun w ↦ Function.update (cleanPoolB wPool r γ) w 1)
        (congrArg₂ (pairsCohR1 mOff M hm hMS wPool) (Fin.ext ?_) (Fin.ext ?_))
      all_goals
        dsimp
        rw [hkT]
        omega
  · have hkLt := k.isLt
    rw [cohMap_wCohNode hP mOff M hm hMS hγ]
    split_ifs with htEqK
    · rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
      · exact hH0
      · have hv := congrArg Fin.val htEqK
        dsimp at hv
        exact absurd ⟨hH1, by omega, by omega⟩ hAct
    · rfl

theorem cCopyCohMini_eq {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht1 : 1 ≤ tOff) (hR : 0 < R) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    (cCopyCohMini hP mOff M hm hMS tOff R ht hClean hRange).eval.1 *
        (oneHotOptPreOp (OptBasePred pTrueChi (poolWDum wPool) (poolQEnc wPool))
          (actPoolDum wPool) (bStarCohMini tOff R hR r) (uBit2_2 r)
          (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r) 1 le_rfl *
          baseCohMiniOp mOff M hm hMS tOff R wPool r G) =
      oneHotOptPreOp (OptBasePred pTrueChi (poolWDum wPool) (poolQEnc wPool))
        (actPoolDum wPool) (bStarCohMini tOff R hR r) (uBit2_2 r)
        (pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r) 1 le_rfl *
        baseCohMiniOp mOff M hm hMS tOff R wPool r
          ((uXorPubHiPred (fun t ↦ decide (tOff ≤ t ∧ t < tOff + R)) r).1 * G) := by
  let hOpt := wOptInj_pairsCohMini hP mOff M hm hMS tOff R ht hClean hRange
  let pairs := pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r
  set PRng : ℕ → Bool := fun t ↦ decide (tOff ≤ t ∧ t < tOff + R)
  dsimp only [baseCohMiniOp, uXorPubHiPred]
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hG fun γ hγ ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  dsimp only [oneHotOptPreOp]
  rw [mkVecOp_mulVec_ket, mkVecOp_mulVec_ket, uVecToggle_mulVec_ket,
      mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  dsimp only [oneHotOptPreVec]
  set γ' := vecToggleBits (rCtrlLo r) (pubCtrlHiPred PRng r) γ
  obtain ⟨hActIff, hbβ, hu2β, hWD, hQE, hPairsZ⟩ :=
    baseCohMiniMap_props hP mOff M hm hMS tOff R hR ht hClean hRange hγ
  obtain ⟨hActIff', hbβ', hu2β', hWD', hQE', hPairsZ'⟩ :=
    baseCohMiniMap_props hP mOff M hm hMS tOff R hR ht hClean hRange
      (validPoolCtrl0_vecToggle r wPool hP (pubCtrlHiPred PRng r)
        (fun _ h ↦ pubCtrlHiPred_zero_at_zero PRng r h) hγ)
  set β := baseCohMiniMap mOff M hm hMS tOff R wPool r γ
  set β' := baseCohMiniMap mOff M hm hMS tOff R wPool r γ'
  have hBV {δ} (h1 : δ (poolWDum wPool) = 0) (h2 : δ (poolQEnc wPool) = 0)
      (h3 : ∀ b p, δ (pairs b p) = 0) :
      OptBasePred pTrueChi (poolWDum wPool) (poolQEnc wPool) δ ∧ ∀ b p, δ (pairs b p) = 0 :=
    ⟨⟨trivial, h1, h2⟩, h3⟩
  rw [ite_eq_left (hBV hWD hQE hPairsZ), ite_eq_left (hBV hWD' hQE' hPairsZ')]
  have hβ'Eq : β' = vecToggleBits (rCtrlLo r) (pubCtrlHiPred PRng r) β :=
    wPoolMap_vecToggle hP (baseCohMiniMap mOff M hm hMS tOff R wPool r)
      (baseCohMiniMap_other mOff M hm hMS tOff R wPool r)
      (fun _ _ h ↦ baseCohMiniMap_pool_congr mOff M hm hMS tOff R wPool r h hP)
      (pubCtrlHiPred PRng r) (fun _ _ ↦ pubCtrlHiPred_pub_congr PRng r) γ
  have hPubβ : pubCtrlHiPred PRng r β = pubCtrlHiPred PRng r γ :=
    pubCtrlHiPred_pub_congr PRng r fun w hw ↦
      baseCohMiniMap_other mOff M hm hMS tOff R wPool r γ w (pubCtrlSet_ne_wPool hP hw)
  have hOthγ' (u : Wire n) (hu : ∀ p : Fin 187, u ≠ rCtrlLo r p) : γ' u = γ u :=
    (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ γ).2 u hu
  obtain ⟨_, hHasγ', _, _, _, _, _, hu2γ', htγ'⟩ :=
    cohW5_pub18_congr r fun u hu ↦ hOthγ' _ (cohW5_pub18_ne_ctrlLo r hu)
  have hpHiNz (k : Fin R) : (pHiMini tOff R ht k).val ≠ 0 := by
    dsimp [pHiMini]
    omega
  have hParNeCLo (k : Fin R) (p : Fin 187) : pairs k ⟨0, by decide⟩ ≠ rCtrlLo r p := by
    obtain ⟨idx, _, hEq⟩ := cohW5_miniNode_idx mOff M hm hMS tOff R ht hRange wPool k
    dsimp only [pairs, pairsCohMini]
    rw [ite_eq_left rfl, hEq]
    exact hP.ne_ctrlLo idx p
  have hChNeCLoNz (k : Fin R) (p : Fin 187) (hp : p.val ≠ 0) :
      pairs k ⟨1, by decide⟩ ≠ rCtrlLo r p := poolClean_ne_ctrlLo_nz hP _ p hp
  dsimp only [cCopyCohMini]
  rw [eval_seq_mulVec]
  have hActEq : actRangeCoh tOff R r γ' ↔ actRangeCoh tOff R r γ := by
    dsimp only [actRangeCoh]
    rw [hHasγ', htγ']
  by_cases hAct : actRangeCoh tOff R r γ
  · have hAct2 := hAct.2
    let kStar : Fin R := ⟨(tStar95 r γ).val - tOff, by omega⟩
    let u2 := idxValPrefix (uBit2_2 r) γ 1 le_rfl
    have hu2Lt : u2 < 2 := idxValPrefix_lt_two_pow (uBit2_2 r) γ 1 le_rfl
    have hbγ : bStarCohMini tOff R hR r γ = kStar := Fin.ext (by
      dsimp [bStarCohMini, kStar]
      omega)
    rw [ite_eq_left (hActIff.mpr hAct), ite_eq_left (hActIff'.mpr (hActEq.mpr hAct)),
        hbβ.trans hbγ, hbβ'.trans ((Fin.ext (congrArg (fun t : Fin 95 ↦ min (t.val - tOff) (R - 1))
          htγ')).trans hbγ),
        (Fin.ext hu2β : (⟨idxValPrefix (uBit2_2 r) β 1 le_rfl, _⟩ : Fin (2 ^ 1)) = ⟨u2, hu2Lt⟩),
        (Fin.ext (hu2β'.trans hu2γ') :
          (⟨idxValPrefix (uBit2_2 r) β' 1 le_rfl, _⟩ : Fin (2 ^ 1)) = ⟨u2, hu2Lt⟩)]
    have hIdx2 := idx2_eq_of_tStar95_coh r hγ.1
    have htVal : kStar.val + tOff = (tStar95 r γ).val := by
      dsimp [kStar]
      omega
    have h1p (p : Fin (2 ^ 1)) (k : Fin R) :
        Function.update β (pairs kStar p) 1 (pairs k p) = if k = kStar then 1 else 0 := by
      by_cases hk : k = kStar
      · subst hk
        rw [ite_eq_left rfl, Function.update_self]
      · rw [ite_eq_right hk, Function.update_of_ne fun e ↦ hk (hOpt.w_inj _ _ _ _ e).1]
        exact hPairsZ k p
    have h0q (p q : Fin (2 ^ 1)) (hpq : q ≠ p) (k : Fin R) :
        Function.update β (pairs kStar p) 1 (pairs k q) = 0 :=
      (Function.update_of_ne (fun e ↦ hpq (hOpt.w_inj _ _ _ _ e).2) 1 β).trans (hPairsZ k q)
    have hFinish (wStar : Wire n) (pStar : Fin 187) (hwNeStar : wStar ≠ rCtrlLo r pStar)
        (hpStarVal : pStar.val = idxValD (rIdx2 r) γ) :
        ket (Function.update (Function.update β wStar 1) (rCtrlLo r pStar)
          (Function.update β wStar 1 (rCtrlLo r pStar) + 1)) =
          ket (Function.update β' wStar 1) := by
      rw [hβ'Eq, Function.update_of_ne hwNeStar.symm, Function.update_comm hwNeStar]
      refine congrArg (fun f ↦ ket (Function.update f wStar 1))
        (cohW5_upd_eq_vecToggle r β β pStar _ _ ?_ ?_ fun _ _ ↦ rfl)
      · rw [hPubβ]
        dsimp only [pubCtrlHiPred, PRng, pubCtrlHi]
        rw [tOfIdx187_of_eq_idx2_coh r hγ.1 hpStarVal, ite_eq_left (decide_eq_true hAct.2),
            cond_nat_beq, ite_eq_left hpStarVal, hAct.1]
      · intro p hpEq
        rw [hPubβ]
        dsimp only [pubCtrlHiPred, pubCtrlHi]
        rw [cond_nat_beq, ite_eq_right (fun e ↦ hpEq (Fin.ext (Eq.trans e hpStarVal.symm))),
            ite_self, add_zero]
    by_cases hu2_0 : u2 = 0
    · rw [(Fin.ext hu2_0 : (⟨u2, hu2Lt⟩ : Fin (2 ^ 1)) = ⟨0, by decide⟩),
          seqCnotVec_mulVec_oneHot R _ _ _ (fun k₁ _ ↦ by exact hParNeCLo k₁ _) _ kStar
            (fun k ↦ by exact h1p ⟨0, by decide⟩ k),
          seqCnotVec_mulVec_zero R _ _ _ _ (fun k ↦ by
            exact (Function.update_of_ne (hChNeCLoNz k _ (by
              dsimp [pLoMini]
              omega)) _ _).trans (h0q ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) k))]
      exact hFinish (pairs kStar ⟨0, by decide⟩) (pLoMini tOff R ht kStar) (hParNeCLo kStar _) (by
        dsimp [pLoMini]
        rw [htVal, hIdx2]
        dsimp [u2] at hu2_0
        omega)
    · have hu2_1 : u2 = 1 := by omega
      rw [(Fin.ext hu2_1 : (⟨u2, hu2Lt⟩ : Fin (2 ^ 1)) = ⟨1, by decide⟩),
          seqCnotVec_mulVec_zero R _ _ _ _
            (fun k ↦ by exact h0q ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide) k),
          seqCnotVec_mulVec_oneHot R _ _ _ (fun k₁ k₂ ↦ by exact hChNeCLoNz k₁ _ (hpHiNz k₂)) _
            kStar (fun k ↦ by exact h1p ⟨1, by decide⟩ k)]
      exact hFinish (pairs kStar ⟨1, by decide⟩) (pHiMini tOff R ht kStar)
        (hChNeCLoNz kStar _ (hpHiNz kStar)) (by
          dsimp [pHiMini]
          rw [htVal, hIdx2]
          dsimp [u2] at hu2_1
          omega)
  · rw [ite_eq_right (fun hb ↦ hAct (hActIff.mp hb)),
        ite_eq_right (fun hb ↦ hAct (hActEq.mp (hActIff'.mp hb))),
        seqCnotVec_mulVec_zero R _ _ _ β (fun k ↦ by exact hPairsZ k ⟨0, by decide⟩),
        seqCnotVec_mulVec_zero R _ _ _ β (fun k ↦ by exact hPairsZ k ⟨1, by decide⟩), hβ'Eq]
    refine congrArg ket (cohW5_ctrlLo_ext r (fun p ↦ ?_)
      (fun u nL ↦ ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ β).2 u nL).symm))
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ β).1 p, hPubβ]
    dsimp only [pubCtrlHiPred, PRng, pubCtrlHi]
    rw [cond_nat_beq]
    rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
    · rw [hH0]
      split_ifs <;> simp
    · rw [hH1]
      by_cases hIn : tOff ≤ tOfIdx187 p ∧ tOfIdx187 p < tOff + R
      · rw [ite_eq_left (decide_eq_true hIn), ite_eq_right (fun hpEq ↦ by
          have := tOfIdx187_of_eq_idx2_coh r hγ.1 hpEq
          exact hAct ⟨hH1, by omega, by omega⟩), add_zero]
      · rw [ite_eq_right (by simp [hIn]), add_zero]

theorem cohW5_eval_X_mul_self {n : ℕ} (w : Wire n) :
    (Circuit.X w).eval.1 * (Circuit.X w).eval.1 = 1 := by
  refine matrix_ext_ket fun δ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_idem, Function.update_self,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec]

theorem cohW5_gat_inv {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ k, wSrc k ≠ t) :
    (Circuit.seq (seqGatherParity K wSrc t hne) (Circuit.X t)).eval.1 *
      (Circuit.seq (Circuit.X t) (seqGatherParity K wSrc t hne)).eval.1 = 1 := by
  rw [eval_seq_eq, eval_seq_eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc (seqGatherParity K wSrc t hne).eval.1,
      eval_seqGatherParity_mul_self K wSrc t hne, Matrix.one_mul]
  exact cohW5_eval_X_mul_self t

theorem subspaceStep_pCohMiniPass {Var : Type} [Fintype Var] [DecidableEq Var] {S n : ℕ}
    (v : Var) {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (tOff R : ℕ) (ht1 : 1 ≤ tOff) (hR : 0 < R) (ht : tOff + R ≤ 92) (hClean : M + R ≤ S + 1)
    (hRange : ∀ k : Fin R,
      mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M)
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    SubspaceStep (Var := Var)
      (opCoh mOff M hm hMS wPool r G)
      (opCoh mOff M hm hMS wPool r
        ((uXorPubHiPred (fun t ↦ decide (tOff ≤ t ∧ t < tOff + R)) r).1 * G))
      (pCohMiniPass v hP mOff M hm hMS tOff R ht hClean hRange) := by
  let hOpt := wOptInj_pairsCohMini hP mOff M hm hMS tOff R ht hClean hRange
  let PBase := OptBasePred (@pTrueChi n) (poolWDum wPool) (poolQEnc wPool)
  let pairs := pairsCohMini mOff M hm hMS tOff R ht hClean hRange wPool r
  let PRng : ℕ → Bool := fun t ↦ decide (tOff ≤ t ∧ t < tOff + R)
  let G' := (uXorPubHiPred PRng r).1 * G
  unfold pCohMiniPass
  exact (subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) _
      (cGatCohMiniIn hP mOff M hm hMS tOff R ht hClean hRange))
    (cGatCohMiniIn_opCoh hP mOff M hm hMS tOff R hR ht hClean hRange G hG)).seq
    ((subspaceStep_mul_right (baseCohMiniOp mOff M hm hMS tOff R wPool r G)
      (subspaceStep_wLastSplitShiftDyn v pTrueChi (actPoolDum wPool) (bStarCohMini tOff R hR r)
        (uBit2_2 r) pairs (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) hOpt
        (fun δ _ ↦ by
          rcases DynCircExt.bit_cases (δ (poolRDum wPool)) with h | h <;>
            simp [actPoolDum, h]))).seq
      ((subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var) _
          (cCopyCohMini hP mOff M hm hMS tOff R ht hClean hRange))
        (cCopyCohMini_eq hP mOff M hm hMS tOff R ht1 hR ht hClean hRange G hG)).seq
        ((subspaceStep_congr_out
          (subspaceStep_mul_right (baseCohMiniOp mOff M hm hMS tOff R wPool r G')
            (subspaceStep_wUncompTreeDyn_id_opt v PBase (actPoolDum wPool)
              (bStarCohMini tOff R hR r) (uBit2_2 r) pairs hOpt.w_inj hOpt.uLo_ne_w))
          (cGatCohMiniIn_opCoh hP mOff M hm hMS tOff R hR ht hClean hRange G'
            (supportedOn_validPoolCtrl0_uVecToggle r wPool hP (pubCtrlHiPred PRng r) _
              (fun _ h ↦ pubCtrlHiPred_zero_at_zero PRng r h) G hG)).symm).seq
          (subspaceStep_congr_out
            (subspaceStep_of_circuit (Var := Var) _
              (cGatCohMiniOut hP mOff M hm hMS tOff R ht hClean hRange))
            (by
              dsimp only [cGatCohMiniOut, cGatCohMiniIn]
              rw [← Matrix.mul_assoc, cohW5_gat_inv R _ _ _, Matrix.one_mul])))))

/-! ### 6. Batch Round-1 Wrapper (`pCohWrap`, `2 * M + 2` `T`) -/

def bStarCohWrap {n : ℕ} (mOff M : ℕ) (hM : 0 < M) (r : RouterReg 187 8 n)
    (δ : BitAssignment n) : Fin M :=
  ⟨min (mValCoh r δ - mOff) (M - 1), by omega⟩

def baseCohWrapMap {S n : ℕ} (mOff M : ℕ) (wPool : Fin (51 + S) → Wire n)
    (r : RouterReg 187 8 n) (γ : BitAssignment n) : BitAssignment n :=
  if actCohPred mOff M r γ then cleanPoolB wPool r γ
  else Function.update (r0Map wPool r γ) (poolRDum wPool) 1

def baseCohWrapOp {S n : ℕ} (mOff M : ℕ) (wPool : Fin (51 + S) → Wire n)
    (r : RouterReg 187 8 n) (X : Operator (2 ^ n)) : Operator (2 ^ n) :=
  mkVecOp (fun γ ↦ ket (baseCohWrapMap mOff M wPool r γ)) * X

theorem baseCohWrapMap_props {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hM : 0 < M) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    {γ : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) :
    let β := baseCohWrapMap mOff M wPool r γ
    (actPoolDum wPool β ↔ actCohPred mOff M r γ) ∧
    bStarCohWrap mOff M hM r β = bStarCohWrap mOff M hM r γ ∧
    idxValPrefix (uBit1_2 r) β 1 le_rfl = idxValPrefix (uBit1_2 r) γ 1 le_rfl ∧
    β (poolWDum wPool) = 0 ∧
    β (poolQEnc wPool) = 0 ∧
    (∀ k p, β (pairsCohR1 mOff M hm hMS wPool k p) = 0) := by
  intro β
  obtain ⟨_, _, _, _, hHi, hu0, hu1, _, _⟩ :=
    cohW5_pub18_congr (α := β) (β := γ) r fun u hu ↦ by
    have hn := pubCtrlSet_ne_wPool hP ⟨u, hu, rfl⟩
    dsimp only [β, baseCohWrapMap]
    split_ifs
    · exact cleanPoolB_other wPool r γ _ hn
    · exact (Function.update_of_ne (hn _) 1 _).trans (r0Map_other wPool r γ _ hn)
  obtain ⟨hActIff, hWD, hQE⟩ := cohW5_actPoolDum_props hP hγ (actCohPred mOff M r γ) rfl
    fun i hi ↦ r0Map_wPool_ge48_zero hP hγ i (by omega)
  refine ⟨hActIff, Fin.ext (by
    dsimp [bStarCohWrap, mValCoh]
    rw [hHi, hu0]), hu1, hWD, hQE, fun k p ↦ ?_⟩
  have hOpt := wOptInj_pairsCohR1 hP mOff M hm hMS
  dsimp only [β, baseCohWrapMap]
  split_ifs with hAct
  · obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool k p
    exact hEq ▸ cleanPoolB_wPool_zero hP hγ idx
  · rw [Function.update_of_ne (hOpt.w_ne_rDum k p)]
    dsimp only [pairsCohR1]
    split_ifs with hp0
    · rw [r0Map_r1RootPool hP hγ]
      split_ifs with hmK
      · rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
        · exact hH0
        · dsimp at hmK
          have := k.isLt
          exact absurd ⟨hH1, by omega, by omega⟩ hAct
      · rfl
    · exact r0Map_wPool_ge48_zero hP hγ _ (Nat.le_add_right 48 k.val)

theorem r1RootPool_ne_rDum {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) (k : Fin M) :
    r1RootPool wPool ⟨mOff + k.val, by
      have := k.isLt
      omega⟩ ≠ poolRDum wPool :=
  (wOptInj_pairsCohR1 hP mOff M hm hMS).w_ne_rDum k ⟨0, by decide⟩

def cGatCohIn {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) : Circuit n :=
  Circuit.seq (Circuit.X (poolRDum wPool))
    (seqGatherParity M (fun k ↦ r1RootPool wPool ⟨mOff + k.val, by
        have := k.isLt
        omega⟩)
      (poolRDum wPool)
      (r1RootPool_ne_rDum hP mOff M hm hMS))

def cGatCohOut {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) : Circuit n :=
  Circuit.seq
    (seqGatherParity M (fun k ↦ r1RootPool wPool ⟨mOff + k.val, by
        have := k.isLt
        omega⟩)
      (poolRDum wPool)
      (r1RootPool_ne_rDum hP mOff M hm hMS))
    (Circuit.X (poolRDum wPool))

def cScrubRDum2M {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) : Circuit n :=
  let hOpt := wOptInj_pairsCohR1 hP mOff M hm hMS
  Circuit.seq (Circuit.X (poolRDum wPool))
    (Circuit.seq
      (seqGatherParity M (fun k ↦ pairsCohR1 mOff M hm hMS wPool k ⟨0, by decide⟩)
        (poolRDum wPool) (fun k ↦ hOpt.w_ne_rDum k ⟨0, by decide⟩))
      (seqGatherParity M (fun k ↦ pairsCohR1 mOff M hm hMS wPool k ⟨1, by decide⟩)
        (poolRDum wPool) (fun k ↦ hOpt.w_ne_rDum k ⟨1, by decide⟩)))

def cRestRDum2M {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) : Circuit n :=
  let hOpt := wOptInj_pairsCohR1 hP mOff M hm hMS
  Circuit.seq
    (seqGatherParity M (fun k ↦ pairsCohR1 mOff M hm hMS wPool k ⟨1, by decide⟩)
      (poolRDum wPool) (fun k ↦ hOpt.w_ne_rDum k ⟨1, by decide⟩))
    (Circuit.seq
      (seqGatherParity M (fun k ↦ pairsCohR1 mOff M hm hMS wPool k ⟨0, by decide⟩)
        (poolRDum wPool) (fun k ↦ hOpt.w_ne_rDum k ⟨0, by decide⟩))
      (Circuit.X (poolRDum wPool)))

/-- Batch Round-1 wrapper expanding `[mOff, mOff + M)` around `body` (`2 * M + 2 + body.T`). -/
def pCohWrap {Var : Type} {S n : ℕ} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let hOpt := wOptInj_pairsCohR1 hP mOff M hm hMS
  .seq (.circuit (cGatCohIn hP mOff M hm hMS))
    (.seq (wLastSplitShiftDyn v M 0 (uBit1_2 r) (pairsCohR1 mOff M hm hMS wPool)
        (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) hOpt)
      (.seq (.circuit (cScrubRDum2M hP mOff M hm hMS))
        (.seq body
          (.seq (.circuit (cRestRDum2M hP mOff M hm hMS))
            (.seq (wUncompTreeDyn v M 1 (uBit1_2 r) (pairsCohR1 mOff M hm hMS wPool)
                hOpt.w_inj hOpt.uLo_ne_w (.circuit .identity) 1 le_rfl)
              (.circuit (cGatCohOut hP mOff M hm hMS)))))))

theorem count_pCohWrap {Var : Type} {S n : ℕ} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) (body : DynamicCircuit Var n) :
    (pCohWrap v hP mOff M hm hMS body).count .T = 2 * M + 2 + body.count .T ∧
    (pCohWrap v hP mOff M hm hMS body).count .TOFF = body.count .TOFF := by
  let hOpt := wOptInj_pairsCohR1 hP mOff M hm hMS
  obtain ⟨tl, fl⟩ := count_wLastSplitShiftDyn v M 0 (uBit1_2 r) (pairsCohR1 mOff M hm hMS wPool)
    (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) hOpt
  obtain ⟨tu, fu⟩ := count_wUncompTreeDyn_opt v M 1 (uBit1_2 r) (pairsCohR1 mOff M hm hMS wPool)
    hOpt.w_inj hOpt.uLo_ne_w (.circuit .identity) 1 le_rfl
  unfold pCohWrap
  dsimp only [DynamicCircuit.count]
  rw [tl, fl, tu, fu]
  constructor <;> simp [cGatCohIn, cGatCohOut, cScrubRDum2M, cRestRDum2M, DynamicCircuit.count,
    Circuit.count_seq, Circuit.X, count_seqGatherParity_t, count_seqGatherParity_toff]

theorem dynWires_pCohWrap {Var : Type} {S n : ℕ} {Sw : Wire n → Prop} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (body : DynamicCircuit Var n) (hBody : DynWires Sw body)
    (hI3 : ∀ d : Fin 3, Sw (idxLo3_2 r d)) (hPool : ∀ i : Fin (51 + S), Sw (wPool i)) :
    DynWires Sw (pCohWrap v hP mOff M hm hMS body) := by
  have hwPairs (k : Fin M) (p : Fin (2 ^ 1)) : Sw (pairsCohR1 mOff M hm hMS wPool k p) := by
    obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool k p
    exact hEq ▸ hPool idx
  have hwRoot (k : Fin M) : Sw (r1RootPool wPool ⟨mOff + k.val, by
      have := k.isLt
      omega⟩) := hwPairs k ⟨0, by decide⟩
  exact ⟨⟨cw_1 (hPool _), cw_seqGatherParity M _ _ _ hwRoot (hPool _)⟩,
    dw_wLastSplitShiftDyn v M 0 _ _ _ _ _ _ (fun _ ↦ hI3 _) hwPairs (hPool _) (hPool _) (hPool _),
    ⟨cw_1 (hPool _), cw_seqGatherParity M _ _ _ (fun k ↦ hwPairs k ⟨0, by decide⟩) (hPool _),
      cw_seqGatherParity M _ _ _ (fun k ↦ hwPairs k ⟨1, by decide⟩) (hPool _)⟩, hBody,
    ⟨cw_seqGatherParity M _ _ _ (fun k ↦ hwPairs k ⟨1, by decide⟩) (hPool _),
      cw_seqGatherParity M _ _ _ (fun k ↦ hwPairs k ⟨0, by decide⟩) (hPool _), cw_1 (hPool _)⟩,
    dw_wUncompTreeDyn_opt v M 1 _ _ _ _ (fun _ ↦ hI3 _) hwPairs
      (rest := .circuit .identity) trivial 1 le_rfl,
    ⟨cw_seqGatherParity M _ _ _ hwRoot (hPool _), cw_1 (hPool _)⟩⟩

theorem cGatCohIn_opR0 {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hM : 0 < M) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    (cGatCohIn hP mOff M hm hMS).eval.1 * opR0 wPool r G =
      oneHotOptPreOp (OptBasePred pTrueChi (poolWDum wPool) (poolQEnc wPool))
        (actPoolDum wPool) (bStarCohWrap mOff M hM r) (uBit1_2 r)
        (pairsCohR1 mOff M hm hMS wPool) 0 (Nat.zero_le 1) *
        baseCohWrapOp mOff M wPool r G := by
  dsimp only [opR0, baseCohWrapOp]
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hG fun γ hγ ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  rw [mkVecOp_mulVec_ket, mkVecOp_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket]
  obtain ⟨_, hbEq, _, hWD, hQE, hPairsZ⟩ := baseCohWrapMap_props hP mOff M hM hm hMS hγ
  dsimp only [cGatCohIn]
  refine cohW5_gatIn_ket _ (r1RootPool_ne_rDum hP mOff M hm hMS)
    (bStarCohWrap mOff M hM r) (uBit1_2 r) (pairsCohR1 mOff M hm hMS wPool)
    (r0Map wPool r γ) (cleanPoolB wPool r γ) (baseCohWrapMap mOff M wPool r γ)
    (actCohPred mOff M r γ) rfl
    (r0Map_wPool_ge48_zero hP hγ ⟨48 + S, by omega⟩ (Nat.le_add_right 48 S))
    (cleanPoolB_wPool_zero hP hγ _) hWD hQE hPairsZ (fun hAct ↦ ?_) (fun hAct k ↦ ?_)
  · have hmBounds := hAct.2
    let kStar : Fin M := ⟨mValCoh r γ - mOff, by omega⟩
    refine ⟨kStar, hbEq.trans (Fin.ext (by
      dsimp [bStarCohWrap, kStar]
      omega)), fun k ↦ ?_, ?_⟩
    · rw [r0Map_r1RootPool hP hγ, hAct.1]
      refine if_congr ?_ rfl rfl
      rw [Fin.ext_iff]
      dsimp [kStar]
      omega
    · have hq24 := idxHi5_2_lt24_of_lt187 r hγ.1
      have hu0Lt := idxValPrefix_lt_two_pow (uBit0_2 r) γ 1 le_rfl
      dsimp only [mValCoh] at hmBounds
      dsimp only [r0Map, pairsCohR1]
      rw [hAct.1, ite_eq_left (rfl : (⟨0, by decide⟩ : Fin (2 ^ 1)).val = 0), r1RootPool_eq_wR0Pool]
      refine congrArg (fun w ↦ Function.update (cleanPoolB wPool r γ) w 1)
        (congrArg₂ (wR0Pool wPool) (Fin.ext ?_) (Fin.ext ?_))
      all_goals
        dsimp [kStar, mValCoh]
        omega
  · rw [r0Map_r1RootPool hP hγ]
    split_ifs with hmK
    · rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
      · exact hH0
      · dsimp at hmK
        have := k.isLt
        exact absurd ⟨hH1, by omega, by omega⟩ hAct
    · rfl

theorem cScrubRDum2M_eq {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hM : 0 < M) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    (G : Operator (2 ^ n)) (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    (cScrubRDum2M hP mOff M hm hMS).eval.1 *
        (oneHotOptPreOp (OptBasePred pTrueChi (poolWDum wPool) (poolQEnc wPool))
          (actPoolDum wPool) (bStarCohWrap mOff M hM r) (uBit1_2 r)
          (pairsCohR1 mOff M hm hMS wPool) 1 le_rfl *
          baseCohWrapOp mOff M wPool r G) =
      opCoh mOff M hm hMS wPool r G := by
  let hOpt := wOptInj_pairsCohR1 hP mOff M hm hMS
  dsimp only [baseCohWrapOp, opCoh, oneHotOptPreOp]
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hG fun γ hγ ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  rw [mkVecOp_mulVec_ket, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  dsimp only [oneHotOptPreVec]
  obtain ⟨hActIff, hbEq, hu1Eq, hWD, hQE, hPairsZ⟩ := baseCohWrapMap_props hP mOff M hM hm hMS hγ
  set β := baseCohWrapMap mOff M wPool r γ
  rw [ite_eq_left ⟨⟨trivial, hWD, hQE⟩, hPairsZ⟩]
  dsimp only [cScrubRDum2M]
  rw [eval_seq_mulVec, eval_seq_mulVec]
  by_cases hAct : actCohPred mOff M r γ
  · have hmBounds := hAct.2
    rw [ite_eq_left (hActIff.mpr hAct), hbEq]
    dsimp only [cohMap]
    rw [dite_eq_left hAct]
    let kStar : Fin M := ⟨mValCoh r γ - mOff, by omega⟩
    let u1 := idxValPrefix (uBit1_2 r) γ 1 le_rfl
    have hu1Lt : u1 < 2 := idxValPrefix_lt_two_pow (uBit1_2 r) γ 1 le_rfl
    rw [show bStarCohWrap mOff M hM r γ = kStar from Fin.ext (by
          dsimp [bStarCohWrap, kStar]
          omega),
        show (⟨idxValPrefix (uBit1_2 r) β 1 le_rfl,
            idxValPrefix_lt_two_pow _ _ 1 le_rfl⟩ : Fin (2 ^ 1)) = ⟨u1, hu1Lt⟩ from
          Fin.ext hu1Eq,
        show β = cleanPoolB wPool r γ from by
          dsimp only [β, baseCohWrapMap]
          exact ite_eq_left hAct]
    let wStar := pairsCohR1 mOff M hm hMS wPool kStar ⟨u1, hu1Lt⟩
    have hXRD : Function.update (cleanPoolB wPool r γ) wStar 1 (poolRDum wPool) = 0 :=
      (Function.update_of_ne (hOpt.w_ne_rDum kStar ⟨u1, hu1Lt⟩).symm 1 _).trans
        (cleanPoolB_wPool_zero hP hγ _)
    rw [ket_X, hXRD, zero_add]
    let η := Function.update (Function.update (cleanPoolB wPool r γ) wStar 1) (poolRDum wPool) 1
    have h1p (p : Fin (2 ^ 1)) (hp : (⟨u1, hu1Lt⟩ : Fin (2 ^ 1)) = p) (k : Fin M) :
        η (pairsCohR1 mOff M hm hMS wPool k p) = if k = kStar then 1 else 0 := by
      dsimp only [η, wStar]
      rw [hp, Function.update_of_ne (hOpt.w_ne_rDum k _)]
      by_cases hk : k = kStar
      · subst hk
        rw [ite_eq_left rfl, Function.update_self]
      · rw [ite_eq_right hk, Function.update_of_ne (fun e ↦ hk (hOpt.w_inj _ _ _ _ e).1)]
        obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool k p
        exact hEq ▸ cleanPoolB_wPool_zero hP hγ idx
    have h0base (q : Fin (2 ^ 1)) (hq : q ≠ ⟨u1, hu1Lt⟩) (k : Fin M) :
        Function.update (cleanPoolB wPool r γ) wStar 1
          (pairsCohR1 mOff M hm hMS wPool k q) = 0 := by
      rw [Function.update_of_ne (fun e ↦ hq (hOpt.w_inj _ _ _ _ e).2)]
      obtain ⟨idx, _, hEq⟩ := pairsCohR1_idx mOff M hm hMS wPool k q
      exact hEq ▸ cleanPoolB_wPool_zero hP hγ idx
    have hηClr : Function.update η (poolRDum wPool) (η (poolRDum wPool) + 1) =
        Function.update (cleanPoolB wPool r γ) wStar 1 := by
      dsimp only [η]
      rw [Function.update_idem, Function.update_self, CharTwo.add_self_eq_zero,
          update_eq_self_of_zero hXRD]
    by_cases hu1_0 : u1 = 0
    · have hp0 : (⟨u1, hu1Lt⟩ : Fin (2 ^ 1)) = ⟨0, by decide⟩ := Fin.ext hu1_0
      rw [seqGatherParity_mulVec_oneHot M _ _ _ η kStar (h1p _ hp0), hηClr]
      exact seqGatherParity_mulVec_zero M _ _ _ _
        (h0base ⟨1, by decide⟩ fun e ↦ absurd (e.trans hp0) (by decide))
    · have hp1 : (⟨u1, hu1Lt⟩ : Fin (2 ^ 1)) = ⟨1, by decide⟩ := Fin.ext (by omega : u1 = 1)
      rw [seqGatherParity_mulVec_zero M _ _ _ η (fun k ↦
            (Function.update_of_ne (hOpt.w_ne_rDum k _) 1 _).trans
              (h0base ⟨0, by decide⟩ (fun e ↦ absurd (e.trans hp1) (by decide)) k)),
          seqGatherParity_mulVec_oneHot M _ _ _ η kStar (h1p _ hp1), hηClr]
  · have hβEq : β = Function.update (r0Map wPool r γ) (poolRDum wPool) 1 := ite_eq_right hAct
    have hZ (p : Fin (2 ^ 1)) (k : Fin M) :
        r0Map wPool r γ (pairsCohR1 mOff M hm hMS wPool k p) = 0 :=
      (Function.update_of_ne (hOpt.w_ne_rDum k p) 1 _).symm.trans (hβEq ▸ hPairsZ k p)
    rw [ite_eq_right (fun hb ↦ hAct (hActIff.mp hb))]
    dsimp only [cohMap]
    rw [dite_eq_right hAct, hβEq, ket_X, Function.update_self, CharTwo.add_self_eq_zero,
        Function.update_idem,
        update_eq_self_of_zero (r0Map_wPool_ge48_zero hP hγ _ (Nat.le_add_right 48 S)),
        seqGatherParity_mulVec_zero M _ _ _ _ (hZ ⟨0, by decide⟩),
        seqGatherParity_mulVec_zero M _ _ _ _ (hZ ⟨1, by decide⟩)]

theorem subspaceStep_pCohWrap {Var : Type} [Fintype Var] [DecidableEq Var] {S n : ℕ}
    (v : Var) {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hM : 0 < M) (hm : mOff + M ≤ 47) (hMS : M ≤ S)
    {G_in G_out : Operator (2 ^ n)}
    (hGin : SupportedOn (ValidCHiPoolCtrl0 r wPool) G_in)
    (hGout : SupportedOn (ValidCHiPoolCtrl0 r wPool) G_out)
    {body : DynamicCircuit Var n}
    (hBody : SubspaceStep (Var := Var)
      (opCoh mOff M hm hMS wPool r G_in) (opCoh mOff M hm hMS wPool r G_out) body) :
    SubspaceStep (Var := Var)
      (opR0 wPool r G_in) (opR0 wPool r G_out)
      (pCohWrap v hP mOff M hm hMS body) := by
  let hOpt := wOptInj_pairsCohR1 hP mOff M hm hMS
  let PBase := OptBasePred (@pTrueChi n) (poolWDum wPool) (poolQEnc wPool)
  let pairs := pairsCohR1 mOff M hm hMS wPool
  have cancelL {A B X Y : Operator (2 ^ n)} (hInv : A * B = 1) (hEq : B * Y = X) : A * X = Y := by
    rw [← hEq, ← Matrix.mul_assoc, hInv, Matrix.one_mul]
  unfold pCohWrap
  exact (subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) _ (cGatCohIn hP mOff M hm hMS))
    (cGatCohIn_opR0 hP mOff M hM hm hMS G_in hGin)).seq
    ((subspaceStep_mul_right (baseCohWrapOp mOff M wPool r G_in)
      (subspaceStep_wLastSplitShiftDyn v pTrueChi (actPoolDum wPool) (bStarCohWrap mOff M hM r)
        (uBit1_2 r) pairs (poolRDum wPool) (poolWDum wPool) (poolQEnc wPool) hOpt
        (fun δ _ ↦ by
          rcases DynCircExt.bit_cases (δ (poolRDum wPool)) with h | h <;>
            simp [actPoolDum, h]))).seq
      ((subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var) _ (cScrubRDum2M hP mOff M hm hMS))
        (cScrubRDum2M_eq hP mOff M hM hm hMS G_in hGin)).seq
        (hBody.seq
          ((subspaceStep_congr_out
            (subspaceStep_of_circuit (Var := Var) _ (cRestRDum2M hP mOff M hm hMS))
            (cancelL (by
              dsimp only [cRestRDum2M, cScrubRDum2M]
              simp only [eval_seq_eq, Matrix.mul_assoc]
              rw [← Matrix.mul_assoc
                    (seqGatherParity M (fun k ↦ pairs k ⟨1, by decide⟩) _ _).eval.1,
                  eval_seqGatherParity_mul_self, Matrix.one_mul,
                  ← Matrix.mul_assoc
                    (seqGatherParity M (fun k ↦ pairs k ⟨0, by decide⟩) _ _).eval.1,
                  eval_seqGatherParity_mul_self, Matrix.one_mul, cohW5_eval_X_mul_self])
              (cScrubRDum2M_eq hP mOff M hM hm hMS G_out hGout))).seq
            ((subspaceStep_congr_out
              (subspaceStep_mul_right (baseCohWrapOp mOff M wPool r G_out)
                (subspaceStep_wUncompTreeDyn_id_opt v PBase (actPoolDum wPool)
                  (bStarCohWrap mOff M hM r) (uBit1_2 r) pairs hOpt.w_inj hOpt.uLo_ne_w))
              (cGatCohIn_opR0 hP mOff M hM hm hMS G_out hGout).symm).seq
              (subspaceStep_congr_out
                (subspaceStep_of_circuit (Var := Var) _ (cGatCohOut hP mOff M hm hMS))
                (cancelL (Y := opR0 wPool r G_out) (by
                  dsimp only [cGatCohOut, cGatCohIn]
                  exact cohW5_gat_inv M _ _ _) rfl)))))))

/-! ### 7. Outer Round-0 & `rCtrlLo[0]` Wrapper (`pCHiOuterWrap`, `48 + body.T`) -/

theorem seqGatherParity_mulVec_sum {n : ℕ} :
    ∀ (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n) (hne : ∀ i, wSrc i ≠ t) (δ : BitAssignment n),
      (seqGatherParity K wSrc t hne).eval.1.mulVec (ket δ) =
        ket (Function.update δ t (δ t + ∑ i : Fin K, δ (wSrc i)))
  | 0, _, t, _, δ => by
      simp only [seqGatherParity, seqNat, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec, Fin.sum_univ_zero, add_zero, Function.update_eq_self]
  | K + 1, wSrc, t, hne, δ => by
      dsimp only [seqGatherParity]
      rw [seqNat, eval_seq_mulVec]
      change (Circuit.CNOT (wSrc (Fin.last K)) t (hne (Fin.last K))).eval.1.mulVec
          ((seqGatherParity K (fun j ↦ wSrc j.castSucc) t (fun j ↦ hne j.castSucc)).eval.1.mulVec
            (ket δ)) = _
      rw [seqGatherParity_mulVec_sum K _ t _ δ, ket_CNOT, Function.update_idem,
          Function.update_self, Function.update_of_ne (hne (Fin.last K)), Fin.sum_univ_castSucc,
          add_assoc]

abbrev ctrlLoNz {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 186) : Wire n :=
  rCtrlLo r k.succ

theorem ctrlLoNz_ne_zero {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 186) :
    ctrlLoNz r k ≠ rCtrlLo r ⟨0, by decide⟩ :=
  rCtrlLo_inj_ne r k.succ ⟨0, by decide⟩ (Fin.succ_ne_zero k)

theorem rHas1_ne_rCtrlLo0 {n : ℕ} (r : RouterReg 187 8 n) :
    rHas1 r ≠ rCtrlLo r ⟨0, by decide⟩ :=
  cohW5_pub18_ne_ctrlLo r (u := ⟨0, rw_lt0 187 8⟩) (by decide) _

def cScrubCtrlLo0 {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
  Circuit.seq (Circuit.CNOT (rHas1 r) (rCtrlLo r ⟨0, by decide⟩) (rHas1_ne_rCtrlLo0 r))
    (seqGatherParity 186 (ctrlLoNz r) (rCtrlLo r ⟨0, by decide⟩) (ctrlLoNz_ne_zero r))

def cRestoreCtrlLo0 {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
  Circuit.seq (Circuit.CNOT (rHas1 r) (rCtrlLo r ⟨0, by decide⟩) (rHas1_ne_rCtrlLo0 r))
    (Circuit.seq (Circuit.CNOT (rRawHas2 r) (rCtrlLo r ⟨0, by decide⟩) (rRawHas2_ne_rCtrlLo r _))
      (seqGatherParity 186 (ctrlLoNz r) (rCtrlLo r ⟨0, by decide⟩) (ctrlLoNz_ne_zero r)))

def pubCtrlLoNo0 {n : ℕ} (r : RouterReg 187 8 n) (α : BitAssignment n)
    (p : Fin 187) : ZMod 2 :=
  if p.val = 0 then 0 else pubCtrlLo r α p

def uXorPubLoNo0 {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
  uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r) (pubCtrlLoNo0 r)
    (fun _ _ hEq ↦ funext fun p ↦ by
      dsimp only [pubCtrlLoNo0]
      rw [congrFun (pubCtrl_congr r fun w ⟨u, hu, hw⟩ ↦ hw ▸
        hEq (r u) fun q ↦ rr_ne r (by
            have := q.isLt
            dsimp [rCtrlLo]
            rw [bp187_eq]
            omega)).1 p])

theorem cohW5_sum_cond_beq {idx : ℕ} (h : idx < 187) (v : ZMod 2) :
    ∑ p : Fin 187, cond (Nat.beq p.val idx) v 0 = v := by
  rw [Finset.sum_eq_single ⟨idx, h⟩]
  · exact (cond_nat_beq _ _ _ _).trans (ite_eq_left rfl)
  · exact fun _ _ hne ↦ (cond_nat_beq _ _ _ _).trans (ite_eq_right fun e ↦ hne (Fin.ext e))
  · exact fun habs ↦ (habs (Finset.mem_univ _)).elim

theorem sum_pubCtrlLo_eq {n : ℕ} (r : RouterReg 187 8 n) {α : BitAssignment n}
    (hlt1 : idxValD (rIdx1 r) α < 187) :
    ∑ p : Fin 187, pubCtrlLo r α p = α (rHas1 r) :=
  cohW5_sum_cond_beq hlt1 _

theorem sum_pubCtrlHi_eq {n : ℕ} (r : RouterReg 187 8 n) {α : BitAssignment n}
    (hlt2 : idxValD (rIdx2 r) α < 187) :
    ∑ p : Fin 187, pubCtrlHi r α p = α (rRawHas2 r) :=
  cohW5_sum_cond_beq hlt2 _

theorem cScrubCtrlLo0_eq {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} {R_mid : Operator (2 ^ n)}
    (hR : SupportedOn (ValidCHiPoolIn r wPool) R_mid) :
    (cScrubCtrlLo0 r).eval.1 * ((uXorPubLo r).1 * R_mid) =
      (uXorPubLoNo0 r).1 * R_mid := by
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hR fun α hα ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  dsimp only [uXorPubLo, uXorPubLoNo0]
  rw [uVecToggle_mulVec_ket, uVecToggle_mulVec_ket]
  set δ := vecToggleBits (rCtrlLo r) (pubCtrlLo r) α
  have hδL (p : Fin 187) : δ (rCtrlLo r p) = pubCtrlLo r α p := by
    dsimp only [δ]
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).1 p, hα.2.2.2.2.2.1 p, zero_add]
  unfold cScrubCtrlLo0
  rw [eval_seq_mulVec, ket_CNOT, seqGatherParity_mulVec_sum, Function.update_idem,
      Function.update_self,
      show (∑ k : Fin 186, Function.update δ (rCtrlLo r ⟨0, by decide⟩)
          (δ (rCtrlLo r ⟨0, by decide⟩) + δ (rHas1 r)) (ctrlLoNz r k)) =
        ∑ k : Fin 186, pubCtrlLo r α k.succ from
        Finset.sum_congr rfl fun k _ ↦
          (Function.update_of_ne (ctrlLoNz_ne_zero r k) _ δ).trans (hδL k.succ),
      hδL ⟨0, by decide⟩,
      show δ (rHas1 r) = α (rHas1 r) from
        (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 _
          (cohW5_pub18_ne_ctrlLo r (u := ⟨0, rw_lt0 187 8⟩) (by decide)),
      ← sum_pubCtrlLo_eq r hα.1, Fin.sum_univ_succ (pubCtrlLo r α),
      show pubCtrlLo r α ⟨0, by decide⟩ +
          (pubCtrlLo r α 0 + ∑ k : Fin 186, pubCtrlLo r α k.succ) +
          ∑ k : Fin 186, pubCtrlLo r α k.succ = 0 from
        (by decide : ∀ a b : ZMod 2, a + (a + b) + b = 0) _ _]
  refine congrArg ket (cohW5_upd_eq_vecToggle r δ α ⟨0, by decide⟩ 0 (pubCtrlLoNo0 r)
    (by simp [hα.2.2.2.2.2.1, pubCtrlLoNo0]) ?_
    (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2)
  intro p hp
  rw [hδL p, hα.2.2.2.2.2.1 p, zero_add]
  dsimp only [pubCtrlLoNo0]
  rw [ite_eq_right fun e ↦ hp (Fin.ext e)]

theorem supportedOn_validPoolCtrl0_uXorPubLoNo0 {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool) {R_mid : Operator (2 ^ n)}
    (hR : SupportedOn (ValidCHiPoolIn r wPool) R_mid) :
    SupportedOn (ValidCHiPoolCtrl0 r wPool) ((uXorPubLoNo0 r).1 * R_mid) :=
  supportedOn_ketMap (uVecToggle_mulVec_ket (rCtrlLo r) (rCtrlLo_inj_ne r) _ _)
    (fun _ hα ↦ validPoolCtrl0_vecToggle r wPool hP (pubCtrlLoNo0 r) (fun _ _ ↦ rfl)
      ⟨hα.2.2.1, hα.2.2.2.1, hα.2.2.2.2.1, hα.2.2.2.2.2.2.1, hα.2.2.2.2.2.2.2,
       hα.2.2.2.2.2.1 ⟨0, by decide⟩⟩) hR

theorem cRestoreCtrlLo0_eq {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} {R_mid : Operator (2 ^ n)}
    (hR : SupportedOn (ValidCHiPoolIn r wPool) R_mid) :
    (cRestoreCtrlLo0 r).eval.1 * ((uXorPubHiFull r).1 * ((uXorPubLoNo0 r).1 * R_mid)) =
      (uXorTargetLo r).1 * R_mid := by
  simp only [← Matrix.mul_assoc]
  refine cohW5_supp_eq hR fun α hα ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  dsimp only [uXorPubLoNo0, uXorPubHiFull, uXorTargetLo]
  rw [uVecToggle_mulVec_ket, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket]
  set γ := vecToggleBits (rCtrlLo r) (pubCtrlLoNo0 r) α
  set η := vecToggleBits (rCtrlLo r) (pubCtrlHi r) γ
  have hηL (p : Fin 187) : η (rCtrlLo r p) = pubCtrlLoNo0 r α p + pubCtrlHi r α p := by
    dsimp only [η]
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ γ).1 p,
        (pubCtrl_congr r fun w ⟨u, hu, hw⟩ ↦ hw ▸
          (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 _
            (cohW5_pub18_ne_ctrlLo r (by omega))).2]
    dsimp only [γ]
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).1 p, hα.2.2.2.2.2.1 p, zero_add]
  have hηOth (u : Wire n) (hu : ∀ p : Fin 187, u ≠ rCtrlLo r p) : η u = α u :=
    ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ γ).2 u hu).trans
      ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 u hu)
  have hη0 : η (rCtrlLo r ⟨0, by decide⟩) = 0 := by
    rw [hηL ⟨0, by decide⟩]
    dsimp only [pubCtrlLoNo0, pubCtrlHi]
    rw [ite_eq_left rfl, zero_add, cond_nat_beq]
    rcases DynCircExt.bit_cases (α (rRawHas2 r)) with h0 | h1
    · simp [h0]
    · rw [h1, ite_eq_right (Ne.symm (hα.2.2.2.2.1 h1))]
  unfold cRestoreCtrlLo0
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_CNOT, ket_CNOT, seqGatherParity_mulVec_sum]
  simp only [Function.update_idem, Function.update_self,
    Function.update_of_ne (rRawHas2_ne_rCtrlLo r ⟨0, by decide⟩), hη0,
    hηOth _ (cohW5_pub18_ne_ctrlLo r (u := ⟨0, rw_lt0 187 8⟩) (by decide)),
    hηOth _ (rRawHas2_ne_rCtrlLo r), zero_add]
  rw [show ∑ k : Fin 186, Function.update η (rCtrlLo r ⟨0, by decide⟩)
          (α (rHas1 r) + α (rRawHas2 r)) (ctrlLoNz r k) =
        (∑ k : Fin 186, pubCtrlLo r α k.succ) + ∑ k : Fin 186, pubCtrlHi r α k.succ from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Function.update_of_ne (ctrlLoNz_ne_zero r k), hηL k.succ]
        dsimp only [pubCtrlLoNo0]
        rw [ite_eq_right (Fin.val_succ k ▸ Nat.succ_ne_zero k.val)],
      ← sum_pubCtrlLo_eq r hα.1, ← sum_pubCtrlHi_eq r hα.2.2.1,
      Fin.sum_univ_succ (pubCtrlLo r α), Fin.sum_univ_succ (pubCtrlHi r α),
      show (pubCtrlLo r α 0 + ∑ k : Fin 186, pubCtrlLo r α k.succ) +
          (pubCtrlHi r α 0 + ∑ k : Fin 186, pubCtrlHi r α k.succ) +
          ((∑ k : Fin 186, pubCtrlLo r α k.succ) + ∑ k : Fin 186, pubCtrlHi r α k.succ) =
        pubCtrlLo r α ⟨0, by decide⟩ + pubCtrlHi r α ⟨0, by decide⟩ from
        (by decide : ∀ a b c d : ZMod 2, (a + b) + (c + d) + (b + d) = a + c) _ _ _ _]
  refine congrArg ket (cohW5_upd_eq_vecToggle r η α ⟨0, by decide⟩ _ _
    (by rw [hα.2.2.2.2.2.1, zero_add]) ?_ hηOth)
  intro p hp
  rw [hηL p, hα.2.2.2.2.2.1 p, zero_add]
  dsimp only [pubCtrlLoNo0]
  rw [ite_eq_right fun e ↦ hp (Fin.ext e)]

def bStarR0Pool {n : ℕ} (r : RouterReg 187 8 n) (δ : BitAssignment n) : Fin 24 :=
  if δ (rRawHas2 r) = 0 then ⟨23, by decide⟩
  else ⟨min (idxValD (idxHi5_2 r) δ) 23, by omega⟩

def cUnzPoolB23 {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) : Circuit n :=
  wUnzeroGate (rRawHas2 r) (poolB wPool ⟨23, by decide⟩) (wPool_ne_rRawHas2 hP _).symm

def cZerPoolB23 {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) : Circuit n :=
  wZeroGate (rRawHas2 r) (poolB wPool ⟨23, by decide⟩) (wPool_ne_rRawHas2 hP _).symm

theorem wR0Pool_ne_qEnc {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (b : Fin 24) (p : Fin (2 ^ 1)) :
    wR0Pool wPool b p ≠ poolQEnc wPool := by
  have := b.isLt
  dsimp only [wR0Pool, poolB, poolOdd0, poolQEnc]
  split_ifs
  · exact wPool_ne hP (by omega : b.val ≠ 50 + S)
  · exact wPool_ne hP (by omega : 24 + b.val ≠ 50 + S)

theorem uBit0_2_ne_qEnc {S n : ℕ} {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n}
    (hP : CHiPoolDisj r wPool) (d : Fin 1) :
    uBit0_2 r d ≠ poolQEnc wPool :=
  (wPool_ne_idxLo3_2 hP _ _).symm

theorem uBit0_2_ne_wR0Pool {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (d : Fin 1) (b : Fin 24) (p : Fin (2 ^ 1)) :
    uBit0_2 r d ≠ wR0Pool wPool b p := by
  dsimp only [wR0Pool, poolB, poolOdd0]
  split_ifs <;> exact (wPool_ne_idxLo3_2 hP _ _).symm

theorem bStarR0Pool_cleanPoolB {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool) (γ : BitAssignment n) :
    bStarR0Pool r (cleanPoolB wPool r γ) = bStarR0Pool r γ := by
  obtain ⟨_, hHas, _, _, hHi, _, _, _, _⟩ := cohW5_pub18_congr r fun u hu ↦
    cleanPoolB_other wPool r γ _ (pubCtrlSet_ne_wPool hP ⟨u, hu, rfl⟩)
  refine Fin.ext ?_
  dsimp only [bStarR0Pool]
  rw [hHas]
  split_ifs <;> dsimp
  rw [hHi]

theorem uBit0_cleanPoolB {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool) (γ : BitAssignment n) :
    idxValPrefix (uBit0_2 r) (cleanPoolB wPool r γ) 1 le_rfl =
      idxValPrefix (uBit0_2 r) γ 1 le_rfl :=
  idxValPrefix_congr _ _ _ (fun _ ↦ cleanPoolB_other wPool r γ _
    (fun i ↦ (wPool_ne_idxLo3_2 hP i _).symm)) 1 le_rfl

theorem cUnzPoolB23_ket {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    {γ : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) :
    (cUnzPoolB23 hP).eval.1.mulVec (ket γ) =
      ket (Function.update (cleanPoolB wPool r γ)
        (wR0Pool wPool (bStarR0Pool r γ) ⟨0, by decide⟩) 1) := by
  dsimp only [cUnzPoolB23, wR0Pool, bStarR0Pool]
  rw [ite_eq_left rfl]
  rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
  · rw [ite_eq_left hH0, cleanPoolB_eq_of_has2_zero hγ hH0]
    have hγEq : γ = Function.update γ (poolB wPool ⟨23, by decide⟩) (γ (rRawHas2 r)) := by
      rw [hH0, update_eq_self_of_zero (by rw [hγ.2.2.2.1 _, hH0, ite_self])]
    conv_lhs => rw [hγEq]
    exact wUnzeroGate_ket (wPool_ne_rRawHas2 hP _).symm (wPool_ne_rRawHas2 hP _).symm (fun _ ↦ rfl)
  · rw [wUnzeroGate_id_of_one (wPool_ne_rRawHas2 hP _).symm hH1,
        ite_eq_right (hH1.symm ▸ one_ne_zero)]
    have hq24 := idxHi5_2_lt24_of_lt187 r hγ.1
    dsimp only [cleanPoolB]
    rw [Function.update_idem]
    refine congrArg ket (funext fun u ↦ ?_)
    by_cases hu : u = poolB wPool ⟨min (idxValD (idxHi5_2 r) γ) 23, by omega⟩
    · subst hu
      rw [Function.update_self, hγ.2.2.2.1 _, hH1, ite_eq_left (Nat.min_eq_left (by omega)).symm]
    · rw [Function.update_of_ne hu]

theorem cZerPoolB23_r0_ket {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    {γ : BitAssignment n} (hγ : ValidCHiPoolCtrl0 r wPool γ) :
    (cZerPoolB23 hP).eval.1.mulVec
        (ket (Function.update (cleanPoolB wPool r γ)
          (wR0Pool wPool (bStarR0Pool r γ)
            ⟨idxValPrefix (uBit0_2 r) γ 1 le_rfl,
              idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩) 1)) =
      ket (r0Map wPool r γ) := by
  let u0 := idxValPrefix (uBit0_2 r) γ 1 le_rfl
  have hu0Lt : u0 < 2 := idxValPrefix_lt_two_pow (uBit0_2 r) γ 1 le_rfl
  dsimp only [cZerPoolB23]
  rcases DynCircExt.bit_cases (γ (rRawHas2 r)) with hH0 | hH1
  · have hi0 := hγ.2.1 hH0
    have hsp : idxValD (rIdx2 r) γ = 8 * idxValD (idxHi5_2 r) γ + idxValD (idxLo3_2 r) γ :=
      idxValD_8_split35 (rIdx2 r) γ
    have hu0_0 : u0 = 0 := by
      have hlo0 : idxValD (idxLo3_2 r) γ = 0 := by omega
      dsimp only [u0, idxValD, idxValPrefix, uBit0_2] at hlo0 ⊢
      split_ifs at hlo0 ⊢ <;> omega
    rw [show wR0Pool wPool (bStarR0Pool r γ) ⟨u0, hu0Lt⟩ = poolB wPool ⟨23, by decide⟩ by
          dsimp only [wR0Pool, bStarR0Pool]
          rw [ite_eq_left hu0_0, ite_eq_left hH0],
        cleanPoolB_eq_of_has2_zero hγ hH0, r0Map_eq_of_has2_zero hP hγ hH0,
        wZeroGate_ket (wPool_ne_rRawHas2 hP _).symm (wPool_ne_rRawHas2 hP _).symm (fun _ ↦ rfl),
        hH0, update_eq_self_of_zero (by rw [hγ.2.2.2.1 _, hH0, ite_self])]
  · rw [wZeroGate_id_of_one (wPool_ne_rRawHas2 hP _).symm
          ((Function.update_of_ne (by
            dsimp only [wR0Pool, poolB, poolOdd0]
            split_ifs <;> exact (wPool_ne_rRawHas2 hP _).symm) 1 _).trans
            ((cleanPoolB_other wPool r γ _ fun i ↦ (wPool_ne_rRawHas2 hP i).symm).trans hH1))]
    dsimp only [r0Map, bStarR0Pool]
    rw [hH1, ite_eq_right one_ne_zero]

/-- Outer Round-0 + `rCtrlLo[0]` wrapper around a multi-batch `body` (`48 + body.T`). -/
def pCHiOuterWrap {Var : Type} {S n : ℕ} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (Circuit.seq (cScrubCtrlLo0 r)
      (Circuit.seq (cUnzPoolB23 hP)
        (wTreePrefix 24 1 (wR0Pool wPool) (wInj_wR0Pool hP) 1 le_rfl))))
    (.seq (wShiftLevels v 24 1 (uBit0_2 r) (wR0Pool wPool) (poolQEnc wPool)
        (wInj_wR0Pool hP) (wR0Pool_ne_qEnc hP) (uBit0_2_ne_qEnc hP) 1 le_rfl)
      (.seq (.circuit (cZerPoolB23 hP))
        (.seq body
          (.seq (.circuit (cUnzPoolB23 hP))
            (.seq (wUncompTreeDyn v 24 1 (uBit0_2 r) (wR0Pool wPool) (wInj_wR0Pool hP)
                (uBit0_2_ne_wR0Pool hP) (.circuit .identity) 1 le_rfl)
              (.circuit (Circuit.seq (cZerPoolB23 hP) (cRestoreCtrlLo0 r))))))))

theorem count_pCHiOuterWrap {Var : Type} {S n : ℕ} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (body : DynamicCircuit Var n) :
    (pCHiOuterWrap v hP body).count .T = 48 + body.count .T ∧
    (pCHiOuterWrap v hP body).count .TOFF = body.count .TOFF := by
  obtain ⟨t0, f0⟩ := count_wTreePrefix 24 1 (wR0Pool wPool) (wInj_wR0Pool hP) 1 le_rfl
  obtain ⟨st, sf⟩ := count_wShiftLevels v 24 1 (uBit0_2 r) (wR0Pool wPool) (poolQEnc wPool)
    (wInj_wR0Pool hP) (wR0Pool_ne_qEnc hP) (uBit0_2_ne_qEnc hP) 1 le_rfl
  obtain ⟨ut, uf⟩ := count_wUncompTreeDyn_opt v 24 1 (uBit0_2 r) (wR0Pool wPool) (wInj_wR0Pool hP)
    (uBit0_2_ne_wR0Pool hP) (.circuit .identity) 1 le_rfl
  unfold pCHiOuterWrap
  dsimp only [DynamicCircuit.count]
  rw [st, sf, ut, uf]
  constructor <;> simp [cScrubCtrlLo0, cRestoreCtrlLo0, cUnzPoolB23, cZerPoolB23, wUnzeroGate,
    wZeroGate, DynamicCircuit.count, Circuit.count_seq, Circuit.X, Circuit.CNOT,
    count_seqGatherParity_t, count_seqGatherParity_toff, t0, f0]

theorem dynWires_pCHiOuterWrap {Var : Type} {S n : ℕ} {Sw : Wire n → Prop} (v : Var)
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (body : DynamicCircuit Var n) (hBody : DynWires Sw body)
    (h1 : Sw (rHas1 r)) (h2 : Sw (rRawHas2 r)) (hI3 : ∀ d : Fin 3, Sw (idxLo3_2 r d))
    (hCLo : ∀ p : Fin 187, Sw (rCtrlLo r p)) (hPool : ∀ i : Fin (51 + S), Sw (wPool i)) :
    DynWires Sw (pCHiOuterWrap v hP body) := by
  have hwR0 (b : Fin 24) (p : Fin (2 ^ 1)) : Sw (wR0Pool wPool b p) := by
    dsimp only [wR0Pool, poolB, poolOdd0]
    split_ifs <;> exact hPool _
  have cwUnz : CircWires Sw (cUnzPoolB23 hP) := ⟨cw_cnot h2 (hPool _), cw_1 (hPool _)⟩
  have cwZer : CircWires Sw (cZerPoolB23 hP) := ⟨cw_1 (hPool _), cw_cnot h2 (hPool _)⟩
  exact ⟨⟨⟨cw_cnot h1 (hCLo _), cw_seqGatherParity 186 _ _ _ (fun _ ↦ hCLo _) (hCLo _)⟩,
      cwUnz, cw_wTreePrefix 24 1 _ _ hwR0 1 le_rfl⟩,
    dw_wShiftLevels v 24 1 _ _ _ _ _ _ (fun _ ↦ hI3 _) hwR0 (hPool _) 1 le_rfl,
    cwZer, hBody, cwUnz,
    dw_wUncompTreeDyn_opt v 24 1 _ _ _ _ (fun _ ↦ hI3 _) hwR0
      (rest := .circuit .identity) trivial 1 le_rfl,
    ⟨cwZer, ⟨cw_cnot h1 (hCLo _), cw_cnot h2 (hCLo _),
      cw_seqGatherParity 186 _ _ _ (fun _ ↦ hCLo _) (hCLo _)⟩⟩⟩

theorem subspaceStep_pCHiOuterWrap {Var : Type} [Fintype Var] [DecidableEq Var] {S n : ℕ}
    (v : Var) {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    {R_mid : Operator (2 ^ n)} (hR : SupportedOn (ValidCHiPoolIn r wPool) R_mid)
    {body : DynamicCircuit Var n}
    (hBody : ∀ G, SupportedOn (ValidCHiPoolCtrl0 r wPool) G →
      SubspaceStep (Var := Var)
        (opR0 wPool r G) (opR0 wPool r ((uXorPubHiFull r).1 * G)) body) :
    SubspaceStep (Var := Var)
      ((uXorPubLo r).1 * R_mid) ((uXorTargetLo r).1 * R_mid) (pCHiOuterWrap v hP body) := by
  let G₀ := (uXorPubLoNo0 r).1 * R_mid
  have hG₀ : SupportedOn (ValidCHiPoolCtrl0 r wPool) G₀ :=
    supportedOn_validPoolCtrl0_uXorPubLoNo0 hP hR
  let G₁ := (uXorPubHiFull r).1 * G₀
  have hG₁ : SupportedOn (ValidCHiPoolCtrl0 r wPool) G₁ :=
    supportedOn_validPoolCtrl0_uVecToggle r wPool hP (pubCtrlHi r) _
      (fun γ hγ ↦ by simpa [pubCtrlHiPred] using pubCtrlHiPred_zero_at_zero (fun _ ↦ true) r hγ)
      G₀ hG₀
  let X₀ : Operator (2 ^ n) := mkVecOp (fun γ ↦ ket (cleanPoolB wPool r γ)) * G₀
  let X₁ : Operator (2 ^ n) := mkVecOp (fun γ ↦ ket (cleanPoolB wPool r γ)) * G₁
  have hw0 (γ : BitAssignment n) (hγ : ValidCHiPoolCtrl0 r wPool γ)
      (b : Fin 24) (p : Fin (2 ^ 1)) : cleanPoolB wPool r γ (wR0Pool wPool b p) = 0 := by
    dsimp only [wR0Pool, poolB, poolOdd0]
    split_ifs <;> exact cleanPoolB_wPool_zero hP hγ _
  have hq0 (γ : BitAssignment n) (hγ : ValidCHiPoolCtrl0 r wPool γ) :
      cleanPoolB wPool r γ (poolQEnc wPool) = 0 := cleanPoolB_wPool_zero hP hγ _
  have hu0Fin (γ : BitAssignment n) :
      (⟨idxValPrefix (uBit0_2 r) (cleanPoolB wPool r γ) 1 le_rfl,
          idxValPrefix_lt_two_pow _ _ 1 le_rfl⟩ : Fin (2 ^ 1)) =
        ⟨idxValPrefix (uBit0_2 r) γ 1 le_rfl, idxValPrefix_lt_two_pow _ γ 1 le_rfl⟩ :=
    Fin.ext (uBit0_cleanPoolB hP γ)
  have hpT (γ : BitAssignment n) : pTrueChi (cleanPoolB wPool r γ) := trivial
  unfold pCHiOuterWrap
  refine (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_).seq
    ((subspaceStep_mul_right X₀
      (subspaceStep_wShiftLevels v (bStarR0Pool r) (uBit0_2 r) (wR0Pool wPool) (poolQEnc wPool)
        (wInj_wR0Pool hP) (wR0Pool_ne_qEnc hP) (uBit0_2_ne_qEnc hP)
        (uBit0_2_ne_wR0Pool hP) 1 le_rfl)).seq
      ((subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_).seq
        ((hBody G₀ hG₀).seq
          ((subspaceStep_congr_out
            (subspaceStep_of_circuit (Var := Var) (opR0 wPool r G₁) _) ?_).seq
            ((subspaceStep_mul_right X₁
              (subspaceStep_wUncompTreeDyn_id_opt v pTrueChi pTrueChi (bStarR0Pool r) (uBit0_2 r)
                (wR0Pool wPool) (wInj_wR0Pool hP) (uBit0_2_ne_wR0Pool hP))).seq
              (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_))))))
  · rw [eval_seq_eq, Matrix.mul_assoc, cScrubCtrlLo0_eq hR]
    dsimp only [X₀]
    rw [← Matrix.mul_assoc (wSuperOp _ _ _ _ _ _)]
    refine cohW5_supp_eq hG₀ fun γ hγ ↦ ?_
    rw [eval_seq_mulVec, cUnzPoolB23_ket hP hγ, ← bStarR0Pool_cleanPoolB hP γ,
        ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket, wSuperOp, mkVecOp_mulVec_ket,
        wSuperVec_bot_pub (bStarR0Pool r) (uBit0_2 r) (wR0Pool wPool) (wInj_wR0Pool hP)
          (poolQEnc wPool) (cleanPoolB wPool r γ) (hw0 γ hγ) (hq0 γ hγ)]
  · dsimp only [X₀, opR0]
    simp only [← Matrix.mul_assoc]
    refine cohW5_supp_eq hG₀ fun γ hγ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket,
        wSuperOp, mkVecOp_mulVec_ket,
        wSuperVec_top_pub (bStarR0Pool r) (uBit0_2 r) (wR0Pool wPool) (poolQEnc wPool)
          (cleanPoolB wPool r γ) (hw0 γ hγ) (hq0 γ hγ),
        bStarR0Pool_cleanPoolB hP γ, hu0Fin γ, cZerPoolB23_r0_ket hP hγ, mkVecOp_mulVec_ket]
  · dsimp only [opR0, X₁]
    simp only [← Matrix.mul_assoc]
    refine cohW5_supp_eq hG₁ fun γ hγ ↦ ?_
    simp only [← Matrix.mulVec_mulVec]
    rw [mkVecOp_mulVec_ket, mkVecOp_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket,
        oneHotOptPreVec, ite_eq_left ⟨hpT γ, hw0 γ hγ⟩, ite_eq_left (hpT γ),
        bStarR0Pool_cleanPoolB hP γ, hu0Fin γ, ← cZerPoolB23_r0_ket hP hγ]
    simp only [cUnzPoolB23, cZerPoolB23, wUnzeroGate, wZeroGate, eval_seq_mulVec,
      mulVec_X_invol_opt, mulVec_CNOT_invol_opt]
  · rw [eval_seq_eq, Matrix.mul_assoc,
        show (cZerPoolB23 hP).eval.1 *
            (oneHotOptPreOp pTrueChi pTrueChi (bStarR0Pool r) (uBit0_2 r) (wR0Pool wPool)
              0 (Nat.zero_le 1) * X₁) = G₁ from by
          refine (?_ : _ = (1 : Operator (2 ^ n)) * G₁).trans (Matrix.one_mul G₁)
          dsimp only [X₁]
          simp only [← Matrix.mul_assoc]
          refine cohW5_supp_eq hG₁ fun γ hγ ↦ ?_
          simp only [← Matrix.mulVec_mulVec]
          rw [mkVecOp_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec,
              ite_eq_left ⟨hpT γ, hw0 γ hγ⟩, ite_eq_left (hpT γ), bStarR0Pool_cleanPoolB hP γ,
              (Fin.ext rfl : (⟨idxValPrefix (uBit0_2 r) (cleanPoolB wPool r γ) 0 (Nat.zero_le 1),
                _⟩ : Fin (2 ^ 1)) = ⟨0, by decide⟩),
              ← cUnzPoolB23_ket hP hγ, Matrix.one_mulVec]
          simp only [cUnzPoolB23, cZerPoolB23, wUnzeroGate, wZeroGate, eval_seq_mulVec,
            mulVec_X_invol_opt, mulVec_CNOT_invol_opt]]
    exact cRestoreCtrlLo0_eq hR

/-! ### 8. Exported Batch Gadget (`pCHi2Batch338`) -/

abbrev tSing0 : Fin 95 := ⟨0, by decide⟩
abbrev tSing92 : Fin 95 := ⟨92, by decide⟩
abbrev tSing94 : Fin 95 := ⟨94, by decide⟩
abbrev pSing4 : Fin 187 := ⟨4, by decide⟩
abbrev pSing184 : Fin 187 := ⟨184, by decide⟩
abbrev pSing186 : Fin 187 := ⟨186, by decide⟩

theorem supp_uXorPubHiPred {S n : ℕ} {r : RouterReg 187 8 n}
    {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool) (P : ℕ → Bool)
    {G : Operator (2 ^ n)} (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G) :
    SupportedOn (ValidCHiPoolCtrl0 r wPool) ((uXorPubHiPred P r).1 * G) :=
  supportedOn_validPoolCtrl0_uVecToggle r wPool hP (pubCtrlHiPred P r) _
    (fun _ hγ ↦ pubCtrlHiPred_zero_at_zero P r hγ) G hG

theorem chainPubHi {Var : Type} [Fintype Var] [DecidableEq Var] {S n : ℕ}
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (F : Operator (2 ^ n) → Operator (2 ^ n))
    {P Q : ℕ → Bool} {G : Operator (2 ^ n)} (hG : SupportedOn (ValidCHiPoolCtrl0 r wPool) G)
    {c₁ c₂ : DynamicCircuit Var n}
    (s₁ : SubspaceStep (Var := Var) (F G) (F ((uXorPubHiPred P r).1 * G)) c₁)
    (s₂ : ∀ X, SupportedOn (ValidCHiPoolCtrl0 r wPool) X →
      SubspaceStep (Var := Var) (F X) (F ((uXorPubHiPred Q r).1 * X)) c₂)
    (hDisj : ∀ t < 95, ¬ (P t = true ∧ Q t = true)) :
    SubspaceStep (Var := Var) (F G)
      (F ((uXorPubHiPred (fun t ↦ P t || Q t) r).1 * G)) (.seq c₁ c₂) :=
  s₁.seq (subspaceStep_congr_out (s₂ _ (supp_uXorPubHiPred hP P hG))
    (by rw [← Matrix.mul_assoc, mul_uXorPubHiPred P Q r hDisj]))

theorem cw_cCohSing {S n : ℕ} {Sw : Wire n → Prop}
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    (mOff M : ℕ) (hm : mOff + M ≤ 47) (hMS : M ≤ S) (tSing : Fin 95) (pSing : Fin 187)
    (ht : mOff ≤ 2 * (tSing.val / 4) + tSing.val % 2 ∧
          2 * (tSing.val / 4) + tSing.val % 2 < mOff + M)
    (hPool : ∀ i : Fin (51 + S), Sw (wPool i)) (hCLo : ∀ p : Fin 187, Sw (rCtrlLo r p)) :
    CircWires Sw (cCohSing hP mOff M hm hMS tSing pSing ht) := by
  obtain ⟨idx, _, hEq⟩ := cohW5_wCohNode_idx mOff M hm hMS wPool tSing ht
  exact cw_cnot (hEq ▸ hPool idx) (hCLo _)

theorem range338 (mOff M tOff R : ℕ)
    (hd : ∀ k : Fin R, decide (mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
      2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M) = true) (k : Fin R) :
    mOff ≤ 2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 ∧
    2 * ((k.val + tOff) / 4) + (k.val + tOff) % 2 < mOff + M :=
  of_decide_eq_true (hd k)

/--
Lift clean pre-Phase-1 kets through `uOneHotToggle (rRawHas2 r) (idxHi5_2 r) (poolB wPool)`
to `SupportedOn (ValidCHiPoolIn r wPool)`.
-/
theorem supportedOn_validCHiPoolIn_uOneHotToggle {S n : ℕ}
    {r : RouterReg 187 8 n} {wPool : Fin (51 + S) → Wire n} (hP : CHiPoolDisj r wPool)
    {P : BitAssignment n → Prop} {R_base : Operator (2 ^ n)} (hR : SupportedOn P R_base)
    (hPre : ∀ β, P β →
      idxValD (rIdx1 r) β < 187 ∧
      (β (rHas1 r) = 0 → idxValD (rIdx1 r) β = 0) ∧
      idxValD (rIdx2 r) β < 187 ∧
      (β (rRawHas2 r) = 0 → idxValD (rIdx2 r) β = 0) ∧
      (β (rRawHas2 r) = 1 → idxValD (rIdx2 r) β ≠ 0) ∧
      (∀ p : Fin 187, β (rCtrlLo r p) = 0) ∧
      (∀ i : Fin (51 + S), β (wPool i) = 0)) :
    SupportedOn (ValidCHiPoolIn r wPool)
      ((uOneHotToggle (rRawHas2 r) (idxHi5_2 r) (poolB wPool)
        (fun _ ↦ (wPool_ne_rRawHas2 hP _).symm)
        (fun d _ ↦ (wPool_ne_idxHi5_2 hP _ d).symm)).1 * R_base) := by
  refine supportedOn_ketMap (uOneHotToggle_mulVec_ket _ _ _ _ _) (fun β hβ ↦ ?_) hR
  obtain ⟨hi1, hz1, hi2, hz2, hnz2, hCLo0, hPool0⟩ := hPre β hβ
  let α := toggleOneHotBits (rRawHas2 r) (idxHi5_2 r) (poolB wPool) β
  have hOth (u : Wire n) (hu : ∀ b : Fin 24, u ≠ poolB wPool b) : α u = β u :=
    toggleOneHotBits_apply_other β hu
  obtain ⟨hHas1, hHas2, hIdx1, hIdx2, hHi2, _, _, _, _⟩ :=
    cohW5_pub18_congr r fun u hu ↦ hOth _ fun _ ↦ (hP.ne_pub18 _ u hu).symm
  refine ⟨hIdx1 ▸ hi1, fun h0 ↦ hIdx1.trans (hz1 (hHas1.symm.trans h0)),
    hIdx2 ▸ hi2, fun h0 ↦ hIdx2.trans (hz2 (hHas2.symm.trans h0)),
    fun h1 ↦ hIdx2 ▸ hnz2 (hHas2.symm.trans h1),
    fun p ↦ (hOth _ fun _ ↦ (hP.ne_ctrlLo _ p).symm).trans (hCLo0 p), fun b ↦ ?_,
    fun k ↦ (hOth _ fun b ↦ by
      have := b.isLt
      exact wPool_ne hP (by omega : 24 + k.val ≠ b.val)).trans (hPool0 _)⟩
  dsimp only [α] at hHi2 hHas2
  rw [hHi2, hHas2]
  exact toggleOneHotBits_apply_out (wOut := poolB wPool)
    (fun b₁ b₂ hne ↦ wPool_ne hP (fun e ↦ hne (Fin.ext e)))
    (fun _ ↦ hPool0 _) (idxHi5_2_lt24_of_lt187 r hi2) b

/--
`338-T` (`0 .TOFF`) 2-batch `q2`-aligned Phase-1 `cHi` gadget (`S = 44`, `95` pool wires),
covering `K = 214`.
-/
def pCHi2Batch338 {Var : Type} {n : ℕ} (v : Var)
    (r : RouterReg 187 8 n) (wPool : Fin 95 → Wire n) (hP : CHiPoolDisj (S := 44) r wPool) :
    DynamicCircuit Var n :=
  pCHiOuterWrap (S := 44) v hP
    (.seq (.seq
        (.circuit (cR0Sing93 (S := 44) hP))
        (pCohWrap (S := 44) v hP 0 22 (by decide) (by decide)
          (.seq (.seq
              (.circuit (cCohSing (S := 44) hP 0 22 (by decide) (by decide)
                tSing0 pSing4 (by decide)))
              (pCohMiniPass (S := 44) v hP 0 22 (by decide) (by decide)
                1 22 (by decide) (by decide) (range338 0 22 1 22 (by decide))))
            (pCohMiniPass (S := 44) v hP 0 22 (by decide) (by decide)
              23 21 (by decide) (by decide) (range338 0 22 23 21 (by decide))))))
      (pCohWrap (S := 44) v hP 22 25 (by decide) (by decide)
        (.seq (.seq (.seq (.seq
            (.circuit (cCohSing (S := 44) hP 22 25 (by decide) (by decide)
              tSing92 pSing184 (by decide)))
            (.circuit (cCohSing (S := 44) hP 22 25 (by decide) (by decide)
              tSing94 pSing186 (by decide))))
          (pCohMiniPass (S := 44) v hP 22 25 (by decide) (by decide)
            44 16 (by decide) (by decide) (range338 22 25 44 16 (by decide))))
          (pCohMiniPass (S := 44) v hP 22 25 (by decide) (by decide)
            60 16 (by decide) (by decide) (range338 22 25 60 16 (by decide))))
        (pCohMiniPass (S := 44) v hP 22 25 (by decide) (by decide)
          76 16 (by decide) (by decide) (range338 22 25 76 16 (by decide))))))

theorem count_pCHi2Batch338 {Var : Type} {n : ℕ} (v : Var)
    (r : RouterReg 187 8 n) (wPool : Fin 95 → Wire n) (hP : CHiPoolDisj (S := 44) r wPool) :
    (pCHi2Batch338 v r wPool hP).count .T = 338 ∧
    (pCHi2Batch338 v r wPool hP).count .TOFF = 0 := by
  unfold pCHi2Batch338
  obtain ⟨to_, fo_⟩ := count_pCHiOuterWrap (S := 44) v hP _
  obtain ⟨tc0, fc0⟩ := count_pCohWrap (S := 44) v hP 0 22 (by decide) (by decide) _
  obtain ⟨tc1, fc1⟩ := count_pCohWrap (S := 44) v hP 22 25 (by decide) (by decide) _
  obtain ⟨tm0a, fm0a⟩ := count_pCohMiniPass (S := 44) v hP 0 22 _ _ 1 22 _ _ _
  obtain ⟨tm0b, fm0b⟩ := count_pCohMiniPass (S := 44) v hP 0 22 _ _ 23 21 _ _ _
  obtain ⟨tm1a, fm1a⟩ := count_pCohMiniPass (S := 44) v hP 22 25 _ _ 44 16 _ _ _
  obtain ⟨tm1b, fm1b⟩ := count_pCohMiniPass (S := 44) v hP 22 25 _ _ 60 16 _ _ _
  obtain ⟨tm1c, fm1c⟩ := count_pCohMiniPass (S := 44) v hP 22 25 _ _ 76 16 _ _ _
  rw [to_, fo_]
  dsimp only [DynamicCircuit.count]
  rw [tc0, fc0, tc1, fc1]
  dsimp only [DynamicCircuit.count]
  rw [tm0a, fm0a, tm0b, fm0b, tm1a, fm1a, tm1b, fm1b, tm1c, fm1c]
  constructor <;> simp [cR0Sing93, cCohSing, Circuit.CNOT]

theorem dynWires_pCHi2Batch338 {Var : Type} {n : ℕ} {Sw : Wire n → Prop} (v : Var)
    (r : RouterReg 187 8 n) (wPool : Fin 95 → Wire n) (hP : CHiPoolDisj (S := 44) r wPool)
    (h1 : Sw (rHas1 r)) (h2 : Sw (rRawHas2 r)) (hI3 : ∀ d : Fin 3, Sw (idxLo3_2 r d))
    (hCLo : ∀ p : Fin 187, Sw (rCtrlLo r p)) (hPool : ∀ i : Fin 95, Sw (wPool i)) :
    DynWires Sw (pCHi2Batch338 v r wPool hP) :=
  dynWires_pCHiOuterWrap (S := 44) v hP _
    ⟨⟨cw_cnot (hPool _) (hCLo _),
      dynWires_pCohWrap (S := 44) v hP 0 22 _ _ _
        ⟨⟨cw_cCohSing (S := 44) hP 0 22 _ _ _ _ _ hPool hCLo,
          dynWires_pCohMiniPass (S := 44) v hP 0 22 _ _ 1 22 _ _ _ hI3 hPool hCLo⟩,
         dynWires_pCohMiniPass (S := 44) v hP 0 22 _ _ 23 21 _ _ _ hI3 hPool hCLo⟩ hI3 hPool⟩,
     dynWires_pCohWrap (S := 44) v hP 22 25 _ _ _
       ⟨⟨⟨⟨cw_cCohSing (S := 44) hP 22 25 _ _ _ _ _ hPool hCLo,
           cw_cCohSing (S := 44) hP 22 25 _ _ _ _ _ hPool hCLo⟩,
          dynWires_pCohMiniPass (S := 44) v hP 22 25 _ _ 44 16 _ _ _ hI3 hPool hCLo⟩,
         dynWires_pCohMiniPass (S := 44) v hP 22 25 _ _ 60 16 _ _ _ hI3 hPool hCLo⟩,
        dynWires_pCohMiniPass (S := 44) v hP 22 25 _ _ 76 16 _ _ _ hI3 hPool hCLo⟩ hI3 hPool⟩
    h1 h2 hI3 hCLo hPool

theorem subspaceStep_pCHi2Batch338 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (wPool : Fin 95 → Wire n)
    (hP : CHiPoolDisj (S := 44) r wPool)
    {R_mid : Operator (2 ^ n)} (hR : SupportedOn (ValidCHiPoolIn (S := 44) r wPool) R_mid) :
    SubspaceStep (Var := Var)
      ((uXorPubLo r).1 * R_mid) ((uXorTargetLo r).1 * R_mid) (pCHi2Batch338 v r wPool hP) := by
  unfold pCHi2Batch338
  refine subspaceStep_pCHiOuterWrap (S := 44) v hP hR fun G hG ↦ ?_
  let P0 : ℕ → Bool := fun t ↦
    (decide (t = 0) || decide (1 ≤ t ∧ t < 1 + 22)) || decide (23 ≤ t ∧ t < 23 + 21)
  let P1 : ℕ → Bool := fun t ↦
    (((decide (t = 92) || decide (t = 94)) || decide (44 ≤ t ∧ t < 44 + 16)) ||
      decide (60 ≤ t ∧ t < 60 + 16)) || decide (76 ≤ t ∧ t < 76 + 16)
  let F0 := opCoh (S := 44) 0 22 (by decide) (by decide) wPool r
  let F1 := opCoh (S := 44) 22 25 (by decide) (by decide) wPool r
  let mp (m M hm hMS t R ht1 hR ht hC hd) :=
    subspaceStep_pCohMiniPass (S := 44) v hP m M hm hMS t R ht1 hR ht hC (range338 m M t R hd)
  refine subspaceStep_congr_out
    (chainPubHi (S := 44) hP (opR0 (S := 44) wPool r) hG
      (chainPubHi (S := 44) hP (opR0 (S := 44) wPool r) hG
        (subspaceStep_cR0Sing93 (S := 44) hP G hG)
        (fun X hX ↦ subspaceStep_pCohWrap (S := 44) v hP 0 22 (by decide) (by decide) (by decide)
          hX (supp_uXorPubHiPred (S := 44) hP P0 hX)
          (chainPubHi (S := 44) hP F0 hX
            (chainPubHi (S := 44) hP F0 hX
              (subspaceStep_cCohSing (S := 44) hP 0 22 (by decide) (by decide)
                tSing0 pSing4 (by decide) (Or.inl ⟨rfl, rfl⟩) X hX)
              (mp 0 22 (by decide) (by decide) 1 22 (by decide) (by decide) (by decide)
                (by decide) (by decide)) (by decide))
            (mp 0 22 (by decide) (by decide) 23 21 (by decide) (by decide) (by decide)
              (by decide) (by decide)) (by decide))) (by decide))
      (fun X hX ↦ subspaceStep_pCohWrap (S := 44) v hP 22 25 (by decide) (by decide) (by decide)
        hX (supp_uXorPubHiPred (S := 44) hP P1 hX)
        (chainPubHi (S := 44) hP F1 hX
          (chainPubHi (S := 44) hP F1 hX
            (chainPubHi (S := 44) hP F1 hX
              (chainPubHi (S := 44) hP F1 hX
                (subspaceStep_cCohSing (S := 44) hP 22 25 (by decide) (by decide)
                  tSing92 pSing184 (by decide) (Or.inr (Or.inl ⟨rfl, rfl⟩)) X hX)
                (subspaceStep_cCohSing (S := 44) hP 22 25 (by decide) (by decide)
                  tSing94 pSing186 (by decide) (Or.inr (Or.inr ⟨rfl, rfl⟩))) (by decide))
              (mp 22 25 (by decide) (by decide) 44 16 (by decide) (by decide) (by decide)
                (by decide) (by decide)) (by decide))
            (mp 22 25 (by decide) (by decide) 60 16 (by decide) (by decide) (by decide)
              (by decide) (by decide)) (by decide))
          (mp 22 25 (by decide) (by decide) 76 16 (by decide) (by decide) (by decide)
            (by decide) (by decide)) (by decide))) (by decide))
    (by rw [uXorPubHiPred_full _ r (by decide)])

attribute [irreducible] pCHi2Batch338
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecQuotient
end
