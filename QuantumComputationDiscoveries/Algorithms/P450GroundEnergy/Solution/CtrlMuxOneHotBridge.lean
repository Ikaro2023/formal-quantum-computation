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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OneHotTree
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.UnsignedBilinearGivens13

/-!
# Control-Multiplexed Catalytic Bridge for `oneHotActiveProg`
Bridges `OneHotTree.oneHotActiveProg` (`OneHotTree`) with `UnsignedGivens`'s zero-`rK` Rank-2
Bilinear `Lac = 2` Givens cascade (`UnsignedBilinearGivens13`):

1. **Total-Domain One-Hot Decoding (`oneHotDecodeIdx`, `ket_oneHotActiveCircuit_total`)**:
   - Proves that for ANY `1 ≤ D` and ANY `m`-bit index `bits : Fin m → ZMod 2` (even out-of-range
     `bitsToNat bits ≥ D`), `oneHotDecodeCircuit m D rIdx rOneHot hDisj` deterministically maps
     clean `rOneHot[1..D-1] = 0` to
     `rOneHot[j] = if j = oneHotDecodeIdx m D hD bits then rOneHot[0] else 0`,
     with `(oneHotDecodeIdx m D hD bits).val = bitsToNat bits` whenever `bitsToNat bits < D`.
   - Hence `oneHotActiveCircuit` outputs `0^D` when `wAct = 0` (`AtMostOneHotBits`) and exact
     one-hot `IsOneHotBits (oneHotDecodeIdx ...)` when `wAct = 1` across **all `2^m` values of
     `rIdx`**,
     guaranteeing exact involution (`U^2 = 1`) on every control basis state including `319..511`.

2. **Control-Diagonal Catalytic Contract (`CtrlMuxCatalyticWith`)**:
   - Refines `RealizesCleanCatalyticSubroutineWith` by recording that the raw `(k_sys + b) + k_ctrl`
     unitary `muxCtrlUnitary W_raw` is block-diagonal in `rCtrl` across **all** `2^b` catalyst basis
     states (not only on `φ_cat`), immediately discharging `CommutesWithWire` on `wAct`, `rIdx`,
     and `rOneHot` for `GlobalCleanSimulates.oneHotActive`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.OneHotMux
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.OneHotSimulates
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 1: Total-Domain `oneHotDecodeIdx` & `ket_oneHotActiveCircuit_total` -/

/-- Deterministic output slot `∈ Fin D` selected by `oneHotDecodeCircuit m D` across ALL `2^m`
input bitstrings `bits : Fin m → ZMod 2` (including out-of-range `bitsToNat bits ≥ D`). -/
def oneHotDecodeIdx : (m D : ℕ) → (hD : 1 ≤ D) → (Fin m → ZMod 2) → Fin D
  | 0, _, hD, _ => ⟨0, hD⟩
  | k + 1, D, hD, bits =>
      let bitsLo : Fin k → ZMod 2 := fun i => bits ⟨i.val, by omega⟩
      if _ : D ≤ 2 ^ k then
        oneHotDecodeIdx k D hD bitsLo
      else
        if bits ⟨k, by omega⟩ = 0 then
          let jLo := oneHotDecodeIdx k (2 ^ k) (Nat.two_pow_pos k) bitsLo
          ⟨jLo.val, by omega⟩
        else
          let jHi := oneHotDecodeIdx k (D - 2 ^ k) (by omega) bitsLo
          ⟨2 ^ k + jHi.val, by omega⟩

theorem oneHotDecodeIdx_val_of_lt :
    ∀ (m D : ℕ) (hD : 1 ≤ D) (bits : Fin m → ZMod 2),
      bitsToNat bits < D →
      (oneHotDecodeIdx m D hD bits).val = bitsToNat bits
  | 0, _, _, _, _ => by simp [oneHotDecodeIdx, bitsToNat]
  | k + 1, D, hD, bits, hu => by
      let bitsLo : Fin k → ZMod 2 := fun i => bits ⟨i.val, by omega⟩
      have hu_decomp : bitsToNat bits = bitsToNat bitsLo + 2 ^ k * (bits ⟨k, by omega⟩).val := by
        simp [bitsToNat, bitsLo]
      have huLo_lt : bitsToNat bitsLo < 2 ^ k := bitsToNat_lt_two_pow bitsLo
      dsimp only [oneHotDecodeIdx]
      split_ifs with hSplit hb0
      · have hbit0 : (bits ⟨k, by omega⟩).val = 0 := by
          rcases UnsignedGivens.zmod2_eq_zero_or_one (bits ⟨k, by omega⟩) with h0 | h1
          · simp [h0]
          · exfalso; rw [h1, ZMod.val_one, mul_one] at hu_decomp; omega
        have hu_eq : bitsToNat bits = bitsToNat bitsLo := by
          rw [hu_decomp, hbit0, mul_zero, add_zero]
        rw [oneHotDecodeIdx_val_of_lt k D hD bitsLo (by omega), hu_eq]
      · have hu_eq : bitsToNat bits = bitsToNat bitsLo := by
          rw [hu_decomp, hb0, ZMod.val_zero, mul_zero, add_zero]
        rw [oneHotDecodeIdx_val_of_lt k (2 ^ k) (Nat.two_pow_pos k) bitsLo huLo_lt, hu_eq]
      · have hb1 : bits ⟨k, by omega⟩ = 1 := by
          rcases UnsignedGivens.zmod2_eq_zero_or_one (bits ⟨k, by omega⟩) with h0 | h1
          · exact absurd h0 hb0
          · exact h1
        have hu_eq : bitsToNat bits = 2 ^ k + bitsToNat bitsLo := by
          rw [hu_decomp, hb1, ZMod.val_one, mul_one, add_comm]
        dsimp only
        rw [oneHotDecodeIdx_val_of_lt k (D - 2 ^ k) (by omega) bitsLo (by omega), hu_eq]

/-- Explicit bit-assignment produced on `ket β` by `oneHotActiveCircuit` when `rOneHot = 0^D`. -/
noncomputable def oneHotActiveAssign {n : ℕ} (m D : ℕ) (hD : 1 ≤ D)
    (wAct : Wire n) (rIdx : QRegister m n) (rOneHot : QRegister D n)
    (β : BitAssignment n) : BitAssignment n :=
  UnsignedGivens.writeReg β rOneHot (fun j =>
    if j = oneHotDecodeIdx m D hD (fun i => β (rIdx i)) then β wAct else 0)

/-! ## Section 2: Control-Diagonal Catalytic Contract (`CtrlMuxCatalyticWith`) -/

section CtrlMuxCombinators

theorem disj_sys_cat_of {n k_sys k_ctrl b : ℕ}
    {rSys : QRegister k_sys n} {rCtrl : QRegister k_ctrl n} {rCat : QRegister b n}
    (hsc : rSys.DisjointWires rCtrl)
    (hac : (rSys.concat rCtrl hsc).DisjointWires rCat) :
    rSys.DisjointWires rCat := by
  rw [QRegister.disjoint_iff]
  intro i j
  exact UnsignedGivens.ne_spin_cat hsc hac i j

theorem disj_sysCat_ctrl_of {n k_sys k_ctrl b : ℕ}
    {rSys : QRegister k_sys n} {rCtrl : QRegister k_ctrl n} {rCat : QRegister b n}
    (hsc : rSys.DisjointWires rCtrl)
    (hac : (rSys.concat rCtrl hsc).DisjointWires rCat) :
    (rSys.concat rCat (disj_sys_cat_of hsc hac)).DisjointWires rCtrl := by
  rw [QRegister.disjoint_iff]
  intro idx l
  refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
  · simp only [QRegister.concat_apply_left]
    exact UnsignedGivens.ne_spin_ctrl hsc i l
  · simp only [QRegister.concat_apply_right]
    exact (UnsignedGivens.ne_ctrl_cat hsc hac l j).symm

theorem disj_sysCatCtrl_work_of {n k_sys k_ctrl b m : ℕ}
    {rSys : QRegister k_sys n} {rCtrl : QRegister k_ctrl n}
    {rCat : QRegister b n} {rWork : QRegister m n}
    (hsc : rSys.DisjointWires rCtrl)
    (hac : (rSys.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSys.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    ((rSys.concat rCat (disj_sys_cat_of hsc hac)).concat rCtrl
      (disj_sysCat_ctrl_of hsc hac)).DisjointWires rWork := by
  rw [QRegister.disjoint_iff]
  intro idx w
  refine Fin.addCases (fun sc => ?_) (fun l => ?_) idx
  · simp only [QRegister.concat_apply_left]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) sc
    · simp only [QRegister.concat_apply_left]
      exact UnsignedGivens.ne_spin_work hsc hac hdisj i w
    · simp only [QRegister.concat_apply_right]
      exact UnsignedGivens.ne_cat_work hsc hac hdisj j w
  · simp only [QRegister.concat_apply_right]
    exact UnsignedGivens.ne_ctrl_work hsc hac hdisj l w

/-- Control-multiplexed catalytic subroutine contract: `d` realizes `muxCtrlUnitary W_raw` on
`(rSys.concat rCat).concat rCtrl` with clean workspace `rWork`, so the raw unitary preserves every
control wire across ALL `2^b` catalyst basis states while acting as `(F c) ⊗ I` on `ψ ⊗ φ_cat`. -/
def CtrlMuxCatalyticWith {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_sys b k_ctrl m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rSys : QRegister k_sys n) (rCat : QRegister b n) (hSysCat : rSys.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hCtrl2 : (rSys.concat rCat hSysCat).DisjointWires rCtrl)
    (rWork : QRegister m n)
    (F : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys))
    (d : DynamicCircuit Var n) : Prop :=
  ∃ W_raw : Fin (2 ^ k_ctrl) → Unitary (2 ^ (k_sys + b)),
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace
      ((rSys.concat rCat hSysCat).concat rCtrl hCtrl2) rWork
      (UnsignedGivens.muxCtrlUnitary W_raw) d ∧
    ∀ (c : Fin (2 ^ k_ctrl)) (ψ : Fin (2 ^ k_sys) → ℂ),
      (W_raw c).1 *ᵥ prodState ψ φ_cat = prodState ((F c).1 *ᵥ ψ) φ_cat

theorem CtrlMuxCatalyticWith.identity {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_sys b k_ctrl m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rSys : QRegister k_sys n) (rCat : QRegister b n) (hSysCat : rSys.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hCtrl2 : (rSys.concat rCat hSysCat).DisjointWires rCtrl)
    (rWork : QRegister m n) :
    CtrlMuxCatalyticWith (Var := Var) φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork
      (fun _ => 1) .identity := by
  refine ⟨fun _ => 1, ?_, fun _ _ => by simp⟩
  rw [UnsignedGivens.muxCtrlUnitary_one]
  exact DynamicCircuit.realizesEmbeddedUnitaryWithCleanWorkspace_identity _ _

theorem CtrlMuxCatalyticWith.congrUnitary {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_sys b k_ctrl m : ℕ} [NeZero (2 ^ n)]
    {φ_cat : Fin (2 ^ b) → ℂ}
    {rSys : QRegister k_sys n} {rCat : QRegister b n} {hSysCat : rSys.DisjointWires rCat}
    {rCtrl : QRegister k_ctrl n} {hCtrl2 : (rSys.concat rCat hSysCat).DisjointWires rCtrl}
    {rWork : QRegister m n}
    {F₁ F₂ : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys)} {d : DynamicCircuit Var n}
    (hd : CtrlMuxCatalyticWith φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork F₁ d)
    (hF : F₁ = F₂) :
    CtrlMuxCatalyticWith φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork F₂ d :=
  hF ▸ hd

theorem CtrlMuxCatalyticWith.seq {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_sys b k_ctrl m : ℕ} [NeZero (2 ^ n)]
    {φ_cat : Fin (2 ^ b) → ℂ}
    {rSys : QRegister k_sys n} {rCat : QRegister b n} {hSysCat : rSys.DisjointWires rCat}
    {rCtrl : QRegister k_ctrl n} {hCtrl2 : (rSys.concat rCat hSysCat).DisjointWires rCtrl}
    {rWork : QRegister m n}
    (hdisj : ((rSys.concat rCat hSysCat).concat rCtrl hCtrl2).DisjointWires rWork)
    {F₁ F₂ : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : CtrlMuxCatalyticWith φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork F₁ d₁)
    (h₂ : CtrlMuxCatalyticWith φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork F₂ d₂) :
    CtrlMuxCatalyticWith φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork
      (fun c => F₂ c * F₁ c) (.seq d₁ d₂) := by
  obtain ⟨W₁, hw₁, hc₁⟩ := h₁
  obtain ⟨W₂, hw₂, hc₂⟩ := h₂
  refine ⟨fun c => W₂ c * W₁ c, ?_, ?_⟩
  · rw [← UnsignedGivens.muxCtrlUnitary_mul]
    exact hw₁.seq hdisj hw₂
  · intro c ψ
    calc
      (W₂ c * W₁ c).1 *ᵥ prodState ψ φ_cat
          = (W₂ c).1 *ᵥ ((W₁ c).1 *ᵥ prodState ψ φ_cat) := by
              rw [Submonoid.coe_mul, Matrix.mulVec_mulVec]
      _ = (W₂ c).1 *ᵥ prodState ((F₁ c).1 *ᵥ ψ) φ_cat := by rw [hc₁]
      _ = prodState ((F₂ c).1 *ᵥ ((F₁ c).1 *ᵥ ψ)) φ_cat := hc₂ c ((F₁ c).1 *ᵥ ψ)
      _ = prodState ((F₂ c * F₁ c).1 *ᵥ ψ) φ_cat := by
              rw [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem CtrlMuxCatalyticWith.ofSysCtrlCircuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_sys b k_ctrl m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rSys : QRegister k_sys n) (rCat : QRegister b n) (hSysCat : rSys.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hCtrl2 : (rSys.concat rCat hSysCat).DisjointWires rCtrl)
    (hsc : rSys.DisjointWires rCtrl)
    (rWork : QRegister m n)
    (F : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys)) (c_static : Circuit n)
    (heval : c_static.eval =
      (rSys.concat rCtrl hsc).embedUnitary (UnsignedGivens.muxCtrlUnitary F)) :
    CtrlMuxCatalyticWith (Var := Var) φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork F
      (.circuit c_static) := by
  let W_raw : Fin (2 ^ k_ctrl) → Unitary (2 ^ (k_sys + b)) :=
    fun c => (locLeft k_sys b).embedUnitary (F c)
  have hcomp_sys : (rSys.concat rCat hSysCat).compose (locLeft k_sys b) = rSys := by
    ext i
    have hi : locLeft k_sys b i = Fin.castAdd b i := by ext; simp [locLeft, locLeftOf]
    simp [QRegister.compose, hi]
  have heval_big : c_static.eval =
      ((rSys.concat rCat hSysCat).concat rCtrl hCtrl2).embedUnitary
        (UnsignedGivens.muxCtrlUnitary W_raw) := by
    rw [heval]
    apply Subtype.ext
    apply UnsignedGivens.matrix_ext_ket
    intro β
    rw [UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
      UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket]
    dsimp only [W_raw]
    rw [← QRegister.embedUnitary_compose, hcomp_sys]
  refine ⟨W_raw,
    DynamicCircuit.realizesEmbeddedUnitaryWithCleanWorkspace_circuit _ rWork _ _ heval_big, ?_⟩
  intro c ψ
  exact embedMatrix_locLeft_mulVec_prodState (F c).1 ψ φ_cat

theorem CtrlMuxCatalyticWith.pairCircuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_ctrl b m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rPair : QRegister 2 n) (rCat : QRegister b n) (hPairCat : rPair.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hPcCtrl : (rPair.concat rCat hPairCat).DisjointWires rCtrl)
    (hpc : rPair.DisjointWires rCtrl)
    (rWork : QRegister m n) (c2 : Circuit 2) :
    CtrlMuxCatalyticWith (Var := Var) φ_cat rPair rCat hPairCat rCtrl hPcCtrl rWork
      (fun _ => c2.eval) (.circuit (c2.onRegister rPair)) := by
  have hcomp : (rPair.concat rCtrl hpc).compose (locLeft 2 k_ctrl) = rPair := by
    ext i
    have hi : locLeft 2 k_ctrl i = Fin.castAdd k_ctrl i := by ext; simp [locLeft, locLeftOf]
    simp [QRegister.compose, hi]
  have heval : (c2.onRegister rPair).eval =
      (rPair.concat rCtrl hpc).embedUnitary (UnsignedGivens.muxCtrlUnitary (fun _ => c2.eval)) := by
    rw [Circuit.eval_onRegister, ← UnsignedGivens.locLeft_embedUnitary_eq_muxCtrlUnitary,
      ← QRegister.embedUnitary_compose, hcomp]
  exact CtrlMuxCatalyticWith.ofSysCtrlCircuit φ_cat rPair rCat hPairCat rCtrl hPcCtrl hpc
    rWork _ _ heval

theorem CtrlMuxCatalyticWith.wrapCliffordFrame {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_ctrl b m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rPair : QRegister 2 n) (rCat : QRegister b n) (hPairCat : rPair.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hPcCtrl : (rPair.concat rCat hPairCat).DisjointWires rCtrl)
    (hpc : rPair.DisjointWires rCtrl)
    (rWork : QRegister m n)
    (hdisj : ((rPair.concat rCat hPairCat).concat rCtrl hPcCtrl).DisjointWires rWork)
    (cPre cPost : Circuit 2)
    {G : Fin (2 ^ k_ctrl) → Unitary (2 ^ 2)} {d : DynamicCircuit Var n}
    (hd : CtrlMuxCatalyticWith φ_cat rPair rCat hPairCat rCtrl hPcCtrl rWork G d) :
    CtrlMuxCatalyticWith φ_cat rPair rCat hPairCat rCtrl hPcCtrl rWork
      (fun c => cPost.eval * G c * cPre.eval)
      (.seq (.circuit (cPre.onRegister rPair)) (.seq d (.circuit (cPost.onRegister rPair)))) := by
  have hpre := CtrlMuxCatalyticWith.pairCircuit (Var := Var) φ_cat rPair rCat hPairCat rCtrl
    hPcCtrl hpc rWork cPre
  have hpost := CtrlMuxCatalyticWith.pairCircuit (Var := Var) φ_cat rPair rCat hPairCat rCtrl
    hPcCtrl hpc rWork cPost
  refine (hpre.seq hdisj (hd.seq hdisj hpost)).congrUnitary ?_
  funext c
  simp only [mul_assoc]

theorem CtrlMuxCatalyticWith.czActivePair0 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_ctrl b m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b) → ℂ)
    (rPair : QRegister 2 n) (rCat : QRegister b n) (hPairCat : rPair.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hPcCtrl : (rPair.concat rCat hPairCat).DisjointWires rCtrl)
    (hpc : rPair.DisjointWires rCtrl)
    (actIdx : Fin k_ctrl)
    (rWork : QRegister m n) :
    let hne : rCtrl actIdx ≠ rPair 0 := (QRegister.disjoint_iff.mp hpc 0 actIdx).symm
    CtrlMuxCatalyticWith (Var := Var) φ_cat rPair rCat hPairCat rCtrl hPcCtrl rWork
      (fun c =>
        if basisBits k_ctrl c actIdx = 0 then 1
        else (QRegister.singleton (0 : Wire 2)).embedUnitary Qubit.Z)
      (.circuit (UnsignedGivens.czCircuit (rCtrl actIdx) (rPair 0) hne)) := by
  intro hne
  apply CtrlMuxCatalyticWith.ofSysCtrlCircuit φ_cat rPair rCat hPairCat rCtrl hPcCtrl hpc rWork
  apply Subtype.ext
  apply UnsignedGivens.matrix_ext_ket
  intro β
  rw [UnsignedGivens.evolve_czCircuit_ket, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket]
  have hact_bit : basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) actIdx = β (rCtrl actIdx) :=
    congrFun (UnsignedGivens.basisBits_symm_eq (fun j => β (rCtrl j))) actIdx
  rw [hact_bit]
  rcases UnsignedGivens.zmod2_eq_zero_or_one (β (rCtrl actIdx)) with ha0 | ha1
  · rw [ha0, zero_mul, UnsignedGivens.zmod2_val_zero, pow_zero, one_smul,
      ite_eq_left_of_eq_true _ _ (eq_true rfl),
      QRegister.embedUnitary_val, Submonoid.coe_one, QRegister.embedMatrix_one, Matrix.one_mulVec]
  · have h10 : (1 : ZMod 2) ≠ 0 := by decide
    have hcomp0 : rPair.compose (QRegister.singleton (0 : Wire 2)) =
        QRegister.singleton (rPair 0) := by
      ext i; rw [Subsingleton.elim i 0]; rfl
    have hz_eq : (QRegister.singleton (rPair 0)).embedUnitary Qubit.Z =
        (Circuit.Z (rPair 0)).eval := by
      rw [Circuit.eval_single]; rfl
    rw [ha1, one_mul, ite_eq_right_of_eq_false _ _ (eq_false h10),
      ← QRegister.embedUnitary_compose, hcomp0, hz_eq, UnsignedGivens.evolve_Z_ket]

private theorem muxLiftReg_embedUnitary_mulVec_prodState {k k₁ b : ℕ}
    (sel : QRegister k₁ k)
    (wSub : Unitary (2 ^ (k₁ + b))) (U : Unitary (2 ^ k₁)) (φ_cat : Fin (2 ^ b) → ℂ)
    (hcatSub : ∀ ζ : Fin (2 ^ k₁) → ℂ, wSub.1 *ᵥ prodState ζ φ_cat = prodState (U.1 *ᵥ ζ) φ_cat)
    (ξ : Fin (2 ^ k) → ℂ) :
    ((UnsignedGivens.muxLiftReg k b sel).embedUnitary wSub).1 *ᵥ prodState ξ φ_cat =
      prodState ((sel.embedUnitary U).1 *ᵥ ξ) φ_cat := by
  let selLift : QRegister (k₁ + b) (k + b) := UnsignedGivens.muxLiftReg k b sel
  funext g
  let x := (locLeft k b).extractIndex g
  let y := (locRight k b).extractIndex g
  let slice : Fin (2 ^ k₁) → ℂ := fun u ↦ ξ (sel.replaceIndex x u)
  have hLiftL : selLift.compose (locLeft k₁ b) = (locLeft k b).compose sel := by
    ext i
    have hi : locLeft k₁ b i = Fin.castAdd b i := by
      ext; simp [locLeft, locLeftOf, QRegister.block]
    simp [selLift, UnsignedGivens.muxLiftReg, QRegister.compose, hi]
  have hLiftR : selLift.compose (locRight k₁ b) = locRight k b := by
    ext j
    have hj : locRight k₁ b j = Fin.natAdd k₁ j := by
      ext; simp [locRight, locRightOf, QRegister.block]
    simp [selLift, UnsignedGivens.muxLiftReg, QRegister.compose, hj]
  have hExtG :
      selLift.extractIndex g = (blockSplitEquiv k₁ b).symm (sel.extractIndex x, y) := by
    apply (blockSplitEquiv k₁ b).injective
    rw [(blockSplitEquiv k₁ b).apply_symm_apply]
    ext1
    · change (locLeft k₁ b).extractIndex (selLift.extractIndex g) = sel.extractIndex x
      rw [← QRegister.extractIndex_compose, hLiftL, QRegister.extractIndex_compose]
    · change (locRight k₁ b).extractIndex (selLift.extractIndex g) = y
      rw [← QRegister.extractIndex_compose, hLiftR]
  have hRepProd : ∀ p : Fin (2 ^ (k₁ + b)),
      prodState ξ φ_cat (selLift.replaceIndex g p) = prodState slice φ_cat p := by
    intro p
    have hRepL : (locLeft k b).extractIndex (selLift.replaceIndex g p) =
        sel.replaceIndex x ((locLeft k₁ b).extractIndex p) := by
      apply (basisBits k).injective
      funext w
      rw [(locLeft k b).basisBits_extractIndex]
      by_cases hw : w ∈ Set.range sel.wires
      · obtain ⟨i, rfl⟩ := hw
        have hwi : locLeft k b (sel i) = selLift (Fin.castAdd b i) := by
          simp [selLift, UnsignedGivens.muxLiftReg, QRegister.compose]
        have hcast : Fin.castAdd b i = locLeft k₁ b i := by
          ext; simp [locLeft, locLeftOf, QRegister.block]
        rw [hwi, selLift.basisBits_replaceIndex_apply, sel.basisBits_replaceIndex_apply,
          (locLeft k₁ b).basisBits_extractIndex, hcast]
      · have hwOut : locLeft k b w ∉ Set.range selLift.wires := by
          rintro ⟨idx, hidx⟩
          refine Fin.addCases (fun i hi ↦ ?_) (fun j hj ↦ ?_) idx hidx
          · simp only [selLift, UnsignedGivens.muxLiftReg, QRegister.concat_apply_left,
              QRegister.compose_apply] at hi
            exact hw ⟨i, (locLeft k b).wires.injective hi⟩
          · have hv := congrArg Fin.val hj
            have hlt : w.val < k := w.isLt
            simp [selLift, UnsignedGivens.muxLiftReg, locLeft, locLeftOf, locRight, locRightOf,
              QRegister.block] at hv
            omega
        rw [selLift.basisBits_replaceIndex_of_not_mem g p _ hwOut,
          sel.basisBits_replaceIndex_of_not_mem x _ w hw,
          ← (locLeft k b).basisBits_extractIndex]
    have hRepR : (locRight k b).extractIndex (selLift.replaceIndex g p) =
        (locRight k₁ b).extractIndex p := by
      apply (basisBits b).injective
      funext j
      have hwj : locRight k b j = selLift (Fin.natAdd k₁ j) := by
        simp [selLift, UnsignedGivens.muxLiftReg]
      have hnat : Fin.natAdd k₁ j = locRight k₁ b j := by
        ext; simp [locRight, locRightOf, QRegister.block]
      rw [(locRight k b).basisBits_extractIndex, hwj, selLift.basisBits_replaceIndex_apply,
        (locRight k₁ b).basisBits_extractIndex, hnat]
    simp only [prodState, prodStateOf, slice, hRepL, hRepR]
  change (selLift.embedMatrix wSub.1).mulVec (prodState ξ φ_cat) g =
    ((sel.embedMatrix U.1).mulVec ξ x) * φ_cat y
  rw [selLift.embedMatrix_mulVec_apply, sel.embedMatrix_mulVec_apply]
  have hSum :
      (∑ p : Fin (2 ^ (k₁ + b)),
        wSub.1 (selLift.extractIndex g) p *
          prodState ξ φ_cat (selLift.basisSplitEquiv.symm (p, (selLift.basisSplitEquiv g).2))) =
      (wSub.1 *ᵥ prodState slice φ_cat) (selLift.extractIndex g) := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    change wSub.1 (selLift.extractIndex g) p * prodState ξ φ_cat (selLift.replaceIndex g p) = _
    rw [hRepProd p]
  rw [hSum, hcatSub slice, hExtG, prodState_symm]
  congr 1

theorem CtrlMuxCatalyticWith.widenSys {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_sys k_sub b k_ctrl m : ℕ} [NeZero (2 ^ n)]
    {φ_cat : Fin (2 ^ b) → ℂ}
    {rSys : QRegister k_sys n} {sel : QRegister k_sub k_sys}
    {rCat : QRegister b n}
    (hSysCat : rSys.DisjointWires rCat)
    (hSubCat : (rSys.compose sel).DisjointWires rCat)
    {rCtrl : QRegister k_ctrl n}
    (hCtrl2 : (rSys.concat rCat hSysCat).DisjointWires rCtrl)
    (hSubCtrl : ((rSys.compose sel).concat rCat hSubCat).DisjointWires rCtrl)
    {rWork : QRegister m n}
    {F : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sub)} {d : DynamicCircuit Var n}
    (hd : CtrlMuxCatalyticWith φ_cat (rSys.compose sel) rCat hSubCat rCtrl hSubCtrl rWork F d) :
    CtrlMuxCatalyticWith φ_cat rSys rCat hSysCat rCtrl hCtrl2 rWork
      (fun c => sel.embedUnitary (F c)) d := by
  obtain ⟨W_sub, hwSub, hcatSub⟩ := hd
  let selSC : QRegister (k_sub + b) (k_sys + b) := UnsignedGivens.muxLiftReg k_sys b sel
  have hcompSC : (rSys.concat rCat hSysCat).compose selSC =
      (rSys.compose sel).concat rCat hSubCat :=
    UnsignedGivens.compose_muxLiftReg rSys rCat hSysCat sel hSubCat
  have hdisjSC : ((rSys.concat rCat hSysCat).compose selSC).DisjointWires rCtrl := by
    rw [hcompSC]; exact hSubCtrl
  have hcompAll :
      ((rSys.concat rCat hSysCat).concat rCtrl hCtrl2).compose
        (UnsignedGivens.muxLiftReg (k_sys + b) k_ctrl selSC) =
      ((rSys.compose sel).concat rCat hSubCat).concat rCtrl hSubCtrl := by
    rw [UnsignedGivens.compose_muxLiftReg (rSys.concat rCat hSysCat) rCtrl hCtrl2 selSC hdisjSC]
    congr 1
  refine ⟨fun c => selSC.embedUnitary (W_sub c), ?_, ?_⟩
  · rw [← UnsignedGivens.muxLiftReg_embedUnitary_muxCtrlUnitary selSC W_sub]
    rw [← hcompAll] at hwSub
    exact hwSub.widenActive
  · intro c ψ
    exact muxLiftReg_embedUnitary_mulVec_prodState sel (W_sub c) (F c) φ_cat (hcatSub c) ψ

theorem CtrlMuxCatalyticWith.widenFineLowTop {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k b_skip B b_high k_ctrl m : ℕ} [NeZero (2 ^ n)]
    {rSys : QRegister k n} {rCat : QRegister (b_skip + B) n}
    (hSysCat : rSys.DisjointWires rCat)
    (hSysHigh : rSys.DisjointWires (rCat.compose (locRight b_skip B)))
    {rCtrl : QRegister k_ctrl n}
    (hCtrl2 : (rSys.concat rCat hSysCat).DisjointWires rCtrl)
    (hCtrl_3 : (rSys.concat (rCat.compose (locRight b_skip B)) hSysHigh).DisjointWires rCtrl)
    {rWork : QRegister m n}
    {F : Fin (2 ^ k_ctrl) → Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : CtrlMuxCatalyticWith (phaseGradientFineLow B b_high)
      rSys (rCat.compose (locRight b_skip B)) hSysHigh rCtrl hCtrl_3 rWork F d) :
    CtrlMuxCatalyticWith (phaseGradientFineLow (b_skip + B) b_high)
      rSys rCat hSysCat rCtrl hCtrl2 rWork F d := by
  obtain ⟨W_10, hw10, hcat10⟩ := hd
  let selInner : QRegister (k + B) ((k + b_skip) + B) :=
    UnsignedGivens.muxLiftReg (k + b_skip) B (locLeft k b_skip)
  let reassoc : QRegister ((k + b_skip) + B) (k + (b_skip + B)) :=
    QRegister.block 0 ((k + b_skip) + B) (by omega)
  let selCat : QRegister (k + B) (k + (b_skip + B)) := reassoc.compose selInner
  have hcompSC : (rSys.concat rCat hSysCat).compose selCat =
      rSys.concat (rCat.compose (locRight b_skip B)) hSysHigh := by
    ext idx
    refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
    · have hi : selCat (Fin.castAdd B i) = Fin.castAdd (b_skip + B) i := by
        ext
        simp [selCat, reassoc, selInner, UnsignedGivens.muxLiftReg, locLeft, locLeftOf,
          QRegister.block,
          QRegister.compose]
      simp [QRegister.compose, hi]
    · have hj : selCat (Fin.natAdd k j) = Fin.natAdd k (locRight b_skip B j) := by
        ext
        simp [selCat, reassoc, selInner, UnsignedGivens.muxLiftReg, locRight, locRightOf,
          QRegister.block,
          QRegister.compose]
        omega
      simp [QRegister.compose, hj]
  have hdisjSC : ((rSys.concat rCat hSysCat).compose selCat).DisjointWires rCtrl := by
    rw [hcompSC]; exact hCtrl_3
  have hcompAll :
      ((rSys.concat rCat hSysCat).concat rCtrl hCtrl2).compose
        (UnsignedGivens.muxLiftReg (k + (b_skip + B)) k_ctrl selCat) =
      (rSys.concat (rCat.compose (locRight b_skip B)) hSysHigh).concat rCtrl hCtrl_3 := by
    rw [UnsignedGivens.compose_muxLiftReg (rSys.concat rCat hSysCat) rCtrl hCtrl2 selCat hdisjSC]
    congr 1
  refine ⟨fun c => selCat.embedUnitary (W_10 c), ?_, ?_⟩
  · rw [← UnsignedGivens.muxLiftReg_embedUnitary_muxCtrlUnitary selCat W_10]
    rw [← hcompAll] at hw10
    exact hw10.widenActive
  · intro c ξ
    let wExt : Unitary (2 ^ ((k + b_skip) + B)) := selInner.embedUnitary (W_10 c)
    have hcatExt : ∀ ζ : Fin (2 ^ (k + b_skip)) → ℂ,
        wExt.1 *ᵥ prodState ζ (phaseGradientFineLow B b_high) =
          prodState (((locLeft k b_skip).embedUnitary (F c)).1 *ᵥ ζ)
            (phaseGradientFineLow B b_high) :=
      muxLiftReg_embedUnitary_mulVec_prodState (locLeft k b_skip) (W_10 c) (F c) _ (hcat10 c)
    have hsel_eq : selCat.embedUnitary (W_10 c) = reassoc.embedUnitary wExt :=
      QRegister.embedUnitary_compose reassoc selInner (W_10 c)
    dsimp only
    rw [hsel_eq]
    funext g
    let ζ : Fin (2 ^ (k + b_skip)) → ℂ :=
      prodState ξ (phaseGradientFineLow b_skip (B + b_high))
    let ePow : Fin (2 ^ ((k + b_skip) + B)) ≃ Fin (2 ^ (k + (b_skip + B))) :=
      finCongr (by rw [Nat.add_assoc])
    have hRepAll : ∀ p : Fin (2 ^ ((k + b_skip) + B)), reassoc.replaceIndex g p = ePow p := by
      intro p
      apply (basisBits (k + (b_skip + B))).injective
      funext w
      have hw : w = reassoc ⟨w.val, by omega⟩ := by ext; simp [reassoc, QRegister.block]
      rw [hw, reassoc.basisBits_replaceIndex_apply]
      simp [reassoc, ePow, QRegister.block, basisBits_eq_div_mod]
    have hAssocProd : ∀ (α : Fin (2 ^ k) → ℂ) (q : Fin (2 ^ ((k + b_skip) + B))),
        prodState α (phaseGradientFineLow (b_skip + B) b_high) (ePow q) =
          prodState (prodState α (phaseGradientFineLow b_skip (B + b_high)))
            (phaseGradientFineLow B b_high) q := by
      intro α q
      let q' : Fin (2 ^ (k + (b_skip + B))) := ePow q
      rw [UnsignedGivens.phaseGradientFineLow_eq_prodState_top b_skip B b_high]
      simp only [prodState, prodStateOf]
      have h1 : (locLeft k (b_skip + B)).extractIndex q' =
          (locLeft k b_skip).extractIndex ((locLeft (k + b_skip) B).extractIndex q) := by
        apply Fin.ext
        rw [extractIndex_locLeft_val, extractIndex_locLeft_val, extractIndex_locLeft_val]
        exact (Nat.mod_mod_of_dvd q.val (Nat.pow_dvd_pow 2 (Nat.le_add_right k b_skip))).symm
      have h2 : (locLeft b_skip B).extractIndex ((locRight k (b_skip + B)).extractIndex q') =
          (locRight k b_skip).extractIndex ((locLeft (k + b_skip) B).extractIndex q) := by
        apply Fin.ext
        rw [extractIndex_locLeft_val, extractIndex_locRight_val,
          extractIndex_locRight_val, extractIndex_locLeft_val]
        change (q.val / 2 ^ k) % 2 ^ b_skip = (q.val % 2 ^ (k + b_skip)) / 2 ^ k
        rw [pow_add 2 k b_skip, Nat.mod_mul_right_div_self]
      have h3 : (locRight b_skip B).extractIndex ((locRight k (b_skip + B)).extractIndex q') =
          (locRight (k + b_skip) B).extractIndex q := by
        apply Fin.ext
        rw [extractIndex_locRight_val, extractIndex_locRight_val, extractIndex_locRight_val]
        change (q.val / 2 ^ k) / 2 ^ b_skip = q.val / 2 ^ (k + b_skip)
        rw [Nat.div_div_eq_div_mul, ← pow_add 2 k b_skip]
      rw [h1, h2, h3, mul_assoc]
    have hExtG : (reassoc.extractIndex g).val = g.val := by
      suffices reassoc.extractIndex g = ePow.symm g from congrArg Fin.val this
      apply (basisBits ((k + b_skip) + B)).injective
      funext idx
      rw [reassoc.basisBits_extractIndex]
      simp [reassoc, ePow, QRegister.block, basisBits_eq_div_mod]
    have hGeEq : ePow (reassoc.extractIndex g) = g := Fin.ext hExtG
    change (reassoc.embedMatrix wExt.1).mulVec
        (prodState ξ (phaseGradientFineLow (b_skip + B) b_high)) g =
      prodState ((F c).1 *ᵥ ξ) (phaseGradientFineLow (b_skip + B) b_high) g
    rw [reassoc.embedMatrix_mulVec_apply]
    have hSum :
        (∑ p : Fin (2 ^ ((k + b_skip) + B)),
          wExt.1 (reassoc.extractIndex g) p *
            prodState ξ (phaseGradientFineLow (b_skip + B) b_high)
              (reassoc.basisSplitEquiv.symm (p, (reassoc.basisSplitEquiv g).2))) =
        (wExt.1 *ᵥ prodState ζ (phaseGradientFineLow B b_high))
          (reassoc.extractIndex g) := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun p _ => ?_
      change wExt.1 (reassoc.extractIndex g) p *
        prodState ξ (phaseGradientFineLow (b_skip + B) b_high)
          (reassoc.replaceIndex g p) = _
      rw [hRepAll p, hAssocProd ξ p]
    rw [hSum, hcatExt ζ, QRegister.embedUnitary_val, embedMatrix_locLeft_mulVec_prodState,
      ← hAssocProd ((F c).1 *ᵥ ξ) (reassoc.extractIndex g), hGeEq]

private theorem embedUnitary_inv_eq' {k n : ℕ} (r : QRegister k n) (U : Unitary (2 ^ k)) :
    (r.embedUnitary U)⁻¹ = r.embedUnitary U⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  change r.embedMatrix U⁻¹.1 * r.embedMatrix U.1 = 1
  rw [← r.embedMatrix_mul]
  have hinv : U⁻¹.1 * U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
  rw [hinv, r.embedMatrix_one]

/-- Control-diagonal catalytic phase-kick bridge (`W_raw c` diagonal on `rCtrl` across ALL `2^B`
catalyst basis states), with optional quarter-turn offset bit `q_off_fn < 2`. -/
theorem CtrlMuxCatalyticWith.ofRawKickWithOffset
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k_ctrl B m : ℕ} [NeZero (2 ^ n)]
    (rPair : QRegister 2 n) (rCat : QRegister B n) (hPairCat : rPair.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hPcCtrl : (rPair.concat rCat hPairCat).DisjointWires rCtrl)
    (rWork : QRegister m n)
    (c_ref : Circuit n) (d : DynamicCircuit Var n)
    (hclean : UnsignedGivens.RealizesCleanRef rWork c_ref d)
    (a_lo_fn : ZMod 2 → Fin (2 ^ k_ctrl) → ℕ)
    (ha_lo : ∀ b₁ c, a_lo_fn b₁ c < 2 ^ B)
    (b_mid_fn b_top_fn q_off_fn : ZMod 2 → Fin (2 ^ k_ctrl) → ℕ)
    (hb_mid : ∀ b₁ c, b_mid_fn b₁ c < 2)
    (hb_top : ∀ b₁ c, b_top_fn b₁ c < 2)
    (hq_off : ∀ b₁ c, q_off_fn b₁ c < 2)
    (hket : ∀ β : BitAssignment n, (∀ idx : Fin m, β (rWork idx) = 0) →
      let b₀ := β (rPair 0)
      let b₁ := β (rPair 1)
      let c := UnsignedGivens.localIdx rCtrl β
      let y := UnsignedGivens.localIdx rCat β
      let ψ_off : ℂ := Complex.I ^ (q_off_fn b₁ c) * (-1 : ℂ) ^ (b₀.val * q_off_fn b₁ c)
      c_ref.eval.1.mulVec (UnsignedGivens.ket β) =
        (ψ_off *
          UnsignedGivens.rawPhaseStepVal B (a_lo_fn b₁ c) (b_mid_fn b₁ c) (b_top_fn b₁ c) b₀ y) •
          UnsignedGivens.ket (UnsignedGivens.writeReg β rCat
            (basisBits B (UnsignedGivens.signedAddModPerm B (a_lo_fn b₁ c) (ha_lo b₁ c) b₀ y)))) :
    let K_fn := fun b₁ c =>
      a_lo_fn b₁ c + 2 ^ B * b_mid_fn b₁ c + 2 ^ (B + 1) * b_top_fn b₁ c +
        2 ^ (B + 1) * q_off_fn b₁ c
    let α_fn := fun b₁ c => 2 * Real.pi * (K_fn b₁ c : ℝ) / (2 : ℝ) ^ (B + 3)
    CtrlMuxCatalyticWith (phaseGradientFineLow B 3) rPair rCat hPairCat rCtrl hPcCtrl rWork
      (fun c => UnsignedGivens.phaseDiagUnitary (UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c))
        (UnsignedGivens.genKick4_unit (α_fn 0 c) (α_fn 1 c))) d := by
  intro K_fn α_fn
  let rPC := rPair.concat rCat hPairCat
  let eSplit := blockSplitEquiv 2 B
  let b0_of : Fin (2 ^ 2) → ZMod 2 := fun p2 => basisBits 2 p2 0
  let b1_of : Fin (2 ^ 2) → ZMod 2 := fun p2 => basisBits 2 p2 1
  let π_c : Fin (2 ^ k_ctrl) → Fin (2 ^ 2) → Equiv.Perm (Fin (2 ^ B)) :=
    fun c p2 => UnsignedGivens.signedAddModPerm B (a_lo_fn (b1_of p2) c) (ha_lo _ c) (b0_of p2)
  let π_prod : Fin (2 ^ k_ctrl) → Equiv.Perm (Fin (2 ^ 2) × Fin (2 ^ B)) := fun c =>
    { toFun := fun p => (p.1, π_c c p.1 p.2)
      invFun := fun p => (p.1, (π_c c p.1).symm p.2)
      left_inv := fun ⟨p2, y⟩ => by simp
      right_inv := fun ⟨p2, y⟩ => by simp }
  let π_full : Fin (2 ^ k_ctrl) → Equiv.Perm (Fin (2 ^ (2 + B))) :=
    fun c => eSplit.trans ((π_prod c).trans eSplit.symm)
  let ψ_off_of : Fin (2 ^ 2) → Fin (2 ^ k_ctrl) → ℂ := fun p2 c =>
    Complex.I ^ (q_off_fn (b1_of p2) c) *
      (-1 : ℂ) ^ ((b0_of p2).val * q_off_fn (b1_of p2) c)
  let φ_step : Fin (2 ^ 2) → Fin (2 ^ k_ctrl) → Fin (2 ^ B) → ℂ :=
    fun p2 c y => ψ_off_of p2 c * UnsignedGivens.rawPhaseStepVal B (a_lo_fn (b1_of p2) c)
      (b_mid_fn (b1_of p2) c) (b_top_fn (b1_of p2) c) (b0_of p2) y
  have hunit_off : ∀ p2 c, star (ψ_off_of p2 c) * ψ_off_of p2 c = 1 := by
    intro p2 c
    have hn : ‖ψ_off_of p2 c‖ = 1 := by
      dsimp [ψ_off_of]
      simp [norm_pow, Complex.norm_I]
    rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
      Complex.ofReal_one]
  have hunit_step : ∀ p2 c y, star (φ_step p2 c y) * φ_step p2 c y = 1 := by
    intro p2 c y
    dsimp [φ_step]
    calc
      star (ψ_off_of p2 c * UnsignedGivens.rawPhaseStepVal B _ _ _ _ y) *
          (ψ_off_of p2 c * UnsignedGivens.rawPhaseStepVal B _ _ _ _ y)
          = (star (ψ_off_of p2 c) * ψ_off_of p2 c) *
              (star (UnsignedGivens.rawPhaseStepVal B _ _ _ _ y) *
                UnsignedGivens.rawPhaseStepVal B _ _ _ _ y) := by
            rw [star_mul]; ring
      _ = 1 * 1 := by rw [hunit_off, UnsignedGivens.star_mul_self_rawPhaseStepVal]
      _ = 1 := mul_one 1
  let d_full : Fin (2 ^ k_ctrl) → Fin (2 ^ (2 + B)) → ℂ :=
    fun c g => φ_step (eSplit g).1 c (eSplit g).2
  have hd_unit : ∀ c g, star (d_full c g) * d_full c g = 1 :=
    fun c g => hunit_step _ c _
  let W_raw : Fin (2 ^ k_ctrl) → Unitary (2 ^ (2 + B)) :=
    fun c =>
      Operator.permutationUnitary (π_full c) *
      UnsignedGivens.phaseDiagUnitary (d_full c) (hd_unit c)
  have hwRaw_mulVec : ∀ c (ψ : Fin (2 ^ (2 + B)) → ℂ),
      (W_raw c).1.mulVec ψ =
        (Operator.permutationUnitary (π_full c)).1.mulVec
          ((UnsignedGivens.phaseDiagUnitary (d_full c) (hd_unit c)).1.mulVec ψ) := by
    intro c ψ; simp only [W_raw, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  have hwRaw_single : ∀ c p2 y,
      (W_raw c).1.mulVec (Pi.single (eSplit.symm (p2, y)) 1) =
        φ_step p2 c y • Pi.single (eSplit.symm (p2, π_c c p2 y)) 1 := by
    intro c p2 y
    let g := eSplit.symm (p2, y)
    rw [hwRaw_mulVec]
    have hdiag : (UnsignedGivens.phaseDiagUnitary (d_full c) (hd_unit c)).1.mulVec (Pi.single g 1) =
        d_full c g • Pi.single g 1 := by
      funext idx
      rw [UnsignedGivens.phaseDiagUnitary_mulVec]
      by_cases h : idx = g
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [hdiag, Matrix.mulVec_smul, Operator.permutationUnitary_mulVec_single]
    simp [g, d_full, π_full, π_prod]
  refine ⟨W_raw, ?_, ?_⟩
  · apply hclean.toEmbeddedUnitary
    apply UnsignedGivens.matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec, UnsignedGivens.register_basisOutcomeProjector_zero_ket]
    by_cases h0 : ∀ i : Fin m, β (rWork i) = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), hket β h0,
        UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket]
      let p2 := UnsignedGivens.localIdx rPair β
      let y := UnsignedGivens.localIdx rCat β
      let c := UnsignedGivens.localIdx rCtrl β
      have hb0_eq : b0_of p2 = β (rPair 0) :=
        congrFun (UnsignedGivens.basisBits_symm_eq (fun i => β (rPair i))) 0
      have hb1_eq : b1_of p2 = β (rPair 1) :=
        congrFun (UnsignedGivens.basisBits_symm_eq (fun i => β (rPair i))) 1
      have hloc_PC : rPC.extractIndex ((basisBits n).symm β) = eSplit.symm (p2, y) := by
        apply eSplit.injective
        rw [eSplit.apply_symm_apply]
        ext1
        · apply (basisBits 2).injective; funext i
          change basisBits 2 ((locLeft 2 B).extractIndex (rPC.extractIndex _)) i =
            basisBits 2 p2 i
          rw [(locLeft 2 B).basisBits_extractIndex, rPC.basisBits_extractIndex,
            UnsignedGivens.basisBits_symm_eq, UnsignedGivens.basisBits_symm_eq]
          have hi : rPC (locLeft 2 B i) = rPair i := by
            have hcast : locLeft 2 B i = Fin.castAdd B i := by ext; simp [locLeft, locLeftOf]
            simp [rPC, hcast]
          rw [hi]
        · apply (basisBits B).injective; funext j
          change basisBits B ((locRight 2 B).extractIndex (rPC.extractIndex _)) j =
            basisBits B y j
          rw [(locRight 2 B).basisBits_extractIndex, rPC.basisBits_extractIndex,
            UnsignedGivens.basisBits_symm_eq, UnsignedGivens.basisBits_symm_eq]
          have hj : rPC (locRight 2 B j) = rCat j := by
            have hnat : locRight 2 B j = Fin.natAdd 2 j := by ext; simp [locRight, locRightOf]
            simp [rPC, hnat]
          rw [hj]
      rw [QRegister.embedUnitary_val, UnsignedGivens.ket, basisState,
        rPC.embedMatrix_mulVec_single_factors,
        hloc_PC, hwRaw_single c p2 y, QRegister.tensorState_smul_left,
        rPC.tensorState_single_replaceIndex]
      have hφ_eq : φ_step p2 c y =
          (Complex.I ^ (q_off_fn (β (rPair 1)) c) *
            (-1 : ℂ) ^ ((β (rPair 0)).val * q_off_fn (β (rPair 1)) c)) *
          UnsignedGivens.rawPhaseStepVal B (a_lo_fn (β (rPair 1)) c) (b_mid_fn (β (rPair 1)) c)
            (b_top_fn (β (rPair 1)) c) (β (rPair 0)) y := by
        dsimp only [φ_step, ψ_off_of]
        rw [hb0_eq, hb1_eq]
      have hπ_eq : π_c c p2 y =
          UnsignedGivens.signedAddModPerm B (a_lo_fn (β (rPair 1)) c) (ha_lo (β (rPair 1)) c)
            (β (rPair 0)) y := by
        dsimp only [π_c]
        rw [hb1_eq, hb0_eq]
      rw [hφ_eq, hπ_eq]
      congr 1; congr 1
      symm
      apply (basisBits n).injective; funext w
      by_cases hwPC : w ∈ Set.range rPC.wires
      · obtain ⟨idx, rfl⟩ := hwPC
        rw [rPC.basisBits_replaceIndex_apply]
        refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
        · have hi_pc : rPC (Fin.castAdd B i) = rPair i := QRegister.concat_apply_left _ _ _ i
          have hnot_cat : rPair i ∉ Set.range rCat.wires := by
            rintro ⟨j, hj⟩; exact QRegister.disjoint_iff.mp hPairCat i j hj.symm
          rw [hi_pc, UnsignedGivens.basisBits_symm_eq,
            UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hnot_cat]
          have hl : Fin.castAdd B i = locLeft 2 B i := by ext; simp [locLeft, locLeftOf]
          rw [hl, ← (locLeft 2 B).basisBits_extractIndex, extractIndex_locLeft_symm,
            UnsignedGivens.basisBits_symm_eq]
        · have hj_pc : rPC (Fin.natAdd 2 j) = rCat j := QRegister.concat_apply_right _ _ _ j
          rw [hj_pc, UnsignedGivens.basisBits_symm_eq, UnsignedGivens.writeReg_apply_reg]
          have hr : Fin.natAdd 2 j = locRight 2 B j := by ext; simp [locRight, locRightOf]
          rw [hr, ← (locRight 2 B).basisBits_extractIndex, extractIndex_locRight_symm]
      · have hnot_cat : w ∉ Set.range rCat.wires := by
          rintro ⟨j, rfl⟩; exact hwPC ⟨Fin.natAdd 2 j, QRegister.concat_apply_right _ _ _ j⟩
        rw [rPC.basisBits_replaceIndex_of_not_mem _ _ _ hwPC, UnsignedGivens.basisBits_symm_eq,
          UnsignedGivens.basisBits_symm_eq,
            UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hnot_cat]
    · simp [h0]
  · have hoff_exp : ∀ (wp : ZMod 2) (q : ℕ), q < 2 →
        Complex.I ^ q * (-1 : ℂ) ^ (wp.val * q) =
          Complex.exp ((if wp = 0 then (1 : ℂ) else -1) *
            (2 * Real.pi * Complex.I * ((2 ^ (B + 1) * q : ℕ) : ℂ)) / 2 ^ (B + 3)) := by
      intro wp q hq
      have hpow : (2 : ℂ) ^ (B + 3) = (2 : ℂ) ^ (B + 1) * 4 := by
        rw [show B + 3 = (B + 1) + 2 by omega, pow_add]; norm_num
      have hB1_ne : (2 : ℂ) ^ (B + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
      have hpi_pos : Complex.exp (↑(Real.pi / 2) * Complex.I) = Complex.I := by
        rw [Complex.exp_mul_I]; simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
      have hpi_neg : Complex.exp (↑(-(Real.pi / 2)) * Complex.I) = -Complex.I := by
        rw [Complex.exp_mul_I, Complex.ofReal_neg]
        simp [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
      have hq_cases : q = 0 ∨ q = 1 := by omega
      rcases hq_cases with rfl | rfl
      · simp
      · rcases UnsignedGivens.zmod2_eq_zero_or_one wp with rfl | rfl
        · simp only [ZMod.val_zero, mul_one, pow_one, pow_zero, ↓reduceIte, one_mul]
          push_cast
          rw [hpow]
          have harg : 2 * ↑Real.pi * Complex.I * 2 ^ (B + 1) / (2 ^ (B + 1) * 4) =
              ↑(Real.pi / 2) * Complex.I := by
            field_simp [hB1_ne]; push_cast; ring
          rw [harg, hpi_pos]
        · have h10 : (1 : ZMod 2) ≠ 0 := by decide
          simp only [ZMod.val_one, mul_one, pow_one, h10, ↓reduceIte]
          push_cast
          rw [hpow]
          have harg : -1 * (2 * ↑Real.pi * Complex.I * 2 ^ (B + 1)) / (2 ^ (B + 1) * 4) =
              ↑(-(Real.pi / 2)) * Complex.I := by
            field_simp [hB1_ne]; push_cast; ring
          rw [harg, hpi_neg]; ring
    have hp2 : ∀ (p2 : Fin (2 ^ 2)) (c : Fin (2 ^ k_ctrl)),
        Complex.exp ((if basisBits 2 p2 0 = 0 then (1 : ℂ) else -1) *
            (2 * ↑Real.pi * Complex.I * ↑(K_fn (basisBits 2 p2 1) c)) / 2 ^ (B + 3)) =
          UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c) p2 := by
      intro p2 c
      dsimp only [α_fn]
      have hcast : ∀ (m_val : ℕ),
          (1 : ℂ) * (2 * ↑Real.pi * Complex.I * (m_val : ℂ)) / 2 ^ (B + 3) =
            ((2 * Real.pi * (m_val : ℝ) / (2 : ℝ) ^ (B + 3) : ℝ) : ℂ) * Complex.I ∧
          (-1 : ℂ) * (2 * ↑Real.pi * Complex.I * (m_val : ℂ)) / 2 ^ (B + 3) =
            -(((2 * Real.pi * (m_val : ℝ) / (2 : ℝ) ^ (B + 3) : ℝ) : ℂ) * Complex.I) := by
        intro m_val; constructor <;> push_cast <;> ring
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      fin_cases p2
      · change Complex.exp ((if basisBits 2 (0 : Fin (2 ^ 2)) 0 = 0 then (1 : ℂ) else -1) *
            (2 * ↑Real.pi * Complex.I * ↑(K_fn (basisBits 2 (0 : Fin (2 ^ 2)) 1) c)) / 2 ^ (B +
              3)) = _
        have hb0 : basisBits 2 (0 : Fin (2 ^ 2)) 0 = 0 := by decide
        have hb1 : basisBits 2 (0 : Fin (2 ^ 2)) 1 = 0 := by decide
        rw [hb0, hb1, ite_eq_left_of_eq_true _ _ (eq_true rfl), (hcast _).1]; rfl
      · change Complex.exp ((if basisBits 2 (1 : Fin (2 ^ 2)) 0 = 0 then (1 : ℂ) else -1) *
            (2 * ↑Real.pi * Complex.I * ↑(K_fn (basisBits 2 (1 : Fin (2 ^ 2)) 1) c)) / 2 ^ (B +
              3)) = _
        have hb0 : basisBits 2 (1 : Fin (2 ^ 2)) 0 = 1 := by decide
        have hb1 : basisBits 2 (1 : Fin (2 ^ 2)) 1 = 0 := by decide
        rw [hb0, hb1, ite_eq_right_of_eq_false _ _ (eq_false h10), (hcast _).2]; rfl
      · change Complex.exp ((if basisBits 2 (2 : Fin (2 ^ 2)) 0 = 0 then (1 : ℂ) else -1) *
            (2 * ↑Real.pi * Complex.I * ↑(K_fn (basisBits 2 (2 : Fin (2 ^ 2)) 1) c)) / 2 ^ (B +
              3)) = _
        have hb0 : basisBits 2 (2 : Fin (2 ^ 2)) 0 = 0 := by decide
        have hb1 : basisBits 2 (2 : Fin (2 ^ 2)) 1 = 1 := by decide
        rw [hb0, hb1, ite_eq_left_of_eq_true _ _ (eq_true rfl), (hcast _).1]; rfl
      · change Complex.exp ((if basisBits 2 (3 : Fin (2 ^ 2)) 0 = 0 then (1 : ℂ) else -1) *
            (2 * ↑Real.pi * Complex.I * ↑(K_fn (basisBits 2 (3 : Fin (2 ^ 2)) 1) c)) / 2 ^ (B +
              3)) = _
        have hb0 : basisBits 2 (3 : Fin (2 ^ 2)) 0 = 1 := by decide
        have hb1 : basisBits 2 (3 : Fin (2 ^ 2)) 1 = 1 := by decide
        rw [hb0, hb1, ite_eq_right_of_eq_false _ _ (eq_false h10), (hcast _).2]; rfl
    have heigen : ∀ c p2 y,
        φ_step p2 c y * phaseGradientFineLow B 3 y =
          UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c) p2 *
              phaseGradientFineLow B 3 (π_c c p2 y) := by
      intro c p2 y
      rw [← hp2 p2 c]
      dsimp [φ_step, ψ_off_of, π_c, b0_of, b1_of]
      rw [mul_assoc, UnsignedGivens.rawPhaseStepVal_mul_phaseGradientFineLow B _ _ _
        (ha_lo _ c) (hb_mid _ c) (hb_top _ c) (basisBits 2 p2 0) y,
        ← mul_assoc, hoff_exp (basisBits 2 p2 0) _ (hq_off _ c), ← Complex.exp_add]
      congr 1; congr 1
      dsimp [K_fn]
      push_cast; ring
    intro c ξ
    funext g_out
    obtain ⟨⟨p2, y_out⟩, rfl⟩ := eSplit.symm.surjective g_out
    let y_in := (π_c c p2).symm y_out
    have hperm_apply : ∀ f : Fin (2 ^ (2 + B)) → ℂ,
        (Operator.permutationUnitary (π_full c)).1.mulVec f (eSplit.symm (p2, y_out)) =
          f (eSplit.symm (p2, y_in)) := by
      intro f
      have hf_sum : f = ∑ z : Fin (2 ^ (2 + B)), f z • Pi.single z 1 := by
        funext w; simp [Pi.single_apply]
      conv_lhs => rw [hf_sum]
      rw [Matrix.mulVec_sum, Finset.sum_apply]
      simp only [Matrix.mulVec_smul, Operator.permutationUnitary_mulVec_single, Pi.smul_apply,
        smul_eq_mul]
      rw [Finset.sum_eq_single (eSplit.symm (p2, y_in))]
      · have hpi : π_full c (eSplit.symm (p2, y_in)) = eSplit.symm (p2, y_out) := by
          simp [π_full, π_prod, y_in]
        rw [hpi, Pi.single_eq_same, mul_one]
      · intro z _ hz
        have hne : eSplit.symm (p2, y_out) ≠ π_full c z := by
          intro heq
          apply hz
          have hpi : π_full c (eSplit.symm (p2, y_in)) = eSplit.symm (p2, y_out) := by
            simp [π_full, π_prod, y_in]
          exact (π_full c).injective (heq.symm.trans hpi.symm)
        rw [Pi.single_eq_of_ne hne, mul_zero]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    change (W_raw c).1.mulVec (prodState ξ (phaseGradientFineLow B 3)) (eSplit.symm (p2, y_out)) =
      prodState ((UnsignedGivens.phaseDiagUnitary (UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c))
        (UnsignedGivens.genKick4_unit (α_fn 0 c) (α_fn 1 c))).1.mulVec ξ)
        (phaseGradientFineLow B 3) (eSplit.symm (p2, y_out))
    rw [hwRaw_mulVec, hperm_apply, UnsignedGivens.phaseDiagUnitary_mulVec, prodState_symm,
      prodState_symm,
      UnsignedGivens.phaseDiagUnitary_mulVec]
    have hd_eq : d_full c (eSplit.symm (p2, y_in)) = φ_step p2 c y_in := by simp [d_full]
    have hπ_in : π_c c p2 y_in = y_out := Equiv.apply_symm_apply (π_c c p2) y_out
    rw [hd_eq]
    calc
      φ_step p2 c y_in * (ξ p2 * phaseGradientFineLow B 3 y_in)
          = ξ p2 * (φ_step p2 c y_in * phaseGradientFineLow B 3 y_in) := by ring
      _ = ξ p2 * (UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c) p2 *
            phaseGradientFineLow B 3 (π_c c p2 y_in)) := by rw [heigen c p2 y_in]
      _ = UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c) p2 * ξ p2 *
            phaseGradientFineLow B 3 y_out := by rw [hπ_in]; ring

theorem CtrlMuxCatalyticWith.ofRawKick
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k_ctrl B m : ℕ} [NeZero (2 ^ n)]
    (rPair : QRegister 2 n) (rCat : QRegister B n) (hPairCat : rPair.DisjointWires rCat)
    (rCtrl : QRegister k_ctrl n) (hPcCtrl : (rPair.concat rCat hPairCat).DisjointWires rCtrl)
    (rWork : QRegister m n)
    (c_ref : Circuit n) (d : DynamicCircuit Var n)
    (hclean : UnsignedGivens.RealizesCleanRef rWork c_ref d)
    (a_lo_fn : ZMod 2 → Fin (2 ^ k_ctrl) → ℕ)
    (ha_lo : ∀ b₁ c, a_lo_fn b₁ c < 2 ^ B)
    (b_mid_fn b_top_fn : ZMod 2 → Fin (2 ^ k_ctrl) → ℕ)
    (hb_mid : ∀ b₁ c, b_mid_fn b₁ c < 2)
    (hb_top : ∀ b₁ c, b_top_fn b₁ c < 2)
    (hket : ∀ β : BitAssignment n, (∀ idx : Fin m, β (rWork idx) = 0) →
      let b₀ := β (rPair 0)
      let b₁ := β (rPair 1)
      let c := UnsignedGivens.localIdx rCtrl β
      let y := UnsignedGivens.localIdx rCat β
      c_ref.eval.1.mulVec (UnsignedGivens.ket β) =
        UnsignedGivens.rawPhaseStepVal B (a_lo_fn b₁ c) (b_mid_fn b₁ c) (b_top_fn b₁ c) b₀ y •
          UnsignedGivens.ket (UnsignedGivens.writeReg β rCat
            (basisBits B (UnsignedGivens.signedAddModPerm B (a_lo_fn b₁ c) (ha_lo b₁ c) b₀ y)))) :
    let K_fn := fun b₁ c => a_lo_fn b₁ c + 2 ^ B * b_mid_fn b₁ c + 2 ^ (B + 1) * b_top_fn b₁ c
    let α_fn := fun b₁ c => 2 * Real.pi * (K_fn b₁ c : ℝ) / (2 : ℝ) ^ (B + 3)
    CtrlMuxCatalyticWith (phaseGradientFineLow B 3) rPair rCat hPairCat rCtrl hPcCtrl rWork
      (fun c => UnsignedGivens.phaseDiagUnitary (UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c))
        (UnsignedGivens.genKick4_unit (α_fn 0 c) (α_fn 1 c))) d := by
  intro K_fn α_fn
  have hbase := CtrlMuxCatalyticWith.ofRawKickWithOffset rPair rCat hPairCat rCtrl hPcCtrl rWork
    c_ref d hclean a_lo_fn ha_lo b_mid_fn b_top_fn (fun _ _ => 0) hb_mid hb_top (fun _ _ =>
      by omega)
    (fun β h0 => by
      dsimp only
      rw [pow_zero, mul_zero, pow_zero, one_mul, one_mul]
      exact hket β h0)
  refine hbase.congrUnitary ?_
  funext c
  simp only [mul_zero, add_zero]
  rfl

theorem ctrlMuxCatalytic_framedPlanePos
    {Var : Type} [Fintype Var] [DecidableEq Var] {n N k_ctrl b_cat m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b_cat) → ℂ)
    (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (rCat : QRegister b_cat n) (rWork : QRegister m n)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    {α₀ α₁ : Fin (2 ^ k_ctrl) → ℝ} {dKick : DynamicCircuit Var n}
    (hkick : CtrlMuxCatalyticWith φ_cat
      (rSpin.compose (GivensOps.pairAdj N p hp)) rCat
      (disj_sys_cat_of (UnsignedGivens.disj_sub_ctrl hsc (GivensOps.pairAdj N p hp))
        (UnsignedGivens.disj_sub_cat hsc hac (GivensOps.pairAdj N p hp)))
      rCtrl
      (disj_sysCat_ctrl_of (UnsignedGivens.disj_sub_ctrl hsc (GivensOps.pairAdj N p hp))
        (UnsignedGivens.disj_sub_cat hsc hac (GivensOps.pairAdj N p hp)))
      rWork
      (fun c => UnsignedGivens.phaseDiagUnitary (UnsignedGivens.genKick4 (α₀ c) (α₁ c))
        (UnsignedGivens.genKick4_unit (α₀ c) (α₁ c))) dKick) :
    CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
      rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
      (fun c =>
        (GivensOps.pairAdj N p hp).embedUnitary (UnsignedGivens.genGivensPosUnitary (α₀ c) (α₁ c)))
      (UnsignedGivens.framedPlanePosDyn p hp rSpin dKick) := by
  let sel := GivensOps.pairAdj N p hp
  have hpc := UnsignedGivens.disj_sub_ctrl hsc sel
  have hac_p := UnsignedGivens.disj_sub_cat hsc hac sel
  have hdw_p := UnsignedGivens.disj_sub_work hsc hac hdisj sel
  have hframed := CtrlMuxCatalyticWith.wrapCliffordFrame φ_cat
    (rSpin.compose sel) rCat (disj_sys_cat_of hpc hac_p)
    rCtrl (disj_sysCat_ctrl_of hpc hac_p) hpc rWork
    (disj_sysCatCtrl_work_of hpc hac_p hdw_p)
    UnsignedGivens.cliffPrePos UnsignedGivens.cliffPostPos hkick
  exact CtrlMuxCatalyticWith.widenSys (disj_sys_cat_of hsc hac) (disj_sys_cat_of hpc hac_p)
    (disj_sysCat_ctrl_of hsc hac) (disj_sysCat_ctrl_of hpc hac_p) hframed

theorem ctrlMuxCatalytic_framedPlaneNeg
    {Var : Type} [Fintype Var] [DecidableEq Var] {n N k_ctrl b_cat m : ℕ} [NeZero (2 ^ n)]
    (φ_cat : Fin (2 ^ b_cat) → ℂ)
    (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (rCat : QRegister b_cat n) (rWork : QRegister m n)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    {α₀ α₁ : Fin (2 ^ k_ctrl) → ℝ} {dKick : DynamicCircuit Var n}
    (hkick : CtrlMuxCatalyticWith φ_cat
      (rSpin.compose (GivensOps.pairAdj N p hp)) rCat
      (disj_sys_cat_of (UnsignedGivens.disj_sub_ctrl hsc (GivensOps.pairAdj N p hp))
        (UnsignedGivens.disj_sub_cat hsc hac (GivensOps.pairAdj N p hp)))
      rCtrl
      (disj_sysCat_ctrl_of (UnsignedGivens.disj_sub_ctrl hsc (GivensOps.pairAdj N p hp))
        (UnsignedGivens.disj_sub_cat hsc hac (GivensOps.pairAdj N p hp)))
      rWork
      (fun c => UnsignedGivens.phaseDiagUnitary (UnsignedGivens.genKick4 (α₀ c) (α₁ c))
        (UnsignedGivens.genKick4_unit (α₀ c) (α₁ c))) dKick) :
    CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
      rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
      (fun c =>
        (GivensOps.pairAdj N p hp).embedUnitary (UnsignedGivens.genGivensNegUnitary (α₀ c) (α₁ c)))
      (UnsignedGivens.framedPlaneNegDyn p hp rSpin dKick) := by
  let sel := GivensOps.pairAdj N p hp
  have hpc := UnsignedGivens.disj_sub_ctrl hsc sel
  have hac_p := UnsignedGivens.disj_sub_cat hsc hac sel
  have hdw_p := UnsignedGivens.disj_sub_work hsc hac hdisj sel
  have hframed := CtrlMuxCatalyticWith.wrapCliffordFrame φ_cat
    (rSpin.compose sel) rCat (disj_sys_cat_of hpc hac_p)
    rCtrl (disj_sysCat_ctrl_of hpc hac_p) hpc rWork
    (disj_sysCatCtrl_work_of hpc hac_p hdw_p)
    UnsignedGivens.cliffPreNeg UnsignedGivens.cliffPostNeg hkick
  exact CtrlMuxCatalyticWith.widenSys (disj_sys_cat_of hsc hac) (disj_sys_cat_of hpc hac_p)
    (disj_sysCat_ctrl_of hsc hac) (disj_sysCat_ctrl_of hpc hac_p) hframed

theorem ctrlMuxCatalytic_framedCtrlApex
    {Var : Type} [Fintype Var] [DecidableEq Var] {n N k_ctrl m_in m : ℕ} [NeZero (2 ^ n)]
    (v : Var) (hN : 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (actIdx : Fin k_ctrl)
    (rCat : QRegister 11 n) (rWork : QRegister m n)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    (w_act1 : Wire n) (hw1_mem : w_act1 ∈ rWork.image)
    (rWork_in : QRegister m_in n)
    (hsub_in : rWork_in.image ⊆ rWork.image)
    (hw1_not_in : w_act1 ∉ rWork_in.image)
    (cKick10 : Circuit n) (dKick10 : DynamicCircuit Var n)
    (hclean_in : UnsignedGivens.RealizesCleanRef rWork_in cKick10 dKick10)
    (hperm_in : ∃ φ_in f_in, UnsignedGivens.PhasedPerm cKick10 φ_in f_in ∧
      ∀ β (w : Wire n), w ∉ (rCat.compose (locRight 1 10)).image → f_in β w = β w)
    (a_lo_fn : ZMod 2 → Fin (2 ^ k_ctrl) → ℕ)
    (ha_lo : ∀ qc c, a_lo_fn qc c < 2 ^ 10)
    (b_mid_fn b_top_fn : ZMod 2 → Fin (2 ^ k_ctrl) → ℕ)
    (hb_mid : ∀ qc c, b_mid_fn qc c < 2)
    (hb_top : ∀ qc c, b_top_fn qc c < 2)
    (hket_in : ∀ β : BitAssignment n, (∀ idx : Fin m_in, β (rWork_in idx) = 0) →
      let rPair0 := rSpin.compose (GivensOps.pairAdj N 0 hN)
      let rCat10 := rCat.compose (locRight 1 10)
      let b₀ := β (rPair0 0)
      let qc := β w_act1
      let c := UnsignedGivens.localIdx rCtrl β
      let y := UnsignedGivens.localIdx rCat10 β
      cKick10.eval.1.mulVec (UnsignedGivens.ket β) =
        UnsignedGivens.rawPhaseStepVal 10 (a_lo_fn qc c) (b_mid_fn qc c) (b_top_fn qc c) b₀ y •
          UnsignedGivens.ket (UnsignedGivens.writeReg β rCat10
            (basisBits 10 (UnsignedGivens.signedAddModPerm 10 (a_lo_fn qc c) (ha_lo qc c) b₀ y)))) :
    let hact_w1 : rCtrl actIdx ≠ w_act1 := by
      obtain ⟨j, rfl⟩ := QRegister.mem_image rWork w_act1 |>.mp hw1_mem
      exact UnsignedGivens.ne_ctrl_work hsc hac hdisj actIdx j
    let hp1_w1 : rSpin ⟨1, hN⟩ ≠ w_act1 := by
      obtain ⟨j, rfl⟩ := QRegister.mem_image rWork w_act1 |>.mp hw1_mem
      exact UnsignedGivens.ne_spin_work hsc hac hdisj ⟨1, hN⟩ j
    let hp0_w1 : rSpin ⟨0, by omega⟩ ≠ w_act1 := by
      obtain ⟨j, rfl⟩ := QRegister.mem_image rWork w_act1 |>.mp hw1_mem
      exact UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ j
    let qc_of := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) => basisBits k_ctrl c actIdx * b₁
    let K_fn : ZMod 2 → Fin (2 ^ k_ctrl) → ℕ := fun b₁ c =>
      let qc := qc_of b₁ c
      a_lo_fn qc c + 2 ^ 10 * b_mid_fn qc c + 2 ^ (10 + 1) * b_top_fn qc c +
        2 ^ (10 + 1) * qc.val
    let α_fn := fun b₁ c => 2 * Real.pi * (K_fn b₁ c : ℝ) / (2 : ℝ) ^ (10 + 3)
    let z0 : Fin N := ⟨0, by omega⟩
    CtrlMuxCatalyticWith (phaseGradientFineLow 11 3)
      rSpin rCat (disj_sys_cat_of hsc hac) rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
      (fun c =>
        (if basisBits k_ctrl c actIdx =
          0 then 1 else (QRegister.singleton z0).embedUnitary Qubit.Z) *
          (GivensOps.pairAdj N 0 hN).embedUnitary (UnsignedGivens.genGivensPosUnitary (α_fn 0 c)
            (α_fn 1 c)))
      (UnsignedGivens.framedCtrlApexDyn v hN rSpin rCtrl hsc actIdx w_act1 hact_w1 hp1_w1 hp0_w1
          dKick10) := by
  intro hact_w1 hp1_w1 hp0_w1 qc_of K_fn α_fn z0
  let sel0 := GivensOps.pairAdj N 0 hN
  let rPair0 := rSpin.compose sel0
  let rCat10 := rCat.compose (locRight 1 10)
  have hpc := UnsignedGivens.disj_sub_ctrl hsc sel0
  have hac_pair := UnsignedGivens.disj_sub_cat hsc hac sel0
  have hdisj_pair := UnsignedGivens.disj_sub_work hsc hac hdisj sel0
  have hac_pair10 := UnsignedGivens.disj_sub_cat_comp hsc hac sel0 (locRight 1 10)
  have hact_p1 : rCtrl actIdx ≠ rPair0 1 := (UnsignedGivens.ne_spin_ctrl hsc ⟨1, hN⟩ actIdx).symm
  have hp0_w1' : rPair0 0 ≠ w_act1 := hp0_w1
  have hp1_w1' : rPair0 1 ≠ w_act1 := hp1_w1
  let cOff := Circuit.S w_act1 ;;ᶜ UnsignedGivens.czCircuit (rPair0 0) w_act1 hp0_w1'
  let cInner := cOff ;;ᶜ cKick10
  let sAct := UnsignedGivens.directBitStep (rCtrl actIdx) (rPair0 1) w_act1 hact_p1 hact_w1 hp1_w1'
  let dWrapped := sAct.wrapDynamic v (DynamicCircuit.seq (.circuit cOff) dKick10)
  have hcOff_disj : Disjoint cOff.support rWork_in.image := by
    rw [Finset.disjoint_left]
    intro q hq
    simp only [cOff, Circuit.support_seq, Finset.mem_union] at hq
    rcases hq with h1 | h2
    · simp only [Circuit.S, Circuit.support_single, Finset.mem_singleton] at h1
      subst h1; exact hw1_not_in
    · have hs := UnsignedGivens.support_czCircuit_subset _ _ _ h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with hq0 | hq1
      · subst hq0
        intro hm_in
        obtain ⟨j, hj⟩ := QRegister.mem_image rWork _ |>.mp (hsub_in hm_in)
        exact UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ j hj.symm
      · subst hq1; exact hw1_not_in
  have hclean_cIn :=
    (UnsignedGivens.RealizesCleanRef.of_disjoint_circuit (Var :=
      Var) rWork_in cOff hcOff_disj).seq hclean_in
  obtain ⟨φ_k, f_k, hp_k, hfix_k⟩ := hperm_in
  let φ_c : BitAssignment n → ℂ := fun γ =>
    Complex.I ^ (γ w_act1).val * (-1 : ℂ) ^ (γ (rPair0 0) * γ w_act1).val * φ_k γ
  have hp_c : UnsignedGivens.PhasedPerm cInner φ_c f_k := by
    intro γ
    dsimp only [cInner, cOff, UnsignedGivens.PhasedPerm]
    rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_S_ket,
      Matrix.mulVec_smul,
      UnsignedGivens.evolve_czCircuit_ket, smul_smul, Matrix.mulVec_smul, hp_k γ, smul_smul]
  have hw1_not_cat10 : w_act1 ∉ rCat10.image := by
    obtain ⟨j, rfl⟩ := QRegister.mem_image rWork w_act1 |>.mp hw1_mem
    rw [QRegister.mem_image]
    rintro ⟨i, hi⟩
    exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) j hi
  have hsAct_ctrl_disj : ∀ w ∈ ({rCtrl actIdx, rPair0 1} : Finset (Wire n)), w ∉ rCat10.image := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [QRegister.mem_image]
    rintro ⟨i, hi⟩
    rcases hw with rfl | rfl
    · exact UnsignedGivens.ne_ctrl_cat hsc hac actIdx (locRight 1 10 i) hi.symm
    · exact UnsignedGivens.ne_spin_cat hsc hac ⟨1, hN⟩ (locRight 1 10 i) hi.symm
  have hwrap_spec := UnsignedGivens.cleanBitStep_wrap_spec
    (UnsignedGivens.isCleanBitStep_directBitStep (rCtrl actIdx)
      (rPair0 1) w_act1 hact_p1 hact_w1 hp1_w1')
    hp_c
    (fun γ => hfix_k γ w_act1 hw1_not_cat10)
    (fun γ w hw => hfix_k γ w (hsAct_ctrl_disj w hw))
  let f_wrap : BitAssignment n → BitAssignment n := fun γ =>
    Function.update
      (f_k (Function.update γ w_act1 (γ w_act1 + γ (rCtrl actIdx) * γ (rPair0 1))))
      w_act1 (γ w_act1)
  have hp_wrap : UnsignedGivens.PhasedPerm (sAct.wrapCircuit cInner) _ f_wrap := hwrap_spec.1
  have hf_wrap_fix : ∀ γ (w : Wire n), w ∉ rCat10.image → f_wrap γ w = γ w := by
    intro γ w hw
    dsimp [f_wrap]
    by_cases hww : w = w_act1
    · subst hww; exact Function.update_self _ _ _
    · rw [Function.update_of_ne hww, hfix_k _ w hw, Function.update_of_ne hww]
  have hdisj_w1_in : (QRegister.singleton sAct.anc).DisjointWires rWork_in := by
    rw [UnsignedGivens.disjointWires_iff_disjoint_image, QRegister.image_singleton,
      Finset.disjoint_singleton_left]
    exact hw1_not_in
  have hc1_not_in : sAct.c₁ ∉ rWork_in.image := by
    intro hm_in
    obtain ⟨j, hj⟩ := QRegister.mem_image rWork _ |>.mp (hsub_in hm_in)
    exact UnsignedGivens.ne_ctrl_work hsc hac hdisj actIdx j hj.symm
  have hc2_not_in : sAct.c₂ ∉ rWork_in.image := by
    intro hm_in
    obtain ⟨j, hj⟩ := QRegister.mem_image rWork _ |>.mp (hsub_in hm_in)
    exact UnsignedGivens.ne_spin_work hsc hac hdisj ⟨1, hN⟩ j hj.symm
  let rConcat := (QRegister.singleton sAct.anc).concat rWork_in hdisj_w1_in
  have hsub_concat : rConcat.image ⊆ rWork.image := by
    rw [UnsignedGivens.image_concat_eq, QRegister.image_singleton, Finset.union_subset_iff,
      Finset.singleton_subset_iff]
    exact ⟨hw1_mem, hsub_in⟩
  have hclean_concat :
      (sAct.wrapCircuit cInner).eval.1 * rConcat.basisOutcomeProjector 0 =
        rConcat.basisOutcomeProjector 0 * (sAct.wrapCircuit cInner).eval.1 *
          rConcat.basisOutcomeProjector 0 := by
    apply UnsignedGivens.cleanProjector_of_phasedPerm_fix rConcat _ hp_wrap
    intro γ idx hidx
    have hmem_w : rConcat idx ∈ rWork.image :=
      hsub_concat (QRegister.mem_image rConcat _ |>.mpr ⟨idx, rfl⟩)
    obtain ⟨j, hj⟩ := QRegister.mem_image rWork _ |>.mp hmem_w
    have hnotin : rConcat idx ∉ rCat10.image := by
      rw [← hj, QRegister.mem_image]
      rintro ⟨i, hi⟩
      exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) j hi
    rw [hf_wrap_fix γ (rConcat idx) hnotin, hidx]
  have hclean_rWork :
      (sAct.wrapCircuit cInner).eval.1 * rWork.basisOutcomeProjector 0 =
        rWork.basisOutcomeProjector 0 * (sAct.wrapCircuit cInner).eval.1 *
          rWork.basisOutcomeProjector 0 := by
    apply UnsignedGivens.cleanProjector_of_phasedPerm_fix rWork _ hp_wrap
    intro γ j hj
    have hnotin : rWork j ∉ rCat10.image := by
      rw [QRegister.mem_image]
      rintro ⟨i, hi⟩
      exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) j hi
    rw [hf_wrap_fix γ (rWork j) hnotin, hj]
  have href_concat := UnsignedGivens.RealizesCleanRef.wrapDynamic v sAct
    (.seq (.circuit cOff) dKick10) cInner rWork_in hdisj_w1_in
    (by simp [sAct, UnsignedGivens.directBitStep])
    (by simp [sAct, UnsignedGivens.directBitStep])
    hc1_not_in hc2_not_in
    (by simp [sAct, UnsignedGivens.directBitStep])
    hwrap_spec.2.2.2 hclean_cIn hclean_concat
  have href_work := href_concat.widenImage hsub_concat hclean_rWork
  have hPairCat10 := disj_sys_cat_of hpc hac_pair10
  have hPcCtrl10 := disj_sysCat_ctrl_of hpc hac_pair10
  have hPairCat := disj_sys_cat_of hpc hac_pair
  have hPcCtrl := disj_sysCat_ctrl_of hpc hac_pair
  have hdisj_pcw := disj_sysCatCtrl_work_of hpc hac_pair hdisj_pair
  have hkick10 := CtrlMuxCatalyticWith.ofRawKickWithOffset
    rPair0 rCat10 hPairCat10 rCtrl hPcCtrl10 rWork (sAct.wrapCircuit cInner) dWrapped href_work
    (fun b₁ c => a_lo_fn (qc_of b₁ c) c) (fun b₁ c => ha_lo _ _)
    (fun b₁ c => b_mid_fn (qc_of b₁ c) c) (fun b₁ c => b_top_fn (qc_of b₁ c) c)
    (fun b₁ c => (qc_of b₁ c).val)
    (fun b₁ c => hb_mid _ _) (fun b₁ c => hb_top _ _) (fun b₁ c => ZMod.val_lt _)
    (fun β h0 => by
      obtain ⟨j_w1, hj_w1⟩ := QRegister.mem_image rWork w_act1 |>.mp hw1_mem
      have hβ_w1 : β w_act1 = 0 := hj_w1 ▸ h0 j_w1
      have hact_bit : basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) actIdx =
        β (rCtrl actIdx) :=
        congrFun (UnsignedGivens.basisBits_symm_eq (fun j => β (rCtrl j))) actIdx
      let q_bit := β (rCtrl actIdx) * β (rPair0 1)
      have hqc_eq : qc_of (β (rPair0 1)) (UnsignedGivens.localIdx rCtrl β) = q_bit := by
        dsimp [qc_of, q_bit]; rw [hact_bit]
      let β₁ := Function.update β w_act1 q_bit
      have hβ₁_in0 : ∀ idx : Fin m_in, β₁ (rWork_in idx) = 0 := by
        intro idx
        have hne : rWork_in idx ≠ w_act1 := fun h =>
          hw1_not_in (QRegister.mem_image rWork_in w_act1 |>.mpr ⟨idx, h⟩)
        have hm_w : rWork_in idx ∈ rWork.image :=
          hsub_in (QRegister.mem_image rWork_in _ |>.mpr ⟨idx, rfl⟩)
        obtain ⟨j, hj⟩ := QRegister.mem_image rWork _ |>.mp hm_w
        dsimp only [β₁]
        rw [Function.update_of_ne hne, ← hj, h0 j]
      have hβ₁_p0 : β₁ (rPair0 0) = β (rPair0 0) :=
        Function.update_of_ne hp0_w1' _ _
      have hβ₁_w1 : β₁ w_act1 = q_bit := Function.update_self _ _ _
      have hβ₁_ctrl : UnsignedGivens.localIdx rCtrl β₁ = UnsignedGivens.localIdx rCtrl β := by
        apply (basisBits k_ctrl).injective; funext l
        rw [UnsignedGivens.basisBits_symm_eq, UnsignedGivens.basisBits_symm_eq]
        exact Function.update_of_ne (by
          intro heq
          exact UnsignedGivens.ne_ctrl_work hsc hac hdisj l j_w1 (heq.trans hj_w1.symm)) _ _
      have hβ₁_cat : UnsignedGivens.localIdx rCat10 β₁ = UnsignedGivens.localIdx rCat10 β := by
        apply (basisBits 10).injective; funext l
        rw [UnsignedGivens.basisBits_symm_eq, UnsignedGivens.basisBits_symm_eq]
        exact Function.update_of_ne (by
          intro heq
          exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 l) j_w1
            (heq.trans hj_w1.symm)) _ _
      dsimp only [sAct, UnsignedGivens.directBitStep, UnsignedGivens.PhasedStep.wrapCircuit, cInner,
        cOff]
      simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_identity_mulVec,
        UnsignedGivens.evolve_TOFF_ket]
      have hupd0 : Function.update β w_act1 (β w_act1 + β (rCtrl actIdx) * β (rPair0 1)) = β₁ := by
        rw [hβ_w1, zero_add]
      have hket₁ : cKick10.eval.1.mulVec (UnsignedGivens.ket β₁) =
          UnsignedGivens.rawPhaseStepVal 10 (a_lo_fn (β₁ w_act1) (UnsignedGivens.localIdx rCtrl β₁))
            (b_mid_fn (β₁ w_act1) (UnsignedGivens.localIdx rCtrl β₁))
            (b_top_fn (β₁ w_act1) (UnsignedGivens.localIdx rCtrl β₁)) (β₁ (rPair0 0))
            (UnsignedGivens.localIdx rCat10 β₁) •
          UnsignedGivens.ket (UnsignedGivens.writeReg β₁ rCat10
            (basisBits 10 (UnsignedGivens.signedAddModPerm 10
              (a_lo_fn (β₁ w_act1) (UnsignedGivens.localIdx rCtrl β₁))
              (ha_lo _ _) (β₁ (rPair0 0)) (UnsignedGivens.localIdx rCat10 β₁)))) :=
        hket_in β₁ hβ₁_in0
      rw [hupd0, UnsignedGivens.evolve_S_ket, Matrix.mulVec_smul,
        UnsignedGivens.evolve_czCircuit_ket, smul_smul,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hket₁, Matrix.mulVec_smul,
        UnsignedGivens.evolve_TOFF_ket, smul_smul]
      simp only [hβ₁_p0, hβ₁_w1, hβ₁_ctrl, hβ₁_cat, UnsignedGivens.zmod2_mul_val, hqc_eq]
      refine congrArg (_ • UnsignedGivens.ket ·) ?_
      have hw1_not_range : w_act1 ∉ Set.range rCat10.wires := by
        rintro ⟨i, hi⟩; exact hw1_not_cat10 (QRegister.mem_image rCat10 _ |>.mpr ⟨i, hi⟩)
      have hact_not_range : rCtrl actIdx ∉ Set.range rCat10.wires := by
        rintro ⟨i, hi⟩; exact UnsignedGivens.ne_ctrl_cat hsc hac actIdx (locRight 1 10 i) hi.symm
      have hp1_not_range : rPair0 1 ∉ Set.range rCat10.wires := by
        rintro ⟨i, hi⟩; exact UnsignedGivens.ne_spin_cat hsc hac ⟨1, hN⟩ (locRight 1 10 i) hi.symm
      rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hw1_not_range,
        UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hact_not_range,
        UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hp1_not_range]
      have hval_cancel : β₁ w_act1 + β₁ (rCtrl actIdx) * β₁ (rPair0 1) = β w_act1 := by
        dsimp only [β₁]
        rw [Function.update_self, Function.update_of_ne hact_w1, Function.update_of_ne hp1_w1']
        dsimp [q_bit]; rw [UnsignedGivens.zmod2_add_self, hβ_w1]
      rw [hval_cancel]
      funext w
      by_cases hww : w = w_act1
      · subst hww
        rw [Function.update_self, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hw1_not_range]
      · rw [Function.update_of_ne hww]
        by_cases hwc : w ∈ Set.range rCat10.wires
        · obtain ⟨i, rfl⟩ := hwc
          rw [UnsignedGivens.writeReg_apply_reg, UnsignedGivens.writeReg_apply_reg]
        · rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwc,
            UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwc]
          dsimp only [β₁]
          exact Function.update_of_ne hww _ _)
  have hkick11 : CtrlMuxCatalyticWith (phaseGradientFineLow 11 3)
      rPair0 rCat hPairCat rCtrl hPcCtrl rWork _ dWrapped :=
    CtrlMuxCatalyticWith.widenFineLowTop (b_skip := 1) (B := 10) (b_high := 3)
      hPairCat hPairCat10 hPcCtrl hPcCtrl10 hkick10
  have hframed := CtrlMuxCatalyticWith.wrapCliffordFrame (phaseGradientFineLow 11 3)
    rPair0 rCat hPairCat rCtrl hPcCtrl hpc rWork hdisj_pcw
    UnsignedGivens.cliffPrePos UnsignedGivens.cliffPostPos hkick11
  have hcz := CtrlMuxCatalyticWith.czActivePair0 (Var := Var) (phaseGradientFineLow 11 3)
    rPair0 rCat hPairCat rCtrl hPcCtrl hpc actIdx rWork
  have hseq := hframed.seq hdisj_pcw hcz
  refine (CtrlMuxCatalyticWith.widenSys (disj_sys_cat_of hsc hac) hPairCat
    (disj_sysCat_ctrl_of hsc hac) hPcCtrl hseq).congrUnitary ?_
  funext c
  rw [UnsignedGivens.embedUnitary_mul_eq]
  congr 1
  by_cases ha0 : basisBits k_ctrl c actIdx = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ha0), ite_eq_left_of_eq_true _ _ (eq_true ha0),
      UnsignedGivens.embedUnitary_one_eq]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ha0), ite_eq_right_of_eq_false _ _ (eq_false ha0),
      ← QRegister.embedUnitary_compose, GivensOps.pairAdj_compose_singleton_zero]

theorem ctrlMuxCatalytic_genericCascadeDyn
    {Var : Type} [Fintype Var] [DecidableEq Var] {n N k_ctrl b_cat m : ℕ} [NeZero (2 ^ n)]
    (hN : 1 < N)
    (φ_cat : Fin (2 ^ b_cat) → ℂ)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (rCat : QRegister b_cat n) (rWork : QRegister m n)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    (planePos planeNeg : (p : ℕ) → p + 1 < N → DynamicCircuit Var n)
    (apex : DynamicCircuit Var n)
    (α₀ α₁ : ℕ → Fin (2 ^ k_ctrl) → ℝ)
    (U_apex : Fin (2 ^ k_ctrl) → Unitary (2 ^ N))
    (hpos : ∀ p (hp : p + 1 < N),
      CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
        rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
        (fun c =>
          (GivensOps.pairAdj N p hp).embedUnitary (UnsignedGivens.genGivensPosUnitary (α₀ p c)
          (α₁ p c)))
        (planePos p hp))
    (hneg : ∀ p (hp : p + 1 < N),
      CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
        rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
        (fun c =>
          (GivensOps.pairAdj N p hp).embedUnitary (UnsignedGivens.genGivensNegUnitary (α₀ p c)
          (α₁ p c)))
        (planeNeg p hp))
    (hapex : CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
      rCtrl (disj_sysCat_ctrl_of hsc hac) rWork U_apex apex) :
    CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
      rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
      (fun c =>
        (UnsignedGivens.genTailUnitary N (fun p => α₀ p c) (fun p => α₁ p c) (N - 2) (by omega))⁻¹ *
          U_apex c *
          UnsignedGivens.genTailUnitary N (fun p => α₀ p c) (fun p => α₁ p c) (N - 2) (by omega))
      (UnsignedGivens.genericCascadeDyn hN planePos planeNeg apex) := by
  have hdw := disj_sysCatCtrl_work_of hsc hac hdisj
  have htpos : ∀ t (ht : t + 1 < N),
      CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
        rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
        (fun c => UnsignedGivens.genTailUnitary N (fun p => α₀ p c) (fun p => α₁ p c) t ht)
        (UnsignedGivens.genericTailPosDyn planePos t ht) := by
    intro t; induction t with
    | zero =>
        intro _
        exact CtrlMuxCatalyticWith.identity φ_cat rSpin rCat _ rCtrl _ rWork
    | succ t ih =>
        intro ht
        refine ((hpos (t + 1) ht).seq hdw (ih (by omega))).congrUnitary ?_
        funext c; rfl
  have htneg : ∀ t (ht : t + 1 < N),
      CtrlMuxCatalyticWith φ_cat rSpin rCat (disj_sys_cat_of hsc hac)
        rCtrl (disj_sysCat_ctrl_of hsc hac) rWork
        (fun c => (UnsignedGivens.genTailUnitary N (fun p => α₀ p c) (fun p => α₁ p c) t ht)⁻¹)
        (UnsignedGivens.genericTailNegDyn planeNeg t ht) := by
    intro t; induction t with
    | zero =>
        intro _
        refine (CtrlMuxCatalyticWith.identity φ_cat rSpin rCat _ rCtrl _ rWork).congrUnitary ?_
        funext _; exact inv_one.symm
    | succ t ih =>
        intro ht
        refine ((ih (by omega)).seq hdw (hneg (t + 1) ht)).congrUnitary ?_
        funext c
        rw [UnsignedGivens.genGivensNegUnitary_eq_inv, ← embedUnitary_inv_eq', ← _root_.mul_inv_rev]
        rfl
  refine (((htpos (N - 2) (by omega)).seq hdw hapex).seq hdw
      (htneg (N - 2) (by omega))).congrUnitary ?_
  funext c
  simp only [mul_assoc]

/-! ## Section 3: `oneHotActiveProg` Pullback on `CtrlMuxCatalyticWith` -/

/-- Any wire `q ∉ Set.range rSC.wires` (including all control wires in `rCtrl`) commutes with
`((rSC.concat rCtrl).embedUnitary (muxCtrlUnitary W_raw)).1`. -/
theorem commutesWithWire_embed_muxCtrlUnitary_of_not_mem
    {n k_3 k_ctrl : ℕ}
    (rSC : QRegister k_3 n) (rCtrl : QRegister k_ctrl n)
    (hCtrl2 : rSC.DisjointWires rCtrl)
    (W_raw : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_3))
    {q : Wire n} (hq : q ∉ Set.range rSC.wires) :
    CommutesWithWire q (((rSC.concat rCtrl hCtrl2).embedUnitary
        (UnsignedGivens.muxCtrlUnitary W_raw)).1) := by
  intro o
  apply matrix_ext_ket
  intro β
  let P := (QRegister.singleton q).basisOutcomeProjector o
  let U := (rSC.concat rCtrl hCtrl2).embedUnitary (UnsignedGivens.muxCtrlUnitary W_raw)
  change (U.1 * P).mulVec (ket β) = (P * U.1).mulVec (ket β)
  have hU_ket : U.1.mulVec (ket β) =
      (rSC.embedMatrix (W_raw (UnsignedGivens.localIdx rCtrl β)).1).mulVec (ket β) :=
    UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket rSC rCtrl hCtrl2 W_raw β
  have hcomm_3 :
      rSC.embedMatrix (W_raw (UnsignedGivens.localIdx rCtrl β)).1 * P =
        P * rSC.embedMatrix (W_raw (UnsignedGivens.localIdx rCtrl β)).1 :=
    CommutesWithWire.embedMatrix_of_not_mem rSC hq (W_raw (UnsignedGivens.localIdx rCtrl β)).1 o
  calc
    (U.1 * P).mulVec (ket β)
        = U.1.mulVec (P.mulVec (ket β)) := (Matrix.mulVec_mulVec (ket β) U.1 P).symm
    _ =
        (rSC.embedMatrix (W_raw (UnsignedGivens.localIdx rCtrl β)).1).mulVec (P.mulVec
        (ket β)) := by
          rw [ket_projector q o β]
          by_cases hb : β q = (o.val : ZMod 2)
          · simp only [hb, ↓reduceIte]; exact hU_ket
          · simp only [hb, ↓reduceIte, Matrix.mulVec_zero]
    _ = (rSC.embedMatrix (W_raw (UnsignedGivens.localIdx rCtrl β)).1 * P).mulVec (ket β) :=
          Matrix.mulVec_mulVec (ket β) _ P
    _ = (P * rSC.embedMatrix (W_raw (UnsignedGivens.localIdx rCtrl β)).1).mulVec (ket β) := by
          rw [hcomm_3]
    _ = P.mulVec ((rSC.embedMatrix (W_raw (UnsignedGivens.localIdx rCtrl β)).1).mulVec (ket β)) :=
          (Matrix.mulVec_mulVec (ket β) P _).symm
    _ = P.mulVec (U.1.mulVec (ket β)) := by rw [← hU_ket]
    _ = (P * U.1).mulVec (ket β) := Matrix.mulVec_mulVec (ket β) P U.1

/-- Lifted `(k_out + G)`-bit control index produced by `oneHotActiveCircuit` when `rOneHot` starts
at `0^G`. -/
noncomputable def oneHotActiveCtrlLift {k_out : ℕ} (m G : ℕ) (hG : 1 ≤ G)
    (actIdx : Fin k_out) (selIdx : QRegister m k_out) (c_out : Fin (2 ^ k_out)) :
    Fin (2 ^ (k_out + G)) :=
  let g₀ := oneHotDecodeIdx m G hG (fun i => basisBits k_out c_out (selIdx i))
  let hotBits : Fin G → ZMod 2 := fun j =>
    if j = g₀ then basisBits k_out c_out actIdx else 0
  (blockSplitEquiv k_out G).symm (c_out, (basisBits G).symm hotBits)

theorem basisBits_oneHotActiveCtrlLift_left {k_out : ℕ} (m G : ℕ) (hG : 1 ≤ G)
    (actIdx : Fin k_out) (selIdx : QRegister m k_out) (c_out : Fin (2 ^ k_out))
    (i : Fin k_out) :
    basisBits (k_out + G) (oneHotActiveCtrlLift m G hG actIdx selIdx c_out) (Fin.castAdd G i) =
      basisBits k_out c_out i := by
  have hl : Fin.castAdd G i = locLeft k_out G i := by ext; simp [locLeft, locLeftOf]
  rw [hl, ← (locLeft k_out G).basisBits_extractIndex]
  dsimp only [oneHotActiveCtrlLift]
  rw [extractIndex_locLeft_symm]

theorem ctrlHotBits_oneHotActiveCtrlLift {k_out : ℕ} (m G : ℕ) (hG : 1 ≤ G)
    (actIdx : Fin k_out) (selIdx : QRegister m k_out) (c_out : Fin (2 ^ k_out)) :
    UnsignedGivens.ctrlHotBits (locRight k_out G)
      (oneHotActiveCtrlLift m G hG actIdx selIdx c_out) =
      fun j : Fin G =>
        if j = oneHotDecodeIdx m G hG (fun i => basisBits k_out c_out (selIdx i)) then
          basisBits k_out c_out actIdx
        else 0 := by
  funext j
  dsimp only [UnsignedGivens.ctrlHotBits, oneHotActiveCtrlLift]
  rw [← (locRight k_out G).basisBits_extractIndex, extractIndex_locRight_symm,
    UnsignedGivens.basisBits_symm_eq]

/-- Per-control-branch unitary on `rSpin : QRegister N n` realized by `oneHotActiveProg` wrapping
`UnsignedGivens.unsignedBilinearLac2CascadeCtrlDyn`. -/
noncomputable def oneHotActiveLac2BranchUnitary
    {N k_out m G : ℕ} (hN : 1 < N) (hG : 1 ≤ G)
    (table : Fin G → Bool → Fin N → ℕ)
    (actIdx : Fin k_out) (selIdx : QRegister m k_out) (subIdx : Fin k_out)
    (c_out : Fin (2 ^ k_out)) : Unitary (2 ^ N) :=
  UnsignedGivens.unsignedBilinearLac2CascadeCtrlUnitary hN table
    (Fin.castAdd G actIdx) (locRight k_out G) (Fin.castAdd G subIdx)
    (oneHotActiveCtrlLift m G hG actIdx selIdx c_out)

theorem oneHotActiveLac2BranchUnitary_eq_one_of_act_zero
    {N k_out m G : ℕ} (hN : 1 < N) (hG : 1 ≤ G)
    (table : Fin G → Bool → Fin N → ℕ)
    (actIdx : Fin k_out) (selIdx : QRegister m k_out) (subIdx : Fin k_out)
    {c_out : Fin (2 ^ k_out)}
    (hact0 : basisBits k_out c_out actIdx = 0) :
    oneHotActiveLac2BranchUnitary hN hG table actIdx selIdx subIdx c_out = 1 := by
  dsimp only [oneHotActiveLac2BranchUnitary]
  have hact_lift :
      basisBits (k_out + G) (oneHotActiveCtrlLift m G hG actIdx selIdx c_out)
        (Fin.castAdd G actIdx) = 0 := by
    rw [basisBits_oneHotActiveCtrlLift_left, hact0]
  have hatmost : UnsignedGivens.AtMostOneHotBits
      (UnsignedGivens.ctrlHotBits (locRight k_out G)
          (oneHotActiveCtrlLift m G hG actIdx selIdx c_out)) := by
    rw [ctrlHotBits_oneHotActiveCtrlLift]
    intro i j _
    left
    simp [hact0]
  exact UnsignedGivens.unsignedBilinearLac2CascadeCtrlUnitary_eq_one_of_act_zero hN table
    (Fin.castAdd G actIdx) (locRight k_out G) (Fin.castAdd G subIdx) hact_lift hatmost

theorem oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one
    {N k_out m G : ℕ} (hN : 1 < N) (hG : 1 ≤ G)
    (table : Fin G → Bool → Fin N → ℕ)
    (actIdx : Fin k_out) (selIdx : QRegister m k_out) (subIdx : Fin k_out)
    {c_out : Fin (2 ^ k_out)}
    (hact1 : basisBits k_out c_out actIdx = 1)
    (hbounds : ∀ (g : Fin G) (b : Bool),
      (∀ (p : ℕ) (hp : p + 1 < N), table g b ⟨p, by omega⟩ < 8192) ∧
      2048 ≤ table g b ⟨0, by omega⟩ ∧
      table g b ⟨0, by omega⟩ < 6144) :
    let g₀ := oneHotDecodeIdx m G hG (fun i => basisBits k_out c_out (selIdx i))
    let b_sel := decide (basisBits k_out c_out subIdx = 1)
    oneHotActiveLac2BranchUnitary hN hG table actIdx selIdx subIdx c_out =
      UnsignedGivens.singleSpinReflectionUnitary N hN 15 (fun j => (table g₀ b_sel j : ℤ)) := by
  intro g₀ b_sel
  dsimp only [oneHotActiveLac2BranchUnitary]
  let c_in := oneHotActiveCtrlLift m G hG actIdx selIdx c_out
  have hact_lift : basisBits (k_out + G) c_in (Fin.castAdd G actIdx) = 1 := by
    dsimp only [c_in]
    rw [basisBits_oneHotActiveCtrlLift_left, hact1]
  have hsub_lift : basisBits (k_out + G) c_in (Fin.castAdd G subIdx) =
      basisBits k_out c_out subIdx :=
    basisBits_oneHotActiveCtrlLift_left m G hG actIdx selIdx c_out subIdx
  have hoh :
      UnsignedGivens.IsOneHotBits g₀ (UnsignedGivens.ctrlHotBits (locRight k_out G) c_in) := by
    dsimp only [c_in]
    rw [ctrlHotBits_oneHotActiveCtrlLift]
    refine ⟨by simp [g₀, hact1], fun j hj => by simp [g₀, hj]⟩
  have hb := hbounds g₀ b_sel
  have hres :=
    UnsignedGivens.unsignedBilinearLac2CascadeCtrlUnitary_eq_singleSpinReflection hN table
    (Fin.castAdd G actIdx) (locRight k_out G) (Fin.castAdd G subIdx) hact_lift hoh
    (by simpa only [hsub_lift] using hb.1)
    (by simpa only [hsub_lift] using hb.2.1)
    (by simpa only [hsub_lift] using hb.2.2)
  simpa only [hsub_lift] using hres

end CtrlMuxCombinators

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.OneHotMux

end
