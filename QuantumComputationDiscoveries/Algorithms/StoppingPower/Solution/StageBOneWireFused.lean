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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MeasBranchHadSem

set_option Elab.async false

@[expose] public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution

open Operator QProg Matrix Real HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open MeasureBranchHadamardSem
  (ket bitSign bitSign_mul_self bit_cases ket_H ket_Z matrix_ext_ket eval_seq_mulVec)
open OctahedralOrbit (singleton_embedMatrix_mulVec_ket)

namespace StageBUnheldTailCommBridge

/-- Transparent operator alias on `n` qubits (`Operator (2 ^ n)`). -/
abbrev QOp (n : ℕ) : Type := Operator (2 ^ n)

/-- Transparent computational-basis `±1` phase mask alias on `n` qubits. -/
abbrev PhaseFn (n : ℕ) : Type := Fin (2 ^ n) → Bool

/-- Subspace transformer predicate. -/
abbrev SubspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (R_in R_out : QOp n) (p : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ N : Observable (Fin (2 ^ n)),
    wp p.compile (fun _ ↦ M) = (fun _ ↦ N) ∧
    R_outᴴ * M.1.1 * R_out = R_inᴴ * N.1.1 * R_in

/-- Computational-basis support predicate. -/
abbrev SupportedOn {n : ℕ} (Pred : BitAssignment n → Prop) (R : QOp n) : Prop :=
  ∀ (A B : QOp n),
    (∀ β : BitAssignment n, Pred β → A.mulVec (ket β) = B.mulVec (ket β)) →
    A * R = B * R

/-- Diagonal `±1` phase unitary. -/
noncomputable def diagSignUnitary {k : ℕ} (phase : PhaseFn k) : Unitary (2 ^ k) :=
  ⟨Matrix.diagonal fun x ↦ if phase x then (-1 : ℂ) else 1, by
    have hsa : star (Matrix.diagonal fun x : Fin (2 ^ k) ↦ if phase x then (-1 : ℂ) else 1) =
        Matrix.diagonal fun x ↦ if phase x then (-1 : ℂ) else 1 := by
      ext x y
      by_cases h : x = y
      · subst h
        by_cases hp : phase x <;> simp [Matrix.diagonal, hp]
      · simp [Matrix.diagonal, h, Ne.symm h]
    have hsq : (Matrix.diagonal fun x : Fin (2 ^ k) ↦ if phase x then (-1 : ℂ) else 1) *
        (Matrix.diagonal fun x ↦ if phase x then (-1 : ℂ) else 1) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext x y
      by_cases h : x = y
      · subst h
        by_cases hp : phase x <;> simp [Matrix.diagonal, hp]
      · simp [Matrix.diagonal, h]
    exact ⟨hsa.symm ▸ hsq, hsa.symm ▸ hsq⟩⟩

end StageBUnheldTailCommBridge

namespace StageBOneWireFusedPost436

/-- Subspace transformer predicate. -/
abbrev SubspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (R_in R_out : Operator (2 ^ n)) (p : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ N : Observable (Fin (2 ^ n)),
    wp p.compile (fun _ ↦ M) = (fun _ ↦ N) ∧
    R_outᴴ * M.1.1 * R_out = R_inᴴ * N.1.1 * R_in

/-- Computational-basis support predicate. -/
abbrev SupportedOn {n : ℕ} (Pred : BitAssignment n → Prop) (R : Operator (2 ^ n)) : Prop :=
  ∀ (A B : Operator (2 ^ n)),
    (∀ β : BitAssignment n, Pred β → A.mulVec (ket β) = B.mulVec (ket β)) →
    A * R = B * R

/-- Conditional single-qubit `Z` gate (`0 T`, `TOFF = 0`). -/
def cBitZ {n : ℕ} (m : Bool) (q : Wire n) : Circuit n :=
  if m then Circuit.Z q else .identity

/-- Forward single-qubit Clifford conjugator for `(b, f)` (`0 T`, `TOFF = 0`). -/
def cPauliGateFwd {n : ℕ} (b f : Bool) (q : Wire n) : Circuit n :=
  match b, f with
  | false, _ => .identity
  | true, false => Circuit.H q
  | true, true => Circuit.S q ;;ᶜ Circuit.Z q ;;ᶜ Circuit.H q

/-- Inverse single-qubit Clifford conjugator for `(b, f)` (`0 T`, `TOFF = 0`). -/
def cPauliGateInv {n : ℕ} (b f : Bool) (q : Wire n) : Circuit n :=
  match b, f with
  | false, _ => .identity
  | true, false => Circuit.H q
  | true, true => Circuit.H q ;;ᶜ Circuit.S q

private theorem cPauliGateFwd_count_t {n : ℕ} (b f : Bool) (q : Wire n) :
    (cPauliGateFwd b f q).count .T = 0 := by cases b <;> cases f <;> rfl

private theorem cPauliGateFwd_count_toff {n : ℕ} (b f : Bool) (q : Wire n) :
    (cPauliGateFwd b f q).count .TOFF = 0 := by cases b <;> cases f <;> rfl

private theorem cPauliGateInv_count_t {n : ℕ} (b f : Bool) (q : Wire n) :
    (cPauliGateInv b f q).count .T = 0 := by cases b <;> cases f <;> rfl

private theorem cPauliGateInv_count_toff {n : ℕ} (b f : Bool) (q : Wire n) :
    (cPauliGateInv b f q).count .TOFF = 0 := by cases b <;> cases f <;> rfl

/-- Applies `g i (r i)` sequentially across the first `k ≤ M` wires of `r : QRegister M n`. -/
def cWireWallAux {n M : ℕ} (r : QRegister M n) (g : Fin M → Wire n → Circuit n) :
    ∀ (k : ℕ), k ≤ M → Circuit n
  | 0, _ => .identity
  | k + 1, hk => cWireWallAux r g k (by omega) ;;ᶜ g ⟨k, hk⟩ (r ⟨k, hk⟩)

theorem cWireWallAux_congr_rec {n M : ℕ} (r : QRegister M n) (g : Fin M → Wire n → Circuit n)
    (aux : ∀ k, k ≤ M → Circuit n)
    (h0 : ∀ h : 0 ≤ M, aux 0 h = .identity)
    (hsucc : ∀ (k : ℕ) (hk : k + 1 ≤ M),
      aux (k + 1) hk = aux k (by omega) ;;ᶜ g ⟨k, hk⟩ (r ⟨k, hk⟩)) :
    ∀ (k : ℕ) (hk : k ≤ M), aux k hk = cWireWallAux r g k hk
  | 0, hk => h0 hk
  | k + 1, hk => by
      rw [hsucc k hk, cWireWallAux_congr_rec r g aux h0 hsucc k (by omega)]
      rfl

private theorem cWireWallAux_count_t {n M : ℕ} (r : QRegister M n) (g : Fin M → Wire n → Circuit n)
    (hg : ∀ i : Fin M, (g i (r i)).count .T = 0) :
    ∀ (k : ℕ) (hk : k ≤ M), (cWireWallAux r g k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cWireWallAux]
      rw [Circuit.count_seq, cWireWallAux_count_t r g hg k (by omega), hg ⟨k, hk⟩]

private theorem cWireWallAux_count_toff {n M : ℕ} (r : QRegister M n)
    (g : Fin M → Wire n → Circuit n)
    (hg : ∀ i : Fin M, (g i (r i)).count .TOFF = 0) :
    ∀ (k : ℕ) (hk : k ≤ M), (cWireWallAux r g k hk).count .TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cWireWallAux]
      rw [Circuit.count_seq, cWireWallAux_count_toff r g hg k (by omega), hg ⟨k, hk⟩]
/-- Lane index `i % 18 : Fin 18` of a flat electron-bank wire index `i`. -/
def lane18 {M : ℕ} (i : Fin M) : Fin 18 :=
  ⟨i.val % 18, Nat.mod_lt _ (by decide)⟩

/-- Flat wire index `18 * s + j : Fin (N_slot * 18)` for slot `s` and lane `j`. -/
def elecFlatIdx {N_slot : ℕ} (s : Fin N_slot) (j : Fin 18) : Fin (N_slot * 18) :=
  ⟨18 * s.val + j.val, by omega⟩

@[simp]
theorem lane18_elecFlatIdx {N_slot : ℕ} (s : Fin N_slot) (j : Fin 18) :
    lane18 (elecFlatIdx s j) = j := by
  ext
  dsimp [lane18, elecFlatIdx]
  omega

/-- Hadamard wall across all `M` wires of `r : QRegister M n` (`0 T`, `TOFF = 0`). -/
def cHadWall {n M : ℕ} (r : QRegister M n) : Circuit n :=
  cWireWallAux r (fun _ q ↦ Circuit.H q) M le_rfl

/-- Forward Clifford conjugation wall across all `M` wires of `r` (`0 T`, `TOFF = 0`). -/
def cPauliWallFwd {n M : ℕ} (b' f : Fin 18 → Bool) (r : QRegister M n) : Circuit n :=
  cWireWallAux r (fun i q ↦ cPauliGateFwd (b' (lane18 i)) (f (lane18 i)) q) M le_rfl

/-- Inverse Clifford conjugation wall across all `M` wires of `r` (`0 T`, `TOFF = 0`). -/
def cPauliWallInv {n M : ℕ} (b' f : Fin 18 → Bool) (r : QRegister M n) : Circuit n :=
  cWireWallAux r (fun i q ↦ cPauliGateInv (b' (lane18 i)) (f (lane18 i)) q) M le_rfl

/-- Branch-global unit scalar `∏ j : Fin 18, if b' j && f j then -I else 1` from fused cleanup. -/
noncomputable def pauliFusedPhase18 (b' f : Fin 18 → Bool) : ℂ :=
  ∏ j : Fin 18, if b' j && f j then (-Complex.I) else 1

theorem pauliFusedPhase18_unit (b' f : Fin 18 → Bool) :
    star (pauliFusedPhase18 b' f) * pauliFusedPhase18 b' f = 1 := by
  have hI : star (-Complex.I) * (-Complex.I) = 1 := by
    rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg, mul_neg, Complex.I_mul_I, neg_neg]
  dsimp only [pauliFusedPhase18]
  rw [star_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ ↦ ?_
  by_cases h : b' j && f j
  · simp only [h, ↓reduceIte, hI]
  · simp [h]

@[simp]
theorem cHadWall_count_t {n M : ℕ} (r : QRegister M n) : (cHadWall r).count .T = 0 :=
  cWireWallAux_count_t r _ (fun _ ↦ rfl) M le_rfl

@[simp]
theorem cHadWall_count_toff {n M : ℕ} (r : QRegister M n) : (cHadWall r).count .TOFF = 0 :=
  cWireWallAux_count_toff r _ (fun _ ↦ rfl) M le_rfl

@[simp]
theorem cPauliWallFwd_count_t {n M : ℕ} (b' f : Fin 18 → Bool) (r : QRegister M n) :
    (cPauliWallFwd b' f r).count .T = 0 :=
  cWireWallAux_count_t r _ (fun _ ↦ cPauliGateFwd_count_t _ _ _) M le_rfl

@[simp]
theorem cPauliWallFwd_count_toff {n M : ℕ} (b' f : Fin 18 → Bool) (r : QRegister M n) :
    (cPauliWallFwd b' f r).count .TOFF = 0 :=
  cWireWallAux_count_toff r _ (fun _ ↦ cPauliGateFwd_count_toff _ _ _) M le_rfl

@[simp]
theorem cPauliWallInv_count_t {n M : ℕ} (b' f : Fin 18 → Bool) (r : QRegister M n) :
    (cPauliWallInv b' f r).count .T = 0 :=
  cWireWallAux_count_t r _ (fun _ ↦ cPauliGateInv_count_t _ _ _) M le_rfl

@[simp]
theorem cPauliWallInv_count_toff {n M : ℕ} (b' f : Fin 18 → Bool) (r : QRegister M n) :
    (cPauliWallInv b' f r).count .TOFF = 0 :=
  cWireWallAux_count_toff r _ (fun _ ↦ cPauliGateInv_count_toff _ _ _) M le_rfl

/-- Zero-pads a `K`-bit `X`-basis measurement outcome `b : Fin K → Bool` to `Fin 18 → Bool`. -/
def extendMask18 (K : ℕ) (b : Fin K → Bool) (j : Fin 18) : Bool :=
  if hj : j.val < K then b ⟨j.val, hj⟩ else false

/-- Prefix of `k ≤ K` zero-`T` `czCircuit`s between `rHeld ⟨t, _⟩` and `rMeas ⟨t, _⟩`. -/
noncomputable def cHeldCzPrefixAux {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld) : ∀ (k : ℕ), k ≤ K → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      cHeldCzPrefixAux K hK rMeas rHeld hMH k (by omega) ;;ᶜ
      DynCircuitExt.czCircuit (rHeld ⟨k, hk⟩) (rMeas ⟨k, by omega⟩)
        (hMH.ne ⟨k, by omega⟩ ⟨k, hk⟩).symm

theorem cHeldCzPrefixAux_count {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (cHeldCzPrefixAux K hK rMeas rHeld hMH k hk).count .TOFF = 0 ∧
      (cHeldCzPrefixAux K hK rMeas rHeld hMH k hk).count .T = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      dsimp only [cHeldCzPrefixAux]
      obtain ⟨h1, h2⟩ := cHeldCzPrefixAux_count K hK rMeas rHeld hMH k (by omega)
      rw [Circuit.count_seq, Circuit.count_seq, h1, h2,
        DynCircuitExt.count_czCircuit_toff, DynCircuitExt.count_czCircuit_t]
      exact ⟨rfl, rfl⟩

/-- Fused 1-wire post-pass (`≤ B_tail + B_fix` `T`, `TOFF = 0` for all `0 ≤ K ≤ 18`),
deferring the `rHeld` `X`-measurement phase fixup across `dUnheldTail` + `cHadWall rElec` and
merging it with the `rMeas` `X`-measurement fixup via `0-T` Clifford conjugation. -/
noncomputable def dPostHoleHeld1wKFused {Var : Type} {n M : ℕ}
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister M n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (dUnheldTail : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (cHeldCzPrefixAux K hK rMeas rHeld hMH K le_rfl))
    (DynCircuitExt.measureXResetAndBranch v K rHeld fun b ↦
      let b' := extendMask18 K b
      .seq dUnheldTail
        (.seq (.circuit (cHadWall rElec))
          (DynCircuitExt.measureXResetAndBranch v 18 rMeas fun f ↦
            .seq (.circuit (cPauliWallFwd b' f rElec))
              (.seq (dFix (fun j ↦ b' j || f j))
                (.circuit (cPauliWallInv b' f rElec))))))

theorem dPostHoleHeld1wKFused_count_toff {Var : Type} {n M : ℕ}
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister M n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (dUnheldTail : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n)
    (hTail : dUnheldTail.count .TOFF = 0)
    (hFix : ∀ m : Fin 18 → Bool, (dFix m).count .TOFF = 0) :
    (dPostHoleHeld1wKFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix).count .TOFF = 0 := by
  dsimp only [dPostHoleHeld1wKFused, DynamicCircuit.count]
  rw [(cHeldCzPrefixAux_count K hK rMeas rHeld hMH K le_rfl).1, zero_add]
  refine Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_TOFF_le v K rHeld _ 0
    fun b ↦ ?_)
  dsimp only [DynamicCircuit.count]
  rw [hTail, cHadWall_count_toff, zero_add, zero_add]
  refine DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 18 rMeas _ 0 fun f ↦ ?_
  dsimp only [DynamicCircuit.count]
  rw [cPauliWallFwd_count_toff, hFix, cPauliWallInv_count_toff]

theorem dPostHoleHeld1wKFused_count_t_le {Var : Type} {n M : ℕ}
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister M n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (dUnheldTail : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n)
    {B_tail B_fix : ℕ}
    (hTail : dUnheldTail.count .T ≤ B_tail)
    (hFix : ∀ m : Fin 18 → Bool, (dFix m).count .T ≤ B_fix) :
    (dPostHoleHeld1wKFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix).count .T ≤
      B_tail + B_fix := by
  dsimp only [dPostHoleHeld1wKFused, DynamicCircuit.count]
  rw [(cHeldCzPrefixAux_count K hK rMeas rHeld hMH K le_rfl).2, zero_add]
  refine DynCircuitExt.count_measureXResetAndBranch_T_le v K rHeld _ (B_tail + B_fix) fun b ↦ ?_
  dsimp only [DynamicCircuit.count]
  rw [cHadWall_count_t, zero_add]
  refine Nat.add_le_add hTail
    (DynCircuitExt.count_measureXResetAndBranch_T_le v 18 rMeas _ B_fix fun f ↦ ?_)
  dsimp only [DynamicCircuit.count]
  rw [cPauliWallFwd_count_t, cPauliWallInv_count_t, zero_add, add_zero]
  exact hFix _

theorem dPostHoleHeld1wKFused_count_t_le_8428 {Var : Type} {n M : ℕ}
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister M n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (dUnheldTail : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n)
    (hTail : dUnheldTail.count .T ≤ 444 * (18 - K))
    (hFix : ∀ m : Fin 18 → Bool, (dFix m).count .T ≤ 436) :
    (dPostHoleHeld1wKFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix).count .T ≤
      8428 - 444 * K :=
  (dPostHoleHeld1wKFused_count_t_le K hK v rElec rMeas rHeld hMH dUnheldTail dFix hTail hFix).trans
    (by omega)

end StageBOneWireFusedPost436
namespace StageBOneWireFusedCaller47493

open StageBUnheldTailCommBridge (diagSignUnitary)
open StageBOneWireFusedPost436
  (cHeldCzPrefixAux cHeldCzPrefixAux_count extendMask18 cBitZ cPauliGateFwd cPauliGateInv
   cWireWallAux cWireWallAux_congr_rec lane18 elecFlatIdx lane18_elecFlatIdx
   cHadWall cHadWall_count_t cHadWall_count_toff
   cPauliWallFwd cPauliWallFwd_count_t cPauliWallFwd_count_toff
   cPauliWallInv cPauliWallInv_count_t cPauliWallInv_count_toff
   pauliFusedPhase18 pauliFusedPhase18_unit
   dPostHoleHeld1wKFused dPostHoleHeld1wKFused_count_toff
   dPostHoleHeld1wKFused_count_t_le dPostHoleHeld1wKFused_count_t_le_8428)

/-- Dimension `2 ^ n` of an `n`-qubit Hilbert space. -/
abbrev QubitDim (n : ℕ) : ℕ := 2 ^ n

/-- Operator type `Operator (2 ^ n)` on `n` qubits. -/
abbrev QOp (n : ℕ) : Type := Operator (QubitDim n)

/-- Lookup table `Fin (2 ^ k) → Fin (2 ^ b)` from `k` data qubits to `b` output bits. -/
abbrev TblFn (k b : ℕ) : Type := Fin (QubitDim k) → Fin (QubitDim b)

/-- Computational-basis `±1` phase function `Fin (2 ^ k) → Bool`. -/
abbrev PhaseFn (k : ℕ) : Type := Fin (QubitDim k) → Bool

/-- Subspace transformer predicate. -/
abbrev SubspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (QubitDim n)]
    (R_in R_out : QOp n) (p : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (QubitDim n)), ∃ N : Observable (Fin (QubitDim n)),
    wp p.compile (fun _ ↦ M) = (fun _ ↦ N) ∧
    R_outᴴ * M.1.1 * R_out = R_inᴴ * N.1.1 * R_in

/-- Computational-basis support predicate. -/
abbrev SupportedOn {n : ℕ} (Pred : BitAssignment n → Prop) (R : QOp n) : Prop :=
  ∀ (A B : QOp n),
    (∀ β : BitAssignment n, Pred β → A.mulVec (ket β) = B.mulVec (ket β)) →
    A * R = B * R

/-- Quantum-slot fused post-pass alias (`rfl`-equal to `dPostHoleHeld1wKFused`). -/
noncomputable abbrev dPostHoleHeld1wKQSlotFused {Var : Type} {n M : ℕ}
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister M n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (dUnheldTail : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n) : DynamicCircuit Var n :=
  dPostHoleHeld1wKFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix

theorem dPostHoleHeld1wKQSlotFused_count_toff {Var : Type} {n M : ℕ}
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister M n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (dUnheldTail : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n)
    (hTail : dUnheldTail.count .TOFF = 0)
    (hFix : ∀ m : Fin 18 → Bool, (dFix m).count .TOFF = 0) :
    (dPostHoleHeld1wKQSlotFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix).count .TOFF = 0 :=
  dPostHoleHeld1wKFused_count_toff K hK v rElec rMeas rHeld hMH dUnheldTail dFix hTail hFix

theorem dPostHoleHeld1wKQSlotFused_count_t_le_8428 {Var : Type} {n M : ℕ}
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister M n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (dUnheldTail : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n)
    (hTail : dUnheldTail.count .T ≤ 444 * (18 - K))
    (hFix : ∀ m : Fin 18 → Bool, (dFix m).count .T ≤ 436) :
    (dPostHoleHeld1wKQSlotFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix).count .T ≤
      8428 - 444 * K :=
  dPostHoleHeld1wKFused_count_t_le_8428 K hK v rElec rMeas rHeld hMH dUnheldTail dFix hTail hFix

/-- Structural congruence identifying a recursive Hadamard register wall with `cHadWall r`. -/
theorem cHadWall_eq_of_rec {n M : ℕ} (r : QRegister M n)
    (aux : ∀ k, k ≤ M → Circuit n)
    (h0 : ∀ h : 0 ≤ M, aux 0 h = .identity)
    (hsucc : ∀ (k : ℕ) (hk : k + 1 ≤ M),
      aux (k + 1) hk = aux k (by omega) ;;ᶜ Circuit.H (r ⟨k, hk⟩)) :
    aux M le_rfl = cHadWall r :=
  cWireWallAux_congr_rec r (fun _ q ↦ Circuit.H q) aux h0 hsucc M le_rfl

private theorem SubspaceStep.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (QubitDim n)] {R₀ R₁ R₂ : QOp n} {p₁ p₂ : DynamicCircuit Var n}
    (h₁ : SubspaceStep R₀ R₁ p₁) (h₂ : SubspaceStep R₁ R₂ p₂) :
    SubspaceStep R₀ R₂ (.seq p₁ p₂) := fun M ↦
  let ⟨N₂, hw₂, hm₂⟩ := h₂ M
  let ⟨N₁, hw₁, hm₁⟩ := h₁ N₂
  ⟨N₁, by
    change wp p₁.compile (wp p₂.compile (fun _ ↦ M)) = _
    rw [hw₂, hw₁], hm₂.trans hm₁⟩

private theorem subspaceStep_of_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (QubitDim n)] (R : QOp n) (c : Circuit n) :
    SubspaceStep (Var := Var) R (c.eval.1 * R) (.circuit c) := fun M ↦
  ⟨qAssignObsMap c.eval M, by
    funext σ
    simp [DynamicCircuit.compile_circuit, wpQAssignCompat], by
    have h1 : (qAssignObsMap c.eval M).1.1 = c.eval.1ᴴ * M.1.1 * c.eval.1 := by
      simp [qAssignObsMap, Observable.conj_coe, HermitianMat.conj_apply_mat,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    change (c.eval.1 * R)ᴴ * M.1.1 * (c.eval.1 * R) = Rᴴ * (qAssignObsMap c.eval M).1.1 * R
    rw [h1]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]⟩

private theorem subspaceStep_congr_out {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (QubitDim n)] {R_in R₁ R₂ : QOp n} {p : DynamicCircuit Var n}
    (hp : SubspaceStep (Var := Var) R_in R₁ p) (heq : R₁ = R₂) :
    SubspaceStep (Var := Var) R_in R₂ p := heq ▸ hp

private theorem subspaceStep_congr_in {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (QubitDim n)] {R₁ R₂ R_out : QOp n} {p : DynamicCircuit Var n}
    (hp : SubspaceStep (Var := Var) R₁ R_out p) (heq : R₂ = R₁) :
    SubspaceStep (Var := Var) R₂ R_out p := heq ▸ hp

private theorem SubspaceStep.smul {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (QubitDim n)] (c : ℂ) {R_in R_out : QOp n} {p : DynamicCircuit Var n}
    (hp : SubspaceStep R_in R_out p) :
    SubspaceStep (c • R_in) (c • R_out) p := fun M ↦ by
  obtain ⟨N, hw, hm⟩ := hp M
  refine ⟨N, hw, ?_⟩
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm]

private theorem SubspaceStep.of_unit_smul_out {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (QubitDim n)] {R_in R_out : QOp n} {ω : ℂ}
    (hω : star ω * ω = 1) {p : DynamicCircuit Var n}
    (hp : SubspaceStep R_in (ω • R_out) p) :
    SubspaceStep R_in R_out p := fun M ↦ by
  obtain ⟨N, hw, hm⟩ := hp M
  refine ⟨N, hw, ?_⟩
  have h1 : (ω • R_out)ᴴ * M.1.1 * (ω • R_out) = R_outᴴ * M.1.1 * R_out := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm ω (star ω), hω, one_smul]
  exact h1.symm.trans hm
private theorem subspaceStep_seq_measureXReset
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k : ℕ} [NeZero (QubitDim n)]
    (v : Var) (rOut : QRegister k n)
    {R₀ R₁ R₂ : QOp n}
    {dPre : DynamicCircuit Var n}
    {cont : (Fin k → Bool) → DynamicCircuit Var n}
    (hPre : SubspaceStep R₀ R₁ dPre)
    (hCont : ∀ f : Fin k → Bool,
      SubspaceStep (DynCircuitExt.xResetKraus rOut f * R₁)
        ((((√(1 / 2)) ^ k : ℝ) : ℂ) • R₂) (cont f)) :
    SubspaceStep R₀ R₂ (.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut cont)) := by
  intro M
  choose MCont hCont_wp hCont_eq using fun f ↦ hCont f M
  obtain ⟨MMid, hMid_wp, hMid_mat⟩ :=
    DynCircuitExt.wp_measureXResetAndBranch_const v k rOut cont M MCont hCont_wp
  obtain ⟨M', hPre_wp, hPre_eq⟩ := hPre MMid
  refine ⟨M', ?_, ?_⟩
  · change wp
      (DynamicCircuit.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut cont)).compile
      (fun _ ↦ M) = fun _ ↦ M'
    rw [DynamicCircuit.compile_seq, wp_qSeq, hMid_wp, hPre_wp]
  · rw [← hPre_eq, hMid_mat, Matrix.mul_sum, Matrix.sum_mul]
    let w : ℝ := (√(1 / 2)) ^ k
    have hstar : star (w : ℂ) = (w : ℂ) := Complex.conj_ofReal w
    have hTerm : ∀ f : Fin k → Bool,
        R₁ᴴ * ((DynCircuitExt.xResetKraus rOut f)ᴴ * (MCont f).1.1 *
          DynCircuitExt.xResetKraus rOut f) * R₁ =
        ((w ^ 2 : ℝ) : ℂ) • (R₂ᴴ * M.1.1 * R₂) := fun f ↦ by
      calc R₁ᴴ * ((DynCircuitExt.xResetKraus rOut f)ᴴ * (MCont f).1.1 *
            DynCircuitExt.xResetKraus rOut f) * R₁
          = (DynCircuitExt.xResetKraus rOut f * R₁)ᴴ * (MCont f).1.1 *
              (DynCircuitExt.xResetKraus rOut f * R₁) := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = ((w : ℂ) • R₂)ᴴ * M.1.1 * ((w : ℂ) • R₂) := (hCont_eq f).symm
        _ = ((w ^ 2 : ℝ) : ℂ) • (R₂ᴴ * M.1.1 * R₂) := by
              simp only [Matrix.conjTranspose_smul, hstar, Matrix.smul_mul,
                Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
              congr 1
              push_cast
              ring
    rw [Finset.sum_congr rfl fun f _ ↦ hTerm f, ← Finset.sum_smul]
    have hsum_c : (∑ _f : Fin k → Bool, ((w ^ 2 : ℝ) : ℂ)) = 1 := by
      exact_mod_cast DynCircuitExt.sum_sqrt_half_pow_sq k
    rw [hsum_c, one_smul]

private theorem eval_comm_embedMatrix_of_disjoint_support {n m : ℕ} (c : Circuit n)
    (r : QRegister m n) (hdisj : ∀ j : Fin m, r j ∉ c.support)
    (A : Matrix (Fin (QubitDim m)) (Fin (QubitDim m)) ℂ) :
    c.eval.1 * r.embedMatrix A = r.embedMatrix A * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g rGate =>
      have hd : rGate.DisjointWires r := by
        rw [QRegister.disjoint_iff]
        intro i j heq
        apply hdisj j
        simp only [Circuit.support_gate, QRegister.mem_image]
        exact ⟨i, heq⟩
      exact QRegister.embedMatrix_comm_of_disjoint rGate r hd g.eval.1 A
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ (fun j hj ↦ hdisj j (Finset.mem_union_left _ hj)),
        ← Matrix.mul_assoc, ih₂ (fun j hj ↦ hdisj j (Finset.mem_union_right _ hj)),
        Matrix.mul_assoc]

private theorem eval_comm_of_disjoint_support {n : ℕ} (c₁ c₂ : Circuit n)
    (hdisj : Disjoint c₁.support c₂.support) :
    c₁.eval * c₂.eval = c₂.eval * c₁.eval := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  induction c₂ with
  | identity => simp
  | gate g r =>
      refine eval_comm_embedMatrix_of_disjoint_support c₁ r (fun j hj ↦ ?_) g.eval.1
      exact Finset.disjoint_left.mp hdisj hj
        (by simp only [Circuit.support_gate, QRegister.mem_image]; exact ⟨j, rfl⟩)
  | seq d₁ d₂ ih₁ ih₂ =>
      rw [Circuit.support_seq, Finset.disjoint_union_right] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc]

private theorem xResetKraus_comm_of_wire_comm {n b : ℕ} :
    ∀ (rMeas : QRegister b n) (M : QOp n),
      (∀ (q : QRegister 1 n), (∀ i, q i ∈ Set.range rMeas.wires) →
        ∀ A : Matrix (Fin (QubitDim 1)) (Fin (QubitDim 1)) ℂ,
          q.embedMatrix A * M = M * q.embedMatrix A) →
      ∀ f : Fin b → Bool,
        DynCircuitExt.xResetKraus rMeas f * M = M * DynCircuitExt.xResetKraus rMeas f := by
  induction b with
  | zero =>
      intro rMeas M _ f
      simp [DynCircuitExt.xResetKraus]
  | succ b ih =>
      intro rMeas M hcomm f
      let q := rMeas.slice 0 1 (by omega)
      let tail := rMeas.slice 1 b (by omega)
      have hq : ∀ i, q i ∈ Set.range rMeas.wires := fun i ↦ ⟨⟨0 + i.val, by omega⟩, rfl⟩
      have htail : ∀ (q' : QRegister 1 n), (∀ i, q' i ∈ Set.range tail.wires) →
          ∀ A : Matrix (Fin (QubitDim 1)) (Fin (QubitDim 1)) ℂ,
            q'.embedMatrix A * M = M * q'.embedMatrix A := fun q' hq' ↦
        hcomm q' fun i ↦ by
          obtain ⟨j, hj⟩ := hq' i
          exact ⟨⟨1 + j.val, by omega⟩, hj⟩
      simp only [DynCircuitExt.xResetKraus]
      have h0 : DynCircuitExt.wireXResetKraus q (f 0) * M =
          M * DynCircuitExt.wireXResetKraus q (f 0) := by
        rw [DynCircuitExt.wireXResetKraus_eq_embedMatrix]
        exact hcomm q hq _
      rw [Matrix.mul_assoc, h0, ← Matrix.mul_assoc, ih tail M htail (Fin.tail f), Matrix.mul_assoc]

private theorem single_support_subset {n : ℕ} (g : PrimitiveGate 1) (q : Wire n) :
    (Circuit.single g q).support ⊆ {q} := by
  intro w hw
  rw [Circuit.support_gate, QRegister.mem_image] at hw
  rcases hw with ⟨_, rfl⟩
  exact Finset.mem_singleton_self q

private theorem cBitZ_support_subset {n : ℕ} (m : Bool) (q : Wire n) :
    (cBitZ m q).support ⊆ {q} := by
  cases m
  · simp [cBitZ]
  · exact single_support_subset .Z q

private theorem cPauliGateFwd_support_subset {n : ℕ} (b f : Bool) (q : Wire n) :
    (cPauliGateFwd b f q).support ⊆ {q} := by
  cases b
  · simp [cPauliGateFwd]
  · cases f
    · exact single_support_subset .H q
    · dsimp only [cPauliGateFwd]
      rw [Circuit.support_seq, Circuit.support_seq]
      exact Finset.union_subset (single_support_subset .S q)
        (Finset.union_subset (single_support_subset .Z q) (single_support_subset .H q))

private theorem cPauliGateInv_support_subset {n : ℕ} (b f : Bool) (q : Wire n) :
    (cPauliGateInv b f q).support ⊆ {q} := by
  cases b
  · simp [cPauliGateInv]
  · cases f
    · exact single_support_subset .H q
    · dsimp only [cPauliGateInv]
      rw [Circuit.support_seq]
      exact Finset.union_subset (single_support_subset .H q) (single_support_subset .S q)

private theorem cPauliGateInv_mul_cPauliGateFwd_eval {n : ℕ} (b f : Bool) (q : Wire n) :
    (cPauliGateInv b f q).eval * (cPauliGateFwd b f q).eval = 1 := by
  cases b
  · simp [cPauliGateInv, cPauliGateFwd]
  · cases f
    · dsimp only [cPauliGateInv, cPauliGateFwd]
      rw [Circuit.eval_single, ← (QRegister.singleton q).embedUnitary_mul, PrimitiveGate.eval,
        Qubit.H_sq, QRegister.embedUnitary_one]
    · dsimp only [cPauliGateInv, cPauliGateFwd]
      simp only [Circuit.eval_seq, Circuit.eval_single, PrimitiveGate.eval,
        ← (QRegister.singleton q).embedUnitary_mul]
      have hq : (Qubit.S * Qubit.H) * ((Qubit.H * Qubit.Z) * Qubit.S) = 1 := by
        calc (Qubit.S * Qubit.H) * ((Qubit.H * Qubit.Z) * Qubit.S)
            = Qubit.S * (Qubit.H * Qubit.H) * (Qubit.Z * Qubit.S) := by simp only [mul_assoc]
          _ = Qubit.S * (Qubit.S * Qubit.Z) := by rw [Qubit.H_sq, mul_one, Qubit.S_Z_comm]
          _ = (Qubit.S * Qubit.S) * Qubit.Z := (mul_assoc _ _ _).symm
          _ = 1 := by rw [Qubit.S_sq, Qubit.Z_sq]
      rw [hq, QRegister.embedUnitary_one]
private theorem cPauliGate_active_eval {n : ℕ} (b f : Bool) (q : Wire n) :
    ((cPauliGateInv b f q).eval * (cBitZ (b || f) q).eval * (cPauliGateFwd b f q).eval *
      (Circuit.H q).eval * (cBitZ b q).eval * (Circuit.H q).eval * (cBitZ f q).eval).1 =
      (if b && f then (-Complex.I) else 1) • (1 : QOp n) := by
  cases b <;> cases f
  · simp only [cPauliGateInv, cPauliGateFwd, cBitZ, Bool.false_or, Bool.false_and, ↓reduceIte,
      Bool.false_eq_true, Circuit.eval_identity, Circuit.eval_single, PrimitiveGate.eval,
      one_mul, mul_one, ← (QRegister.singleton q).embedUnitary_mul]
    rw [Qubit.H_sq, QRegister.embedUnitary_one, Submonoid.coe_one, one_smul]
  · simp only [cPauliGateInv, cPauliGateFwd, cBitZ, Bool.false_or, Bool.false_and, ↓reduceIte,
      Bool.false_eq_true, Circuit.eval_identity, Circuit.eval_single, PrimitiveGate.eval,
      one_mul, mul_one, ← (QRegister.singleton q).embedUnitary_mul, mul_assoc]
    have hq : Qubit.Z * (Qubit.H * (Qubit.H * Qubit.Z)) = 1 := by
      rw [← mul_assoc Qubit.H Qubit.H Qubit.Z, Qubit.H_sq, one_mul, Qubit.Z_sq]
    rw [hq, QRegister.embedUnitary_one, Submonoid.coe_one, one_smul]
  · simp only [cPauliGateInv, cPauliGateFwd, cBitZ, Bool.true_or, Bool.and_false, ↓reduceIte,
      Bool.false_eq_true, Circuit.eval_identity, Circuit.eval_single, PrimitiveGate.eval,
      mul_one, ← (QRegister.singleton q).embedUnitary_mul, mul_assoc]
    have hq : Qubit.H * (Qubit.Z * (Qubit.H * (Qubit.H * (Qubit.Z * Qubit.H)))) = 1 := by
      rw [← mul_assoc Qubit.H Qubit.H, Qubit.H_sq, one_mul,
        ← mul_assoc Qubit.Z Qubit.Z, Qubit.Z_sq, one_mul, Qubit.H_sq]
    rw [hq, QRegister.embedUnitary_one, Submonoid.coe_one, one_smul]
  · have hHZH : Qubit.H * Qubit.Z * Qubit.H = Qubit.X := by
      rw [Qubit.H_mul_Z_eq_X_mul_H, mul_assoc, Qubit.H_sq, mul_one]
    simp only [cPauliGateInv, cPauliGateFwd, cBitZ, Bool.true_or, Bool.and_true, ↓reduceIte,
      Circuit.eval_seq, Circuit.eval_single, PrimitiveGate.eval,
      ← (QRegister.singleton q).embedUnitary_mul, mul_assoc]
    have hq : (Qubit.S * (Qubit.H * (Qubit.Z * (Qubit.H * (Qubit.Z *
        (Qubit.S * (Qubit.H * (Qubit.Z * (Qubit.H * Qubit.Z))))))))).1 =
        (-Complex.I) • (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) := by
      have heq : Qubit.S * (Qubit.H * (Qubit.Z * (Qubit.H * (Qubit.Z *
          (Qubit.S * (Qubit.H * (Qubit.Z * (Qubit.H * Qubit.Z)))))))) =
          Qubit.S * Qubit.X * Qubit.Z * Qubit.S * Qubit.X * Qubit.Z := by
        calc Qubit.S * (Qubit.H * (Qubit.Z * (Qubit.H * (Qubit.Z *
                (Qubit.S * (Qubit.H * (Qubit.Z * (Qubit.H * Qubit.Z))))))))
            = Qubit.S * (Qubit.H * Qubit.Z * Qubit.H) * Qubit.Z * Qubit.S *
                (Qubit.H * Qubit.Z * Qubit.H) * Qubit.Z := by simp only [mul_assoc]
          _ = Qubit.S * Qubit.X * Qubit.Z * Qubit.S * Qubit.X * Qubit.Z := by rw [hHZH]
      rw [heq]
      simp only [Submonoid.coe_mul, Qubit.S, Qubit.X, Qubit.Z]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [QRegister.embedUnitary_val, hq, QRegister.embedMatrix_smul, QRegister.embedMatrix_one]

private def WallSupp {n M : ℕ} (r : QRegister M n) (g : Fin M → Wire n → Circuit n) : Prop :=
  ∀ i : Fin M, (g i (r i)).support ⊆ {r i}

private theorem cWireWallAux_support_mem {n M : ℕ} (r : QRegister M n)
    (g : Fin M → Wire n → Circuit n) (hg : WallSupp r g) :
    ∀ (k : ℕ) (hk : k ≤ M) {w : Wire n},
      w ∈ (cWireWallAux r g k hk).support → ∃ t : Fin k, r ⟨t.val, by omega⟩ = w
  | 0, _, _, hw => by simp [cWireWallAux] at hw
  | k + 1, hk, w, hw => by
      dsimp only [cWireWallAux] at hw
      rw [Circuit.support_seq, Finset.mem_union] at hw
      rcases hw with hw1 | hw2
      · obtain ⟨t, ht⟩ := cWireWallAux_support_mem r g hg k (by omega) hw1
        exact ⟨⟨t.val, by omega⟩, ht⟩
      · exact ⟨⟨k, Nat.lt_succ_self k⟩, (Finset.mem_singleton.mp (hg ⟨k, hk⟩ hw2)).symm⟩

private theorem cWireWallAux_eval_mul {n M : ℕ} (r : QRegister M n)
    (g₁ g₂ : Fin M → Wire n → Circuit n) (hg₁ : WallSupp r g₁) (hg₂ : WallSupp r g₂) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (cWireWallAux r g₁ k hk).eval * (cWireWallAux r g₂ k hk).eval =
        (cWireWallAux r (fun i q ↦ g₂ i q ;;ᶜ g₁ i q) k hk).eval
  | 0, _ => mul_one 1
  | k + 1, hk => by
      have ih := cWireWallAux_eval_mul r g₁ g₂ hg₁ hg₂ k (by omega)
      have hdisj : Disjoint (cWireWallAux r g₁ k (by omega)).support
          (g₂ ⟨k, hk⟩ (r ⟨k, hk⟩)).support := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        obtain ⟨t, ht⟩ := cWireWallAux_support_mem r g₁ hg₁ k (by omega) hw1
        have hidx : (⟨t.val, by omega⟩ : Fin M) = ⟨k, hk⟩ :=
          r.wires.injective (ht.trans (Finset.mem_singleton.mp (hg₂ ⟨k, hk⟩ hw2)))
        have hval : t.val = k := congrArg Fin.val hidx
        omega
      have hcomm := eval_comm_of_disjoint_support _ _ hdisj
      dsimp only [cWireWallAux]
      simp only [Circuit.eval_seq]
      calc ((g₁ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval * (cWireWallAux r g₁ k (by omega)).eval) *
              ((g₂ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval * (cWireWallAux r g₂ k (by omega)).eval)
          = (g₁ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval *
              ((cWireWallAux r g₁ k (by omega)).eval * (g₂ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval) *
              (cWireWallAux r g₂ k (by omega)).eval := by simp only [mul_assoc]
        _ = ((g₁ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval * (g₂ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval) *
              ((cWireWallAux r g₁ k (by omega)).eval *
                (cWireWallAux r g₂ k (by omega)).eval) := by
              rw [hcomm]
              simp only [mul_assoc]
        _ = ((g₁ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval * (g₂ ⟨k, hk⟩ (r ⟨k, hk⟩)).eval) *
              (cWireWallAux r (fun i q ↦ g₂ i q ;;ᶜ g₁ i q) k (by omega)).eval := by rw [ih]

private theorem wall_mul {n M : ℕ} {r : QRegister M n}
    {g₁ g₂ : Fin M → Wire n → Circuit n} (h₁ : WallSupp r g₁) (h₂ : WallSupp r g₂) :
    (cWireWallAux r g₁ M le_rfl).eval * (cWireWallAux r g₂ M le_rfl).eval =
      (cWireWallAux r (fun i q ↦ g₂ i q ;;ᶜ g₁ i q) M le_rfl).eval ∧
      WallSupp r (fun i q ↦ g₂ i q ;;ᶜ g₁ i q) :=
  ⟨cWireWallAux_eval_mul r g₁ g₂ h₁ h₂ M le_rfl, fun i ↦ by
    dsimp only
    rw [Circuit.support_seq]
    exact Finset.union_subset (h₂ i) (h₁ i)⟩

private theorem cWireWallAux_eval_smul_one {n M : ℕ} (r : QRegister M n)
    (g : Fin M → Wire n → Circuit n) (ω : Fin M → ℂ)
    (hg : ∀ i : Fin M, (g i (r i)).eval.1 = ω i • (1 : QOp n)) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (cWireWallAux r g k hk).eval.1 =
        (∏ t : Fin k, ω ⟨t.val, by omega⟩) • (1 : QOp n)
  | 0, _ => by simp [cWireWallAux]
  | k + 1, hk => by
      dsimp only [cWireWallAux]
      rw [Circuit.eval_seq, Submonoid.coe_mul, hg ⟨k, hk⟩,
        cWireWallAux_eval_smul_one r g ω hg k (by omega),
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
        Fin.prod_univ_castSucc]
      exact congrArg (· • (1 : QOp n)) (mul_comm _ _)

private inductive InFiber {n M : ℕ} (r : QRegister M n) (β : BitAssignment n) :
    (Fin (QubitDim n) → ℂ) → Prop
  | ket_mem (α : BitAssignment n)
      (h_out : ∀ w : Wire n, w ∉ Set.range r.wires → α w = β w) : InFiber r β (ket α)
  | zero_mem : InFiber r β 0
  | add_mem {ψ₁ ψ₂} : InFiber r β ψ₁ → InFiber r β ψ₂ → InFiber r β (ψ₁ + ψ₂)
  | smul_mem (c : ℂ) {ψ} : InFiber r β ψ → InFiber r β (c • ψ)

private theorem inFiber_mulVec_eq {n M : ℕ} {r : QRegister M n} {β : BitAssignment n}
    {A B : QOp n}
    (hAB : ∀ α : BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range r.wires → α w = β w) →
      A.mulVec (ket α) = B.mulVec (ket α))
    {ψ : Fin (QubitDim n) → ℂ} (hψ : InFiber r β ψ) :
    A.mulVec ψ = B.mulVec ψ := by
  induction hψ with
  | ket_mem α h_out => exact hAB α h_out
  | zero_mem => simp
  | add_mem _ _ ih₁ ih₂ => rw [Matrix.mulVec_add, Matrix.mulVec_add, ih₁, ih₂]
  | smul_mem c _ ih => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ih]

private theorem inFiber_update {n M : ℕ} {r : QRegister M n} {α β : BitAssignment n}
    (h_out : ∀ w : Wire n, w ∉ Set.range r.wires → α w = β w) (i : Fin M) (v : ZMod 2) :
    InFiber r β (ket (Function.update α (r i) v)) :=
  InFiber.ket_mem _ fun w hw ↦ by
    rw [Function.update_of_ne (fun heq ↦ hw ⟨i, heq.symm⟩)]
    exact h_out w hw

private theorem inFiber_single {n M : ℕ} {r : QRegister M n} {β : BitAssignment n}
    (g : PrimitiveGate 1) (i : Fin M) {ψ : Fin (QubitDim n) → ℂ} (hψ : InFiber r β ψ) :
    InFiber r β ((Circuit.single g (r i)).eval.1.mulVec ψ) := by
  induction hψ with
  | ket_mem α h_out =>
      have hG := singleton_embedMatrix_mulVec_ket (r i) g.eval.1 α
      have hk : ∀ γ : BitAssignment n, OctahedralOrbit.ket γ = ket γ :=
        fun _ ↦ rfl
      simp only [hk] at hG
      rw [Circuit.eval_single, QRegister.embedUnitary_val]
      change InFiber r β (((QRegister.singleton (r i)).embedMatrix g.eval.1).mulVec (ket α))
      rw [hG]
      exact InFiber.add_mem (InFiber.smul_mem _ (inFiber_update h_out i 0))
        (InFiber.smul_mem _ (inFiber_update h_out i 1))
  | zero_mem =>
      rw [Matrix.mulVec_zero]
      exact InFiber.zero_mem
  | add_mem _ _ ih₁ ih₂ =>
      rw [Matrix.mulVec_add]
      exact InFiber.add_mem ih₁ ih₂
  | smul_mem c _ ih =>
      rw [Matrix.mulVec_smul]
      exact InFiber.smul_mem c ih

private theorem inFiber_cWireWallAux {n M : ℕ} (r : QRegister M n)
    (g : Fin M → Wire n → Circuit n)
    (hg : ∀ (i : Fin M) (β : BitAssignment n) (ψ : Fin (QubitDim n) → ℂ),
      InFiber r β ψ → InFiber r β ((g i (r i)).eval.1.mulVec ψ)) :
    ∀ (k : ℕ) (hk : k ≤ M) {β : BitAssignment n} {ψ : Fin (QubitDim n) → ℂ},
      InFiber r β ψ → InFiber r β ((cWireWallAux r g k hk).eval.1.mulVec ψ)
  | 0, _, _, _, hψ => by simpa [cWireWallAux] using hψ
  | k + 1, hk, β, ψ, hψ => by
      dsimp only [cWireWallAux]
      rw [eval_seq_mulVec]
      exact hg ⟨k, hk⟩ β _ (inFiber_cWireWallAux r g hg k (by omega) hψ)

private theorem supportedOn_of_inFiber {n M : ℕ} (r : QRegister M n) (c : Circuit n)
    {Pred : BitAssignment n → Prop}
    (hIgn : ∀ α β : BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range r.wires → α w = β w) → (Pred α ↔ Pred β))
    (hFib : ∀ β : BitAssignment n, InFiber r β (c.eval.1.mulVec (ket β)))
    {R : QOp n} (hSupp : SupportedOn Pred R) :
    SupportedOn Pred (c.eval.1 * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hSupp (A * c.eval.1) (B * c.eval.1) fun β hPredβ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact inFiber_mulVec_eq (fun α h_out ↦ hAB α ((hIgn α β h_out).mpr hPredβ)) (hFib β)
private noncomputable def cMaskZWall {n N_slot : ℕ} (s₀ : Fin N_slot) (m : Fin 18 → Bool)
    (r : QRegister (N_slot * 18) n) : Circuit n :=
  cWireWallAux r (fun i q ↦ cBitZ (decide (i.val / 18 = s₀.val) && m (lane18 i)) q)
    (N_slot * 18) le_rfl

private theorem inFiber_cPauliGateFwd {n M : ℕ} {r : QRegister M n} {β : BitAssignment n}
    (b f : Bool) (i : Fin M) {ψ : Fin (QubitDim n) → ℂ} (hψ : InFiber r β ψ) :
    InFiber r β ((cPauliGateFwd b f (r i)).eval.1.mulVec ψ) := by
  cases b
  · simpa [cPauliGateFwd] using hψ
  · cases f
    · exact inFiber_single .H i hψ
    · dsimp only [cPauliGateFwd]
      rw [eval_seq_mulVec, eval_seq_mulVec]
      exact inFiber_single .H i (inFiber_single .Z i (inFiber_single .S i hψ))

private theorem inFiber_cBitZ {n M : ℕ} {r : QRegister M n} {β : BitAssignment n}
    (m : Bool) (i : Fin M) {ψ : Fin (QubitDim n) → ℂ} (hψ : InFiber r β ψ) :
    InFiber r β ((cBitZ m (r i)).eval.1.mulVec ψ) := by
  cases m
  · simpa [cBitZ] using hψ
  · exact inFiber_single .Z i hψ

private theorem inFiber_cHadWall {n M : ℕ} (r : QRegister M n) {β : BitAssignment n}
    {ψ : Fin (QubitDim n) → ℂ} (hψ : InFiber r β ψ) :
    InFiber r β ((cHadWall r).eval.1.mulVec ψ) :=
  inFiber_cWireWallAux r (fun _ q ↦ Circuit.H q)
    (fun i _ _ h ↦ inFiber_single (r := r) .H i h) M le_rfl hψ

private theorem inFiber_cPauliWallFwd_wall {n M : ℕ} (b' f : Fin 18 → Bool) (r : QRegister M n)
    {β : BitAssignment n} {ψ : Fin (QubitDim n) → ℂ} (hψ : InFiber r β ψ) :
    InFiber r β ((cPauliWallFwd b' f r).eval.1.mulVec ψ) :=
  inFiber_cWireWallAux r (fun i q ↦ cPauliGateFwd (b' (lane18 i)) (f (lane18 i)) q)
    (fun i _ _ h ↦ inFiber_cPauliGateFwd (r := r) _ _ i h) M le_rfl hψ

private theorem inFiber_cMaskZWall {n N_slot : ℕ} (s₀ : Fin N_slot) (m : Fin 18 → Bool)
    (rElec : QRegister (N_slot * 18) n) {β : BitAssignment n}
    {ψ : Fin (QubitDim n) → ℂ} (hψ : InFiber rElec β ψ) :
    InFiber rElec β ((cMaskZWall s₀ m rElec).eval.1.mulVec ψ) :=
  inFiber_cWireWallAux rElec
    (fun i q ↦ cBitZ (decide (i.val / 18 = s₀.val) && m (lane18 i)) q)
    (fun i _ _ h ↦ inFiber_cBitZ (r := rElec) _ i h) (N_slot * 18) le_rfl hψ

private theorem cBitZ_mulVec_ket {n : ℕ} (b : Bool) (q : Wire n) (α : BitAssignment n) :
    (cBitZ b q).eval.1.mulVec (ket α) = (if b then bitSign (α q) else 1) • ket α := by
  cases b
  · simp [cBitZ]
  · exact ket_Z q α

private theorem cBitZWallAux_mulVec_ket {n M : ℕ} (r : QRegister M n) (zFlag : Fin M → Bool)
    (α : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (cWireWallAux r (fun i q ↦ cBitZ (zFlag i) q) k hk).eval.1.mulVec (ket α) =
        (∏ t : Fin k, if zFlag ⟨t.val, by omega⟩ then bitSign (α (r ⟨t.val, by omega⟩)) else 1) •
          ket α
  | 0, _ => by simp [cWireWallAux]
  | k + 1, hk => by
      dsimp only [cWireWallAux]
      rw [eval_seq_mulVec, cBitZWallAux_mulVec_ket r zFlag α k (by omega), Matrix.mulVec_smul,
        cBitZ_mulVec_ket, smul_smul, Fin.prod_univ_castSucc]
      rfl

private theorem prod_slot_eq_prod_fin18 {N_slot : ℕ} (s₀ : Fin N_slot)
    (F : Fin (N_slot * 18) → ℂ) :
    (∏ i : Fin (N_slot * 18), if i.val / 18 = s₀.val then F i else 1) =
      ∏ j : Fin 18, F (elecFlatIdx s₀ j) := by
  let emb : Fin 18 ↪ Fin (N_slot * 18) :=
    ⟨elecFlatIdx s₀, fun j₁ j₂ h ↦ by
      have hv := congrArg Fin.val h
      dsimp only [elecFlatIdx] at hv
      exact Fin.ext (by omega)⟩
  rw [← Finset.prod_subset (Finset.subset_univ ((Finset.univ : Finset (Fin 18)).map emb))]
  · rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hj : j.val < 18 := j.isLt
    have hdiv : (emb j).val / 18 = s₀.val := by
      change (18 * s₀.val + j.val) / 18 = s₀.val
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hdiv)]
    rfl
  · intro i _ hiNot
    by_cases hdiv : i.val / 18 = s₀.val
    · exfalso
      apply hiNot
      rw [Finset.mem_map]
      refine ⟨⟨i.val % 18, Nat.mod_lt _ (by decide)⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      have hmod := Nat.div_add_mod i.val 18
      change 18 * s₀.val + i.val % 18 = i.val
      omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hdiv)]

private theorem cMaskZWall_mulVec_ket {n N_slot : ℕ} (s₀ : Fin N_slot) (m : Fin 18 → Bool)
    (rElec : QRegister (N_slot * 18) n) (α : BitAssignment n) :
    (cMaskZWall s₀ m rElec).eval.1.mulVec (ket α) =
      (∏ j : Fin 18, if m j then bitSign (α (rElec (elecFlatIdx s₀ j))) else 1) • ket α := by
  dsimp only [cMaskZWall]
  rw [cBitZWallAux_mulVec_ket]
  refine congrArg (· • ket α) ?_
  have hrew : (∏ t : Fin (N_slot * 18),
      if (decide (t.val / 18 = s₀.val) && m (lane18 ⟨t.val, t.isLt⟩)) = true
      then bitSign (α (rElec ⟨t.val, t.isLt⟩)) else 1) =
      ∏ i : Fin (N_slot * 18),
        if i.val / 18 = s₀.val
        then (if m (lane18 i) then bitSign (α (rElec i)) else 1) else 1 := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    by_cases hdiv : i.val / 18 = s₀.val <;> simp [hdiv]
  rw [hrew, prod_slot_eq_prod_fin18]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [lane18_elecFlatIdx]

private theorem cHadWall_eval_mul_self {n M : ℕ} (r : QRegister M n) :
    (cHadWall r).eval * (cHadWall r).eval = 1 := by
  have hH : WallSupp r (fun _ q ↦ Circuit.H q) := fun i ↦ single_support_subset .H (r i)
  dsimp only [cHadWall]
  rw [cWireWallAux_eval_mul r _ _ hH hH]
  apply Subtype.ext
  rw [cWireWallAux_eval_smul_one r _ (fun _ ↦ 1) (fun i ↦ by
    rw [Circuit.eval_seq, Circuit.eval_single, ← (QRegister.singleton (r i)).embedUnitary_mul,
      PrimitiveGate.eval, Qubit.H_sq, QRegister.embedUnitary_one, Submonoid.coe_one, one_smul])]
  simp

private theorem pauliWall_conj_hadWall_maskZ_eval {n N_slot : ℕ}
    (s₀ : Fin N_slot) (b' f : Fin 18 → Bool) (rElec : QRegister (N_slot * 18) n) :
    ((cPauliWallInv b' f rElec).eval *
      (cMaskZWall s₀ (fun j ↦ b' j || f j) rElec).eval *
      (cPauliWallFwd b' f rElec).eval *
      (cHadWall rElec).eval *
      (cMaskZWall s₀ b' rElec).eval *
      (cHadWall rElec).eval *
      (cMaskZWall s₀ f rElec).eval).1 =
      pauliFusedPhase18 b' f • (1 : QOp n) := by
  let gInv : Fin (N_slot * 18) → Wire n → Circuit n :=
    fun i q ↦ cPauliGateInv (b' (lane18 i)) (f (lane18 i)) q
  let gZbf : Fin (N_slot * 18) → Wire n → Circuit n :=
    fun i q ↦ cBitZ (decide (i.val / 18 = s₀.val) && (b' (lane18 i) || f (lane18 i))) q
  let gFwd : Fin (N_slot * 18) → Wire n → Circuit n :=
    fun i q ↦ cPauliGateFwd (b' (lane18 i)) (f (lane18 i)) q
  let gH : Fin (N_slot * 18) → Wire n → Circuit n := fun _ q ↦ Circuit.H q
  let gZb : Fin (N_slot * 18) → Wire n → Circuit n :=
    fun i q ↦ cBitZ (decide (i.val / 18 = s₀.val) && b' (lane18 i)) q
  let gZf : Fin (N_slot * 18) → Wire n → Circuit n :=
    fun i q ↦ cBitZ (decide (i.val / 18 = s₀.val) && f (lane18 i)) q
  have hInv : WallSupp rElec gInv := fun _ ↦ cPauliGateInv_support_subset _ _ _
  have hZbf : WallSupp rElec gZbf := fun _ ↦ cBitZ_support_subset _ _
  have hFwd : WallSupp rElec gFwd := fun _ ↦ cPauliGateFwd_support_subset _ _ _
  have hH : WallSupp rElec gH := fun _ ↦ single_support_subset .H _
  have hZb : WallSupp rElec gZb := fun _ ↦ cBitZ_support_subset _ _
  have hZf : WallSupp rElec gZf := fun _ ↦ cBitZ_support_subset _ _
  dsimp only [cPauliWallInv, cMaskZWall, cPauliWallFwd, cHadWall]
  obtain ⟨e1, s1⟩ := wall_mul hInv hZbf
  obtain ⟨e2, s2⟩ := wall_mul s1 hFwd
  obtain ⟨e3, s3⟩ := wall_mul s2 hH
  obtain ⟨e4, s4⟩ := wall_mul s3 hZb
  obtain ⟨e5, s5⟩ := wall_mul s4 hH
  obtain ⟨e6, _⟩ := wall_mul s5 hZf
  rw [e1, e2, e3, e4, e5, e6, cWireWallAux_eval_smul_one rElec _
    (fun i ↦ if i.val / 18 = s₀.val then (if b' (lane18 i) && f (lane18 i) then -Complex.I else 1)
      else 1)]
  · refine congrArg (· • (1 : QOp n)) ?_
    have hprod := prod_slot_eq_prod_fin18 s₀
      (fun i ↦ if b' (lane18 i) && f (lane18 i) then (-Complex.I) else 1)
    dsimp only [pauliFusedPhase18]
    refine (Finset.prod_congr rfl fun t _ ↦ rfl).trans (hprod.trans ?_)
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [lane18_elecFlatIdx]
  · intro i
    dsimp only [gInv, gZbf, gFwd, gH, gZb, gZf]
    simp only [Circuit.eval_seq, mul_assoc]
    by_cases hdiv : i.val / 18 = s₀.val
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hdiv)]
      simp only [decide_eq_true hdiv, Bool.true_and]
      simpa only [mul_assoc] using cPauliGate_active_eval (b' (lane18 i)) (f (lane18 i)) (rElec i)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hdiv)]
      simp only [decide_eq_false hdiv, Bool.false_and, cBitZ, Bool.false_eq_true, ↓reduceIte,
        Circuit.eval_identity, one_mul, mul_one]
      have hHH : (Circuit.H (rElec i)).eval * (Circuit.H (rElec i)).eval = 1 := by
        rw [Circuit.eval_single, ← (QRegister.singleton (rElec i)).embedUnitary_mul,
          PrimitiveGate.eval, Qubit.H_sq, QRegister.embedUnitary_one]
      have hIF := cPauliGateInv_mul_cPauliGateFwd_eval (b' (lane18 i)) (f (lane18 i)) (rElec i)
      have hU : (cPauliGateInv (b' (lane18 i)) (f (lane18 i)) (rElec i)).eval *
          ((cPauliGateFwd (b' (lane18 i)) (f (lane18 i)) (rElec i)).eval *
            ((Circuit.H (rElec i)).eval * (Circuit.H (rElec i)).eval)) = 1 := by
        rw [hHH, mul_one, hIF]
      rw [hU, Submonoid.coe_one, one_smul]
private theorem pauliWall_conj_hadWall_diag_eq_unit_smul {n N_slot : ℕ}
    (rElec : QRegister (N_slot * 18) n)
    (U_diag : (Fin 18 → Bool) → QOp n)
    (slotOf : BitAssignment n → Fin N_slot)
    (hSlot_ign : ∀ α β : BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range rElec.wires → α w = β w) → slotOf α = slotOf β)
    (hU_ket : ∀ (m : Fin 18 → Bool) (α : BitAssignment n),
      (U_diag m).mulVec (ket α) =
        (∏ j : Fin 18, if m j then bitSign (α (rElec (elecFlatIdx (slotOf α) j))) else 1) • ket α)
    (b' f : Fin 18 → Bool) :
    (cPauliWallInv b' f rElec).eval.1 * U_diag (fun j ↦ b' j || f j) *
      (cPauliWallFwd b' f rElec).eval.1 * (cHadWall rElec).eval.1 * U_diag b' *
      (cHadWall rElec).eval.1 * U_diag f =
      pauliFusedPhase18 b' f • (1 : QOp n) := by
  apply matrix_ext_ket
  intro β
  let s₀ := slotOf β
  have hSub : ∀ (m : Fin 18 → Bool) {ψ : Fin (QubitDim n) → ℂ},
      InFiber rElec β ψ →
      (U_diag m).mulVec ψ = (cMaskZWall s₀ m rElec).eval.1.mulVec ψ := fun m _ hψ ↦
    inFiber_mulVec_eq (fun α h_out ↦ by
      rw [hU_ket m α, cMaskZWall_mulVec_ket]
      simp only [s₀, hSlot_ign α β h_out]) hψ
  have hf0 : InFiber rElec β (ket β) := InFiber.ket_mem β fun _ _ ↦ rfl
  have hf2 := inFiber_cHadWall rElec (inFiber_cMaskZWall s₀ f rElec hf0)
  have hf5 := inFiber_cPauliWallFwd_wall b' f rElec
    (inFiber_cHadWall rElec (inFiber_cMaskZWall s₀ b' rElec hf2))
  simp only [← Matrix.mulVec_mulVec]
  rw [hSub f hf0, hSub b' hf2, hSub (fun j ↦ b' j || f j) hf5]
  simpa only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] using
    congrArg (fun M : QOp n ↦ M.mulVec (ket β)) (pauliWall_conj_hadWall_maskZ_eval s₀ b' f rElec)

private theorem comm_of_diag_ket {n : ℕ} (D₁ D₂ : QOp n)
    (d₁ d₂ : BitAssignment n → ℂ)
    (h₁ : ∀ α : BitAssignment n, D₁.mulVec (ket α) = d₁ α • ket α)
    (h₂ : ∀ α : BitAssignment n, D₂.mulVec (ket α) = d₂ α • ket α) :
    D₁ * D₂ = D₂ * D₁ := by
  apply matrix_ext_ket
  intro α
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h₂ α, Matrix.mulVec_smul, h₁ α,
    Matrix.mulVec_smul, h₂ α, smul_smul, smul_smul, mul_comm]

private theorem supportedOn_diag_ket {n : ℕ} {Pred : BitAssignment n → Prop}
    (D : QOp n) (d : BitAssignment n → ℂ)
    (hD : ∀ α : BitAssignment n, D.mulVec (ket α) = d α • ket α)
    {R : QOp n} (hSupp : SupportedOn Pred R) :
    SupportedOn Pred (D * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hSupp (A * D) (B * D) fun β hP ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD β,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hAB β hP]

private theorem u_diag_mul_self {n N_slot : ℕ} (rElec : QRegister (N_slot * 18) n)
    (U_diag : (Fin 18 → Bool) → QOp n)
    (slotOf : BitAssignment n → Fin N_slot)
    (hU_ket : ∀ (m : Fin 18 → Bool) (α : BitAssignment n),
      (U_diag m).mulVec (ket α) =
        (∏ j : Fin 18, if m j then bitSign (α (rElec (elecFlatIdx (slotOf α) j))) else 1) • ket α)
    (m : Fin 18 → Bool) :
    U_diag m * U_diag m = 1 := by
  apply matrix_ext_ket
  intro α
  rw [← Matrix.mulVec_mulVec, hU_ket m α, Matrix.mulVec_smul, hU_ket m α, smul_smul,
    Matrix.one_mulVec, ← Finset.prod_mul_distrib]
  have hp : (∏ j : Fin 18,
      (if m j then bitSign (α (rElec (elecFlatIdx (slotOf α) j))) else 1) *
        (if m j then bitSign (α (rElec (elecFlatIdx (slotOf α) j))) else 1)) = 1 := by
    refine Finset.prod_eq_one fun j _ ↦ ?_
    cases m j <;> simp [bitSign_mul_self]
  rw [hp, one_smul]

private theorem eq_smul_of_inv_mul {n : ℕ} {D X Y : QOp n} {c : ℂ}
    (hSq : D * D = 1) (hCol : D * X = c • Y) : X = c • (D * Y) := by
  rw [← Matrix.one_mul X, ← hSq, Matrix.mul_assoc, hCol, Matrix.mul_smul]

private theorem xResetKraus_comm_cHadWall {n b M : ℕ}
    (rMeas : QRegister b n) (rElec : QRegister M n)
    (hME : rMeas.DisjointWires rElec) (f : Fin b → Bool) :
    DynCircuitExt.xResetKraus rMeas f * (cHadWall rElec).eval.1 =
      (cHadWall rElec).eval.1 * DynCircuitExt.xResetKraus rMeas f :=
  xResetKraus_comm_of_wire_comm rMeas _ (fun q hq A ↦
    (eval_comm_embedMatrix_of_disjoint_support (cHadWall rElec) q (fun i hj ↦ by
      obtain ⟨j, hj_eq⟩ := hq i
      obtain ⟨t, ht⟩ := cWireWallAux_support_mem rElec _
        (fun k ↦ single_support_subset .H (rElec k)) M le_rfl hj
      exact hME.ne j ⟨t.val, t.isLt⟩ (hj_eq.trans ht.symm)) A).symm) f

/-- Split-invariant `SubspaceStep` bridge for `dPostHoleHeld1wKQSlotFused`, decoupling the
pre-`MX(rMeas)` tail support invariant `Inv_mid` (`dUnheldTail`) from the post-`MX(rMeas)` fixup
support invariant `Inv_post` (`dFix`) so `dFix` inherits all `K + 18` post-measurement clean
ancillas (`rHeld` and `rMeas` in `|0⟩`). -/
theorem subspaceStep_dPostHoleHeld1wKFused_split {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N_slot : ℕ} [NeZero (QubitDim n)]
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rElec : QRegister (N_slot * 18) n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hME : rMeas.DisjointWires rElec) (hMH : rMeas.DisjointWires rHeld)
    {dUnheldTail : DynamicCircuit Var n}
    {dFix : (Fin 18 → Bool) → DynamicCircuit Var n}
    {Inv_mid Inv_post : BitAssignment n → Prop}
    {U_hold U_kickK U_kick18 R_mid T_set R : QOp n}
    {U_diag : (Fin 18 → Bool) → QOp n}
    {slotOf : BitAssignment n → Fin N_slot}
    {dK d18 : BitAssignment n → ℂ}
    (hInv_post_ign : ∀ α β : BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range rElec.wires → α w = β w) → (Inv_post α ↔ Inv_post β))
    (hSlot_ign : ∀ α β : BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range rElec.wires → α w = β w) → slotOf α = slotOf β)
    (hU_ket : ∀ (m : Fin 18 → Bool) (α : BitAssignment n),
      (U_diag m).mulVec (ket α) =
        (∏ j : Fin 18, if m j then bitSign (α (rElec (elecFlatIdx (slotOf α) j))) else 1) • ket α)
    (hKickK_ket : ∀ α : BitAssignment n, U_kickK.mulVec (ket α) = dK α • ket α)
    (hKick18_ket : ∀ α : BitAssignment n, U_kick18.mulVec (ket α) = d18 α • ket α)
    (hSuppMid : SupportedOn Inv_mid R_mid)
    (hSuppR : SupportedOn Inv_post R)
    (hCz : (cHeldCzPrefixAux K hK rMeas rHeld hMH K le_rfl).eval.1 * (U_hold * R_mid) =
      U_hold * (U_kickK * R_mid))
    (hHeldCollapse : ∀ b : Fin K → Bool,
      U_diag (extendMask18 K b) *
        (DynCircuitExt.xResetKraus rHeld b * (U_hold * (U_kickK * R_mid))) =
        (((√(1 / 2)) ^ K : ℝ) : ℂ) • (U_kickK * R_mid))
    (hTail : ∀ {R₀ : QOp n}, SupportedOn Inv_mid R₀ →
      SubspaceStep (U_kickK * R₀) (U_kick18 * R₀) dUnheldTail)
    (hPreMeasEq : (cHadWall rElec).eval.1 * (U_kick18 * R_mid) = T_set * R)
    (hMeasCommDiag : ∀ (m f : Fin 18 → Bool),
      DynCircuitExt.xResetKraus rMeas f * U_diag m =
        U_diag m * DynCircuitExt.xResetKraus rMeas f)
    (hMeasCollapse : ∀ f : Fin 18 → Bool,
      U_diag f * (DynCircuitExt.xResetKraus rMeas f * (T_set * R)) =
        (((√(1 / 2)) ^ 18 : ℝ) : ℂ) • R)
    (hFix : ∀ (m : Fin 18 → Bool) {R₀ : QOp n}, SupportedOn Inv_post R₀ →
      SubspaceStep R₀ (U_diag m * R₀) (dFix m)) :
    SubspaceStep (U_hold * R_mid) R
      (dPostHoleHeld1wKQSlotFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix) := by
  dsimp only [dPostHoleHeld1wKQSlotFused, dPostHoleHeld1wKFused]
  have hDiagSq := u_diag_mul_self rElec U_diag slotOf hU_ket
  refine subspaceStep_seq_measureXReset v rHeld
    (subspaceStep_congr_out (subspaceStep_of_circuit _ _) hCz) fun b ↦ ?_
  let b' := extendMask18 K b
  refine subspaceStep_congr_in (SubspaceStep.smul (((√(1 / 2)) ^ K : ℝ) : ℂ) ?_)
    (eq_smul_of_inv_mul (hDiagSq b') (hHeldCollapse b))
  have sTail : SubspaceStep (U_diag b' * (U_kickK * R_mid)) (U_diag b' * (U_kick18 * R_mid))
      dUnheldTail := by
    refine subspaceStep_congr_in
      (subspaceStep_congr_out (hTail (supportedOn_diag_ket _ _ (hU_ket b') hSuppMid)) ?_) ?_
    · rw [← Matrix.mul_assoc, comm_of_diag_ket U_kick18 (U_diag b') d18 _ hKick18_ket (hU_ket b'),
        Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, comm_of_diag_ket (U_diag b') U_kickK _ dK (hU_ket b') hKickK_ket,
        Matrix.mul_assoc]
  let W_b := (cHadWall rElec).eval.1 * U_diag b' * (cHadWall rElec).eval.1
  have hHH : (cHadWall rElec).eval.1 * (cHadWall rElec).eval.1 = 1 :=
    congrArg Subtype.val (cHadWall_eval_mul_self rElec)
  have sHad : SubspaceStep (Var := Var) (U_diag b' * (U_kick18 * R_mid)) (W_b * (T_set * R))
      (.circuit (cHadWall rElec)) := by
    refine subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ (cHadWall rElec)) ?_
    calc (cHadWall rElec).eval.1 * (U_diag b' * (U_kick18 * R_mid))
        = (cHadWall rElec).eval.1 *
            (U_diag b' * (((cHadWall rElec).eval.1 * (cHadWall rElec).eval.1) *
              (U_kick18 * R_mid))) := by rw [hHH, Matrix.one_mul]
      _ = W_b * ((cHadWall rElec).eval.1 * (U_kick18 * R_mid)) := by
            dsimp only [W_b]
            simp only [Matrix.mul_assoc]
      _ = W_b * (T_set * R) := by rw [hPreMeasEq]
  refine sTail.seq (subspaceStep_seq_measureXReset v rMeas sHad fun f ↦ ?_)
  have hcH := xResetKraus_comm_cHadWall rMeas rElec hME f
  have hCommWb : DynCircuitExt.xResetKraus rMeas f * W_b =
      W_b * DynCircuitExt.xResetKraus rMeas f := by
    dsimp only [W_b]
    calc DynCircuitExt.xResetKraus rMeas f *
            ((cHadWall rElec).eval.1 * U_diag b' * (cHadWall rElec).eval.1)
        = ((cHadWall rElec).eval.1 * DynCircuitExt.xResetKraus rMeas f) *
            (U_diag b' * (cHadWall rElec).eval.1) := by
            rw [← hcH]
            simp only [Matrix.mul_assoc]
      _ = (cHadWall rElec).eval.1 * ((U_diag b' * DynCircuitExt.xResetKraus rMeas f) *
            (cHadWall rElec).eval.1) := by
            rw [← hMeasCommDiag b' f]
            simp only [Matrix.mul_assoc]
      _ = ((cHadWall rElec).eval.1 * U_diag b' * (cHadWall rElec).eval.1) *
            DynCircuitExt.xResetKraus rMeas f := by
            rw [Matrix.mul_assoc (U_diag b'), hcH]
            simp only [Matrix.mul_assoc]
  have hMeasIn : DynCircuitExt.xResetKraus rMeas f * (W_b * (T_set * R)) =
      (((√(1 / 2)) ^ 18 : ℝ) : ℂ) • (W_b * (U_diag f * R)) := by
    rw [← Matrix.mul_assoc, hCommWb, Matrix.mul_assoc,
      eq_smul_of_inv_mul (hDiagSq f) (hMeasCollapse f), Matrix.mul_smul]
  refine subspaceStep_congr_in (SubspaceStep.smul (((√(1 / 2)) ^ 18 : ℝ) : ℂ) ?_) hMeasIn
  refine SubspaceStep.of_unit_smul_out (pauliFusedPhase18_unit b' f) ?_
  have hSuppHad : ∀ {X : QOp n}, SupportedOn Inv_post X →
      SupportedOn Inv_post ((cHadWall rElec).eval.1 * X) := fun hX ↦
    supportedOn_of_inFiber rElec (cHadWall rElec) hInv_post_ign
      (fun β ↦ inFiber_cHadWall rElec (InFiber.ket_mem β fun _ _ ↦ rfl)) hX
  have hSuppWb : SupportedOn Inv_post (W_b * (U_diag f * R)) := by
    have hEqWb : W_b * (U_diag f * R) =
        (cHadWall rElec).eval.1 * (U_diag b' * ((cHadWall rElec).eval.1 * (U_diag f * R))) := by
      dsimp only [W_b]
      simp only [Matrix.mul_assoc]
    rw [hEqWb]
    exact hSuppHad (supportedOn_diag_ket _ _ (hU_ket b')
      (hSuppHad (supportedOn_diag_ket _ _ (hU_ket f) hSuppR)))
  have hSuppFwd : SupportedOn Inv_post
      ((cPauliWallFwd b' f rElec).eval.1 * (W_b * (U_diag f * R))) :=
    supportedOn_of_inFiber rElec (cPauliWallFwd b' f rElec) hInv_post_ign
      (fun β ↦ inFiber_cPauliWallFwd_wall b' f rElec (InFiber.ket_mem β fun _ _ ↦ rfl)) hSuppWb
  refine subspaceStep_congr_out
    ((subspaceStep_of_circuit _ (cPauliWallFwd b' f rElec)).seq
      ((hFix (fun j ↦ b' j || f j) hSuppFwd).seq
        (subspaceStep_of_circuit _ (cPauliWallInv b' f rElec)))) ?_
  calc (cPauliWallInv b' f rElec).eval.1 *
          (U_diag (fun j ↦ b' j || f j) *
            ((cPauliWallFwd b' f rElec).eval.1 * (W_b * (U_diag f * R))))
      = ((cPauliWallInv b' f rElec).eval.1 * U_diag (fun j ↦ b' j || f j) *
          (cPauliWallFwd b' f rElec).eval.1 * (cHadWall rElec).eval.1 * U_diag b' *
          (cHadWall rElec).eval.1 * U_diag f) * R := by
          dsimp only [W_b]
          simp only [Matrix.mul_assoc]
    _ = pauliFusedPhase18 b' f • R := by
          rw [pauliWall_conj_hadWall_diag_eq_unit_smul rElec U_diag slotOf hSlot_ign hU_ket b' f,
            Matrix.smul_mul, Matrix.one_mul]
/-- Computational-basis `±1` phase function for a prefix of `k ≤ 18` `CZ` kicks between
active electron slot `slotOf (basisBits n g)` of `rElec` and `rMeas`. -/
def kickPrefixPhase {n N_slot : ℕ} (k : ℕ) (hk : k ≤ 18)
    (rElec : QRegister (N_slot * 18) n) (rMeas : QRegister 18 n)
    (slotOf : BitAssignment n → Fin N_slot) : PhaseFn n :=
  fun g ↦
    let β := basisBits n g
    let s₀ := slotOf β
    decide ((∑ j : Fin k,
      β (rElec (elecFlatIdx s₀ ⟨j.val, by omega⟩)) * β (rMeas ⟨j.val, by omega⟩)) = 1)

private theorem ket_eq_single {n : ℕ} (α : BitAssignment n) :
    ket α = (Pi.single ((basisBits n).symm α) 1 : Fin (QubitDim n) → ℂ) := by
  have h := DynCircuitExt.gsingle_eq_ket ((basisBits n).symm α)
  rw [(basisBits n).apply_symm_apply] at h
  exact h.symm

private theorem bool_zmod2_sign_eq (b : Bool) (z : ZMod 2) :
    (if (b && decide (z ≠ 0)) = true then (-1 : ℂ) else 1) =
      if b then bitSign z else 1 := by
  cases b <;> rcases bit_cases z with rfl | rfl <;> simp [bitSign]

private theorem bitSign_add (a b : ZMod 2) :
    bitSign (a + b) = bitSign a * bitSign b := by
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    simp only [bitSign, zero_add, add_zero, h11, one_ne_zero, ↓reduceIte] <;>
    norm_num

private theorem bitSign_sum {m : ℕ} (f : Fin m → ZMod 2) :
    bitSign (∑ i : Fin m, f i) = ∏ i : Fin m, bitSign (f i) := by
  induction m with
  | zero => simp [bitSign]
  | succ m ih => rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, bitSign_add, ih]

private theorem decide_eq_one_sign (z : ZMod 2) :
    (if decide (z = 1) = true then (-1 : ℂ) else 1) = bitSign z := by
  rcases bit_cases z with rfl | rfl <;> simp [bitSign]

private theorem diagSignUnitary_mulVec_single {n : ℕ} (phase : PhaseFn n) (g : Fin (QubitDim n)) :
    (diagSignUnitary phase).1.mulVec (Pi.single g 1) =
      (if phase g then (-1 : ℂ) else 1) • Pi.single g 1 := by
  funext x
  rw [Matrix.mulVec_single_one]
  dsimp only [diagSignUnitary]
  by_cases hxg : x = g
  · subst hxg
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hxg]

private theorem diagSignUnitary_kickPrefixPhase_ket {n N_slot : ℕ} (k : ℕ) (hk : k ≤ 18)
    (rElec : QRegister (N_slot * 18) n) (rMeas : QRegister 18 n)
    (slotOf : BitAssignment n → Fin N_slot) (α : BitAssignment n) :
    (diagSignUnitary (kickPrefixPhase k hk rElec rMeas slotOf)).1.mulVec (ket α) =
      (∏ j : Fin k,
        bitSign (α (rElec (elecFlatIdx (slotOf α) ⟨j.val, by omega⟩)) *
          α (rMeas ⟨j.val, by omega⟩))) • ket α := by
  rw [ket_eq_single α, diagSignUnitary_mulVec_single, ← ket_eq_single α]
  refine congrArg (· • ket α) ?_
  have hPh : kickPrefixPhase k hk rElec rMeas slotOf ((basisBits n).symm α) =
      decide ((∑ j : Fin k,
        α (rElec (elecFlatIdx (slotOf α) ⟨j.val, by omega⟩)) *
          α (rMeas ⟨j.val, by omega⟩)) = 1) :=
    congrArg (fun β : BitAssignment n ↦
      decide ((∑ j : Fin k,
        β (rElec (elecFlatIdx (slotOf β) ⟨j.val, by omega⟩)) *
          β (rMeas ⟨j.val, by omega⟩)) = 1))
      ((basisBits n).apply_symm_apply α)
  rw [hPh, decide_eq_one_sign, bitSign_sum]

private theorem prod_fin18_extendMask18 (K : ℕ) (hK : K ≤ 18) (b : Fin K → Bool)
    (g : Fin 18 → ℂ) :
    (∏ j : Fin 18, if extendMask18 K b j then g j else 1) =
      ∏ t : Fin K, if b t then g ⟨t.val, by omega⟩ else 1 := by
  let emb : Fin K ↪ Fin 18 := ⟨fun t ↦ ⟨t.val, by omega⟩, fun _ _ h ↦ by
    injection h with hv
    exact Fin.ext hv⟩
  rw [← Finset.prod_subset (Finset.subset_univ ((Finset.univ : Finset (Fin K)).map emb))]
  · rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun t _ ↦ ?_
    have h1 : extendMask18 K b (emb t) = b t := by
      dsimp only [extendMask18, emb]
      split_ifs with h
      · rfl
      · exact False.elim (h t.isLt)
    rw [h1]
    rfl
  · intro j _ hjNot
    by_cases hj : j.val < K
    · exfalso
      apply hjNot
      rw [Finset.mem_map]
      exact ⟨⟨j.val, hj⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · simp [extendMask18, hj]

/-- `𝔽₂` inner-product parity. -/
abbrev f2Parity (b : ℕ) (f : Fin b → Bool) (v : Fin (QubitDim b)) : Bool :=
  (List.finRange b).foldr (fun i acc ↦ xor (f i && decide (basisBits b v i ≠ 0)) acc) false

/-- Table-write operator. -/
noncomputable abbrev setTableOp {n k b : ℕ}
    (rData : QRegister k n) (rMeas : QRegister b n) (tbl : TblFn k b) : QOp n :=
  Matrix.of fun i h ↦ if i = rMeas.replaceIndex h (tbl (rData.extractIndex h)) then 1 else 0

private theorem embedUnitary_diagSignUnitary_mulVec_single {n k : ℕ}
    (r : QRegister k n) (phase : PhaseFn k) (g : Fin (QubitDim n)) :
    (r.embedUnitary (diagSignUnitary phase)).1.mulVec (Pi.single g 1) =
      (if phase (r.extractIndex g) then (-1 : ℂ) else 1) • Pi.single g 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change (r.embedMatrix (Matrix.diagonal fun z ↦ if phase z then (-1 : ℂ) else 1)) i g =
    ((if phase (r.extractIndex g) then (-1 : ℂ) else 1) •
      (Pi.single g (1 : ℂ) : Fin (QubitDim n) → ℂ)) i
  rw [QRegister.embedMatrix_apply]
  by_cases hig : i = g
  · subst hig
    simp [Matrix.diagonal]
  · simp only [Pi.smul_apply, Pi.single_eq_of_ne hig, smul_zero]
    by_cases henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv g).2
    · have hex : r.extractIndex i ≠ r.extractIndex g := fun heq ↦ hig <|
        r.basisSplitEquiv.injective
          (Prod.ext (by simpa [QRegister.basisSplitEquiv_apply_fst] using heq) henv)
      simp [henv, Matrix.diagonal, hex]
    · simp [henv]
private theorem xor_sign_eq (a b : Bool) :
    (if xor a b then (-1 : ℂ) else 1) =
      (if a then (-1 : ℂ) else 1) * (if b then (-1 : ℂ) else 1) := by
  cases a <;> cases b <;> norm_num

private theorem foldr_xor_sign_eq {α : Type*} (l : List α) (p : α → Bool) :
    (if l.foldr (fun i acc ↦ xor (p i) acc) false then (-1 : ℂ) else 1) =
      (l.map fun i ↦ if p i then (-1 : ℂ) else 1).prod := by
  induction l with
  | nil => simp
  | cons a tl ih => rw [List.foldr_cons, List.map_cons, List.prod_cons, xor_sign_eq, ih]

private theorem sign_f2Parity_eq_prod (b : ℕ) (f : Fin b → Bool) (v : Fin (QubitDim b)) :
    (if f2Parity b f v then (-1 : ℂ) else 1) =
      ∏ i : Fin b, if f i && decide (basisBits b v i ≠ 0) then (-1 : ℂ) else 1 := by
  unfold f2Parity
  rw [foldr_xor_sign_eq, Fin.prod_univ_def]

private theorem setTableOp_mulVec_single {n k b : ℕ}
    (rData : QRegister k n) (rMeas : QRegister b n) (tbl : TblFn k b) (h : Fin (QubitDim n)) :
    (setTableOp rData rMeas tbl).mulVec (Pi.single h 1) =
      Pi.single (rMeas.replaceIndex h (tbl (rData.extractIndex h))) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change setTableOp rData rMeas tbl i h =
    (Pi.single (rMeas.replaceIndex h (tbl (rData.extractIndex h))) (1 : ℂ) : Fin (QubitDim n) → ℂ) i
  unfold setTableOp
  rw [Matrix.of_apply]
  by_cases hi : i = rMeas.replaceIndex h (tbl (rData.extractIndex h))
  · subst hi
    simp
  · simp [hi]

private theorem matrix_eq_of_mulVec_single {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ g : Fin d, A.mulVec (Pi.single g 1) = B.mulVec (Pi.single g 1)) :
    A = B := by
  ext i g
  have hgi := congrFun (h g) i
  simp only [Matrix.mulVec_single_one] at hgi
  exact hgi

private theorem basisOutcomeProjector_zero_mulVec_single {n w : ℕ}
    (r : QRegister w n) (g : Fin (QubitDim n)) :
    (r.basisOutcomeProjector 0).mulVec (Pi.single g 1) =
      if r.extractIndex g = 0 then Pi.single g 1 else 0 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change (r.basisOutcomeProjector 0) i g =
    (if r.extractIndex g = 0 then (Pi.single g (1 : ℂ) : Fin (QubitDim n) → ℂ) else 0) i
  rw [QRegister.basisOutcomeProjector_eq_diagonal]
  by_cases hig : i = g
  · subst hig
    by_cases hz : r.extractIndex i = 0 <;> simp [Matrix.diagonal, hz]
  · by_cases hz : r.extractIndex g = 0 <;> simp [Matrix.diagonal, hig, hz]

private theorem replaceIndex_replaceIndex_zero {n b : ℕ}
    (rMeas : QRegister b n) (h : Fin (QubitDim n)) (v : Fin (QubitDim b))
    (hh0 : rMeas.extractIndex h = 0) :
    rMeas.replaceIndex (rMeas.replaceIndex h v) 0 = h := by
  apply rMeas.basisSplitEquiv.injective
  rw [rMeas.basisSplitEquiv_replaceIndex, rMeas.basisSplitEquiv_replaceIndex]
  exact Prod.ext (by simp [QRegister.basisSplitEquiv_apply_fst, hh0]) rfl

private theorem tableXReset_mul_setTableOp_mul_zeroMeas {n k b : ℕ}
    (rData : QRegister k n) (rMeas : QRegister b n) (tbl : TblFn k b) (f : Fin b → Bool) :
    (rData.embedUnitary (diagSignUnitary (fun x ↦ f2Parity b f (tbl x)))).1 *
      DynCircuitExt.xResetKraus rMeas f *
      setTableOp rData rMeas tbl *
      rMeas.basisOutcomeProjector 0 =
    (((√(1 / 2)) ^ b : ℝ) : ℂ) • rMeas.basisOutcomeProjector 0 := by
  apply matrix_eq_of_mulVec_single
  intro g
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    basisOutcomeProjector_zero_mulVec_single, Matrix.smul_mulVec,
    basisOutcomeProjector_zero_mulVec_single]
  by_cases hg0 : rMeas.extractIndex g = 0
  · simp only [hg0, ↓reduceIte]
    rw [setTableOp_mulVec_single]
    let g' := rMeas.replaceIndex g (tbl (rData.extractIndex g))
    change (rData.embedUnitary (diagSignUnitary (fun x ↦ f2Parity b f (tbl x)))).1.mulVec
      ((DynCircuitExt.xResetKraus rMeas f).mulVec (Pi.single g' 1)) = _
    rw [DynCircuitExt.xResetKraus_mulVec_single, rMeas.extractIndex_replaceIndex g _,
      replaceIndex_replaceIndex_zero rMeas g _ hg0, ← sign_f2Parity_eq_prod,
      Matrix.mulVec_smul, embedUnitary_diagSignUnitary_mulVec_single, smul_smul]
    refine congrArg₂ (· • ·) ?_ rfl
    cases f2Parity b f (tbl (rData.extractIndex g)) <;> simp
  · simp [hg0]

private noncomputable def uTblParity {n kData : ℕ}
    (rData : QRegister kData n) (tbl : TblFn kData 18) (m : Fin 18 → Bool) : QOp n :=
  (rData.embedUnitary (diagSignUnitary (fun d ↦ f2Parity 18 m (tbl d)))).1

private theorem uTblParity_mulVec_ket {n kData N_slot : ℕ}
    (rData : QRegister kData n) (rElec : QRegister (N_slot * 18) n)
    (slotOf : BitAssignment n → Fin N_slot) (tbl : TblFn kData 18)
    (hTbl_bits : ∀ (g : Fin (QubitDim n)) (j : Fin 18),
      basisBits 18 (tbl (rData.extractIndex g)) j =
        basisBits n g (rElec (elecFlatIdx (slotOf (basisBits n g)) j)))
    (m : Fin 18 → Bool) (α : BitAssignment n) :
    (uTblParity rData tbl m).mulVec (ket α) =
      (∏ j : Fin 18,
        if m j then bitSign (α (rElec (elecFlatIdx (slotOf α) j))) else 1) • ket α := by
  let g : Fin (QubitDim n) := (basisBits n).symm α
  have hg : basisBits n g = α := (basisBits n).apply_symm_apply α
  dsimp only [uTblParity]
  rw [ket_eq_single α, embedUnitary_diagSignUnitary_mulVec_single, sign_f2Parity_eq_prod,
    ← ket_eq_single α]
  refine congrArg (· • ket α) (Finset.prod_congr rfl fun j _ ↦ ?_)
  have hbit : basisBits 18 (tbl (rData.extractIndex g)) j =
      α (rElec (elecFlatIdx (slotOf α) j)) := by
    simpa only [hg] using hTbl_bits g j
  rw [hbit, bool_zmod2_sign_eq]

private theorem xResetKraus_comm_uTblParity {n kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister 18 n)
    (hDM : rData.DisjointWires rMeas) (tbl : TblFn kData 18) (m f : Fin 18 → Bool) :
    DynCircuitExt.xResetKraus rMeas f * uTblParity rData tbl m =
      uTblParity rData tbl m * DynCircuitExt.xResetKraus rMeas f :=
  xResetKraus_comm_of_wire_comm rMeas _ (fun q hq A ↦
    QRegister.embedMatrix_comm_of_disjoint q rData (by
      rw [QRegister.disjoint_iff]
      intro i d hd
      obtain ⟨j, hj⟩ := hq i
      exact hDM.ne d j (hj.trans hd).symm) A _) f

private theorem meas_xReset_setTableOp_collapse {n kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister 18 n) (tbl : TblFn kData 18)
    {R : QOp n} (hPm : rMeas.basisOutcomeProjector 0 * R = R) (f : Fin 18 → Bool) :
    uTblParity rData tbl f *
        (DynCircuitExt.xResetKraus rMeas f * (setTableOp rData rMeas tbl * R)) =
      (((√(1 / 2)) ^ 18 : ℝ) : ℂ) • R := by
  dsimp only [uTblParity]
  calc (rData.embedUnitary (diagSignUnitary (fun d ↦ f2Parity 18 f (tbl d)))).1 *
          (DynCircuitExt.xResetKraus rMeas f * (setTableOp rData rMeas tbl * R))
      = ((rData.embedUnitary (diagSignUnitary (fun d ↦ f2Parity 18 f (tbl d)))).1 *
          DynCircuitExt.xResetKraus rMeas f *
          setTableOp rData rMeas tbl *
          rMeas.basisOutcomeProjector 0) * R := by
          conv_lhs => rw [← hPm]
          simp only [Matrix.mul_assoc]
    _ = (((√(1 / 2)) ^ 18 : ℝ) : ℂ) • R := by
          rw [tableXReset_mul_setTableOp_mul_zeroMeas rData rMeas tbl f, Matrix.smul_mul, hPm]
private theorem cHeldCzPrefixAux_eval_mulVec_ket {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld) (α : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (cHeldCzPrefixAux K hK rMeas rHeld hMH k hk).eval.1.mulVec (ket α) =
        (∏ t : Fin k,
          bitSign (α (rHeld ⟨t.val, by omega⟩) * α (rMeas ⟨t.val, by omega⟩))) • ket α
  | 0, _ => by simp [cHeldCzPrefixAux]
  | k + 1, hk => by
      dsimp only [cHeldCzPrefixAux]
      rw [eval_seq_mulVec, cHeldCzPrefixAux_eval_mulVec_ket K hK rMeas rHeld hMH α k (by omega),
        Matrix.mulVec_smul]
      have hcz : (DynCircuitExt.czCircuit (rHeld ⟨k, hk⟩) (rMeas ⟨k, by omega⟩)
          (hMH.ne ⟨k, by omega⟩ ⟨k, hk⟩).symm).eval.1.mulVec (ket α) =
          bitSign (α (rHeld ⟨k, hk⟩) * α (rMeas ⟨k, by omega⟩)) • ket α :=
        DynCircuitExt.gket_czCircuit (rHeld ⟨k, hk⟩) (rMeas ⟨k, by omega⟩) _ α
      rw [hcz, smul_smul, Fin.prod_univ_castSucc]
      rfl

private theorem cHeldCzPrefixAux_mul_hold_eq {n N_slot : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rElec : QRegister (N_slot * 18) n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld)
    (slotOf : BitAssignment n → Fin N_slot)
    {Inv_mid : BitAssignment n → Prop}
    {U_hold U_kickK R_mid : QOp n}
    (hKickK_eq : U_kickK = (diagSignUnitary (kickPrefixPhase K hK rElec rMeas slotOf)).1)
    (hSuppMid : SupportedOn Inv_mid R_mid)
    (hHold_ket : ∀ β : BitAssignment n, Inv_mid β →
      ∃ α : BitAssignment n,
        U_hold.mulVec (ket β) = ket α ∧
        (∀ t : Fin K, β (rHeld t) = 0) ∧
        (∀ t : Fin K, α (rHeld t) = β (rElec (elecFlatIdx (slotOf β) ⟨t.val, by omega⟩))) ∧
        (∀ w : Wire n, w ∉ Set.range rHeld.wires → α w = β w)) :
    (cHeldCzPrefixAux K hK rMeas rHeld hMH K le_rfl).eval.1 * (U_hold * R_mid) =
      U_hold * (U_kickK * R_mid) := by
  subst hKickK_eq
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hSuppMid _ _ fun β hInv ↦ ?_
  obtain ⟨α, hHold, _, hHeld, hOut⟩ := hHold_ket β hInv
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHold,
    cHeldCzPrefixAux_eval_mulVec_ket K hK rMeas rHeld hMH α K le_rfl,
    diagSignUnitary_kickPrefixPhase_ket K hK rElec rMeas slotOf β,
    Matrix.mulVec_smul, hHold]
  refine congrArg (· • ket α) (Finset.prod_congr rfl fun t _ ↦ ?_)
  have hM_out : rMeas ⟨t.val, by omega⟩ ∉ Set.range rHeld.wires := fun ⟨s, hs⟩ ↦
    hMH.ne ⟨t.val, by omega⟩ s hs.symm
  have ht_eq : (⟨t.val, t.isLt⟩ : Fin K) = t := Fin.ext rfl
  rw [ht_eq, hHeld t, hOut _ hM_out]

private theorem held_xReset_collapse {n kData N_slot : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rData : QRegister kData n) (rElec : QRegister (N_slot * 18) n)
    (rHeld : QRegister K n)
    (slotOf : BitAssignment n → Fin N_slot) (tbl : TblFn kData 18)
    (hTbl_bits : ∀ (g : Fin (QubitDim n)) (j : Fin 18),
      basisBits 18 (tbl (rData.extractIndex g)) j =
        basisBits n g (rElec (elecFlatIdx (slotOf (basisBits n g)) j)))
    {Inv_mid : BitAssignment n → Prop}
    {U_hold U_kickK R_mid : QOp n}
    {dK : BitAssignment n → ℂ}
    (hKickK_ket : ∀ α : BitAssignment n, U_kickK.mulVec (ket α) = dK α • ket α)
    (hSuppMid : SupportedOn Inv_mid R_mid)
    (hHold_ket : ∀ β : BitAssignment n, Inv_mid β →
      ∃ α : BitAssignment n,
        U_hold.mulVec (ket β) = ket α ∧
        (∀ t : Fin K, β (rHeld t) = 0) ∧
        (∀ t : Fin K, α (rHeld t) = β (rElec (elecFlatIdx (slotOf β) ⟨t.val, by omega⟩))) ∧
        (∀ w : Wire n, w ∉ Set.range rHeld.wires → α w = β w))
    (b : Fin K → Bool) :
    uTblParity rData tbl (extendMask18 K b) *
      (DynCircuitExt.xResetKraus rHeld b * (U_hold * (U_kickK * R_mid))) =
      (((√(1 / 2)) ^ K : ℝ) : ℂ) • (U_kickK * R_mid) := by
  have hSuppKick : SupportedOn Inv_mid (U_kickK * R_mid) :=
    supportedOn_diag_ket U_kickK dK hKickK_ket hSuppMid
  have hEq := hSuppKick
    (uTblParity rData tbl (extendMask18 K b) * DynCircuitExt.xResetKraus rHeld b * U_hold)
    ((((√(1 / 2)) ^ K : ℝ) : ℂ) • (1 : QOp n))
    fun β hInv ↦ by
      obtain ⟨α, hHold, hZero, hHeld, hOut⟩ := hHold_ket β hInv
      let gα : Fin (QubitDim n) := (basisBits n).symm α
      have hgα : basisBits n gα = α := (basisBits n).apply_symm_apply α
      have hRepBits : basisBits n (rHeld.replaceIndex gα 0) = β := by
        funext w
        by_cases hw : w ∈ Set.range rHeld.wires
        · obtain ⟨t, rfl⟩ := hw
          rw [QRegister.basisBits_replaceIndex_apply, basisBits_zero, Pi.zero_apply,
            (hZero t).symm]
        · rw [QRegister.basisBits_replaceIndex_of_not_mem rHeld gα 0 w hw, hgα, hOut w hw]
      have hRepKet : (Pi.single (rHeld.replaceIndex gα 0) 1 : Fin (QubitDim n) → ℂ) = ket β := by
        have hs := DynCircuitExt.gsingle_eq_ket (rHeld.replaceIndex gα 0)
        rw [hRepBits] at hs
        exact hs
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHold,
        ket_eq_single α, DynCircuitExt.xResetKraus_mulVec_single K rHeld b gα,
        hRepKet, Matrix.mulVec_smul,
        uTblParity_mulVec_ket rData rElec slotOf tbl hTbl_bits (extendMask18 K b) β,
        prod_fin18_extendMask18 K hK b
          (fun j ↦ bitSign (β (rElec (elecFlatIdx (slotOf β) j)))),
        smul_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
      refine congrArg (· • ket β) ?_
      have hP1 : (∏ t : Fin K,
          if (b t && decide (basisBits K (rHeld.extractIndex gα) t ≠ 0)) = true
          then (-1 : ℂ) else 1) =
          ∏ t : Fin K,
            if b t then bitSign (β (rElec (elecFlatIdx (slotOf β) ⟨t.val, by omega⟩))) else 1 := by
        refine Finset.prod_congr rfl fun t _ ↦ ?_
        rw [QRegister.basisBits_extractIndex, hgα, hHeld t, bool_zmod2_sign_eq]
      rw [hP1, mul_assoc, ← Finset.prod_mul_distrib]
      have hSq : (∏ t : Fin K,
          (if b t then bitSign (β (rElec (elecFlatIdx (slotOf β) ⟨t.val, by omega⟩))) else 1) *
            (if b t then bitSign (β (rElec (elecFlatIdx (slotOf β) ⟨t.val, by omega⟩))) else 1)) =
          1 := by
        refine Finset.prod_eq_one fun t _ ↦ ?_
        cases b t <;> simp [bitSign_mul_self]
      rw [hSq, mul_one]
  rw [Matrix.smul_mul, Matrix.one_mul] at hEq
  simpa only [Matrix.mul_assoc] using hEq

/-- Quantum-slot `SubspaceStep` bridge for `dPostHoleHeld1wKQSlotFused` (`≤ 8,428 - 444*K`
`T`, `0 TOFF`), discharging `cHeldCzPrefixAux` ket action, `rHeld` `X`-measurement parity collapse,
`rMeas` disjointness commutation, and `tableXReset_mul_setTableOp_mul_zeroMeas` collapse while
splitting `Inv_mid` (`dUnheldTail`) from `Inv_post` (`dFix`). -/
theorem subspaceStep_dPostHoleHeld1wKQSlotFused {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData N_slot : ℕ} [NeZero (QubitDim n)]
    (K : ℕ) (hK : K ≤ 18) (v : Var)
    (rData : QRegister kData n) (rElec : QRegister (N_slot * 18) n)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hDM : rData.DisjointWires rMeas)
    (hME : rMeas.DisjointWires rElec)
    (hMH : rMeas.DisjointWires rHeld)
    (slotOf : BitAssignment n → Fin N_slot)
    (tbl : TblFn kData 18)
    {dUnheldTail : DynamicCircuit Var n}
    {dFix : (Fin 18 → Bool) → DynamicCircuit Var n}
    {Inv_mid Inv_post : BitAssignment n → Prop}
    {U_hold U_kickK U_kick18 R_mid R : QOp n}
    (hInv_post_ign : ∀ α β : BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range rElec.wires → α w = β w) → (Inv_post α ↔ Inv_post β))
    (hSlot_ign : ∀ α β : BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range rElec.wires → α w = β w) → slotOf α = slotOf β)
    (hTbl_bits : ∀ (g : Fin (QubitDim n)) (j : Fin 18),
      basisBits 18 (tbl (rData.extractIndex g)) j =
        basisBits n g (rElec (elecFlatIdx (slotOf (basisBits n g)) j)))
    (hKickK_eq : U_kickK = (diagSignUnitary (kickPrefixPhase K hK rElec rMeas slotOf)).1)
    (hKick18_eq : U_kick18 = (diagSignUnitary (kickPrefixPhase 18 le_rfl rElec rMeas slotOf)).1)
    (hHold_ket : ∀ β : BitAssignment n, Inv_mid β →
      ∃ α : BitAssignment n,
        U_hold.mulVec (ket β) = ket α ∧
        (∀ t : Fin K, β (rHeld t) = 0) ∧
        (∀ t : Fin K, α (rHeld t) = β (rElec (elecFlatIdx (slotOf β) ⟨t.val, by omega⟩))) ∧
        (∀ w : Wire n, w ∉ Set.range rHeld.wires → α w = β w))
    (hSuppMid : SupportedOn Inv_mid R_mid)
    (hSuppR : SupportedOn Inv_post R)
    (hPm : rMeas.basisOutcomeProjector 0 * R = R)
    (hTail : ∀ {R₀ : QOp n}, SupportedOn Inv_mid R₀ →
      SubspaceStep (U_kickK * R₀) (U_kick18 * R₀) dUnheldTail)
    (hPreMeasEq : (cHadWall rElec).eval.1 * (U_kick18 * R_mid) = setTableOp rData rMeas tbl * R)
    (hFix : ∀ (m : Fin 18 → Bool) {R₀ : QOp n}, SupportedOn Inv_post R₀ →
      SubspaceStep R₀
        ((rData.embedUnitary (diagSignUnitary (fun d ↦ f2Parity 18 m (tbl d)))).1 * R₀)
        (dFix m)) :
    SubspaceStep (U_hold * R_mid) R
      (dPostHoleHeld1wKQSlotFused K hK v rElec rMeas rHeld hMH dUnheldTail dFix) := by
  have hKickK_ket : ∀ α : BitAssignment n,
      U_kickK.mulVec (ket α) =
        (∏ j : Fin K,
          bitSign (α (rElec (elecFlatIdx (slotOf α) ⟨j.val, by omega⟩)) *
            α (rMeas ⟨j.val, by omega⟩))) • ket α := by
    rw [hKickK_eq]
    exact diagSignUnitary_kickPrefixPhase_ket K hK rElec rMeas slotOf
  have hKick18_ket : ∀ α : BitAssignment n,
      U_kick18.mulVec (ket α) =
        (∏ j : Fin 18,
          bitSign (α (rElec (elecFlatIdx (slotOf α) ⟨j.val, by omega⟩)) *
            α (rMeas ⟨j.val, by omega⟩))) • ket α := by
    rw [hKick18_eq]
    exact diagSignUnitary_kickPrefixPhase_ket 18 le_rfl rElec rMeas slotOf
  exact subspaceStep_dPostHoleHeld1wKFused_split K hK v rElec rMeas rHeld hME hMH
    hInv_post_ign hSlot_ign
    (uTblParity_mulVec_ket rData rElec slotOf tbl hTbl_bits)
    hKickK_ket hKick18_ket hSuppMid hSuppR
    (cHeldCzPrefixAux_mul_hold_eq K hK rElec rMeas rHeld hMH slotOf hKickK_eq hSuppMid hHold_ket)
    (held_xReset_collapse K hK rData rElec rHeld slotOf tbl hTbl_bits hKickK_ket hSuppMid hHold_ket)
    hTail hPreMeasEq
    (xResetKraus_comm_uTblParity rData rMeas hDM tbl)
    (meas_xReset_setTableOp_collapse rData rMeas tbl hPm)
    hFix

end StageBOneWireFusedCaller47493
end QuantumComputation.Specs.StoppingPowerSolution
end
