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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GridGuard654Refl

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section CleanAncillaCombinators
local instance (priority := 1000000) instNeZeroTwoPow_CleanAncillaCombinators (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Clean-Ancilla and Dynamic-Circuit Combinators

General, algorithm-independent combinators for `CleanAncilla` assertion restrictions, concatenated
clean-ancilla registers, `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace`, and
`DynamicCircuit` sequencing and register placement.
-/

public section

open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

/-! ## DynamicCircuit Sequencing and Register Placement -/

namespace DynCircuitExt
open _root_.DynamicCircuit

variable {Var : Type} {n k a : ℕ}

/-- Execute a list of dynamic circuits from left to right. -/
def sequence : List (DynamicCircuit Var n) → DynamicCircuit Var n
  | [] => .identity
  | p :: ps => .seq p (sequence ps)

@[simp] theorem sequence_nil : sequence ([] : List (DynamicCircuit Var n)) = .identity := rfl

@[simp] theorem sequence_cons (p : DynamicCircuit Var n) (ps : List (DynamicCircuit Var n)) :
    sequence (p :: ps) = .seq p (sequence ps) := rfl

@[simp] theorem support_sequence (ps : List (DynamicCircuit Var n)) :
    (sequence ps).support = (ps.map support).foldr (· ∪ ·) ∅ := by
  induction ps <;> simp_all

@[simp] theorem count_sequence (g : PrimitiveGate a) (ps : List (DynamicCircuit Var n)) :
    (sequence ps).count g = (ps.map (count g)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

/-- Weakest precondition of a compiled sequence of dynamic circuits folds `wp p.compile` from
right to left over the list. -/
@[simp] theorem wp_sequence_compile [DecidableEq Var] [NeZero (2 ^ n)]
    (ps : List (DynamicCircuit Var n)) (Θ : CQAssertionCompat Var (2 ^ n)) :
    wp (sequence ps).compile Θ = ps.foldr (fun p acc ↦ wp p.compile acc) Θ := by
  induction ps with
  | nil =>
      funext σ
      simp [sequence]
  | cons p ps ih =>
      simp only [sequence_cons, compile_seq, wp_qSeq, List.foldr_cons, ih]

/-- Relocating a `k`-wire dynamic circuit onto an `n`-wire register preserves every worst-case
primitive gate count. -/
@[simp] theorem count_onRegister (g : PrimitiveGate a) (placement : QRegister k n)
    (p : DynamicCircuit Var k) : (DynCircuitExt.onRegister placement p).count g = p.count g := by
  induction p with
  | circuit c => simp
  | measure v r => rfl
  | qIf cond t f iht ihf =>
      dsimp only [onRegister, DynamicCircuit.count] at *
      rw [iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Relocating a dynamic circuit mentions only wires selected by its placement register. -/
theorem support_onRegister_subset (placement : QRegister k n) (p : DynamicCircuit Var k) :
    (DynCircuitExt.onRegister placement p).support ⊆ placement.image := by
  induction p with
  | circuit c => exact Circuit.support_onRegister_subset placement c
  | measure v r => exact QRegister.image_compose_subset placement r
  | qIf cond t f iht ihf => exact Finset.union_subset iht ihf
  | seq p₁ p₂ ih₁ ih₂ => exact Finset.union_subset ih₁ ih₂

end DynCircuitExt
end
end CleanAncillaCombinators

section CleanAncillaDynamicSeq
local instance (priority := 1000000) instNeZeroTwoPow_CleanAncillaDynamicSeq (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Store-Closed Clean-Ancilla Dynamic Circuit Composition

General, algorithm-independent QHL combinators for composing `DynamicCircuit` subroutines that
realize register-embedded unitaries using clean workspace ancillas (such as Gidney temporary-AND
compute/measurement-uncompute pairs and measurement-uncomputed QROM lookups) across arbitrary
sequential chains (`seq`, `sequenceList`, `List.replicate`, and conjugation sandwiches
`V⁻¹ * W ^ R * V`), plus zero-`NoTouch` semantic register-widening combinators (`widenWorkspace`
and `widenActive`) and direct lifting into `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace`.
-/

public section

open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

namespace DynCircuitExt
open _root_.DynamicCircuit

variable {Var : Type} {n k m a : ℕ}

section CleanWorkspaceComposition

variable [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]

/-- Bridge directly from `RealizesEmbeddedUnitaryWithCleanWorkspace` on `(rSys ++ rActAnc)` +
clean pool `rWork` (`rAnc = rActAnc ++ rWork`) to the specification predicate
`RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys outcomes rAnc hSysAnc`. -/
theorem
    RealizesEmbeddedUnitaryWithCleanWorkspace.toRealizesUnitaryFromBasisOutcomesAndZeroWorkspace
    {kSys mAct mWork : ℕ} (rSys : QRegister kSys n) (outcomes : Finset (Fin (2 ^ kSys)))
    (rActAnc : QRegister mAct n) (rWork : QRegister mWork n)
    (hSysAct : rSys.DisjointWires rActAnc) (hSubWork : rActAnc.DisjointWires rWork)
    (hSysAnc : rSys.DisjointWires (rActAnc.concat rWork hSubWork))
    {u : Unitary (2 ^ (kSys + mAct))} {d : DynamicCircuit Var n}
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace (rSys.concat rActAnc hSysAct) rWork u d) :
    let rAnc := rActAnc.concat rWork hSubWork
    let locAct : QRegister (kSys + mAct) (kSys + (mAct + mWork)) :=
      QRegister.block 0 (kSys + mAct) (by omega)
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace
      rSys outcomes rAnc hSysAnc (locAct.embedUnitary u) d.compile := by
  intro rAnc locAct M
  obtain ⟨M', hwp, hproj⟩ := hd M
  intro σ
  apply le_of_eq
  ext1
  ext1
  have hCommOut (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
      rAnc.basisOutcomeProjector 0 *
        (rSys.basisOutcomesProjector outcomes * A * rSys.basisOutcomesProjector outcomes) *
        rAnc.basisOutcomeProjector 0 =
      rSys.basisOutcomesProjector outcomes *
        (rAnc.basisOutcomeProjector 0 * A * rAnc.basisOutcomeProjector 0) *
        rSys.basisOutcomesProjector outcomes := by
    have hc : rAnc.basisOutcomeProjector 0 * rSys.basisOutcomesProjector outcomes =
        rSys.basisOutcomesProjector outcomes * rAnc.basisOutcomeProjector 0 := by
      rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomesProjector,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
    exact (by simp only [Matrix.mul_assoc] :
        rAnc.basisOutcomeProjector 0 *
          (rSys.basisOutcomesProjector outcomes * A * rSys.basisOutcomesProjector outcomes) *
          rAnc.basisOutcomeProjector 0 =
        (rAnc.basisOutcomeProjector 0 * rSys.basisOutcomesProjector outcomes) * A *
          (rSys.basisOutcomesProjector outcomes * rAnc.basisOutcomeProjector 0)).trans
      ((congrArg₂ (fun X Y ↦ X * A * Y) hc hc.symm).trans (by simp only [Matrix.mul_assoc]))
  have hZeroBits {ℓ : ℕ} (x : Fin (2 ^ ℓ)) : x = 0 ↔ ∀ t : Fin ℓ, basisBits ℓ x t = 0 := by
    rw [← (basisBitsEquiv ℓ).apply_eq_iff_eq, funext_iff]
    simp only [basisBits_eq_div_mod, Fin.val_zero, Nat.zero_div, Nat.zero_mod, Nat.cast_zero]
  have hAncSplit : rAnc.basisOutcomeProjector 0 =
      rActAnc.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 := by
    simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
    have hiff : rAnc.extractIndex g = 0 ↔
        rActAnc.extractIndex g = 0 ∧ rWork.extractIndex g = 0 := by
      simp only [hZeroBits, QRegister.basisBits_extractIndex]
      exact ⟨fun h ↦
          ⟨fun i ↦ by simpa only [rAnc, QRegister.concat_apply_left] using h (Fin.castAdd mWork i),
           fun j ↦ by simpa only [rAnc, QRegister.concat_apply_right] using h (Fin.natAdd mAct j)⟩,
        fun ⟨h1, h2⟩ ↦ Fin.addCases
          (fun i ↦ by simpa only [rAnc, QRegister.concat_apply_left] using h1 i)
          (fun j ↦ by simpa only [rAnc, QRegister.concat_apply_right] using h2 j)⟩
    by_cases h1 : rActAnc.extractIndex g = 0
    · by_cases h2 : rWork.extractIndex g = 0
      · simp [hiff, h1, h2]
      · simp [hiff, h1, h2]
    · simp [hiff, h1]
  have hRegEq : (rSys.concat rAnc hSysAnc).compose locAct = rSys.concat rActAnc hSysAct := by
    ext idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp [QRegister.compose, show locAct (Fin.castAdd mAct i) = Fin.castAdd (mAct + mWork) i by
        ext
        simp [locAct]]
    · simp [QRegister.compose, rAnc, show locAct (Fin.natAdd kSys j) =
        Fin.natAdd kSys (Fin.castAdd mWork j) by
        ext
        simp [locAct]]
  have hRestrOut (B : CQAssertionCompat Var (2 ^ n)) (r : QRegister kSys n)
      (outs : Finset (Fin (2 ^ kSys))) (st : Store Var) :
      (CQAssertion.restrictToBasisOutcomes B r outs st).1 =
        (B st).1.conj (r.basisOutcomesProjector outs) := rfl
  have hWpQ : (wpQAssignCompat ((rSys.concat rAnc hSysAnc).embedUnitary (locAct.embedUnitary
      u)) (fun _ ↦ M) σ).1.1 = ((rSys.concat rActAnc hSysAct).embedUnitary u).1ᴴ * M.1.1 *
      ((rSys.concat rActAnc hSysAct).embedUnitary u).1 := by
    rw [← QRegister.embedUnitary_compose, hRegEq]
    simp [wpQAssignCompat, qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hAssoc (B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
      (rActAnc.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) * B *
          (rActAnc.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) =
        rActAnc.basisOutcomeProjector 0 *
          (rWork.basisOutcomeProjector 0 * B * rWork.basisOutcomeProjector 0) *
          rActAnc.basisOutcomeProjector 0 := by
    have hc : rActAnc.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 =
        rWork.basisOutcomeProjector 0 * rActAnc.basisOutcomeProjector 0 := by
      simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
      exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
    exact (congrArg (((rActAnc.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) * B) * ·)
      hc).trans (by simp only [Matrix.mul_assoc])
  simp only [CQAssertion.restrictToZeroAncilla_coe, hRestrOut, HermitianMat.conj_apply_mat,
    QRegister.basisOutcomeProjector_conjTranspose, QRegister.basisOutcomesProjector_conjTranspose,
    hwp]
  rw [hCommOut, hCommOut, hAncSplit, hAssoc, hAssoc]
  change rSys.basisOutcomesProjector outcomes * (rActAnc.basisOutcomeProjector 0 *
    (rWork.basisOutcomeProjector 0 * (wpQAssignCompat ((rSys.concat rAnc hSysAnc).embedUnitary
    (locAct.embedUnitary u)) (fun _ ↦ M) σ).1.1 * rWork.basisOutcomeProjector 0) *
    rActAnc.basisOutcomeProjector 0) * rSys.basisOutcomesProjector outcomes =
    rSys.basisOutcomesProjector outcomes * (rActAnc.basisOutcomeProjector 0 *
    (rWork.basisOutcomeProjector 0 * M'.1.1 * rWork.basisOutcomeProjector 0) *
    rActAnc.basisOutcomeProjector 0) * rSys.basisOutcomesProjector outcomes
  rw [hWpQ, ← hproj]

/-- `R`-fold iteration `Nat.repeat (.seq d) R .identity` realizes `u ^ R` with clean workspace. -/
theorem RealizesEmbeddedUnitaryWithCleanWorkspace.repeatSeqIdentity {rAct : QRegister k n}
    {rWork : QRegister m n} (hdisj : rAct.DisjointWires rWork) {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d)
    (R : ℕ) : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (u ^ R)
      (Nat.repeat (.seq d) R .identity) := by
  induction R with
  | zero =>
      simpa [Nat.repeat] using
        realizesEmbeddedUnitaryWithCleanWorkspace_identity (Var := Var) rAct rWork
  | succ R ih => simpa only [Nat.repeat, pow_succ] using hd.seq hdisj ih

end CleanWorkspaceComposition

end DynCircuitExt
end
end CleanAncillaDynamicSeq

section InPlaceFullAddSlice
local instance (priority := 1000000) instNeZeroTwoPow_InPlaceFullAddSlice (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# 1-Wire In-Place Gidney Full Adder & Clean-Workspace Temporary-AND Phase Engine
(`InPlaceFullAddSlice`)

Zero-`.TOFF` clean-workspace `TempPhaseProg` combinators built on core `QuantumComputation`, proving
`ScopedBlock.withInPlaceFullAdd_block`
(`1` clean carry wire, `0` sum wires, `countTempAnd = 1 = 4 T`, `0` uncompute `T`).
-/

public section

open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

namespace InPlaceFullAddSlice

section BasisKetAndProjectors

variable {n : ℕ}

@[local simp] private theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β

@[local simp] private theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j := (basisBitsEquiv q).symm_apply_apply j

private noncomputable def writeReg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))

@[local simp] private theorem writeReg_apply_reg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

end BasisKetAndProjectors

@[local simp] private lemma zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

namespace CliffProg

theorem inv_supportsBelow {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound → c.inv.SupportsBelow bound
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => ⟨inv_supportsBelow c₂ h₂, inv_supportsBelow c₁ h₁⟩

end CliffProg

namespace TempPhaseProg

def x {m : ℕ} (q : Wire m) : TempPhaseProg m := .cliff (.x q)
end TempPhaseProg

theorem ScopedBlock.cast_rem {M rem₁ rem₂ : ℕ} (h : rem₁ = rem₂)
    {s : BitAssignment M → BitAssignment M} {leaf p : TempPhaseProg M}
    (hb : ScopedBlock M rem₁ s leaf p) : ScopedBlock M rem₂ s leaf p := h ▸ hb

/-- Base `ScopedBlock` for a `.z` phase kick on wire `q`. -/
theorem ScopedBlock.z_kick {M rem : ℕ} (q : Wire M) :
    ScopedBlock M rem id (.z q) (.z q) where
  valid := trivial
  bits _ _ := rfl
  sign _ _ := rfl

end InPlaceFullAddSlice
end
end InPlaceFullAddSlice

section MeasureBranchHadamardSem
local instance (priority := 1000000) instNeZeroTwoPow_MeasureBranchHadamardSem (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Compositional Clean-Workspace QHL Semantics & `[irreducible]` Hadamard Syndrome Uncomputation

Reusable, algorithm-independent QHL semantics and gate/support bounds for streaming syndrome
accumulation and single-variable sequential Hadamard measurement uncomputation:

1. **Basis-ket & Clean-Projector Algebra (`ket`, `projZeroAll`)**:
   Public `ket β` extensionality (`matrix_ext_ket`), multi-wire clean `|0⋯0⟩` projector
   `projZeroAll k scr`, register-projector equivalence
   (`projZeroAll_eq_basisOutcomeProjector_zero`),
   concatenation (`projZeroAll_append`), automatic diagonal commutativity, Hermiticity,
   idempotence,
   and `Circuit.TOFF` commutativity for disjoint scratch wires.
2. **Compositional Clean-Workspace Unitary Equivalence (`RealizesCleanUnitary`)**:
   Closes clean-ancilla dynamic circuits under `.identity`, `.circuit`, `.seq` (preserving clean
   workspace), workspace sub-projector lifting (`mono_proj`), unitary congruence on clean subspace
   (`congr_unitary`), and 4-`T` `DynamicCircuit.withTempAnd` brackets (`withTempAnd_projZeroAll`).
3. **Single-Variable `[irreducible]` Sequential Measurement (`measureAndBranchSeq`)**:
   Sequentially measures `m` wires reusing a single classical variable `(v : Var)`, proves `O(m)`
   symbolic `.T`/`.TOFF` gate and wire-support bounds, proves branching clean-workspace Kraus
   summation (`wp_measureAndBranchSeq_dynamic`), and locks `measureAndBranchSeq` `[irreducible]` so
   downstream Lean kernel `whnf` / `isDefEq` runs in `O(1)` time regardless of `m`.
4. **End-to-End `m`-Wire Hadamard + `X`-Reset + Phase-Fixup Uncomputation
   (`RealizesCleanUnitary.streamingSyndromeUncompute`)**:
   Proves in full `2 ^ n` matrix generality that applying `hadamardAll m qs`, measuring all `m`
   syndrome wires into `v`, resetting measured `|1⟩` outcomes to `|0⟩` via `0`-`T` `xReset m qs g`,
   and applying diagonal phase fixup `fixupPhase g` restores all `m` syndrome wires + scratch wires
   to `|0⟩` and realizes the exact target clean unitary `U_target`.
5. **Bidirectional Bridge
   (`toRealizesEmbeddedUnitaryWithCleanWorkspace` /
   `ofRealizesEmbeddedUnitaryWithCleanWorkspace`)**:
   Equates `RealizesCleanUnitary` with `DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace`
   for `[Unique Var]` (e.g. `Var = Unit`) with zero adapter boilerplate.
-/

public section

open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

namespace MeasureBranchHadamardSem

/-! ## Section 1: Public Computational-Basis Ket & Multi-Wire Clean-Projector Helpers -/

/-! ## Section 3: `[irreducible]` Single-Variable Sequential Measurement & Dynamic Kraus Sum -/

section SequentialMeasurement

attribute [local semireducible] measureAndBranchSeq
/-- Symbolic `O(m)` wire-support inclusion for `measureAndBranchSeq`. -/
theorem measureAndBranchSeq_support_subset {Var : Type} {n : ℕ} (v : Var)
    (S : Finset (Wire n)) :
    ∀ (m : ℕ) (qs : Fin m → QRegister 1 n) (k : (Fin m → Bool) → DynamicCircuit Var n),
      (∀ i, (qs i).image ⊆ S) →
      (∀ outcome, (k outcome).support ⊆ S) →
      (measureAndBranchSeq v m qs k).support ⊆ S
  | 0, _, k, _, hk => hk Fin.elim0
  | m + 1, qs, k, hqs, hk => by
      simp only [measureAndBranchSeq, support_seq, support_measure, support_qIf,
        Finset.union_subset_iff]
      exact ⟨hqs 0,
        measureAndBranchSeq_support_subset v S m _ _ (fun i => hqs i.succ) (fun _ => hk _),
        measureAndBranchSeq_support_subset v S m _ _ (fun i => hqs i.succ) (fun _ => hk _)⟩

attribute [local irreducible] measureAndBranchSeq
end SequentialMeasurement

end MeasureBranchHadamardSem
end
end MeasureBranchHadamardSem

section OctahedralOrbitUnfold
local instance (priority := 1000000) instNeZeroTwoPow_OctahedralOrbitUnfold (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Octahedral Orbit $S_3 \ltimes (\mathbb{Z}_2)^3$ Unfolding and Clean-Ancilla Toffoli Lowering

Implements the reversible 48-element octahedral group ($O_h = S_3 \ltimes (\mathbb{Z}_2)^3$)
coordinate permutation and `nz`-guarded sign unfolding network, together
with a clean-ancilla `DynamicCircuit.substToffoliCircuit` pass lowering any `Circuit` not touching
a reusable clean ancilla wire `wAnc` to `DynamicCircuit.jonesToffoli` (`count .TOFF = 0`).

## Main Declarations
1. **Canonical 3D Octahedral Orbits & 68-Bit Alias Words**:
   - `orbitCount5983`, `orbitLambda4`, `orbitBlockCount1496`, `orbitWordWidth68`,
     `orbitStagingWidth272`, `IsCanonicalOrbit32`, `packOrbitCoord15`, `packOrbitAliasWord68`.
2. **Mathematical $O_h = S_3 \ltimes (\mathbb{Z}_2)^3$ Bijection & Stabilizer Guard**:
   - `s3PermFwd`, `s3PermRev`, `s3PermFwd_sum_sq_eq`, `s3PermFwd_bijective_for_all_params`,
     `octSignGuarded`, `octSignGuarded_eq_zero_of_mag_zero`, `octSignGuarded_val_mag_ne_neg_zero`
     (zero negative-zero `(1, 0)` violations under `StoppingPower.IsGridState`).
3. **Whole-Circuit `jonesToffoli` Lowering (`substToffoliCircuit`)**:
   - `DynamicCircuit.substToffoliCircuit`, `count_substToffoliCircuit_toff` (`= 0`),
     `count_substToffoliCircuit_t` (`= c.count .T + 4 * c.count .TOFF`),
     `restrictToZeroAncilla_wp_substToffoliCircuit_of_update_eq`
     (with zero leading `.measure`).
4. **Executable `Circuit` & `DynamicCircuit` (`TOFF = 0`) Unfolding Network**:
   - `cswapBitCircuit`, `cswapRegCircuit`, `octahedralS3SwapCircuit`,
     `octahedralSignGuardedCircuit`, `octahedralOrbitUnfold6GuardedCircuit`, and their
     `DynamicCircuit` lowerings (`octahedralOrbitUnfold6GuardedDyn`: `0` `TOFF` gates, `84` `T`
     gates = `21` Toffoli-equivalents).
-/

public section

open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-! ## Section 3: Whole-Circuit Clean-Ancilla `jonesToffoli` Lowering (`substToffoliCircuit`) -/

namespace DynCircuitExt
open _root_.DynamicCircuit

variable {Var : Type} {n : ℕ}

/-- Replace every `.gate .toffoli r` in a `Circuit n` (whose support avoids `wAnc`) with Cody
Jones' 4-`T` `jonesToffoli` on reusable clean ancilla wire `wAnc`. -/
def substToffoliCircuit (v : Var) (wAnc : Wire n) :
    (c : Circuit n) → (wAnc ∉ c.support) → DynamicCircuit Var n
  | .identity, _ => .identity
  | .gate .toffoli r, hc =>
      have h01 : r 0 ≠ r 1 := fun h ↦ absurd (r.wires.injective h) (by decide)
      have h0a : r 0 ≠ wAnc := fun h ↦ hc ((QRegister.mem_image r wAnc).mpr ⟨0, h⟩)
      have h1a : r 1 ≠ wAnc := fun h ↦ hc ((QRegister.mem_image r wAnc).mpr ⟨1, h⟩)
      have h2a : r 2 ≠ wAnc := fun h ↦ hc ((QRegister.mem_image r wAnc).mpr ⟨2, h⟩)
      jonesToffoli v (r 0) (r 1) (r 2) wAnc h01 h0a h1a h2a
  | .gate .x r, _ => .circuit (.gate .x r)
  | .gate .y r, _ => .circuit (.gate .y r)
  | .gate .z r, _ => .circuit (.gate .z r)
  | .gate .h r, _ => .circuit (.gate .h r)
  | .gate .s r, _ => .circuit (.gate .s r)
  | .gate .t r, _ => .circuit (.gate .t r)
  | .gate .cnot r, _ => .circuit (.gate .cnot r)
  | .gate .swap r, _ => .circuit (.gate .swap r)
  | .seq c₁ c₂, hc =>
      .seq
        (substToffoliCircuit v wAnc c₁ (fun h ↦ hc (Finset.mem_union_left _ h)))
        (substToffoliCircuit v wAnc c₂ (fun h ↦ hc (Finset.mem_union_right _ h)))

/-- `substToffoliCircuit` eliminates all primitive `TOFF` gates (`count .TOFF = 0`). -/
@[simp] theorem count_substToffoliCircuit_toff (v : Var) (wAnc : Wire n)
    (c : Circuit n) (hc : wAnc ∉ c.support) :
    (substToffoliCircuit v wAnc c hc).count PrimitiveGate.TOFF = 0 := by
  induction c with
  | identity => rfl
  | gate g r =>
      cases g <;> simp [substToffoliCircuit]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only[substToffoliCircuit, count, ih₁ (fun h ↦ hc (Finset.mem_union_left _ h)),
          ih₂ (fun h ↦ hc (Finset.mem_union_right _ h)), add_zero]

/-- `substToffoliCircuit` uses `c.count .T + 4 * c.count .TOFF` `T` gates. -/
@[simp] theorem count_substToffoliCircuit_t (v : Var) (wAnc : Wire n) (c : Circuit n)
    (hc : wAnc ∉ c.support) : (substToffoliCircuit v wAnc c hc).count PrimitiveGate.T =
    c.count PrimitiveGate.T + 4 * c.count PrimitiveGate.TOFF := by
  induction c with
  | identity => rfl
  | gate g r =>
      cases g <;> simp [substToffoliCircuit]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [substToffoliCircuit, count, Circuit.count_seq,
        ih₁ (fun h ↦ hc (Finset.mem_union_left _ h)),
        ih₂ (fun h ↦ hc (Finset.mem_union_right _ h))]
      omega

end DynCircuitExt

/-! ## Section 4: Executable `Circuit` & `DynamicCircuit` (`TOFF = 0`) Octahedral Unfolding -/

end
end OctahedralOrbitUnfold

section Dyadic128CoulombMath
local instance (priority := 1000000) instNeZeroTwoPow_Dyadic128CoulombMath (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Exact $128^3$ Dyadic Coulomb Kernel, $O_h$ Orbit Bijection & Integer-Shell Split

Mathematical core for the dyadic octahedral Coulomb kernel:
1. Modular negation `negMod128`, folded magnitude `foldMag128 : Fin 128 → Fin 65`, sorting
   canonicalizer `canonTriple128`, and completely **computable** tetrahedral rank equivalence
   `tetRank65 : CanonicalTriple65 ≃ Fin 47905` mapping `(0, 0, 0) ↔ 0` via the exact polynomial
   `w * (w + 1) * (w + 2) / 6 + v * (v + 1) / 2 + u`.
2. $\mathbb{Z}_{128}^3$ character orthogonality `sum_char128Vec_eq` on `[-127, 127]^3`, real dual
   Coulomb kernel `w128Dual : FineCoord128 → ℝ` matching `StoppingPower.coulombKernel` on
   `[-62, 62]^3 \ {0}` (`sum_w128Dual_mul_char128Vec`), on-site self-interaction constant
   `w128Zero := w128Dual 0`, and exact 48-element $O_h = S_3 \ltimes (\mathbb{Z}_2)^3$ invariance
   `w128Dual_eq_orbit` (plus $O_h$-invariance of sub-grid parity Hamming weight
   `subGridWeight128_eq_orbit`).
3. Exact 48-element $O_h$ group action orbit-stabilizer bridge
   `sum_allOrbits_octAction128_eq_sum_fineCoord128` connecting `octahedralAction7Dyn` directly to
   sums over all `2,097,152` elements of `FineCoord128` (including `0` and Nyquist `64` with zero
   stabilizer guards!).
4. Interleaved dyadic coordinates `fineCoord128 : SubGridParity128 → SubGridCoord64 →
   FineCoord128`,
   exact coarse target site characterization `subMod128_fineCoord128_eq` (with carry
   `b₀ w && subGridParity128 d w`, reducing at `d = 0` to co-located `y₂ = y₁`), and decidable
   integer-shell head/tail splits (`kHead128` / `kTail128` and `Fin 4`-class `kHead128ByWeight` /
   `kTail128ByWeight`) summing unconditionally to `w128Dual d` (`39` orbits at `R_sq = 34`, `40`
   orbits at `R_sq = 35`, with `w128Zero` at Orbit `0`).
-/

public section

namespace Dyadic128CoulombMath

open Real SpecsAux.SpecMirror
open scoped BigOperators

theorem coulombKernel_neg (ν : Fin 3 → ℤ) : coulombKernel (-ν) = coulombKernel ν := by
  dsimp [coulombKernel, waveNumberSq, waveVector, dotProduct]
  congr 2
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp
  ring

/-! ## Section 3: Interleaved `8 × 64^3` Bijection, `(b_0, d)` Displacement & Decidable Split -/

end Dyadic128CoulombMath
end
end Dyadic128CoulombMath

section Dyadic128OrbitTableCert
local instance (priority := 1000000) instNeZeroTwoPow_Dyadic128OrbitTableCert (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Certified 47,905-Orbit $128^3$ Q30 Coulomb Table & Multi-Shell Norm Bounds

Pure-`Nat` kernel-decided certificate for the $O_h$-canonical $47,905$-orbit dual Coulomb kernel
`w128Orbit` / `w128Dual` on $\mathbb{Z}_{128}^3$:

1. **Computable Pure-`Nat` Q30 Table (`w128OrbitBiasedQ30`, `w128OrbitQ30`)**:
   - `abs_w128Orbit_sub_q30_le`: $|w_{128}(\text{idx}) - \text{q30}(\text{idx}) / 2^{30}| \le
     2^{-30}$,
   - `abs_w128Dual_sub_q30_le`: $|w_{128}(d) - \text{q30}(\text{rank}(d)) / 2^{30}| \le 2^{-30}$,
   - `total_qrom30_pair70741_error_le`: $70741 \cdot 2^{-30} \le 5 \times 10^{-4}$.
2. **Exact Origin & Open-Box $[-62, 62]^3$ Sum Bounds (`w128Zero`)**:
   - `w128Zero_eq_sum_momentumTransferBox62`, `w128Zero_bounds`,
   - `sum_coulombKernel_le_of_mem_Icc62`, `mul_218_w128Zero_le`, `mul_436_w128Zero_le`.
3. **All Three Integer-Shell Head/Tail Splits (`rSqOpt = ![32, 33, 34, 27]`, `R_sq = 34`, `R_sq =
   27`)**:
   - Exact shell separation (`0 ≤ kHead`, `kMin ≤ kTail ≤ cCut`), pointwise `=` identity with
     `HeavyHeadAndProjectile128.kHead` / `kTail`, per-sub-grid support count `≤ 109`, and
     unconditional `U_en` + `V_ee` norm certificates across all three shells.
-/

public section

namespace Dyadic128OrbitTableCert

open Real SpecsAux.SpecMirror
open Dyadic128CoulombMath
open scoped BigOperators

theorem cast_strictSubNat {a b : ℕ} (h : b ≤ a) :
    ((strictSubNat a b : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) := by
  rw [strictSubNat_eq]
  exact Nat.cast_sub h

def rSqOpt : Fin 4 → ℕ := ![32, 33, 34, 27]

/-- Per-parity-weight rational soft-core cutoffs `[1.377913800, 1.448953881, 1.423981480,
1.401286400]`. -/
noncomputable def cCutOptByWeight : Fin 4 → ℝ := ![1377913800 / 1000000000, 1448953881 /
    1000000000, 1423981480 / 1000000000, 1401286400 / 1000000000]

/-- Per-parity-weight rational minima `[-0.059731800, -0.067569800, -0.059712800, -0.059707300]`.
-/
noncomputable def kMinOptByWeight : Fin 4 → ℝ := ![-59731800 / 1000000000, -67569800 /
    1000000000, -59712800 / 1000000000, -59707300 / 1000000000]

theorem w128OrbitQ30Real_zero_eq : w128OrbitQ30Real 0 = (24194760416 : ℝ) / 2 ^ 30 := by
  unfold w128OrbitQ30Real w128OrbitQ30
  rw [show w128OrbitBiasedQ30 0 = 25268502240 from rfl]
  norm_num

private theorem q30_shell_split {r2 rSq qb lo fl hi : ℕ} {c : ℝ}
    (hok : (if r2 ≤ rSq then decide (lo ≤ qb) else decide (qb ≤ hi)) = true)
    (hfl : fl ≤ 1 + lo) (hlo_c : c * 2 ^ 30 + 1073741824 ≤ (lo : ℝ))
    (hfl_c : (fl : ℝ) ≤ c * 2 ^ 30 + 1073741825)
    (hhi_c : (hi : ℝ) ≤ c * 2 ^ 30 + 1073741824) :
    if r2 ≤ rSq then
      c ≤ ((qb : ℝ) - 1073741824) / 2 ^ 30 ∧
        ((qb : ℝ) - 1073741824) / 2 ^ 30 - c ≤ ((strictSubNat (1 + qb) fl : ℕ) : ℝ) / 2 ^ 30
    else ((qb : ℝ) - 1073741824) / 2 ^ 30 ≤ c := by
  by_cases hc : r2 ≤ rSq
  · rw [ite_pos_eq hc, decide_eq_true_eq] at hok
    rw [ite_pos_eq hc, cast_strictSubNat (by omega)]
    have hm : (lo : ℝ) ≤ (qb : ℝ) := by exact_mod_cast hok
    push_cast
    norm_num at hlo_c hfl_c ⊢
    exact ⟨by linarith, by linarith⟩
  · rw [ite_neg_eq hc, decide_eq_true_eq] at hok
    rw [ite_neg_eq hc]
    have hm : (qb : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hok
    norm_num at hhi_c ⊢
    linarith

private theorem q30_min_split {qb lo : ℕ} {km : ℝ} (hmin : lo ≤ qb)
    (hkm : km * 2 ^ 30 + 1073741824 ≤ (lo : ℝ)) :
    km ≤ ((qb : ℝ) - 1073741824) / 2 ^ 30 := by
  have hm : (lo : ℝ) ≤ (qb : ℝ) := by exact_mod_cast hmin
  norm_num at hkm ⊢
  linarith

/-- Direct quantized `Q30` shell & minimum certificate across all `47,905` canonical orbits
(zero boundary ULP leakage across all `2,096,280` exterior points of `ℤ_{128}^3`). -/
theorem w128OrbitQ30Real_shell_cert (idx : Fin orbitCount47905) :
    let t := tetRank65.symm idx
    let wt := orbitParityWeight idx
    let r2 := canonicalNormSq65 t
    let qb := w128OrbitBiasedQ30 idx
    (kMinOptByWeight wt ≤ w128OrbitQ30Real idx) ∧
    (-67569800 / 1000000000 ≤ w128OrbitQ30Real idx) ∧
    (if r2 ≤ rSqOpt wt then
       cCutOptByWeight wt ≤ w128OrbitQ30Real idx ∧
       w128OrbitQ30Real idx - cCutOptByWeight wt ≤
         ((strictSubNat (1 + qb) (floorCutOptQbNat wt.val) : ℕ) : ℝ) / 2 ^ 30
     else w128OrbitQ30Real idx ≤ cCutOptByWeight wt) ∧
    (if r2 ≤ 34 then
       (1401286360 / 1000000000 : ℝ) ≤ w128OrbitQ30Real idx ∧
       w128OrbitQ30Real idx - (1401286360 / 1000000000 : ℝ) ≤
         ((strictSubNat (1 + qb) 2578361596 : ℕ) : ℝ) / 2 ^ 30
     else w128OrbitQ30Real idx ≤ (1401286360 / 1000000000 : ℝ)) ∧
    (if r2 ≤ 27 then
       (1559578100 / 1000000000 : ℝ) ≤ w128OrbitQ30Real idx ∧
       w128OrbitQ30Real idx - (1559578100 / 1000000000 : ℝ) ≤
         ((strictSubNat (1 + qb) 2748326057 : ℕ) : ℝ) / 2 ^ 30
     else w128OrbitQ30Real idx ≤ (1559578100 / 1000000000 : ℝ)) := by
  set t := tetRank65.symm idx
  have ht_eq : tetUnrank65 idx = t := rfl
  generalize hwt_def : orbitParityWeight idx = wt
  have hwt_val : wt.val = (t.u.val % 2) + (t.v.val % 2) + (t.w.val % 2) := by
    rw [← hwt_def]
    rfl
  set r2 := canonicalNormSq65 t
  have hr2_eq : t.u.val * t.u.val + t.v.val * t.v.val + t.w.val * t.w.val = r2 := by
    dsimp [r2, canonicalNormSq65]
    ring
  set qb := w128OrbitBiasedQ30 idx
  have hok := canonicalTriple_orbitOk t
  dsimp only [orbitTripleOk] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hqb_eq :
      (posConst328Nat +
        (t.u.val |> u56Col |> dot160 (wqVec160 (u56Col t.w.val) (u56Col t.v.val))) -
        (negConst328Nat + (bBiasNat * sum160 (wqVec160 (u56Col t.w.val) (u56Col t.v.val)) +
          sumU328 t.u.val))) / shift298Nat = qb := by
    simp only [qb, w128OrbitBiasedQ30, ht_eq, evalTripleBiasedQ30]
  rw [hqb_eq, ← hwt_val, hr2_eq] at hok
  rcases hok with ⟨⟨⟨⟨_, hmin⟩, hopt⟩, h34⟩, h27⟩
  have hq30_real : w128OrbitQ30Real idx = ((qb : ℝ) - 1073741824) / 2 ^ 30 := by
    unfold w128OrbitQ30Real w128OrbitQ30
    push_cast
    rfl
  rw [hq30_real]
  have hrSq_eq : rSqOptNat wt.val = rSqOpt wt := by
    fin_cases wt
    all_goals rfl
  rw [hrSq_eq] at hopt
  have hkMin : kMinOptByWeight wt ≤ ((qb : ℝ) - 1073741824) / 2 ^ 30 := by
    fin_cases wt
    all_goals exact q30_min_split hmin (by norm_num [kMinOptByWeight, loMinQbNat])
  have hkLo : (-67569800 / 1000000000 : ℝ) ≤ kMinOptByWeight wt := by
    fin_cases wt
    all_goals norm_num [kMinOptByWeight]
  refine ⟨hkMin, le_trans hkLo hkMin, ?_,
    q30_shell_split (fl := 2578361596) h34 (by decide) (by norm_num) (by norm_num) (by norm_num),
    q30_shell_split (fl := 2748326057) h27 (by decide) (by norm_num) (by norm_num) (by norm_num)⟩
  fin_cases wt
  · exact q30_shell_split (fl := floorCutOptQbNat 0) hopt (by decide)
      (by norm_num [cCutOptByWeight, loInOptQbNat])
      (by norm_num [cCutOptByWeight, floorCutOptQbNat])
      (by norm_num [cCutOptByWeight, hiOutOptQbNat])
  · exact q30_shell_split (fl := floorCutOptQbNat 1) hopt (by decide)
      (by norm_num [cCutOptByWeight, loInOptQbNat])
      (by norm_num [cCutOptByWeight, floorCutOptQbNat])
      (by norm_num [cCutOptByWeight, hiOutOptQbNat])
  · exact q30_shell_split (fl := floorCutOptQbNat 2) hopt (by decide)
      (by norm_num [cCutOptByWeight, loInOptQbNat])
      (by norm_num [cCutOptByWeight, floorCutOptQbNat])
      (by norm_num [cCutOptByWeight, hiOutOptQbNat])
  · exact q30_shell_split (fl := floorCutOptQbNat 3) hopt (by decide)
      (by norm_num [cCutOptByWeight, loInOptQbNat])
      (by norm_num [cCutOptByWeight, floorCutOptQbNat])
      (by norm_num [cCutOptByWeight, hiOutOptQbNat])

end Dyadic128OrbitTableCert
end
end Dyadic128OrbitTableCert

section PosMomSelectSandwich
local instance (priority := 1000000) instNeZeroTwoPow_PosMomSelectSandwich (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# 2-Toffoli Pos/Mom `SELECT` Outer-Conjugation Sandwich (`PosMomSelectSandwich`)

Shared operator-algebraic and `Circuit n` combinators for multiplexing momentum-diagonal channels
(`MomSlots`, encoded on slot bit `s₂ = 1`, e.g. `s ∈ {4, 5}`) and position-diagonal channels
(`PosSlots`, encoded on slot bit `s₂ = 0`, e.g. `s ∈ {0, 1, 2, 3}`) inside a single self-inverse
`SELECT` unitary with **only `1` Toffoli one-way (`2` Toffolis round-trip)** and **zero extra
`T`-gates** from phase kickback (`CZ` + `X · CZ · X`):

- `momCleanOp U_mom D_momGate := U_momᴴ * D_momGate * U_mom`
  (`cMomRaw ;;ᶜ TOFF s₂ qMomRaw qMomParity ;;ᶜ cMomRaw.inverse`)
- `posMomCoreOp U_pos D_momPhase D_posPhase := U_posᴴ * (D_posPhase * D_momPhase) * U_pos`
  (`cPos ;;ᶜ CZ s₂ qMomParity ;;ᶜ X s₂ ;;ᶜ CZ s₂ qPosSign ;;ᶜ X s₂ ;;ᶜ cPos.inverse`)
- `posMomSelectOp U_mom D_momGate U_qft U_pos D_momPhase D_posPhase`
  (`cMomClean ;;ᶜ cQft ;;ᶜ cCore ;;ᶜ cQft.inverse ;;ᶜ cMomClean.inverse`)

Key dimension-polymorphic (`{d : ℕ}`) theorems (zero unfolding of `2 ^ n`):
1. **Unconditional Hermiticity & Involution** (`posMomSelectOp_isHermitian`,
   `posMomSelectOp_mul_self`): holds on ALL `d` states (including off-grid / dirty-ancilla states),
   discharging the self-adjointness conjunct `U.1ᴴ = U.1` of `IsQubitizedBlockEncodingUnitary` in
   two lines without basis-state case splits.
2. **Exact `PosSlots` (`s₂ = 0`) Collapse** (`posMomSelectOp_on_posSlot`): whenever `U_mom`
   preserves `P₀` (`D_momGate * P₀ = P₀` and `D_momPhase * P₀ = P₀`), BOTH forward and inverse
   `momCleanOp` collapse syntactically to `1`, yielding
   `posMomSelectOp ... * P₀ = (U_qftᴴ * U_posᴴ * D_posPhase * U_pos * U_qft) * P₀`.
3. **Exact `MomSlots` (`s₂ = 1`) Collapse** (`posMomSelectOp_on_momSlot`): whenever `D_posPhase`
   acts trivially on `P₁` (`D_posPhase * P₁ = P₁`) and `U_qft`, `U_pos` commute with `P₁` and
   `D_momPhase`, **BOTH `U_pos` AND `U_qft` cancel out to `1` syntactically** by unitarity
   (`Uᴴ * U = 1`) even when `U_pos` is non-diagonal (e.g. contains `QFT_256^3`, anchor twists,
   Select-Swap QROM, and streaming grid guards), yielding
   `posMomSelectOp ... * P₁ = (momCleanOp U_mom D_momGate * D_momPhase * momCleanOp U_mom
   D_momGate) * P₁`.
4. **Full Block Decomposition (`posMomSelectOp_eq_add_slots`)**: when `P₀ + P₁ = 1`, decomposes the
   entire `SELECT` unitary into its exact `PosSlots` + `MomSlots` blocks in one step.
-/

public section

namespace PosMomSelectSandwich

open Operator Matrix

section PolymorphicAlgebra

variable {d : ℕ}

/-- Commutation with a Hermitian operator lifts automatically from `U` to `Uᴴ`. -/
theorem conjTranspose_comm_of_comm {U P : Operator d} (hP : Pᴴ = P)
    (hcomm : U * P = P * U) : Uᴴ * P = P * Uᴴ := by
  calc Uᴴ * P = (P * U)ᴴ := by rw [conjTranspose_mul, hP]
    _ = P * Uᴴ := by rw [← hcomm, conjTranspose_mul, hP]

/-- Complete `PosSlots + MomSlots` block decomposition via `P₀ + P₁ = 1`. -/
theorem posMomSelectOp_eq_add_slots {S S₀ S₁ P₀ P₁ : Operator d} (hsum : P₀ + P₁ = 1)
    (h₀ : S * P₀ = S₀ * P₀) (h₁ : S * P₁ = S₁ * P₁) : S = S₀ * P₀ + S₁ * P₁ := by
  exact (Matrix.mul_one S).symm.trans (by rw [← hsum, Matrix.mul_add, h₀, h₁])

end PolymorphicAlgebra

/-! ## Section 2: Concrete `Circuit n` Constructors, Denotations & Exact Gate Counts -/

section CircuitInstantiation

variable {n : ℕ}

theorem slotBitProj_conjTranspose (w : Wire n) (b : Fin 2) :
    (slotBitProj w b)ᴴ = slotBitProj w b := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [slotBitProj, apply_ite (starRingEnd ℂ)]
  · simp [slotBitProj, hxy, Ne.symm hxy]

theorem slotBitProj_mul_self (w : Wire n) (b : Fin 2) :
    slotBitProj w b * slotBitProj w b = slotBitProj w b := by
  rw [slotBitProj, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  by_cases hb : (basisBits n x w).val = b.val
  · simp [hb]
  · simp [hb]

end CircuitInstantiation

end PosMomSelectSandwich
end
end PosMomSelectSandwich

section StoppingPowerSubspaceInvariance
local instance (priority := 1000000) instNeZeroTwoPow_StoppingPowerSubspaceInvariance
    (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Fermionic & Grid Subspace Invariance (`StoppingPowerSubspaceInvariance`)

Subspace-invariance combinators and Hermiticity lemmas for
`QuantumComputationSpecs.Algorithms.StoppingPower`:
- `gridProjector` / `gridStatesProj`: Hermiticity, idempotence, and commutation with operators
  supported on `gridStates` (`fermionicProjector spinUp`, `hamiltonian c`).
- `fermionicGridProjector`: proves `fermionicGridProjector spinUp = fermionicProjector spinUp`
  and equivalence of `ApproximatesTimeEvolution` on `fermionicGridProjector spinUp` vs
  `fermionicProjector spinUp`.
- `PreservesFermionicGridSubspace` and its multiplicative and power closure
  (`preservesFermionicGridSubspace_pow`).
- Proofs of `fermionicProjector_isHermitian` and `hamiltonian_isHermitian` for all
  `c : Configuration` and `spinUp`.
-/

public section

namespace SpecsAux

open Operator Matrix SpecsAux.SpecMirror

open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem structureFactor_neg (c : Configuration) (ν : Fin 3 → ℤ) :
    structureFactor c (-ν) = star (structureFactor c ν) := by
  simp only [structureFactor, stepVector_neg, neg_dotProduct, map_sum, Complex.star_def,
    ← Complex.exp_conj]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  simp [Complex.conj_ofReal]

/-- `hamiltonian c` is Hermitian for every `c : Configuration`. -/
theorem hamiltonian_isHermitian (c : Configuration) : (hamiltonian c).IsHermitian := by
  classical
  ext x y
  simp only [Matrix.conjTranspose_apply, hamiltonian, Matrix.of_apply, Complex.star_def]
  by_cases hxy : IsGridState x ∧ IsGridState y
  · have hsub (a) : momentum y a - momentum x a = -(momentum x a - momentum y a) := by abel
    simp only [hxy.1, hxy.2, and_self, ↓reduceIte, map_add, Complex.conj_ofReal]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (congrArg Complex.ofReal ?_)
    · by_cases heq : x = y
      · subst heq
        simp only [↓reduceIte, Complex.conj_ofReal]
      · simp only [heq, Ne.symm heq, ↓reduceIte, map_zero]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [apply_ite (starRingEnd ℂ), map_zero]
      refine if_congr ⟨fun h b hb ↦ (h b hb).symm, fun h b hb ↦ (h b hb).symm⟩ ?_ rfl
      rw [hsub a, coulombKernel_neg, structureFactor_neg]
      simp [Complex.conj_ofReal]
    · refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
      refine if_congr ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, fun d hd1 hd2 ↦ (h2 d hd1 hd2).symm, h3.symm⟩,
        fun ⟨h1, h2, h3⟩ ↦ ⟨h1, fun d hd1 hd2 ↦ (h2 d hd1 hd2).symm, h3.symm⟩⟩ ?_ rfl
      rw [hsub a, coulombKernel_neg]
  · simp only [show ¬(IsGridState y ∧ IsGridState x) from fun h ↦ hxy h.symm,
      hxy, ↓reduceIte, map_zero]

end SpecsAux
end
end StoppingPowerSubspaceInvariance

end QuantumComputation.Specs.StoppingPowerSolution
