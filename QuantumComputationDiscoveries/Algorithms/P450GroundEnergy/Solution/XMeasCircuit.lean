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

public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs

/-!
# Dynamic-Circuit Clean-Ancilla, Temporary-AND, and X-Measurement Toolkit (`XMeasCircuit`)

Foundational `DynamicCircuit` verification toolkit (`TOFF = 0`, single classical
measurement variable `v : Var`), providing:

1. **4-Conjunct `CleanRealizes` Contract (`XMeasCircuit.CleanRealizes`):**
   Definitionally equal (`rfl`) to `CleanDyn.CleanRealizes`, bundling `TOFF = 0`,
   `v`-update invariance, exact clean-ancilla weakest precondition against `rAct.embedUnitary U`,
   and clean-ancilla postcondition restoration, together with:
   - `CleanRealizes.mkOfWpClean` / `CleanRealizes.mkOfDisjoint`: automatic derivation of the
     4th conjunct (`wp_clean_post`) for arbitrary `v`-dependent postconditions from the 3rd
     conjunct (`wp_clean`).
   - Sequential composition (`CleanRealizes.seq`, `CleanRealizes.dynSequence`) with zero
     register-disjointness side conditions.
   - Sub-active lifting (`CleanRealizes.liftActive`, `CleanRealizes.liftActiveOfEq`), Finset-based
     sub-scratch lifting (`CleanRealizes.liftScratch`, `CleanRealizes.congrScratch`), clean
     temporary-wire absorption (`CleanRealizes.absorbCleanActive`), register relocation
     (`dynOnRegister`, `CleanRealizes.onRegister`), and top-level bridge to
     `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace`.

2. **Gidney Temporary-AND Sandwich (`andSandwichDyn`):**
   General `andCompute ;; body ;; andUncompute` combinator (`4 + body.count .T` `T` gates,
   `0` `T` gates on uncompute, `body.count .TOFF` `TOFF` gates) proved for arbitrary
   `body : DynamicCircuit Var N` satisfying `CleanRealizes` (enabling nested ripple-carry and tree
   AND cascades), plus `.circuit c` specialization (`andSandwichCircuit`), `jonesToffoli`, and
   recursive Toffoli-to-Jones circuit substitution (`substToffoliDyn`).

3. **Single-Variable (`v : Var`) `0-T` X-Measurement Uncompute & `0-T` Z-Basis Reset:**
   - Direct phase-fixup wire uncompute (`xMeasUnloadWireDyn`) and `c`-bit chunked tree uncompute
     (`xMeasChunkUnloadDyn`) on a single classical variable `v : Var`.
   - `0-T` Z-basis deterministic wire/register reset (`zResetWireDyn`, `zResetRegDyn`).
   - Accumulator-update `0-T` multi-wire X-measurement uncompute (`xMeasAccUnloadRegDyn`) paired
     with one accumulator-controlled phase fixup and `0-T` Z-basis accumulator reset.
-/

@[expose] public section

/-- High-priority `NeZero (2 ^ k)` instance preventing `Nat.instNeZeroSucc` from unfolding large
exponents above `exponentiation.threshold`. -/
instance (priority := 100000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-! ## Section 1: `DynamicCircuit` Combinators, Kraus Paths, and `cleanFinsetProj` -/

/-- Relocate an `m`-wire `DynamicCircuit` onto an ordered `m`-wire register in an `N`-wire
ambient system, preserving every primitive gate count. -/
def dynOnRegister {Var : Type} {m N : ℕ} (placement : QRegister m N) :
    DynamicCircuit Var m → DynamicCircuit Var N :=
  DynamicCircuit.qcFold
    (fun c ↦ .circuit (c.onRegister placement))
    (fun v r ↦ .measure v (placement.compose r))
    DynamicCircuit.qcRawQIf
    .seq

@[simp]
theorem dynOnRegister_circuit {Var : Type} {m N : ℕ} (placement : QRegister m N) (c : Circuit m) :
    dynOnRegister (Var := Var) placement (.circuit c) = .circuit (c.onRegister placement) :=
  DynamicCircuit.qcFold_circuit _ _ _ _ c

@[simp]
theorem dynOnRegister_identity {Var : Type} {m N : ℕ} (placement : QRegister m N) :
    dynOnRegister (Var := Var) placement .identity = .identity :=
  dynOnRegister_circuit placement .identity

@[simp]
theorem dynOnRegister_measure {Var : Type} {m N : ℕ} (placement : QRegister m N)
    (v : Var) (r : QRegister 1 m) :
    dynOnRegister placement (.measure v r) = .measure v (placement.compose r) :=
  DynamicCircuit.qcFold_measure _ _ _ _ v r

@[simp]
theorem dynOnRegister_qIf {Var : Type} {m N : ℕ} (placement : QRegister m N) (g : QCRawGuard Var)
    (t f : DynamicCircuit Var m) :
    dynOnRegister placement (DynamicCircuit.qcRawQIf g t f) =
      DynamicCircuit.qcRawQIf g (dynOnRegister placement t) (dynOnRegister placement f) :=
  DynamicCircuit.qcFold_qIf _ _ _ _ g t f

@[simp]
theorem dynOnRegister_seq {Var : Type} {m N : ℕ} (placement : QRegister m N)
    (p₁ p₂ : DynamicCircuit Var m) :
    dynOnRegister placement (.seq p₁ p₂) =
      .seq (dynOnRegister placement p₁) (dynOnRegister placement p₂) :=
  DynamicCircuit.qcFold_seq _ _ _ _ p₁ p₂

@[simp]
theorem count_dynOnRegister {Var : Type} {m N a : ℕ} (g : PrimitiveGate a)
    (placement : QRegister m N) (P : DynamicCircuit Var m) :
    (dynOnRegister placement P).count g = P.count g := by
  induction P using DynamicCircuit.qcInd with
  | circuit c => simp [Circuit.count_onRegister]
  | measure _ _ => simp
  | qIf _ _ _ iht ihf => simp [iht, ihf]
  | seq _ _ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Diagonal projector onto global computational-basis states whose bits vanish on every physical
wire in `S`. -/
noncomputable def cleanFinsetProj {n : ℕ} (S : Finset (Wire n)) : Operator (2 ^ n) :=
  Matrix.diagonal fun i : Fin (2 ^ n) ↦ if ∀ w ∈ S, basisBits n i w = 0 then 1 else 0

@[simp]
theorem cleanFinsetProj_empty {n : ℕ} : cleanFinsetProj (∅ : Finset (Wire n)) = 1 := by
  simp [cleanFinsetProj]

@[simp]
theorem cleanFinsetProj_conjTranspose {n : ℕ} (S : Finset (Wire n)) :
    (cleanFinsetProj S)ᴴ = cleanFinsetProj S := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ∀ w ∈ S, basisBits n i w = 0 <;> simp [cleanFinsetProj, h]
  · simp [cleanFinsetProj, hij, Ne.symm hij]

private theorem finset_union_self {α : Type*} [DecidableEq α] (S : Finset α) : S ∪ S = S := by
  ext x; simp

@[simp]
theorem cleanFinsetProj_mul_union {n : ℕ} (S₁ S₂ : Finset (Wire n)) :
    cleanFinsetProj S₁ * cleanFinsetProj S₂ = cleanFinsetProj (S₁ ∪ S₂) := by
  simp only [cleanFinsetProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have hunion : (∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0) ↔
      (∀ w ∈ S₁, basisBits n i w = 0) ∧ (∀ w ∈ S₂, basisBits n i w = 0) := by
    simp only [Finset.mem_union, or_imp, forall_and]
  by_cases h₁ : ∀ w ∈ S₁, basisBits n i w = 0
  · by_cases h₂ : ∀ w ∈ S₂, basisBits n i w = 0
    · have h₁₂ : ∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0 := hunion.mpr ⟨h₁, h₂⟩
      simp only [eq_true h₁, eq_true h₂, eq_true h₁₂, ↓reduceIte, mul_one]
    · have h₁₂ : ¬ ∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0 := fun h ↦ h₂ (hunion.mp h).2
      simp only [eq_true h₁, eq_false h₂, eq_false h₁₂, ↓reduceIte, mul_zero]
  · have h₁₂ : ¬ ∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0 := fun h ↦ h₁ (hunion.mp h).1
    simp only [eq_false h₁, eq_false h₁₂, ↓reduceIte, zero_mul]

theorem cleanFinsetProj_mul_self {n : ℕ} (S : Finset (Wire n)) :
    cleanFinsetProj S * cleanFinsetProj S = cleanFinsetProj S := by
  rw [cleanFinsetProj_mul_union, finset_union_self]

theorem cleanFinsetProj_comm {n : ℕ} (S₁ S₂ : Finset (Wire n)) :
    cleanFinsetProj S₁ * cleanFinsetProj S₂ = cleanFinsetProj S₂ * cleanFinsetProj S₁ := by
  rw [cleanFinsetProj_mul_union, cleanFinsetProj_mul_union, Finset.union_comm]

theorem cleanFinsetProj_mul_le_one {n : ℕ} (S : Finset (Wire n)) :
    cleanFinsetProj S * (cleanFinsetProj S)ᴴ ≤ 1 := by
  rw [cleanFinsetProj_conjTranspose, cleanFinsetProj_mul_self]
  change (1 - cleanFinsetProj S).PosSemidef
  rw [cleanFinsetProj, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs <;> simp

private theorem basisBits_zero_apply (k : ℕ) (j : Fin k) :
    basisBits k (0 : Fin (2 ^ k)) j = 0 := by
  rw [basisBits_eq_div_mod]
  simp

theorem basisOutcomeProjector_zero_eq_cleanFinsetProj {k n : ℕ} (r : QRegister k n) :
    r.basisOutcomeProjector 0 = cleanFinsetProj r.image := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, cleanFinsetProj]
  congr 1
  funext global
  have hiff : r.extractIndex global = 0 ↔ ∀ w ∈ r.image, basisBits n global w = 0 := by
    constructor
    · intro h w hw
      obtain ⟨j, rfl⟩ := (r.mem_image w).mp hw
      rw [← r.basisBits_extractIndex global j, h, basisBits_zero_apply]
    · intro h
      apply (basisBits k).injective
      funext j
      rw [r.basisBits_extractIndex, basisBits_zero_apply]
      exact h (r j) (QRegister.mem_image r (r j) |>.mpr ⟨j, rfl⟩)
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (hiff.mp h₁) h₂
  · exact absurd (hiff.mpr h₂) h₁
  · rfl

/-- Restrict a classical-quantum assertion pointwise onto the zero subspace of wire set `S`. -/
noncomputable def restrictAssertionToCleanFinset {Var : Type} [Fintype Var] {n : ℕ}
    (Θ : QCAssertion Var (2 ^ n)) (S : Finset (Wire n)) : QCAssertion Var (2 ^ n) :=
  Θ.conj (cleanFinsetProj S) (cleanFinsetProj_mul_le_one S)

@[simp]
theorem restrictAssertionToCleanFinset_coe {Var : Type} [Fintype Var] {n : ℕ}
    (Θ : QCAssertion Var (2 ^ n)) (S : Finset (Wire n)) (σ : Store Var) :
    (restrictAssertionToCleanFinset Θ S σ).1 = (Θ σ).1.conj (cleanFinsetProj S) := rfl

theorem restrictAssertionToZeroAncilla_eq_cleanFinset {Var : Type} [Fintype Var] {k n : ℕ}
    (Θ : QCAssertion Var (2 ^ n)) (r : QRegister k n) :
    restrictAssertionToZeroAncilla Θ r = restrictAssertionToCleanFinset Θ r.image := by
  funext σ
  apply Subtype.ext
  simp only [restrictAssertionToZeroAncilla_coe, restrictAssertionToCleanFinset_coe,
    basisOutcomeProjector_zero_eq_cleanFinsetProj]

theorem restrictAssertionToCleanFinset_union {Var : Type} [Fintype Var] {n : ℕ}
    (Θ : QCAssertion Var (2 ^ n)) (S₁ S₂ : Finset (Wire n)) :
    restrictAssertionToCleanFinset Θ (S₁ ∪ S₂) =
      restrictAssertionToCleanFinset (restrictAssertionToCleanFinset Θ S₁) S₂ := by
  funext σ
  apply Subtype.ext
  simp only [restrictAssertionToCleanFinset_coe, conj_conj, cleanFinsetProj_comm S₂ S₁,
    cleanFinsetProj_mul_union]

theorem embedMatrix_comm_cleanFinsetProj {k n : ℕ} (r : QRegister k n) (S : Finset (Wire n))
    (hdisj : Disjoint r.image S) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix A * cleanFinsetProj S = cleanFinsetProj S * r.embedMatrix A := by
  ext i j
  rw [cleanFinsetProj, Matrix.mul_diagonal, Matrix.diagonal_mul,
    r.embedMatrix_apply_of_agreeOutside]
  by_cases hag : r.AgreeOutside i j
  · have hbits : (∀ w ∈ S, basisBits n i w = 0) ↔ (∀ w ∈ S, basisBits n j w = 0) := by
      refine forall₂_congr fun w hw ↦ ?_
      have hnot : w ∉ Set.range r.wires := by
        rintro ⟨l, rfl⟩
        exact Finset.disjoint_left.mp hdisj (r.mem_image (r l) |>.mpr ⟨l, rfl⟩) hw
      rw [hag w hnot]
    simp only [hag, ↓reduceIte]
    split_ifs with hj hi hi
    · ring
    · exact absurd (hbits.mpr hj) hi
    · exact absurd (hbits.mp hi) hj
    · ring
  · simp only [hag, ↓reduceIte, zero_mul, mul_zero]

/-! ### Finite Kraus-Path Representation of `DynamicCircuit` -/

private noncomputable def dynPaths {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} :
    DynamicCircuit Var n → Store Var → List (Operator (2 ^ n) × Store Var) :=
  DynamicCircuit.qcRec
    (fun c σ ↦ [(c.eval.1, σ)])
    (fun v r σ ↦
      (List.finRange 2).map fun o ↦
        (r.basisOutcomeProjector o, Function.update σ v (Int.ofNat o.val)))
    (fun cond _ _ iht ihf σ ↦ if cond.holds σ then iht σ else ihf σ)
    (fun _ _ ih₁ ih₂ σ ↦
      (ih₁ σ).flatMap fun x ↦
        (ih₂ x.2).map fun y ↦ (y.1 * x.1, y.2))

@[simp]
private theorem dynPaths_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (c : Circuit n) (σ : Store Var) :
    dynPaths (.circuit c) σ = [(c.eval.1, σ)] := rfl

@[simp]
private theorem dynPaths_measure {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : QRegister 1 n) (σ : Store Var) :
    dynPaths (.measure v r) σ =
      (List.finRange 2).map fun o ↦
        (r.basisOutcomeProjector o, Function.update σ v (Int.ofNat o.val)) := rfl

@[simp]
private theorem dynPaths_qIf {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (cond : QCRawGuard Var) (t f : DynamicCircuit Var n) (σ : Store Var) :
    dynPaths (DynamicCircuit.qcRawQIf cond t f) σ =
      if cond.holds σ then dynPaths t σ else dynPaths f σ := rfl

@[simp]
private theorem dynPaths_seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (p₁ p₂ : DynamicCircuit Var n) (σ : Store Var) :
    dynPaths (.seq p₁ p₂) σ =
      (dynPaths p₁ σ).flatMap fun x ↦
        (dynPaths p₂ x.2).map fun y ↦ (y.1 * x.1, y.2) := rfl

private theorem conj_map_list_sum {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℂ)
    (hs : List (HermitianMat (Fin d₂) ℂ)) :
    hs.sum.conj M = (hs.map fun H ↦ H.conj M).sum := by
  induction hs with
  | nil => simp
  | cons h hs ih => simp only [List.sum_cons, map_add, List.map_cons, ih]

private theorem wp_compile_eq_sum_dynPaths {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (P : DynamicCircuit Var n) (Θ : QCAssertion Var (2 ^ n)) (σ : Store Var) :
    (wp P.compile Θ σ).1 =
      ((dynPaths P σ).map fun x ↦ (Θ x.2).1.conj x.1ᴴ).sum := by
  induction P using DynamicCircuit.qcInd generalizing Θ σ with
  | circuit c =>
      simp [qcWpQAssign, qcQAssignObsMap, Matrix.star_eq_conjTranspose]
  | measure v r =>
      have hsubst0 : Store.subst σ v 0 = Function.update σ v 0 := by
        funext y; simp [Store.subst, Function.update]
      have hsubst1 : Store.subst σ v 1 = Function.update σ v 1 := by
        funext y; simp [Store.subst, Function.update]
      simp only [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
        qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe, QCAssertion.subst_apply,
        CompleteMeasurement.toMeasurement_coe, QRegister.computationalBasisMeasurement_apply,
        qc_qMeasure_outcome_herm_eq_conj, dynPaths_measure]
      change ∑ o : Fin 2, _ = _
      rw [Fin.sum_univ_two]
      simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Fin.succ_zero_eq_one, Fin.val_zero, Fin.val_one,
        Int.ofNat_eq_natCast, Nat.cast_zero, Nat.cast_one,
        QRegister.basisOutcomeProjector_conjTranspose]
      rw [hsubst0, hsubst1]
  | qIf cond t f iht ihf =>
      simp only [DynamicCircuit.compile_qcRawQIf, wp_qcRawQIf, dynPaths_qIf]
      by_cases hc : cond.holds σ <;> simp [hc, iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynamicCircuit.compile_seq, wp_qSeq, ih₁, dynPaths_seq]
      have hflat :
          ∀ l : List (Operator (2 ^ n) × Store Var),
            (l.map fun x ↦ (wp p₂.compile Θ x.2).1.conj x.1ᴴ).sum =
              ((l.flatMap fun x ↦ (dynPaths p₂ x.2).map fun y ↦ (y.1 * x.1, y.2)).map
                fun z ↦ (Θ z.2).1.conj z.1ᴴ).sum := by
        intro l
        induction l with
        | nil => simp
        | cons x xs ihl =>
            simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
              List.sum_append, ← ihl, ih₂ Θ x.2, conj_map_list_sum, List.map_map]
            congr 1
            refine congrArg List.sum (List.map_congr_left fun y _ ↦ ?_)
            simp only [Function.comp_apply, conj_conj, Matrix.conjTranspose_mul]
      exact hflat (dynPaths p₁ σ)

/-- Exact 4-conjunct clean-ancilla dynamic-circuit contract (definitionally equal to
`CleanDyn.CleanRealizes`):
1. `P.count .TOFF = 0`.
2. `wp P.compile Θ` preserves invariance under updating `v`.
3. On `v`-independent postconditions `Θ`, restricting `wp P.compile Θ` to `|0^s⟩` on `rScr` equals
   restricting `wp_qAssign (rAct.embedUnitary U) Θ` to `|0^s⟩` on `rScr`.
4. Restricting any postcondition `Θ` to `|0^s⟩` on `rScr` before `wp P.compile` leaves the
   clean-ancilla precondition unchanged. -/
def CleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ) ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    restrictAssertionToZeroAncilla (wp P.compile Θ) rScr =
      restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr) ∧
  (∀ Θ : QCAssertion Var (2 ^ N),
    restrictAssertionToZeroAncilla (wp P.compile (restrictAssertionToZeroAncilla Θ rScr)) rScr =
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr)

namespace CleanRealizes

section Projections

variable {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
variable {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
variable {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}

theorem count_toff (h : CleanRealizes v rAct rScr U P) : P.count PrimitiveGate.TOFF = 0 := h.1

theorem wp_update (h : CleanRealizes v rAct rScr U P) (Θ : QCAssertion Var (2 ^ N))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) (σ : Store Var) (val : ℤ) :
    (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ :=
  h.2.1 Θ hΘ σ val

theorem wp_clean (h : CleanRealizes v rAct rScr U P) (Θ : QCAssertion Var (2 ^ N))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictAssertionToZeroAncilla (wp P.compile Θ) rScr =
      restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr :=
  h.2.2.1 Θ hΘ

theorem wp_clean_post (h : CleanRealizes v rAct rScr U P) (Θ : QCAssertion Var (2 ^ N)) :
    restrictAssertionToZeroAncilla (wp P.compile (restrictAssertionToZeroAncilla Θ rScr)) rScr =
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr :=
  h.2.2.2 Θ

end Projections

/-! ### Automatic `wp_clean_post` Derivation via Kraus Positivity -/

/-- Complementary scratch observable `1 - rScr.cleanObservable`, vanishing iff `rScr` is `|0^s⟩`. -/
noncomputable def dirtyObservable {s N : ℕ} (rScr : QRegister s N) :
    Observable (Fin (2 ^ N)) :=
  ⟨1 - rScr.cleanObservable.1, sub_nonneg.mpr rScr.cleanObservable.2.2,
    sub_le_self 1 rScr.cleanObservable.2.1⟩

@[simp]
theorem dirtyObservable_mat {s N : ℕ} (rScr : QRegister s N) :
    (dirtyObservable rScr).1.mat = 1 - rScr.basisOutcomeProjector 0 := by
  simp [dirtyObservable, QRegister.cleanObservable]

private theorem list_sum_eq_zero_of_nonneg {α : Type*} [AddCommMonoid α] [PartialOrder α]
    [IsOrderedAddMonoid α] {l : List α} (hnonneg : ∀ x ∈ l, 0 ≤ x) (hsum : l.sum = 0) :
    ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => intro _ hx; cases hx
  | cons a as ih =>
      rw [List.sum_cons] at hsum
      have ha0 : 0 ≤ a := hnonneg a List.mem_cons_self
      have has0 : 0 ≤ as.sum := List.sum_nonneg fun x hx ↦ hnonneg x (List.mem_cons_of_mem a hx)
      have ha_le : a ≤ 0 := hsum ▸ le_add_of_nonneg_right has0
      have ha_eq : a = 0 := le_antisymm ha_le ha0
      have has_eq : as.sum = 0 := by simpa only [ha_eq, zero_add] using hsum
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact ha_eq
      · exact ih (fun y hy ↦ hnonneg y (List.mem_cons_of_mem a hy)) has_eq x hmem

private theorem matrix_eq_zero_of_conjTranspose_mul_self_eq_zero {d : ℕ}
    {B : Matrix (Fin d) (Fin d) ℂ} (h : Bᴴ * B = 0) : B = 0 := by
  ext i j
  have hdiag : (Bᴴ * B) j j = 0 := by rw [h]; rfl
  have hre : ∑ k : Fin d, Complex.normSq (B k j) = 0 := by
    have hsum : (∑ k : Fin d, (Complex.normSq (B k j) : ℂ)) = 0 := by
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
        Complex.normSq_eq_conj_mul_self] using hdiag
    exact_mod_cast hsum
  have hterm : Complex.normSq (B i j) = 0 :=
    Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ Complex.normSq_nonneg (B k j)) |>.mp hre i
      (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp hterm

/-- Whenever `wp P.compile` maps the dirty-scratch observable `1 - P_scr` to `0` on the clean
scratch subspace `P_scr`, every Kraus path `K` of `P` preserves `P_scr` (`P_scr * K * P_scr =
K * P_scr`), and therefore `wp_clean_post` holds for ALL assertions `Θ` (even `v`-dependent). -/
theorem clean_post_of_dirty_eq_zero {Var : Type} [Finite Var] [DecidableEq Var] {N s : ℕ}
    (rScr : QRegister s N) (P : DynamicCircuit Var N)
    (hdirty : restrictAssertionToZeroAncilla (wp P.compile (fun _ ↦ dirtyObservable rScr)) rScr =
      0)
    (Θ : QCAssertion Var (2 ^ N)) :
    restrictAssertionToZeroAncilla (wp P.compile (restrictAssertionToZeroAncilla Θ rScr)) rScr =
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr := by
  cases nonempty_fintype Var
  funext σ
  apply Subtype.ext
  have hP₀_herm : (rScr.basisOutcomeProjector 0)ᴴ = rScr.basisOutcomeProjector 0 :=
    rScr.basisOutcomeProjector_conjTranspose 0
  have hP₀_idem : rScr.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 :=
    rScr.basisOutcomeProjector_mul_self 0
  have hσ0 : ((restrictAssertionToZeroAncilla
      (wp P.compile (fun _ ↦ dirtyObservable rScr)) rScr σ).1) = 0 :=
    congrArg Subtype.val (congrFun hdirty σ)
  rw [restrictAssertionToZeroAncilla_coe, wp_compile_eq_sum_dynPaths, conj_map_list_sum] at hσ0
  have hterms := list_sum_eq_zero_of_nonneg
    (l := ((dynPaths P σ).map fun x ↦ ((dirtyObservable rScr).1).conj x.1ᴴ).map
      (fun H ↦ H.conj (rScr.basisOutcomeProjector 0)))
    (fun T hT ↦ by
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hT
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hH
      exact (((dirtyObservable rScr).1).conj x.1ᴴ).conj_nonneg (rScr.basisOutcomeProjector 0)
        (((dirtyObservable rScr).1).conj_nonneg x.1ᴴ (dirtyObservable rScr).2.1))
    hσ0
  rw [restrictAssertionToZeroAncilla_coe, restrictAssertionToZeroAncilla_coe,
    wp_compile_eq_sum_dynPaths, wp_compile_eq_sum_dynPaths, conj_map_list_sum, conj_map_list_sum,
    List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx ↦ ?_)
  have hx0 : (((dirtyObservable rScr).1).conj x.1ᴴ).conj (rScr.basisOutcomeProjector 0) = 0 :=
    hterms _ (List.mem_map_of_mem (List.mem_map_of_mem hx))
  have hBsq : ((1 - rScr.basisOutcomeProjector 0) * x.1 * rScr.basisOutcomeProjector 0)ᴴ *
      ((1 - rScr.basisOutcomeProjector 0) * x.1 * rScr.basisOutcomeProjector 0) = 0 := by
    have hmat : rScr.basisOutcomeProjector 0 *
        (x.1ᴴ * (1 - rScr.basisOutcomeProjector 0) * x.1) * rScr.basisOutcomeProjector 0 = 0 := by
      have hm := congrArg HermitianMat.mat hx0
      simpa only [conj_apply_mat, hP₀_herm, Matrix.conjTranspose_conjTranspose,
        dirtyObservable_mat, mat_zero, Matrix.mul_assoc] using hm
    calc ((1 - rScr.basisOutcomeProjector 0) * x.1 * rScr.basisOutcomeProjector 0)ᴴ *
          ((1 - rScr.basisOutcomeProjector 0) * x.1 * rScr.basisOutcomeProjector 0)
        = rScr.basisOutcomeProjector 0 *
            (x.1ᴴ * ((1 - rScr.basisOutcomeProjector 0) *
              (1 - rScr.basisOutcomeProjector 0)) * x.1) *
            rScr.basisOutcomeProjector 0 := by
              simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
                Matrix.conjTranspose_one, hP₀_herm, Matrix.mul_assoc]
      _ = rScr.basisOutcomeProjector 0 *
            (x.1ᴴ * (1 - rScr.basisOutcomeProjector 0) * x.1) *
            rScr.basisOutcomeProjector 0 := by
              have hidem : (1 - rScr.basisOutcomeProjector 0) *
                  (1 - rScr.basisOutcomeProjector 0) = 1 - rScr.basisOutcomeProjector 0 := by
                simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP₀_idem,
                  sub_self, sub_zero]
              rw [hidem]
      _ = 0 := hmat
  have hB0 : (1 - rScr.basisOutcomeProjector 0) * x.1 * rScr.basisOutcomeProjector 0 = 0 :=
    matrix_eq_zero_of_conjTranspose_mul_self_eq_zero hBsq
  have hKP : rScr.basisOutcomeProjector 0 * x.1 * rScr.basisOutcomeProjector 0 =
      x.1 * rScr.basisOutcomeProjector 0 := by
    have hsub : x.1 * rScr.basisOutcomeProjector 0 -
        rScr.basisOutcomeProjector 0 * x.1 * rScr.basisOutcomeProjector 0 = 0 := by
      simpa only [Matrix.sub_mul, Matrix.one_mul] using hB0
    exact (sub_eq_zero.mp hsub).symm
  have hadj : rScr.basisOutcomeProjector 0 * x.1ᴴ * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 * x.1ᴴ := by
    have h := congrArg conjTranspose hKP
    simpa only [Matrix.conjTranspose_mul, hP₀_herm, ← Matrix.mul_assoc] using h
  simp only [Function.comp_apply, restrictAssertionToZeroAncilla_coe, conj_conj,
    ← Matrix.mul_assoc]
  rw [hadj]

/-- Constructor for `CleanRealizes` that derives the 4th conjunct (`wp_clean_post`) automatically
whenever `(rAct.embedUnitary U).1` preserves `rScr.basisOutcomeProjector 0`. -/
theorem mkOfWpClean {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hToff : P.count PrimitiveGate.TOFF = 0)
    (hUpd : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ)
    (hClean : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr =
        restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr)
    (hPres : rScr.basisOutcomeProjector 0 * ((rAct.embedUnitary U).1 *
        rScr.basisOutcomeProjector 0) =
      (rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0) :
    CleanRealizes v rAct rScr U P := by
  refine ⟨hToff, hUpd, hClean, clean_post_of_dirty_eq_zero rScr P ?_⟩
  rw [hClean (fun _ ↦ dirtyObservable rScr) (fun _ _ ↦ rfl)]
  funext σ
  apply Subtype.ext
  apply HermitianMat.ext
  have hP₀_herm : (rScr.basisOutcomeProjector 0)ᴴ = rScr.basisOutcomeProjector 0 :=
    rScr.basisOutcomeProjector_conjTranspose 0
  have hP₀_idem : rScr.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 :=
    rScr.basisOutcomeProjector_mul_self 0
  have hunit : (rAct.embedUnitary U).1ᴴ * (rAct.embedUnitary U).1 = 1 :=
    congrArg Subtype.val (Unitary.star_mul_self (rAct.embedUnitary U))
  have hadj : rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U).1ᴴ *
      rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U).1ᴴ := by
    have h := congrArg conjTranspose hPres
    simpa only [Matrix.conjTranspose_mul, hP₀_herm, ← Matrix.mul_assoc] using h
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_apply_mat, hP₀_herm,
    Matrix.conjTranspose_conjTranspose, dirtyObservable_mat]
  change rScr.basisOutcomeProjector 0 *
      ((rAct.embedUnitary U).1ᴴ * (1 - rScr.basisOutcomeProjector 0) *
        (rAct.embedUnitary U).1) * rScr.basisOutcomeProjector 0 = 0
  calc rScr.basisOutcomeProjector 0 *
        ((rAct.embedUnitary U).1ᴴ * (1 - rScr.basisOutcomeProjector 0) *
          (rAct.embedUnitary U).1) * rScr.basisOutcomeProjector 0
      = rScr.basisOutcomeProjector 0 * ((rAct.embedUnitary U).1ᴴ * (rAct.embedUnitary U).1) *
          rScr.basisOutcomeProjector 0 -
          (rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U).1ᴴ *
            rScr.basisOutcomeProjector 0) *
          ((rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0) := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = rScr.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0 -
          (rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U).1ᴴ) *
          ((rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0) := by
            rw [hunit, Matrix.mul_one, hadj]
    _ = rScr.basisOutcomeProjector 0 -
          rScr.basisOutcomeProjector 0 * ((rAct.embedUnitary U).1ᴴ * (rAct.embedUnitary U).1) *
          rScr.basisOutcomeProjector 0 := by
            rw [hP₀_idem]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hunit, Matrix.mul_one, hP₀_idem, sub_self]

/-- Constructor for `CleanRealizes` when `rAct` and `rScr` are wire-disjoint, deriving
`wp_clean_post` automatically. -/
theorem mkOfDisjoint {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hdisj : Disjoint rAct.image rScr.image)
    (hToff : P.count PrimitiveGate.TOFF = 0)
    (hUpd : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ)
    (hClean : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr =
        restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr) :
    CleanRealizes v rAct rScr U P := by
  refine mkOfWpClean hToff hUpd hClean ?_
  rw [basisOutcomeProjector_zero_eq_cleanFinsetProj, QRegister.embedUnitary_val,
    embedMatrix_comm_cleanFinsetProj rAct rScr.image hdisj U.1, ← Matrix.mul_assoc,
    cleanFinsetProj_mul_self]

/-! ### Basic Constructors & Congruence -/

theorem identity {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N) :
    CleanRealizes v rAct rScr 1 DynamicCircuit.identity := by
  refine ⟨rfl, fun Θ hΘ σ val ↦ hΘ σ val, fun Θ _ ↦ ?_, fun Θ ↦ ?_⟩
  · have hwp1 : qcWpQAssign (1 : Unitary (2 ^ N)) Θ = Θ := by
      funext σ
      apply Subtype.ext
      simp [qcWpQAssign, qcQAssignObsMap]
    simp only [DynamicCircuit.compile_identity, wp, QRegister.embedUnitary_one, hwp1]
  · funext σ
    apply Subtype.ext
    simp [conj_conj]

theorem congrUnitary {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U U' : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanRealizes v rAct rScr U P)
    (hUU' : (rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0 =
      (rAct.embedUnitary U').1 * rScr.basisOutcomeProjector 0) :
    CleanRealizes v rAct rScr U' P := by
  refine ⟨h.count_toff, h.wp_update, fun Θ hΘ ↦ ?_, h.wp_clean_post⟩
  rw [h.wp_clean Θ hΘ]
  funext σ
  apply Subtype.ext
  have hP₀_herm : (rScr.basisOutcomeProjector 0)ᴴ = rScr.basisOutcomeProjector 0 :=
    rScr.basisOutcomeProjector_conjTranspose 0
  have hadj : rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U).1ᴴ =
      rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U').1ᴴ := by
    have hc := congrArg conjTranspose hUU'
    simpa only [Matrix.conjTranspose_mul, hP₀_herm] using hc
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hadj]

/-! ### Sequential Composition (Zero Disjointness Hypotheses) -/

theorem seq {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U₁ U₂ : Unitary (2 ^ k)} {P₁ P₂ : DynamicCircuit Var N}
    (h₁ : CleanRealizes v rAct rScr U₁ P₁) (h₂ : CleanRealizes v rAct rScr U₂ P₂) :
    CleanRealizes v rAct rScr (U₂ * U₁) (.seq P₁ P₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [DynamicCircuit.count, h₁.count_toff, h₂.count_toff, add_zero]
  · intro Θ hΘ σ val
    exact h₁.wp_update (wp P₂.compile Θ) (h₂.wp_update Θ hΘ) σ val
  · intro Θ hΘ
    change restrictAssertionToZeroAncilla (wp P₁.compile (wp P₂.compile Θ)) rScr = _
    rw [← h₁.wp_clean_post (wp P₂.compile Θ), h₂.wp_clean Θ hΘ,
      h₁.wp_clean_post (qcWpQAssign (rAct.embedUnitary U₂) Θ),
      h₁.wp_clean (qcWpQAssign (rAct.embedUnitary U₂) Θ) (fun σ val ↦ by
        simp only [qcWpQAssign, hΘ σ val]),
      qc_wp_qAssign_comp, ← rAct.embedUnitary_mul]
  · intro Θ
    change restrictAssertionToZeroAncilla
        (wp P₁.compile (wp P₂.compile (restrictAssertionToZeroAncilla Θ rScr))) rScr =
      restrictAssertionToZeroAncilla (wp P₁.compile (wp P₂.compile Θ)) rScr
    rw [← h₁.wp_clean_post (wp P₂.compile (restrictAssertionToZeroAncilla Θ rScr)),
      h₂.wp_clean_post Θ, h₁.wp_clean_post (wp P₂.compile Θ)]

theorem liftActive {Var : Type} [Fintype Var] [DecidableEq Var] {N k m s : ℕ}
    {v : Var} {rAct : QRegister k N} {inner : QRegister m k} {rScr : QRegister s N}
    {U : Unitary (2 ^ m)} {P : DynamicCircuit Var N}
    (h : CleanRealizes v (rAct.compose inner) rScr U P) :
    CleanRealizes v rAct rScr (inner.embedUnitary U) P := by
  refine ⟨h.count_toff, h.wp_update, fun Θ hΘ ↦ ?_, h.wp_clean_post⟩
  simpa only [QRegister.embedUnitary_compose] using h.wp_clean Θ hΘ

theorem liftActiveOfEq {Var : Type} [Fintype Var] [DecidableEq Var] {N k m s : ℕ}
    {v : Var} {rSub : QRegister m N} {rAct : QRegister k N} {inner : QRegister m k}
    {rScr : QRegister s N} {U : Unitary (2 ^ m)} {P : DynamicCircuit Var N}
    (heq : rSub = rAct.compose inner) (h : CleanRealizes v rSub rScr U P) :
    CleanRealizes v rAct rScr (inner.embedUnitary U) P :=
  liftActive (heq ▸ h)

/-- Absorb clean temporary wires from `rAct` into a larger scratch register `rScr` whenever the
realized unitary `rAct.embedUnitary U` agrees on `rScr.basisOutcomeProjector 0` with a reduced
unitary `rKeep.embedUnitary U_keep` that preserves `rScr.basisOutcomeProjector 0`. -/
theorem absorbCleanActive {Var : Type} [Fintype Var] [DecidableEq Var] {N k k' s₁ s : ℕ}
    {v : Var} {rAct : QRegister k N} {rKeep : QRegister k' N}
    {rScr₁ : QRegister s₁ N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {U_keep : Unitary (2 ^ k')} {P : DynamicCircuit Var N}
    (h : CleanRealizes v rAct rScr₁ U P)
    (hsub : rScr₁.image ⊆ rScr.image)
    (heq : (rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0 =
      (rKeep.embedUnitary U_keep).1 * rScr.basisOutcomeProjector 0)
    (hPres : rScr.basisOutcomeProjector 0 * ((rKeep.embedUnitary U_keep).1 *
        rScr.basisOutcomeProjector 0) =
      (rKeep.embedUnitary U_keep).1 * rScr.basisOutcomeProjector 0) :
    CleanRealizes v rKeep rScr U_keep P := by
  let Sdiff := rScr.image \ rScr₁.image
  have hunion : rScr.image = rScr₁.image ∪ Sdiff := (Finset.union_sdiff_of_subset hsub).symm
  have hsplit (Ψ : QCAssertion Var (2 ^ N)) :
      restrictAssertionToZeroAncilla Ψ rScr =
        restrictAssertionToCleanFinset (restrictAssertionToZeroAncilla Ψ rScr₁) Sdiff := by
    rw [restrictAssertionToZeroAncilla_eq_cleanFinset Ψ rScr,
      restrictAssertionToZeroAncilla_eq_cleanFinset Ψ rScr₁, hunion,
      restrictAssertionToCleanFinset_union]
  refine mkOfWpClean h.count_toff h.wp_update (fun Θ hΘ ↦ ?_) hPres
  rw [hsplit, h.wp_clean Θ hΘ, ← hsplit]
  funext σ
  apply Subtype.ext
  have hP₀_herm : (rScr.basisOutcomeProjector 0)ᴴ = rScr.basisOutcomeProjector 0 :=
    rScr.basisOutcomeProjector_conjTranspose 0
  have hadj : rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U).1ᴴ =
      rScr.basisOutcomeProjector 0 * (rKeep.embedUnitary U_keep).1ᴴ := by
    have hc := congrArg conjTranspose heq
    simpa only [Matrix.conjTranspose_mul, hP₀_herm] using hc
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hadj]

/-! ### Register Relocation (`CleanRealizes.onRegister`) -/

private noncomputable def envLiftMatrix {m N : ℕ} (placement : QRegister m N)
    (ψ : (placement.Environment → ZMod 2) → ℂ) : Matrix (Fin (2 ^ N)) (Fin (2 ^ m)) ℂ :=
  fun i l ↦ (if placement.extractIndex i = l then 1 else 0) * ψ (placement.basisSplitEquiv i).2

private theorem embedMatrix_mul_envLiftMatrix {m N : ℕ} (placement : QRegister m N)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (ψ : (placement.Environment → ZMod 2) → ℂ) :
    placement.embedMatrix K * envLiftMatrix placement ψ = envLiftMatrix placement ψ * K := by
  ext i l
  simp only [Matrix.mul_apply, QRegister.embedMatrix_apply, envLiftMatrix]
  let summand : Fin (2 ^ N) → ℂ := fun j ↦
    (K (placement.extractIndex i) (placement.extractIndex j) *
      if (placement.basisSplitEquiv i).2 = (placement.basisSplitEquiv j).2 then 1 else 0) *
    ((if placement.extractIndex j = l then 1 else 0) * ψ (placement.basisSplitEquiv j).2)
  rw [show (∑ j : Fin (2 ^ N), _) = ∑ j, summand j from rfl,
    ← placement.basisSplitEquiv.symm.sum_comp summand, Fintype.sum_prod_type]
  have hlocal (l' : Fin (2 ^ m)) (e : placement.Environment → ZMod 2) :
      placement.extractIndex (placement.basisSplitEquiv.symm (l', e)) = l' := by
    rw [← placement.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  simp only [summand, hlocal, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single l]
  · simp only [↓reduceIte, one_mul]
    rw [Finset.sum_eq_single (placement.basisSplitEquiv i).2]
    · simp only [↓reduceIte, mul_one]
      rw [Finset.sum_eq_single (placement.extractIndex i)]
      · simp [mul_comm]
      · intro l' _ hl'
        simp [Ne.symm hl']
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro e _ he
      simp [Ne.symm he]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l' _ hl'
    simp [hl']
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem envLiftMatrix_conjTranspose_mul_self {m N : ℕ} (placement : QRegister m N)
    (ψ : (placement.Environment → ZMod 2) → ℂ)
    (hψ : ∑ e, Complex.normSq (ψ e) = 1) :
    (envLiftMatrix placement ψ)ᴴ * envLiftMatrix placement ψ = 1 := by
  ext l₁ l₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, envLiftMatrix, Matrix.one_apply]
  let summand : Fin (2 ^ N) → ℂ := fun i ↦
    star ((if placement.extractIndex i = l₁ then 1 else 0) * ψ (placement.basisSplitEquiv i).2) *
    ((if placement.extractIndex i = l₂ then 1 else 0) * ψ (placement.basisSplitEquiv i).2)
  rw [show (∑ i : Fin (2 ^ N), _) = ∑ i, summand i from rfl,
    ← placement.basisSplitEquiv.symm.sum_comp summand, Fintype.sum_prod_type]
  have hlocal (l' : Fin (2 ^ m)) (e : placement.Environment → ZMod 2) :
      placement.extractIndex (placement.basisSplitEquiv.symm (l', e)) = l' := by
    rw [← placement.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  simp only [summand, hlocal, Equiv.apply_symm_apply]
  by_cases hll : l₁ = l₂
  · subst hll
    rw [Finset.sum_eq_single l₁]
    · simp only [↓reduceIte, one_mul, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast hψ
    · intro l' _ hl'
      simp [hl']
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [hll, ↓reduceIte]
    refine Finset.sum_eq_zero fun l' _ ↦ Finset.sum_eq_zero fun e _ ↦ ?_
    by_cases hl₁ : l' = l₁
    · subst hl₁; simp [hll]
    · simp [hl₁]

private noncomputable def pullbackAssertion {Var : Type} [Fintype Var] {m N : ℕ}
    (placement : QRegister m N) (ψ : (placement.Environment → ZMod 2) → ℂ)
    (hψ : ∑ e, Complex.normSq (ψ e) = 1)
    (Θ : QCAssertion Var (2 ^ N)) : QCAssertion Var (2 ^ m) :=
  fun σ ↦
    ⟨(Θ σ).1.conj (envLiftMatrix placement ψ)ᴴ,
      (Θ σ).1.conj_nonneg (envLiftMatrix placement ψ)ᴴ (Θ σ).2.1,
      (HermitianMat.conj_mono (Θ σ).2.2).trans
        (le_of_eq (HermitianMat.ext (by
          simp only [conj_apply_mat, mat_one, Matrix.mul_one, Matrix.conjTranspose_conjTranspose,
            envLiftMatrix_conjTranspose_mul_self placement ψ hψ])))⟩

@[simp]
private theorem pullbackAssertion_coe {Var : Type} [Fintype Var] {m N : ℕ}
    (placement : QRegister m N) (ψ : (placement.Environment → ZMod 2) → ℂ)
    (hψ : ∑ e, Complex.normSq (ψ e) = 1)
    (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    (pullbackAssertion placement ψ hψ Θ σ).1 =
      (Θ σ).1.conj (envLiftMatrix placement ψ)ᴴ := rfl

private theorem dynPaths_dynOnRegister {Var : Type} [Fintype Var] [DecidableEq Var] {m N : ℕ}
    (placement : QRegister m N) (P : DynamicCircuit Var m) (σ : Store Var) :
    dynPaths (dynOnRegister placement P) σ =
      (dynPaths P σ).map fun x ↦ (placement.embedMatrix x.1, x.2) := by
  induction P using DynamicCircuit.qcInd generalizing σ with
  | circuit c =>
      simp only [dynOnRegister_circuit, dynPaths_circuit, Circuit.eval_onRegister,
        QRegister.embedUnitary_val, List.map_cons, List.map_nil]
  | measure v r =>
      simp only [dynOnRegister_measure, dynPaths_measure, List.map_map]
      refine List.map_congr_left fun o _ ↦ ?_
      simp only [Function.comp_apply, QRegister.basisOutcomeProjector,
        QRegister.embedMatrix_compose]
  | qIf cond t f iht ihf =>
      simp only [dynOnRegister_qIf, dynPaths_qIf]
      by_cases hc : cond.holds σ <;> simp [hc, iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [dynOnRegister_seq, dynPaths_seq, ih₁, List.flatMap_map, List.map_flatMap]
      refine List.flatMap_congr fun x _ ↦ ?_
      rw [ih₂, List.map_map, List.map_map]
      refine List.map_congr_left fun y _ ↦ ?_
      simp only [Function.comp_apply, QRegister.embedMatrix_mul]

private theorem wp_dynOnRegister_pullback {Var : Type} [Fintype Var] [DecidableEq Var] {m N : ℕ}
    (placement : QRegister m N) (ψ : (placement.Environment → ZMod 2) → ℂ)
    (hψ : ∑ e, Complex.normSq (ψ e) = 1)
    (P : DynamicCircuit Var m) (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    (wp (dynOnRegister placement P).compile Θ σ).1.conj (envLiftMatrix placement ψ)ᴴ =
      (wp P.compile (pullbackAssertion placement ψ hψ Θ) σ).1 := by
  rw [wp_compile_eq_sum_dynPaths, wp_compile_eq_sum_dynPaths, dynPaths_dynOnRegister,
    conj_map_list_sum, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
  have hinter : placement.embedMatrix x.1 * envLiftMatrix placement ψ =
      envLiftMatrix placement ψ * x.1 :=
    embedMatrix_mul_envLiftMatrix placement x.1 ψ
  have hadj : (envLiftMatrix placement ψ)ᴴ * (placement.embedMatrix x.1)ᴴ =
      x.1ᴴ * (envLiftMatrix placement ψ)ᴴ := by
    have hc := congrArg conjTranspose hinter
    simpa only [Matrix.conjTranspose_mul] using hc
  simp only [Function.comp_apply, pullbackAssertion_coe, conj_conj]
  rw [hadj]

private theorem quadratic_envLiftMatrix_apply {m N : ℕ} (placement : QRegister m N)
    (D : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) (ψ : (placement.Environment → ZMod 2) → ℂ)
    (l₁ l₂ : Fin (2 ^ m)) :
    ((envLiftMatrix placement ψ)ᴴ * D * envLiftMatrix placement ψ) l₁ l₂ =
      ∑ e₁, ∑ e₂, star (ψ e₁) *
        D (placement.basisSplitEquiv.symm (l₁, e₁))
          (placement.basisSplitEquiv.symm (l₂, e₂)) * ψ e₂ := by
  have hlocal (l' : Fin (2 ^ m)) (e : placement.Environment → ZMod 2) :
      placement.extractIndex (placement.basisSplitEquiv.symm (l', e)) = l' := by
    rw [← placement.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  have hmul_right (i : Fin (2 ^ N)) :
      (D * envLiftMatrix placement ψ) i l₂ =
        ∑ e₂, D i (placement.basisSplitEquiv.symm (l₂, e₂)) * ψ e₂ := by
    simp only [Matrix.mul_apply, envLiftMatrix]
    let f₂ : Fin (2 ^ N) → ℂ := fun j ↦
      D i j * ((if placement.extractIndex j = l₂ then 1 else 0) * ψ (placement.basisSplitEquiv j).2)
    rw [show (∑ j : Fin (2 ^ N), _) = ∑ j, f₂ j from rfl,
      ← placement.basisSplitEquiv.symm.sum_comp f₂, Fintype.sum_prod_type]
    simp only [f₂, hlocal, Equiv.apply_symm_apply]
    rw [Finset.sum_eq_single l₂]
    · simp
    · intro l' _ hl'; simp [hl']
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [hmul_right]
  let f₁ : Fin (2 ^ N) → ℂ := fun i ↦
    (envLiftMatrix placement ψ)ᴴ l₁ i *
      ∑ e₂, D i (placement.basisSplitEquiv.symm (l₂, e₂)) * ψ e₂
  rw [show (∑ i : Fin (2 ^ N), _) = ∑ i, f₁ i from rfl,
    ← placement.basisSplitEquiv.symm.sum_comp f₁, Fintype.sum_prod_type]
  simp only [f₁, Matrix.conjTranspose_apply, envLiftMatrix, hlocal, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single l₁]
  · simp only [↓reduceIte, one_mul, Finset.mul_sum, mul_assoc]
  · intro l' _ hl'; simp [hl']
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem matrix_eq_of_envLiftMatrix_quad_eq {m N : ℕ} (placement : QRegister m N)
    {A B : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ}
    (hquad : ∀ ψ : (placement.Environment → ZMod 2) → ℂ,
      ∑ e, Complex.normSq (ψ e) = 1 →
        (envLiftMatrix placement ψ)ᴴ * A * envLiftMatrix placement ψ =
          (envLiftMatrix placement ψ)ᴴ * B * envLiftMatrix placement ψ) :
    A = B := by
  let D := A - B
  have hD0 : ∀ ψ : (placement.Environment → ZMod 2) → ℂ,
      ∑ e, Complex.normSq (ψ e) = 1 →
        (envLiftMatrix placement ψ)ᴴ * D * envLiftMatrix placement ψ = 0 := by
    intro ψ hψ
    simp only [D, Matrix.mul_sub, Matrix.sub_mul, hquad ψ hψ, sub_self]
  have hdiag (l₁ l₂ : Fin (2 ^ m)) (e : placement.Environment → ZMod 2) :
      D (placement.basisSplitEquiv.symm (l₁, e))
        (placement.basisSplitEquiv.symm (l₂, e)) = 0 := by
    let ψ : (placement.Environment → ZMod 2) → ℂ := Pi.single e 1
    have hψ : ∑ e', Complex.normSq (ψ e') = 1 := by
      rw [Finset.sum_eq_single e]
      · simp [ψ]
      · intro e' _ he'; simp [ψ, Pi.single_eq_of_ne he']
      · intro h; exact absurd (Finset.mem_univ _) h
    have h0 := congrFun (congrFun (hD0 ψ hψ) l₁) l₂
    rw [quadratic_envLiftMatrix_apply, Matrix.zero_apply] at h0
    rw [Finset.sum_eq_single e] at h0
    · rw [Finset.sum_eq_single e] at h0
      · simpa [ψ] using h0
      · intro e₂ _ he₂; simp [ψ, Pi.single_eq_of_ne he₂]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro e₁ _ he₁; simp [ψ, Pi.single_eq_of_ne he₁]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hoff (l₁ l₂ : Fin (2 ^ m)) (e₁ e₂ : placement.Environment → ZMod 2) (hne : e₁ ≠ e₂)
      (c : ℂ) (hc : Complex.normSq c = 1) :
      c * D (placement.basisSplitEquiv.symm (l₁, e₁))
          (placement.basisSplitEquiv.symm (l₂, e₂)) +
        star c * D (placement.basisSplitEquiv.symm (l₁, e₂))
          (placement.basisSplitEquiv.symm (l₂, e₁)) = 0 := by
    let r : ℂ := (√(1 / 2) : ℝ)
    have hr_norm : Complex.normSq r = 1 / 2 := by
      dsimp only [r]
      rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hr_star_mul : star r * r = (1 / 2 : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hr_norm]
      norm_num
    let ψ : (placement.Environment → ZMod 2) → ℂ :=
      fun e ↦ if e = e₁ then r else if e = e₂ then r * c else 0
    have hψ : ∑ e, Complex.normSq (ψ e) = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₁),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ e₂⟩)]
      have hrest : ∑ x ∈ (Finset.univ.erase e₁).erase e₂, Complex.normSq (ψ x) = 0 := by
        refine Finset.sum_eq_zero fun x hx ↦ ?_
        have hx2 : x ≠ e₂ := (Finset.mem_erase.mp hx).1
        have hx1 : x ≠ e₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        simp [ψ, hx1, hx2]
      rw [hrest, add_zero]
      simp only [ψ, ↓reduceIte, hne.symm, map_mul, hr_norm, hc]
      norm_num
    have h0 := congrFun (congrFun (hD0 ψ hψ) l₁) l₂
    rw [quadratic_envLiftMatrix_apply, Matrix.zero_apply] at h0
    have hsum2 {f : (placement.Environment → ZMod 2) → ℂ}
        (hf : ∀ x, x ≠ e₁ → x ≠ e₂ → f x = 0) :
        ∑ x, f x = f e₁ + f e₂ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₁),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ e₂⟩)]
      have hr0 : ∑ x ∈ (Finset.univ.erase e₁).erase e₂, f x = 0 :=
        Finset.sum_eq_zero fun x hx ↦
          hf x (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1 (Finset.mem_erase.mp hx).1
      rw [hr0, add_zero]
    rw [hsum2 (fun x hx1 hx2 ↦ by simp [ψ, hx1, hx2]),
      hsum2 (fun x hx1 hx2 ↦ by simp [ψ, hx1, hx2]),
      hsum2 (fun x hx1 hx2 ↦ by simp [ψ, hx1, hx2])] at h0
    simp only [ψ, ↓reduceIte, hne.symm, hdiag, mul_zero, zero_mul, add_zero, zero_add,
      star_mul] at h0
    have hlin : (star r * r) *
        (c * D (placement.basisSplitEquiv.symm (l₁, e₁))
            (placement.basisSplitEquiv.symm (l₂, e₂)) +
          star c * D (placement.basisSplitEquiv.symm (l₁, e₂))
            (placement.basisSplitEquiv.symm (l₂, e₁))) = 0 := by
      linear_combination h0
    rw [hr_star_mul] at hlin
    linear_combination 2 * hlin
  have hentry (i j : Fin (2 ^ N)) : D i j = 0 := by
    obtain ⟨⟨l₁, e₁⟩, rfl⟩ := placement.basisSplitEquiv.symm.surjective i
    obtain ⟨⟨l₂, e₂⟩, rfl⟩ := placement.basisSplitEquiv.symm.surjective j
    by_cases he : e₁ = e₂
    · subst he; exact hdiag l₁ l₂ e₁
    · have h1 := hoff l₁ l₂ e₁ e₂ he 1 (by simp)
      have hI := hoff l₁ l₂ e₁ e₂ he Complex.I (by simp)
      simp only [one_mul, star_one, Complex.star_def, Complex.conj_I] at h1 hI
      have hI_prod :
          Complex.I *
            (D (placement.basisSplitEquiv.symm (l₁, e₁))
                (placement.basisSplitEquiv.symm (l₂, e₂)) -
              D (placement.basisSplitEquiv.symm (l₁, e₂))
                (placement.basisSplitEquiv.symm (l₂, e₁))) = 0 := by
        linear_combination hI
      have hsub_zero := (mul_eq_zero.mp hI_prod).resolve_left Complex.I_ne_zero
      linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * hsub_zero
  ext i j
  exact sub_eq_zero.mp (hentry i j)

private theorem hermitianMat_eq_of_conj_envLiftMatrix_eq {m N : ℕ}
    (placement : QRegister m N) {H₁ H₂ : HermitianMat (Fin (2 ^ N)) ℂ}
    (h : ∀ ψ : (placement.Environment → ZMod 2) → ℂ,
      ∑ e, Complex.normSq (ψ e) = 1 →
        H₁.conj (envLiftMatrix placement ψ)ᴴ = H₂.conj (envLiftMatrix placement ψ)ᴴ) :
    H₁ = H₂ := by
  apply HermitianMat.ext
  refine matrix_eq_of_envLiftMatrix_quad_eq placement fun ψ hψ ↦ ?_
  have hm := congrArg HermitianMat.mat (h ψ hψ)
  simpa only [conj_apply_mat, Matrix.conjTranspose_conjTranspose] using hm

/-- Relocate a local `m`-wire `CleanRealizes` contract onto an `N`-wire ambient system through
`placement : QRegister m N`. -/
theorem onRegister {Var : Type} [Fintype Var] [DecidableEq Var] {m N k s : ℕ}
    (placement : QRegister m N)
    {v : Var} {rAct : QRegister k m} {rScr : QRegister s m}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var m}
    (h : CleanRealizes v rAct rScr U P) :
    CleanRealizes v (placement.compose rAct) (placement.compose rScr) U
      (dynOnRegister placement P) := by
  have hpull_upd (Θ : QCAssertion Var (2 ^ N))
      (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
      (ψ : (placement.Environment → ZMod 2) → ℂ) (hψ : ∑ e, Complex.normSq (ψ e) = 1) :
      ∀ σ val, pullbackAssertion placement ψ hψ Θ (Function.update σ v val) =
        pullbackAssertion placement ψ hψ Θ σ := by
    intro σ val
    simp only [pullbackAssertion, hΘ σ val]
  have hpull_restrict (Ψ : QCAssertion Var (2 ^ N))
      (ψ : (placement.Environment → ZMod 2) → ℂ) (hψ : ∑ e, Complex.normSq (ψ e) = 1) :
      pullbackAssertion placement ψ hψ (restrictAssertionToZeroAncilla Ψ (placement.compose rScr)) =
        restrictAssertionToZeroAncilla (pullbackAssertion placement ψ hψ Ψ) rScr := by
    funext σ
    apply Subtype.ext
    have hP : (placement.compose rScr).basisOutcomeProjector 0 =
        placement.embedMatrix (rScr.basisOutcomeProjector 0) :=
      QRegister.embedMatrix_compose placement rScr (compProj 0)
    have hinter : placement.embedMatrix (rScr.basisOutcomeProjector 0) *
          envLiftMatrix placement ψ =
        envLiftMatrix placement ψ * rScr.basisOutcomeProjector 0 :=
      embedMatrix_mul_envLiftMatrix placement (rScr.basisOutcomeProjector 0) ψ
    have hadj : (envLiftMatrix placement ψ)ᴴ *
          placement.embedMatrix (rScr.basisOutcomeProjector 0) =
        rScr.basisOutcomeProjector 0 * (envLiftMatrix placement ψ)ᴴ := by
      have hc := congrArg conjTranspose hinter
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        ← QRegister.embedMatrix_conjTranspose, rScr.basisOutcomeProjector_conjTranspose 0] at hc
      exact hc
    simp only [pullbackAssertion_coe, restrictAssertionToZeroAncilla_coe, conj_conj, hP]
    rw [hadj]
  have hstep_wp (Φ : QCAssertion Var (2 ^ N)) (σ : Store Var)
      (ψ : (placement.Environment → ZMod 2) → ℂ) (hψ : ∑ e, Complex.normSq (ψ e) = 1) :
      (restrictAssertionToZeroAncilla (wp (dynOnRegister placement P).compile Φ)
        (placement.compose rScr) σ).1.conj (envLiftMatrix placement ψ)ᴴ =
      (restrictAssertionToZeroAncilla
        (wp P.compile (pullbackAssertion placement ψ hψ Φ)) rScr σ).1 := by
    rw [← pullbackAssertion_coe placement ψ hψ _ σ, hpull_restrict]
    simp only [restrictAssertionToZeroAncilla_coe, pullbackAssertion_coe,
      wp_dynOnRegister_pullback placement ψ hψ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [count_dynOnRegister] using h.count_toff
  · intro Θ hΘ σ val
    apply Subtype.ext
    refine hermitianMat_eq_of_conj_envLiftMatrix_eq placement fun ψ hψ ↦ ?_
    rw [wp_dynOnRegister_pullback placement ψ hψ P Θ (Function.update σ v val),
      wp_dynOnRegister_pullback placement ψ hψ P Θ σ,
      h.wp_update (pullbackAssertion placement ψ hψ Θ) (hpull_upd Θ hΘ ψ hψ) σ val]
  · intro Θ hΘ
    funext σ
    apply Subtype.ext
    refine hermitianMat_eq_of_conj_envLiftMatrix_eq placement fun ψ hψ ↦ ?_
    have hR : (restrictAssertionToZeroAncilla
          (qcWpQAssign ((placement.compose rAct).embedUnitary U) Θ)
          (placement.compose rScr) σ).1.conj (envLiftMatrix placement ψ)ᴴ =
        (restrictAssertionToZeroAncilla
          (qcWpQAssign (rAct.embedUnitary U) (pullbackAssertion placement ψ hψ Θ)) rScr σ).1 := by
      rw [← pullbackAssertion_coe placement ψ hψ _ σ, hpull_restrict]
      have hinter : placement.embedMatrix (rAct.embedMatrix U.1) * envLiftMatrix placement ψ =
          envLiftMatrix placement ψ * rAct.embedMatrix U.1 :=
        embedMatrix_mul_envLiftMatrix placement (rAct.embedMatrix U.1) ψ
      have hadj : (envLiftMatrix placement ψ)ᴴ *
            (placement.embedMatrix (rAct.embedMatrix U.1))ᴴ =
          (rAct.embedMatrix U.1)ᴴ * (envLiftMatrix placement ψ)ᴴ := by
        have hc := congrArg conjTranspose hinter
        simpa only [Matrix.conjTranspose_mul] using hc
      simp only [restrictAssertionToZeroAncilla_coe, pullbackAssertion_coe, qcWpQAssign,
        qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        QRegister.embedUnitary_compose, QRegister.embedUnitary_val, conj_conj]
      rw [hadj]
    rw [hstep_wp Θ σ ψ hψ, hR,
      h.wp_clean (pullbackAssertion placement ψ hψ Θ) (hpull_upd Θ hΘ ψ hψ)]
  · intro Θ
    funext σ
    apply Subtype.ext
    refine hermitianMat_eq_of_conj_envLiftMatrix_eq placement fun ψ hψ ↦ ?_
    rw [hstep_wp (restrictAssertionToZeroAncilla Θ (placement.compose rScr)) σ ψ hψ,
      hstep_wp Θ σ ψ hψ, hpull_restrict Θ ψ hψ,
      h.wp_clean_post (pullbackAssertion placement ψ hψ Θ)]

/-! ### Top-Level Bridge to `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace` -/

end CleanRealizes

/-- Computational-basis ket `|β⟩` indexed by wire bit assignments `β : BitAssignment n`. -/
noncomputable abbrev ket {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

private theorem single_eq_ket {n : ℕ} (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket, basisState]

/-- Two `2 ^ n × 2 ^ n` matrices are equal iff their `mulVec` actions agree on every `ket β`. -/
theorem matrix_ext_ket {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have hij := congrFun (h (basisBits n j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using hij

/-- Sign `(-1)^b : ℂ` associated with a `ZMod 2` bit `b`. -/
abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

/-- Real constant `1 / √2` coerced to `ℂ`. -/
noncomputable def sqrtHalf : ℂ := (√(1 / 2) : ℝ)

theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

private theorem zmod2_add_self (b : ZMod 2) : b + b = 0 := by
  rcases bit_cases b with rfl | rfl <;> rfl

private theorem zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a := by
  rw [add_assoc, zmod2_add_self, add_zero]

@[simp]
theorem bitSign_zero : bitSign 0 = 1 := rfl

@[simp]
theorem bitSign_one : bitSign 1 = -1 := rfl

theorem bitSign_mul_self (b : ZMod 2) : bitSign b * bitSign b = 1 := by
  rcases bit_cases b with rfl | rfl <;> norm_num [bitSign]

@[simp]
theorem star_bitSign (b : ZMod 2) : star (bitSign b) = bitSign b := by
  rcases bit_cases b with rfl | rfl <;> simp [bitSign]

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitSign, one_add_one_zmod2]

theorem sqrtHalf_mul_sqrtHalf : sqrtHalf * sqrtHalf = 1 / 2 := by
  dsimp only [sqrtHalf]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  push_cast
  ring

@[simp]
theorem star_sqrtHalf : star sqrtHalf = sqrtHalf := by
  dsimp only [sqrtHalf]
  exact Complex.conj_ofReal _

private noncomputable def writeReg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))

private theorem writeReg_eq_update {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    simp only [writeReg, QRegister.basisBits_replaceIndex_apply, basisBits_basisBitsEquiv_symm]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · simp only [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw,
      basisBits_basisBitsEquiv_symm]
    exact (Function.update_of_ne (fun h ↦ hw ⟨i₀, h.symm⟩) _ _).symm

private theorem embedMatrix_mulVec_ket {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k),
        A l ((basisBits k).symm (fun i ↦ β (r i))) • ket (writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits n).symm β) =
      (basisBits k).symm (fun i ↦ β (r i)) := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

theorem singleton_embedMatrix_mulVec_ket {n : ℕ} (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
      A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hloc : ((basisBits 1).symm (fun i ↦ β (QRegister.singleton q i)) : Fin 2) =
      if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [embedMatrix_mulVec_ket, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]

theorem ket_X {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, one_add_one_zmod2]

theorem ket_Z {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = bitSign (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

theorem ket_H {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) =
      sqrtHalf • (ket (Function.update β q 0) +
        bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((√(1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, sqrtHalf, smul_add, Complex.real_smul]

theorem ket_projector {n : ℕ} (q : Wire n) (o : Fin 2) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector o).mulVec (ket β) =
      if β q = (o.val : ZMod 2) then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  have h : ∀ (b : ZMod 2) (o : Fin 2),
      (((basisBits 1).symm (fun _ ↦ b) : Fin 2) = o ↔ b = (o.val : ZMod 2)) := by decide
  have hext : (QRegister.singleton q).extractIndex ((basisBits n).symm β) =
      (basisBits 1).symm (fun _ ↦ β q) := by
    simp [QRegister.extractIndex]
  simp only [hext]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ((h _ _).1 h1) h2 |
    exact absurd ((h _ _).2 h2) h1

theorem ket_projector_zero {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 :=
  ket_projector q 0 β

theorem ket_projector_one {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (ket β) =
      if β q = 1 then ket β else 0 :=
  ket_projector q 1 β

theorem ket_cleanFinsetProj {n : ℕ} (S : Finset (Wire n)) (β : BitAssignment n) :
    (cleanFinsetProj S).mulVec (ket β) = if ∀ w ∈ S, β w = 0 then ket β else 0 := by
  funext i
  simp only [cleanFinsetProj, ket, basisState, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
    Pi.single_apply]
  rw [Finset.sum_eq_single ((basisBits n).symm β)]
  · by_cases hi : i = (basisBits n).symm β
    · subst hi
      simp only [↓reduceIte, basisBits_basisBitsEquiv_symm, mul_one]
      split_ifs <;> simp
    · simp only [hi, ↓reduceIte, zero_mul]
      split_ifs <;> simp [hi]
  · intro j _ hj
    simp only [hj, ↓reduceIte, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Diagonal phase-flip unitary multiplying each computational basis state `|β⟩` by
`(-1)^(f β)`. -/
noncomputable def phaseFlipUnitary {n : ℕ} (f : BitAssignment n → ZMod 2) : Unitary (2 ^ n) :=
  ⟨Matrix.diagonal (fun i : Fin (2 ^ n) ↦ bitSign (f (basisBits n i))), by
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    dsimp only [bitSign]
    split <;> simp⟩

theorem phaseFlipUnitary_val {n : ℕ} (f : BitAssignment n → ZMod 2) :
    (phaseFlipUnitary f).1 =
      Matrix.diagonal (fun i : Fin (2 ^ n) ↦ bitSign (f (basisBits n i))) := rfl

theorem phaseFlipUnitary_mulVec_ket {n : ℕ} (f : BitAssignment n → ZMod 2)
    (β : BitAssignment n) :
    (phaseFlipUnitary f).1.mulVec (ket β) = bitSign (f β) • ket β := by
  funext i
  simp only [phaseFlipUnitary_val, ket, basisState, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single ((basisBits n).symm β)]
  · by_cases hi : i = (basisBits n).symm β
    · subst hi; simp
    · simp [hi]
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp]
theorem phaseFlipUnitary_zero {n : ℕ} :
    phaseFlipUnitary (fun _ : BitAssignment n ↦ 0) = 1 := by
  apply Subtype.ext
  simp [phaseFlipUnitary_val]

theorem phaseFlipUnitary_add {n : ℕ} (f₁ f₂ : BitAssignment n → ZMod 2) :
    phaseFlipUnitary (fun β ↦ f₁ β + f₂ β) = phaseFlipUnitary f₁ * phaseFlipUnitary f₂ := by
  apply Subtype.ext
  simp only [phaseFlipUnitary_val, Submonoid.coe_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact bitSign_add _ _

@[simp]
theorem phaseFlipUnitary_mul_self {n : ℕ} (f : BitAssignment n → ZMod 2) :
    phaseFlipUnitary f * phaseFlipUnitary f = 1 := by
  rw [← phaseFlipUnitary_add]
  have hzero : (fun β : BitAssignment n ↦ f β + f β) = fun _ ↦ 0 := by
    funext β; exact zmod2_add_self (f β)
  rw [hzero, phaseFlipUnitary_zero]

@[simp]
theorem phaseFlipUnitary_conjTranspose {n : ℕ} (f : BitAssignment n → ZMod 2) :
    (phaseFlipUnitary f).1ᴴ = (phaseFlipUnitary f).1 := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [phaseFlipUnitary_val]
  · simp [phaseFlipUnitary_val, hij, Ne.symm hij]

theorem phaseFlipUnitary_comm_cleanFinsetProj {n : ℕ} (f : BitAssignment n → ZMod 2)
    (S : Finset (Wire n)) :
    (phaseFlipUnitary f).1 * cleanFinsetProj S = cleanFinsetProj S * (phaseFlipUnitary f).1 := by
  simp only [phaseFlipUnitary_val, cleanFinsetProj, Matrix.diagonal_mul_diagonal, mul_comm]

theorem embedUnitary_phaseFlipUnitary {k n : ℕ} (r : QRegister k n)
    (fLoc : BitAssignment k → ZMod 2) :
    r.embedUnitary (phaseFlipUnitary fLoc) =
      phaseFlipUnitary (fun β ↦ fLoc (fun i ↦ β (r i))) := by
  apply Subtype.ext
  rw [QRegister.embedUnitary_val, phaseFlipUnitary_val, phaseFlipUnitary_val,
    r.embedMatrix_diagonal]
  congr 1
  funext global
  congr 2
  funext i
  exact r.basisBits_extractIndex global i

/-- Computational-basis permutation toggling wire `q` by `f β` (`f` independent of `q`). -/
noncomputable def xorWirePerm {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) : Equiv.Perm (Fin (2 ^ n)) :=
  (basisBits n).trans
    ({ toFun := fun β ↦ Function.update β q (β q + f β)
       invFun := fun β ↦ Function.update β q (β q + f β)
       left_inv := fun β ↦ by
         dsimp only
         rw [Function.update_idem, Function.update_self, hf β (β q + f β),
           zmod2_add_cancel_right, Function.update_eq_self]
       right_inv := fun β ↦ by
         dsimp only
         rw [Function.update_idem, Function.update_self, hf β (β q + f β),
           zmod2_add_cancel_right, Function.update_eq_self] } :
      Equiv.Perm (BitAssignment n)) |>.trans (basisBits n).symm

/-- Reversible classical XOR oracle `|β⟩ ↦ |Function.update β q (β q + f β)⟩` on wire `q` for any
Boolean function `f` independent of `q`. -/
noncomputable def xorWireUnitary {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) : Unitary (2 ^ n) :=
  Operator.permutationUnitary (xorWirePerm q f hf)

theorem xorWireUnitary_mulVec_ket {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) (β : BitAssignment n) :
    (xorWireUnitary q f hf).1.mulVec (ket β) = ket (Function.update β q (β q + f β)) := by
  rw [xorWireUnitary, ket, basisState, Operator.permutationUnitary_mulVec_single]
  simp [xorWirePerm, ket, basisState]

@[simp]
theorem xorWireUnitary_mul_self {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) :
    xorWireUnitary q f hf * xorWireUnitary q f hf = 1 := by
  apply Subtype.ext
  refine matrix_ext_ket fun β ↦ ?_
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, xorWireUnitary_mulVec_ket,
    xorWireUnitary_mulVec_ket, Function.update_idem, Function.update_self, hf β (β q + f β),
    zmod2_add_cancel_right, Function.update_eq_self, Submonoid.coe_one, Matrix.one_mulVec]

@[simp]
theorem xorWireUnitary_conjTranspose {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) :
    (xorWireUnitary q f hf).1ᴴ = (xorWireUnitary q f hf).1 := by
  have hunit : (xorWireUnitary q f hf).1ᴴ * (xorWireUnitary q f hf).1 = 1 :=
    congrArg Subtype.val (Unitary.star_mul_self (xorWireUnitary q f hf))
  have hsq : (xorWireUnitary q f hf).1 * (xorWireUnitary q f hf).1 = 1 :=
    congrArg Subtype.val (xorWireUnitary_mul_self q f hf)
  calc (xorWireUnitary q f hf).1ᴴ
      = (xorWireUnitary q f hf).1ᴴ * ((xorWireUnitary q f hf).1 * (xorWireUnitary q f hf).1) := by
          rw [hsq, Matrix.mul_one]
    _ = ((xorWireUnitary q f hf).1ᴴ * (xorWireUnitary q f hf).1) * (xorWireUnitary q f hf).1 := by
          rw [Matrix.mul_assoc]
    _ = (xorWireUnitary q f hf).1 := by rw [hunit, Matrix.one_mul]

/-- Measure wire `q` in the computational basis into `v` and run `onOne` iff `σ v ≠ 0`. -/
def remeasureIfDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (onOne : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.measure v (QRegister.singleton q)) (qcQIf (fun σ ↦ σ v) onOne .identity)

@[simp]
theorem count_remeasureIfDyn {Var : Type} {n a : ℕ} (g : PrimitiveGate a) (v : Var) (q : Wire n)
    (onOne : DynamicCircuit Var n) :
    (remeasureIfDyn v q onOne).count g = onOne.count g := by
  simp [remeasureIfDyn]

theorem wp_remeasureIfDyn_apply {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (onOne : DynamicCircuit Var n)
    (Θ : QCAssertion Var (2 ^ n)) (σ : Store Var) :
    (wp (remeasureIfDyn v q onOne).compile Θ σ).1 =
      (Θ (Function.update σ v 0)).1.conj ((QRegister.singleton q).basisOutcomeProjector 0) +
        (wp onOne.compile Θ (Function.update σ v 1)).1.conj
          ((QRegister.singleton q).basisOutcomeProjector 1) := by
  cases nonempty_fintype Var
  have hsubst0 : Store.subst σ v 0 = Function.update σ v 0 := by
    funext y; simp [Store.subst, Function.update]
  have hsubst1 : Store.subst σ v 1 = Function.update σ v 1 := by
    funext y; simp [Store.subst, Function.update]
  simp only [remeasureIfDyn, DynamicCircuit.compile_seq, DynamicCircuit.compile_measure,
    DynamicCircuit.compile_qIf, DynamicCircuit.compile_identity, QProg.measureRegister, wp_qSeq,
      wp_qIf, wp_skip, qc_wp_qMeasure',
    qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe, QCAssertion.subst_apply,
    CompleteMeasurement.toMeasurement_coe, QRegister.computationalBasisMeasurement_apply,
    qc_qMeasure_outcome_herm_eq_conj]
  change ∑ o : Fin 2, _ = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    QRegister.basisOutcomeProjector_conjTranspose]
  rw [hsubst0, hsubst1]
  simp only [Function.update_self, ne_eq, not_true_eq_false, ↓reduceIte, one_ne_zero,
    not_false_eq_true]

/-- Because `remeasureIfDyn` immediately overwrites `v` with the measurement outcome on `q`, its
weakest precondition is unconditionally invariant under updating `v` for ALL postconditions `Θ`. -/
theorem wp_remeasureIfDyn_update_self {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (onOne : DynamicCircuit Var n)
    (Θ : QCAssertion Var (2 ^ n)) (σ : Store Var) (val : ℤ) :
    (wp (remeasureIfDyn v q onOne).compile Θ) (Function.update σ v val) =
      (wp (remeasureIfDyn v q onOne).compile Θ) σ := by
  apply Subtype.ext
  rw [wp_remeasureIfDyn_apply, wp_remeasureIfDyn_apply, Function.update_idem, Function.update_idem]

/-- Master `0`-branch X-measurement Kraus identity on `cleanFinsetProj S` (`q ∈ S`). -/
theorem xMeas_kraus_zero {n : ℕ} (q : Wire n) (S : Finset (Wire n)) (hq : q ∈ S)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β) :
    ((QRegister.singleton q).basisOutcomeProjector 0 * (Circuit.H q).eval.1) *
        (xorWireUnitary q f hf).1 * cleanFinsetProj S =
      sqrtHalf • cleanFinsetProj S := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec, ket_cleanFinsetProj]
  split_ifs with hS
  · have hβq : β q = 0 := hS q hq
    have hupd0 : Function.update β q 0 = β := by rw [← hβq, Function.update_eq_self]
    rw [xorWireUnitary_mulVec_ket, hβq, zero_add, ket_H, Function.update_idem,
      Function.update_self, hupd0, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      ket_projector_zero, ket_projector_zero, hβq, Function.update_self]
    simp only [↓reduceIte, one_ne_zero, smul_zero, add_zero]
  · simp only [Matrix.mulVec_zero, smul_zero]

/-- Master `1`-branch X-measurement Kraus identity (including `X q` reset to `|0⟩`) on
`cleanFinsetProj S` (`q ∈ S`). -/
theorem xMeas_kraus_one {n : ℕ} (q : Wire n) (S : Finset (Wire n)) (hq : q ∈ S)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β) :
    ((Circuit.X q).eval.1 * (QRegister.singleton q).basisOutcomeProjector 1 *
        (Circuit.H q).eval.1) * (xorWireUnitary q f hf).1 * cleanFinsetProj S =
      sqrtHalf • (cleanFinsetProj S * (phaseFlipUnitary f).1) := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    phaseFlipUnitary_mulVec_ket, Matrix.mulVec_smul, ket_cleanFinsetProj]
  split_ifs with hS
  · have hβq : β q = 0 := hS q hq
    have hupd0 : Function.update β q 0 = β := by rw [← hβq, Function.update_eq_self]
    rw [xorWireUnitary_mulVec_ket, hβq, zero_add, ket_H, Function.update_idem,
      Function.update_self, hupd0, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.mulVec_smul, ket_projector_one, ket_projector_one, hβq, Function.update_self]
    simp only [zero_ne_one, ↓reduceIte, zero_add]
    rw [Matrix.mulVec_smul, ket_X, Function.update_idem, Function.update_self,
      one_add_one_zmod2, Function.update_idem, hupd0]
  · simp only [Matrix.mulVec_zero, smul_zero]

private theorem xMeas_kraus_zero_adj {n : ℕ} (q : Wire n) (S : Finset (Wire n)) (hq : q ∈ S)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β) :
    cleanFinsetProj S * (xorWireUnitary q f hf).1ᴴ * (Circuit.H q).eval.1ᴴ *
        (QRegister.singleton q).basisOutcomeProjector 0 =
      sqrtHalf • cleanFinsetProj S := by
  have hc := congrArg conjTranspose (xMeas_kraus_zero q S hq f hf)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_sqrtHalf,
    cleanFinsetProj_conjTranspose, QRegister.basisOutcomeProjector_conjTranspose,
    ← Matrix.mul_assoc] using hc

private theorem xMeas_kraus_one_adj {n : ℕ} (q : Wire n) (S : Finset (Wire n)) (hq : q ∈ S)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β) :
    cleanFinsetProj S * (xorWireUnitary q f hf).1ᴴ * (Circuit.H q).eval.1ᴴ *
        (QRegister.singleton q).basisOutcomeProjector 1 * (Circuit.X q).eval.1ᴴ =
      (sqrtHalf • (phaseFlipUnitary f).1) * cleanFinsetProj S := by
  have hc := congrArg conjTranspose (xMeas_kraus_one q S hq f hf)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_sqrtHalf,
    cleanFinsetProj_conjTranspose, phaseFlipUnitary_conjTranspose,
    QRegister.basisOutcomeProjector_conjTranspose, Matrix.smul_mul, ← Matrix.mul_assoc] using hc

private theorem conj_sqrtHalf_smul_add_self {d : ℕ} (H : HermitianMat (Fin d) ℂ)
    (M : Operator d) :
    H.conj (sqrtHalf • M) + H.conj (sqrtHalf • M) = H.conj M := by
  apply HermitianMat.ext
  ext i j
  simp only [mat_add, conj_apply_mat, Matrix.conjTranspose_smul, star_sqrtHalf,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination 2 * ((M * H.mat * Mᴴ) i j * sqrtHalf_mul_sqrtHalf)

/-! ### Form A: Direct Phase-Fixup Wire Uncompute (`xMeasUnloadWireDyn`) & Chunked Tree -/

/-- Uncompute a single entangled wire `q` (`|β⟩ ↦ |Function.update β q (β q + f β)⟩`) back to `|0⟩`
using `H q`, computational-basis measurement into `v`, and on `σ v ≠ 0`: `X q ;; fixup` (`0` extra
`T` gates beyond `fixup.count .T`). -/
def xMeasUnloadWireDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (fixup : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (.H q)) (remeasureIfDyn v q (.seq (.circuit (.X q)) fixup))

@[simp]
theorem count_xMeasUnloadWireDyn_t {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (fixup : DynamicCircuit Var n) :
    (xMeasUnloadWireDyn v q fixup).count PrimitiveGate.T = fixup.count PrimitiveGate.T := by
  simp [xMeasUnloadWireDyn]

@[simp]
theorem count_xMeasUnloadWireDyn_toff {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (fixup : DynamicCircuit Var n) :
    (xMeasUnloadWireDyn v q fixup).count PrimitiveGate.TOFF = fixup.count PrimitiveGate.TOFF := by
  simp [xMeasUnloadWireDyn]

theorem wp_xMeasUnloadWireDyn_update_self {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (fixup : DynamicCircuit Var n)
    (Θ : QCAssertion Var (2 ^ n)) (σ : Store Var) (val : ℤ) :
    (wp (xMeasUnloadWireDyn v q fixup).compile Θ) (Function.update σ v val) =
      (wp (xMeasUnloadWireDyn v q fixup).compile Θ) σ := by
  cases nonempty_fintype Var
  simp only [xMeasUnloadWireDyn, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp,
    DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, wp_remeasureIfDyn_update_self]

/-- Master `cleanFinsetProj` cancellation step for `xorWireUnitary q f hf` followed by
`xMeasUnloadWireDyn v q fixup`. -/
theorem restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (S : Finset (Wire n)) (hq : q ∈ S)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β)
    (fixup : DynamicCircuit Var n) (Θ : QCAssertion Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (hFix : restrictAssertionToCleanFinset (wp fixup.compile Θ) S =
      restrictAssertionToCleanFinset (qcWpQAssign (phaseFlipUnitary f) Θ) S) :
    restrictAssertionToCleanFinset
      (qcWpQAssign (xorWireUnitary q f hf) (wp (xMeasUnloadWireDyn v q fixup).compile Θ)) S =
      restrictAssertionToCleanFinset Θ S := by
  funext σ
  apply Subtype.ext
  have hFix1 : (wp fixup.compile Θ (Function.update σ v 1)).1.conj (cleanFinsetProj S) =
      (Θ σ).1.conj (cleanFinsetProj S * (phaseFlipUnitary f).1) := by
    have hc := congrArg Subtype.val (congrFun hFix (Function.update σ v 1))
    simpa only [restrictAssertionToCleanFinset_coe, qcWpQAssign, qcQAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      phaseFlipUnitary_conjTranspose, conj_conj, hΘ σ 1] using hc
  have hcancel_zf : (sqrtHalf • (phaseFlipUnitary f).1) *
      (cleanFinsetProj S * (phaseFlipUnitary f).1) = sqrtHalf • cleanFinsetProj S := by
    have hsq : (phaseFlipUnitary f).1 * (phaseFlipUnitary f).1 = 1 :=
      congrArg Subtype.val (phaseFlipUnitary_mul_self f)
    rw [Matrix.smul_mul, ← Matrix.mul_assoc, phaseFlipUnitary_comm_cleanFinsetProj,
      Matrix.mul_assoc, hsq, Matrix.mul_one]
  simp only [restrictAssertionToCleanFinset_coe, xMeasUnloadWireDyn, DynamicCircuit.compile_seq,
    DynamicCircuit.compile_circuit, wp, DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign,
    qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    wp_remeasureIfDyn_apply, map_add, conj_conj, ← Matrix.mul_assoc, hΘ σ 0]
  rw [xMeas_kraus_zero_adj q S hq f hf, xMeas_kraus_one_adj q S hq f hf, ← conj_conj, hFix1,
    conj_conj, hcancel_zf, conj_sqrtHalf_smul_add_self]

/-- Tail sub-register dropping wire `0` from `QRegister (c + 1) n`. -/
def qRegTail {c n : ℕ} (r : QRegister (c + 1) n) : QRegister c n :=
  ⟨fun i ↦ r i.succ, fun _ _ h ↦ Fin.succ_injective _ (r.wires.injective h)⟩

/-- Bitwise specification of `xorChunkUnitary r fs` on computational basis assignments. -/
noncomputable def xorRegBits {n : ℕ} :
    {c : ℕ} → QRegister c n → (Fin c → BitAssignment n → ZMod 2) → BitAssignment n → BitAssignment n
  | 0, _, _, β => β
  | _ + 1, r, fs, β =>
      Function.update (xorRegBits (qRegTail r) (fun i ↦ fs i.succ) β) (r 0)
        (β (r 0) + fs 0 β)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit
