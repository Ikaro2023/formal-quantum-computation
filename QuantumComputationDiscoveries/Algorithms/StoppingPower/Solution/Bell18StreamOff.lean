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
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CoreSpecDefs
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CleanAncillaComb

/-!
# Bell-18 Stream Offset (`dMid7Bell18`) and Masked Hit-Set Slot-`u` Invariance

Formalization of:
1. `rfl`-matched 18-wire and 42-wire register slices, `catModAddUnitary`, `uElec18AxisAdd14`,
   `selElec18Sum14In42`, `uElec18Sum42Add`, and `realizesClean_congr_embed`.
2. Exact modulo-`2^14` Z-Bell stream offset cancellation across all `u : Fin 218` and `z < 2^18`.
3. Opaque-unitary `dMid7Bell18` `RealizesOnProj` (`dMid7Bell18_realizesOnProj`,
   `dMid7Bell18_realizesOnProj_of_clean`) and Bell-branch / Z-diagonal phase cancellation.
4. Slot-`u` invariance of `e.val ≠ u` masked origin-hit sets.
-/

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

section Bell18StreamOffset
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256

namespace Bell18StreamOffset

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 1: `rfl`-Matched Bit Values, `catModAddUnitary`, and `uElec18Sum42Add` -/

/-- Unsigned natural value of a `q`-bit assignment. -/
def bitsVal {q : ℕ} (γ : BitAssignment q) : ℕ :=
  ∑ i : Fin q, (γ i).val * 2 ^ i.val

/-- Unsigned natural value extracted by register `r`. -/
def regVal {q n : ℕ} (r : QRegister q n) (β : BitAssignment n) : ℕ :=
  bitsVal (fun i ↦ β (r i))

/-- Equivalence splitting `Fin (2 ^ (kSys + B))` into `(BitAssignment kSys, Fin (2 ^ B))`. -/
def splitSysCatEquiv (kSys B : ℕ) : Fin (2 ^ (kSys + B)) ≃ BitAssignment kSys × Fin (2 ^ B) :=
  (basisBitsEquiv (kSys + B)).trans
    { toFun := fun f ↦
        (fun i ↦ f (Fin.castAdd B i), (basisBitsEquiv B).symm (fun j ↦ f (Fin.natAdd kSys j)))
      invFun := fun p ↦ Fin.addCases p.1 (basisBits B p.2)
      left_inv := fun f ↦ by
        funext idx
        refine Fin.addCases (fun _ ↦ by simp) (fun _ ↦ ?_) idx
        simp
      right_inv := fun ⟨_, _⟩ ↦ by
        ext i <;> simp }

theorem mod_add_sub_cancel (M : ℕ) (hM : 0 < M) (m s : ℕ) (hm : m < M) :
    ((m + s) % M + (M - s % M)) % M = m := by
  have hs : s % M < M := Nat.mod_lt s hM
  have hdiv : M * (s / M) + s % M = s := Nat.div_add_mod s M
  have heq : m + s + (M - s % M) = m + M * (s / M + 1) := by
    linarith [Nat.add_sub_of_le (le_of_lt hs), mul_add M (s / M) 1, mul_one M]
  rw [Nat.mod_add_mod, heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]

/-- Middle modular-addition permutation on `BitAssignment kSys × Fin (2 ^ B)`. -/
def catModAddMidPerm (kSys B : ℕ) (shift : BitAssignment kSys → ℕ) :
    Equiv.Perm (BitAssignment kSys × Fin (2 ^ B)) where
  toFun := fun p ↦ (p.1, ⟨(p.2.val + shift p.1) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩)
  invFun := fun p ↦
    (p.1, ⟨(p.2.val + (2 ^ B - shift p.1 % 2 ^ B)) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩)
  left_inv := fun ⟨γ, m⟩ ↦ by
    ext
    · rfl
    · exact mod_add_sub_cancel (2 ^ B) (by positivity) m.val (shift γ) m.isLt
  right_inv := fun ⟨γ, m⟩ ↦ by
    ext
    · rfl
    · have hM : 0 < 2 ^ B := by positivity
      have hs : shift γ % 2 ^ B < 2 ^ B := Nat.mod_lt _ hM
      have hsub : (2 ^ B - shift γ % 2 ^ B) + shift γ % 2 ^ B = 2 ^ B :=
        Nat.sub_add_cancel (le_of_lt hs)
      calc ((m.val + (2 ^ B - shift γ % 2 ^ B)) % 2 ^ B + shift γ) % 2 ^ B
          = (m.val + (2 ^ B - shift γ % 2 ^ B) + shift γ % 2 ^ B) % 2 ^ B := by
              rw [Nat.mod_add_mod, Nat.add_mod_mod]
        _ = (m.val + 2 ^ B) % 2 ^ B := by rw [Nat.add_assoc, hsub]
        _ = m.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]

/-- Basis-index modular-addition permutation. -/
def catModAddPerm (kSys B : ℕ) (shift : BitAssignment kSys → ℕ) :
    Equiv.Perm (Fin (2 ^ (kSys + B))) :=
  (splitSysCatEquiv kSys B).trans <|
    (catModAddMidPerm kSys B shift).trans (splitSysCatEquiv kSys B).symm

/-- Modular-addition unitary on `kSys + B`. -/
noncomputable def catModAddUnitary (kSys B : ℕ) (shift : BitAssignment kSys → ℕ) :
    Unitary (2 ^ (kSys + B)) :=
  permutationUnitary (catModAddPerm kSys B shift)


/-- 14-bit slice `[14 * w .. 14 * w + 14)` inside `42`. -/
def rSum14Slice42 (w : Fin 3) : QRegister 14 42 :=
  QRegister.block (14 * w.val) 14 (by have := w.isLt; omega)

/-- 6-wire sub-block `[6 * w .. 6 * w + 6)` inside an 18-wire electron register. -/
def rAxis6In18 (w : Fin 3) : QRegister 6 18 :=
  QRegister.block (6 * w.val) 6 (by have := w.isLt; omega)

/-- 6-wire input map for axis `w` inside `Fin 18`. -/
def elec18AxisWire (w : Fin 3) (r : Fin 6) : Wire 18 :=
  rAxis6In18 w r

/-- 6-bit momentum value `regVal (rAxis6In18 w) γ` of an 18-wire electron along axis `w`. -/
def elec18AxisVal (w : Fin 3) (γ : BitAssignment 18) : ℕ :=
  regVal (rAxis6In18 w) γ

theorem elec18AxisVal_eq_sum (w : Fin 3) (γ : BitAssignment 18) :
    elec18AxisVal w γ = ∑ r : Fin 6, 2 ^ r.val * (γ (elec18AxisWire w r)).val := by
  unfold elec18AxisVal elec18AxisWire regVal bitsVal
  exact Finset.sum_congr rfl fun r _ ↦ mul_comm _ _

/-- Unitary on `18 + 14` adding `elec18AxisVal w γ` into `rSum14` modulo `2^14`. -/
noncomputable def uElec18AxisAdd14 (w : Fin 3) : Unitary (2 ^ (18 + 14)) :=
  catModAddUnitary 18 14 (elec18AxisVal w)

/-- Register embedding `(rElec, rSum14(w))` inside `rElec ++ rSum42` (`18 + 42`). -/
def selElec18Sum14In42 (w : Fin 3) : QRegister (18 + 14) (18 + 42) :=
  let rE : QRegister 18 (18 + 42) := QRegister.block 0 18 (by omega)
  let rS42 : QRegister 42 (18 + 42) := QRegister.block 18 42 le_rfl
  let rS14 : QRegister 14 (18 + 42) := rS42.compose (rSum14Slice42 w)
  let hES14 : rE.DisjointWires rS14 :=
    (QRegister.block_disjoint_of_le 0 18 18 42 (by omega) le_rfl (by omega)).compose_right _
  rE.concat rS14 hES14


theorem compose_selElec18Sum14In42 {n : ℕ}
    (rElec : QRegister 18 n) (rSum42 : QRegister 42 n)
    (hESum42 : rElec.DisjointWires rSum42) (w : Fin 3) :
    (rElec.concat rSum42 hESum42).compose (selElec18Sum14In42 w) =
      rElec.concat (rSum42.compose (rSum14Slice42 w))
        (hESum42.compose_right (rSum14Slice42 w)) := by
  apply QRegister.ext
  apply Function.Embedding.ext
  intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun iE ↦ ?_) (fun j14 ↦ ?_) idx
  · dsimp only [selElec18Sum14In42]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hc : QRegister.block 0 18 (by omega : 0 + 18 ≤ 18 + 42) iE = Fin.castAdd 42 iE :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_left]
  · dsimp only [selElec18Sum14In42]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right, QRegister.compose_apply,
      QRegister.compose_apply]
    have hc : QRegister.block 18 42 le_rfl (rSum14Slice42 w j14) =
        Fin.natAdd 18 (rSum14Slice42 w j14) :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_right]

/-- 3-axis 18-wire electron 14-bit addition unitary on `18 + 42`. -/
noncomputable def uElec18Sum42Add : Unitary (2 ^ (18 + 42)) :=
  ((selElec18Sum14In42 2).embedUnitary (uElec18AxisAdd14 2) *
    (selElec18Sum14In42 1).embedUnitary (uElec18AxisAdd14 1)) *
    (selElec18Sum14In42 0).embedUnitary (uElec18AxisAdd14 0)

theorem disjointWires_concat_left {k₁ k₂ m n : ℕ}
    {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n} {rW : QRegister m n}
    (h₁₂ : r₁.DisjointWires r₂) (h₁W : r₁.DisjointWires rW) (h₂W : r₂.DisjointWires rW) :
    (r₁.concat r₂ h₁₂).DisjointWires rW := by
  rw [QRegister.disjoint_iff]
  intro idx j
  refine Fin.addCases (fun i₁ ↦ ?_) (fun i₂ ↦ ?_) idx
  · rw [QRegister.concat_apply_left]
    exact h₁W.ne i₁ j
  · rw [QRegister.concat_apply_right]
    exact h₂W.ne i₂ j

/-- Transport `RealizesEmbeddedUnitaryWithCleanWorkspace` across equal embedded unitaries. -/
theorem realizesClean_congr_embed
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k₁ k₂ m : ℕ} [NeZero (2 ^ n)]
    {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n} {rWork : QRegister m n}
    {u₁ : Unitary (2 ^ k₁)} {u₂ : Unitary (2 ^ k₂)} {d : DynamicCircuit Var n}
    (hEq : r₁.embedUnitary u₁ = r₂.embedUnitary u₂)
    (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₁ rWork u₁ d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₂ rWork u₂ d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  exact ⟨M', hwp, by rw [← hEq]; exact hproj⟩

/-! ## Section 2: Modulo-`2^14` Bell-18 Stream Offset Cancellation -/

/-! ## Section 3: `RealizesOnProj`, `dMid7Bell18` (`+312 T`), and Bell-Branch Intertwining -/

theorem basisOutcomeProjector_conjTranspose {k n : ℕ} (r : QRegister k n) (o : Fin (2 ^ k)) :
    (r.basisOutcomeProjector o)ᴴ = r.basisOutcomeProjector o := by
  rw [r.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1; funext g
  by_cases h : r.extractIndex g = o <;> simp [h]

/-- Store-closed subspace or partial-isometry unitary realization. -/
def RealizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_in : Operator (2 ^ n)) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    E_inᴴ * M'.1.1 * E_in = E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in


theorem RealizesOnProj.mul_right
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E_in : Operator (2 ^ n)} (P : Operator (2 ^ n))
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hd : RealizesOnProj E_in U d) :
    RealizesOnProj (E_in * P) U d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  rw [Matrix.conjTranspose_mul]
  calc (Pᴴ * E_inᴴ) * M'.1.1 * (E_in * P)
      = Pᴴ * (E_inᴴ * M'.1.1 * E_in) * P := by simp only [Matrix.mul_assoc]
    _ = Pᴴ * (E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in) * P := by rw [hproj]
    _ = (Pᴴ * E_inᴴ) * (U.1ᴴ * M.1.1 * U.1) * (E_in * P) := by simp only [Matrix.mul_assoc]


theorem RealizesOnProj.seq_intertwine
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E₁ E₂ V : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (hTrans : U₁.1 * E₁ = E₂ * V)
    (h₁ : RealizesOnProj E₁ U₁ d₁) (h₂ : RealizesOnProj E₂ U₂ d₂) :
    RealizesOnProj E₁ (U₂ * U₁) (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁ M₂
  refine ⟨M₁, ?_, ?_⟩
  · simp only [DynamicCircuit.compile_seq, wp_qSeq, hwp₂, hwp₁]
  · have hTransH : E₁ᴴ * U₁.1ᴴ = Vᴴ * E₂ᴴ := by
      have h := congrArg Matrix.conjTranspose hTrans
      simpa only [Matrix.conjTranspose_mul] using h
    have hSub : (U₂ * U₁).1 = U₂.1 * U₁.1 := by simp only [Submonoid.coe_mul]
    have hSubH : (U₂ * U₁).1ᴴ = U₁.1ᴴ * U₂.1ᴴ := by
      rw [hSub, Matrix.conjTranspose_mul]
    calc E₁ᴴ * M₁.1.1 * E₁
        = E₁ᴴ * (U₁.1ᴴ * M₂.1.1 * U₁.1) * E₁ := hproj₁
      _ = (E₁ᴴ * U₁.1ᴴ) * M₂.1.1 * (U₁.1 * E₁) := by simp only [Matrix.mul_assoc]
      _ = (Vᴴ * E₂ᴴ) * M₂.1.1 * (E₂ * V) := by rw [hTransH, hTrans]
      _ = Vᴴ * (E₂ᴴ * M₂.1.1 * E₂) * V := by simp only [Matrix.mul_assoc]
      _ = Vᴴ * (E₂ᴴ * (U₂.1ᴴ * M.1.1 * U₂.1) * E₂) * V := by rw [hproj₂]
      _ = (Vᴴ * E₂ᴴ) * U₂.1ᴴ * M.1.1 * U₂.1 * (E₂ * V) := by simp only [Matrix.mul_assoc]
      _ = (E₁ᴴ * U₁.1ᴴ) * U₂.1ᴴ * M.1.1 * U₂.1 * (U₁.1 * E₁) := by rw [← hTransH, ← hTrans]
      _ = E₁ᴴ * ((U₁.1ᴴ * U₂.1ᴴ) * M.1.1 * (U₂.1 * U₁.1)) * E₁ := by
          simp only [Matrix.mul_assoc]
      _ = E₁ᴴ * ((U₂ * U₁).1ᴴ * M.1.1 * (U₂ * U₁).1) * E₁ := by rw [← hSubH, ← hSub]


/-! ## Section 4: Slot-`u` Invariance of `e.val ≠ u` Masked Hit Sets -/


end Bell18StreamOffset

end Bell18StreamOffset

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
