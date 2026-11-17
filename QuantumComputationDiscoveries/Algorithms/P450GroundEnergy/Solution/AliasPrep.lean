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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasComparator

/-!
# Coherent Alias Sampling State Preparation

Top-level coherent alias-sampling state preparation (`PREP` and `PREP†`) and block-encoding module
over `CleanDyn` (`CleanRealizes`, `TOFF = 0`):

1. **QROM Target-XOR Specification & Packed Alias Row Layout:**
   - Self-inverse `aliasTableXorUnitary` (`rfl`-aligned with `InnerTable.tableXorUnitary` and
     bridged to `qromUnitary` via `eq_aliasTableXorUnitary_of_mulVec_ket`).
   - `packAliasRow` encoding `(alt, keep, payX, payAlt)` and little-endian `combineAddr`
     (`(combineAddr x ctx).val = x.val + 2 ^ idxBits * ctx.val`).
2. **Coherent Alias `PREP` & `PREP†` Circuits:**
   - Primary single-QROM `coherentAliasPrep` and `coherentAliasPrepDag` (`PREP†` realizes
     `PREP⁻¹`, keeping `keep` in coherent garbage across `SELECT` so `PREP` and `PREP†` each
     invoke QROM once) plus secondary `coherentAliasPrepUncompKeep` /
     `coherentAliasPrepUncompKeepDag`.
   - Concrete P450 instantiations: `outerAliasPrepProg` (`D = 184`, `b = 10`,
     `88 + g.tCount + T_qrom` `T` gates) and `innerAliasPrepProg` (`D = 30`, `b = 9`, `ctxBits = 7`,
     `payBits = 1`, `74 + g.tCount + T_qrom` `T` gates).
3. **Operator-Norm Perturbation & Exact LCU / Marginal Probability Theorems:**
   - `norm_coherentAliasUnitary_sub_le`, `norm_unitary_conj_sub_le`, `norm_unitary_conj_sub_le'`,
     `norm_outerAliasUnitary_sub_le`, and `norm_innerAliasUnitary_sub_le`.
   - `IsValidAliasTable`, `card_aliasFiber_eq_weight`, `coherentAlias_stateVec_ket`,
     `coherentAlias_marginal_prob`, deterministic payload entanglement, and exact LCU projection
     identity `coherentAlias_lcu_mulVec_ket`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
namespace CoherentAlias

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 1: QROM Target-XOR Unitary & Packed Alias Row Layout -/

/-- Classical involution on `m + w` wires XORing `f x` into the high `w` wires `[m .. m + w)`. -/
def aliasTableXorBits (m w : ℕ) (f : Fin (2 ^ m) → BitAssignment w)
    (β : BitAssignment (m + w)) : BitAssignment (m + w) :=
  let x : Fin (2 ^ m) := (basisBits m).symm (fun i ↦ β ⟨i.val, by omega⟩)
  fun q ↦
    if hq : m ≤ q.val then
      β q + f x ⟨q.val - m, by omega⟩
    else
      β q

theorem aliasTableXorBits_self (m w : ℕ) (f : Fin (2 ^ m) → BitAssignment w)
    (β : BitAssignment (m + w)) :
    aliasTableXorBits m w f (aliasTableXorBits m w f β) = β := by
  set β₁ := aliasTableXorBits m w f β
  have hx : (fun i : Fin m ↦ β₁ ⟨i.val, by omega⟩) = fun i ↦ β ⟨i.val, by omega⟩ := by
    funext i
    simp [β₁, aliasTableXorBits, show ¬ (m ≤ i.val) by omega]
  funext q
  dsimp only [aliasTableXorBits]
  rw [hx]
  by_cases hq : m ≤ q.val
  · simp [hq, β₁, aliasTableXorBits, zmod2_add_cancel_right]
  · simp [hq, β₁, aliasTableXorBits]

/-- Self-inverse `(m + w)`-wire QROM target-XOR unitary `|x⟩|y⟩ ↦ |x⟩|y ⊕ f(x)⟩`. -/
noncomputable def aliasTableXorUnitary (m w : ℕ) (f : Fin (2 ^ m) → BitAssignment w) :
    Unitary (2 ^ (m + w)) :=
  bitPermUnitary ⟨aliasTableXorBits m w f, aliasTableXorBits m w f,
    aliasTableXorBits_self m w f, aliasTableXorBits_self m w f⟩

@[simp]
theorem aliasTableXorUnitary_mul_self (m w : ℕ) (f : Fin (2 ^ m) → BitAssignment w) :
    aliasTableXorUnitary m w f * aliasTableXorUnitary m w f = 1 :=
  bitPermUnitary_mul_self _ (aliasTableXorBits_self m w f)

@[simp]
theorem aliasTableXorUnitary_inv (m w : ℕ) (f : Fin (2 ^ m) → BitAssignment w) :
    (aliasTableXorUnitary m w f)⁻¹ = aliasTableXorUnitary m w f :=
  bitPermUnitary_inv_of_involutive _ (aliasTableXorBits_self m w f)

/-- Bridge characterization: any `(m + w)`-qubit unitary acting on basis kets via
`aliasTableXorBits m w f` equals `aliasTableXorUnitary m w f`. -/
theorem eq_aliasTableXorUnitary_of_mulVec_ket {m w : ℕ}
    (f : Fin (2 ^ m) → BitAssignment w) (Q : Unitary (2 ^ (m + w)))
    (hQ : ∀ β : BitAssignment (m + w), Q.1 *ᵥ ket β = ket (aliasTableXorBits m w f β)) :
    Q = aliasTableXorUnitary m w f := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [hQ β, show aliasTableXorUnitary m w f =
      (QRegister.whole (m + w)).embedUnitary (aliasTableXorUnitary m w f)
      from (QRegister.whole_embedUnitary _).symm,
    aliasTableXorUnitary, embedUnitary_bitPermUnitary_mulVec_ket, writeReg_whole]
  rfl

/-- Combine `x : Fin (2 ^ idxBits)` (low bits) and `ctx : Fin (2 ^ ctxBits)` (high bits) into an
address in `Fin (2 ^ (idxBits + ctxBits))`. -/
noncomputable def combineAddr {idxBits ctxBits : ℕ}
    (x : Fin (2 ^ idxBits)) (ctx : Fin (2 ^ ctxBits)) :
    Fin (2 ^ (idxBits + ctxBits)) :=
  (basisBits (idxBits + ctxBits)).symm fun u ↦
    if h : u.val < idxBits then
      basisBits idxBits x ⟨u.val, h⟩
    else
      basisBits ctxBits ctx ⟨u.val - idxBits, by omega⟩

theorem combineAddr_val {idxBits ctxBits : ℕ}
    (x : Fin (2 ^ idxBits)) (ctx : Fin (2 ^ ctxBits)) :
    (combineAddr x ctx).val = x.val + 2 ^ idxBits * ctx.val := by
  set g := combineAddr x ctx
  let rLo : QRegister idxBits (idxBits + ctxBits) := QRegister.block 0 idxBits (by omega)
  let rHi : QRegister ctxBits (idxBits + ctxBits) := QRegister.block idxBits ctxBits le_rfl
  have hlo_eq : rLo.extractIndex g = x := by
    rw [QRegister.extractIndex]
    have hb : (fun i : Fin idxBits ↦ basisBits (idxBits + ctxBits) g (rLo i)) =
        basisBits idxBits x := by
      funext i
      dsimp only [g, combineAddr, rLo]
      rw [basisBits_symm_apply]
      simp [i.isLt]
    rw [hb, symm_basisBits_apply]
  have hhi_eq : rHi.extractIndex g = ctx := by
    rw [QRegister.extractIndex]
    have hb : (fun i : Fin ctxBits ↦ basisBits (idxBits + ctxBits) g (rHi i)) =
        basisBits ctxBits ctx := by
      funext i
      dsimp only [g, combineAddr, rHi]
      rw [basisBits_symm_apply]
      have hnlt : ¬ (idxBits + i.val < idxBits) := by omega
      simp [hnlt]
    rw [hb, symm_basisBits_apply]
  have hlo_v := extractIndex_block_val (by omega : 0 + idxBits ≤ idxBits + ctxBits) g
  have hhi_v := extractIndex_block_val (le_rfl : idxBits + ctxBits ≤ idxBits + ctxBits) g
  have hdiv_lt : g.val / 2 ^ idxBits < 2 ^ ctxBits := by
    apply Nat.div_lt_of_lt_mul
    simpa only [Nat.pow_add] using g.isLt
  have hmod : g.val % 2 ^ idxBits = x.val := by
    simpa [rLo, _root_.pow_zero, hlo_eq] using hlo_v.symm
  have hdiv : g.val / 2 ^ idxBits = ctx.val := by
    simpa [rHi, Nat.mod_eq_of_lt hdiv_lt, hhi_eq] using hhi_v.symm
  rw [← Nat.mod_add_div g.val (2 ^ idxBits), hmod, hdiv]

/-- QROM output bit width `idxBits + b + 2 * payBits` holding `(alt, keep, payX, payAlt)`. -/
abbrev aliasOutBits (idxBits b payBits : ℕ) : ℕ :=
  idxBits + b + 2 * payBits

/-- Total QROM `(address, output)` bit width `(idxBits + ctxBits) + (idxBits + b + 2 * payBits)`. -/
abbrev aliasQromBits (idxBits ctxBits b payBits : ℕ) : ℕ :=
  (idxBits + ctxBits) + aliasOutBits idxBits b payBits

/-- Total active alias register width `aliasQromBits + b + 1`. -/
abbrev aliasActBits (idxBits ctxBits b payBits : ℕ) : ℕ :=
  aliasQromBits idxBits ctxBits b payBits + b + 1

/-! ## Section 2: Coherent Alias Sub-Registers, `PREP` & `PREP†` Circuits -/

/-- Sampled index sub-register `[0 .. idxBits)` inside `aliasActBits`. -/
def aliasIdxReg (idxBits ctxBits b payBits : ℕ) :
    QRegister idxBits (aliasActBits idxBits ctxBits b payBits) :=
  QRegister.block 0 idxBits (by dsimp [aliasActBits, aliasQromBits, aliasOutBits]; omega)

/-- External context sub-register `[idxBits .. idxBits + ctxBits)` inside `aliasActBits`. -/
def aliasCtxReg (idxBits ctxBits b payBits : ℕ) :
    QRegister ctxBits (aliasActBits idxBits ctxBits b payBits) :=
  QRegister.block idxBits ctxBits (by dsimp [aliasActBits, aliasQromBits, aliasOutBits]; omega)

/-- QROM `(address, output)` sub-register `[0 .. aliasQromBits)` inside `aliasActBits`. -/
def aliasQromReg (idxBits ctxBits b payBits : ℕ) :
    QRegister (aliasQromBits idxBits ctxBits b payBits)
      (aliasActBits idxBits ctxBits b payBits) :=
  QRegister.block 0 (aliasQromBits idxBits ctxBits b payBits) (by dsimp [aliasActBits]; omega)

theorem compose_disjointWires_left {N K k₀ s : ℕ}
    {rAlias : QRegister K N} {rScr : QRegister s N}
    (rSub : QRegister k₀ K) (hdisj : rAlias.DisjointWires rScr) :
    (rAlias.compose rSub).DisjointWires rScr := by
  rw [QRegister.disjoint_iff] at hdisj ⊢
  intro i j
  exact hdisj (rSub i) j

end CoherentAlias
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
