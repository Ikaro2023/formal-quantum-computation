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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CoherentAlias
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AngleTables
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CatalystAndQFT
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM

/-!
# Coherent Alias State Preparation Adapter (`OuterAliasPrep`)

Turnkey adapter connecting:
1. Ancilla-free uniform preparations (`prepUniform30Dyn`, `prepUniform184Dyn`, `740 T`, `0 TOFF`,
   `0` scratch, `≤ 1e-13`) from `CatalystAndQFT`,
2. Pruned unary QROM (`unaryQromLoadDyn`), minimum-ancilla `SelectSwap` QROM
   (`selectSwapCleanLoadReuseDyn`), and `0-T` X-measurement QROM unloads (`qromXMeasUnloadDyn`,
   `qromXMeasUnloadInPlaceDyn`) from `SelectSwapQROM`, and
3. Robin-Hood / Walker alias tables (`OuterWeights.innerAliasTable`, `OuterWeights.outerAliasTable`)
   from `AngleTables`
into `CoherentAlias.coherentAliasPrep`, `CoherentAlias.coherentAliasPrepDag`, and the asymmetric
X-measurement block-encoding sandwich `PREP ;; SEL ;; PREP†_XMeas`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasPrep
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

attribute [local irreducible] oneBodyWeights fragmentWeights innerWeights

/-- Equivalence between `XMeasCircuit.CleanRealizes` and `CleanDyn.CleanRealizes`. -/
theorem cleanRealizes_sbx_iff {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)] (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N) :
    XMeasCircuit.CleanRealizes v rAct rScr U P ↔ CleanDyn.CleanRealizes v rAct rScr U P :=
  ⟨fun h ↦ ⟨h.count_toff, h.wp_update, h.wp_clean, h.wp_clean_post⟩,
   fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2, h3, h4⟩⟩

/-- Convert a `Bool`-valued lookup table `T : ℕ → (Fin w → Bool)` truncated at `L` into the
`BitAssignment`-valued table function consumed by `CoherentAlias.aliasTableXorUnitary`. -/
def boolTableToAliasFn (m w L : ℕ) (T : ℕ → (Fin w → Bool))
    (addr : Fin (2 ^ m)) : BitAssignment w :=
  fun j ↦ if addr.val < L ∧ T addr.val j then 1 else 0

theorem xorLoadUnitary_eq_aliasTableXorUnitary (m w L : ℕ) (T : ℕ → (Fin w → Bool)) :
    SelectSwapQROM.xorLoadUnitary m w L T =
      aliasTableXorUnitary m w (boolTableToAliasFn m w L T) := by
  apply eq_aliasTableXorUnitary_of_mulVec_ket
  intro β
  let rIdx : QRegister m (m + w) := QRegister.block 0 m (by omega)
  let rOut : QRegister w (m + w) := QRegister.block m w (by omega)
  have hDisj : rIdx.DisjointWires rOut :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by
      have hv := congrArg Fin.val hij
      simp only [rIdx, rOut, QRegister.block_apply_val] at hv
      have := i.isLt
      omega
  have hWhole : rIdx.concat rOut hDisj = QRegister.whole (m + w) := by
    ext k
    rcases hsum : finSumFinEquiv.symm k with i | j
    · have hk : k = Fin.castAdd w i := by simpa using congrArg finSumFinEquiv hsum
      subst hk
      simp [rIdx.concat_apply_left rOut hDisj i, rIdx, QRegister.whole]
    · have hk : k = Fin.natAdd m j := by simpa using congrArg finSumFinEquiv hsum
      subst hk
      simp [rIdx.concat_apply_right rOut hDisj j, rOut, QRegister.whole]
  have hU : SelectSwapQROM.xorLoadUnitary m w L T =
      (rIdx.concat rOut hDisj).embedUnitary (SelectSwapQROM.xorLoadUnitary m w L T) := by
    rw [hWhole, QRegister.whole_embedUnitary]
  rw [hU, SelectSwapQROM.embed_xorLoadUnitary_mulVec_ket]
  congr 1
  funext q
  have hAddr : (basisBits m).symm (fun i ↦ β (rIdx i)) =
      (basisBits m).symm (fun i ↦ β ⟨i.val, by omega⟩) := by
    congr 1
    funext i
    exact congrArg β (Fin.ext (by simp [rIdx]))
  by_cases hq : m ≤ q.val
  · have hqOut : rOut ⟨q.val - m, by omega⟩ = q := Fin.ext (by simp [rOut]; omega)
    conv_lhs => rw [← hqOut, SelectSwapQROM.xorRegBits_apply_reg]
    simp [aliasTableXorBits, boolTableToAliasFn, hq, hqOut, hAddr]
  · have hNotOut : q ∉ rOut.image := by
      intro hmem
      obtain ⟨j, rfl⟩ := (QRegister.mem_image rOut _).mp hmem
      exact hq (by simp [rOut])
    rw [SelectSwapQROM.xorRegBits_apply_of_not_mem _ rOut _ q hNotOut]
    simp [aliasTableXorBits, hq]

/-- QROM output sub-register `[idxBits + ctxBits .. aliasQromBits)` inside `aliasActBits`. -/
def aliasOutReg (idxBits ctxBits b payBits : ℕ) :
    QRegister (aliasOutBits idxBits b payBits) (aliasActBits idxBits ctxBits b payBits) :=
  QRegister.block (idxBits + ctxBits) (aliasOutBits idxBits b payBits)
    (by dsimp [aliasActBits, aliasQromBits]; omega)

/-! ## Section 2: Unary Load, SelectSwap Load & Pooled X-Measurement Unload Adapters -/

/-- Matrix `A` preserves computational-basis wire values on `T` (`A i j = 0` whenever `i` and `j`
differ on some wire in `T`). -/
def PreservesWires {N : ℕ} (A : Operator (2 ^ N)) (T : Finset (Wire N)) : Prop :=
  ∀ i j : Fin (2 ^ N), (∃ w ∈ T, basisBits N i w ≠ basisBits N j w) → A i j = 0

private theorem zeroProjOn_mulVec_apply {N : ℕ} (S : Finset (Wire N)) (v : Fin (2 ^ N) → ℂ)
    (i : Fin (2 ^ N)) :
    (SelectSwapQROM.zeroProjOn S *ᵥ v) i =
      if ∀ w ∈ S, basisBits N i w = 0 then v i else 0 := by
  simp only [SelectSwapQROM.zeroProjOn, Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem preservesWires_comm_zeroProjOn {N : ℕ} {A : Operator (2 ^ N)} {T S : Finset (Wire N)}
    (hA : PreservesWires A T) (hSub : S ⊆ T) :
    A * SelectSwapQROM.zeroProjOn S = SelectSwapQROM.zeroProjOn S * A := by
  apply matrix_ext_ket; intro β; funext i
  simp only [← Matrix.mulVec_mulVec, SelectSwapQROM.zeroProjOn_mulVec_ket,
    zeroProjOn_mulVec_apply]
  have hcol : (A *ᵥ ket β) i = A i ((basisBits N).symm β) := by
    simp [ket, basisState]
  by_cases hβ : ∀ w ∈ S, β w = 0
  · rw [ite_eq_left hβ, hcol]
    by_cases hi : ∀ w ∈ S, basisBits N i w = 0
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi]
      push Not at hi; obtain ⟨w, hwS, hne⟩ := hi
      exact hA i _ ⟨w, hSub hwS, by simpa [hβ w hwS] using hne⟩
  · rw [ite_eq_right hβ, Matrix.mulVec_zero, Pi.zero_apply]
    by_cases hi : ∀ w ∈ S, basisBits N i w = 0
    · rw [ite_eq_left hi, hcol]
      push Not at hβ; obtain ⟨w, hwS, hne⟩ := hβ
      exact (hA i _ ⟨w, hSub hwS, by simpa [hi w hwS] using Ne.symm hne⟩).symm
    · rw [ite_eq_right hi]

theorem preservesWires_mul {N : ℕ} {A B : Operator (2 ^ N)} {T : Finset (Wire N)}
    (hA : PreservesWires A T) (hB : PreservesWires B T) :
    PreservesWires (A * B) T := by
  intro i j ⟨w, hw, hij⟩
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hik : basisBits N i w = basisBits N k w
  · rw [hB k j ⟨w, hw, fun hkj ↦ hij (hik.trans hkj)⟩, mul_zero]
  · rw [hA i k ⟨w, hw, hik⟩, zero_mul]

theorem preservesWires_diagonal {N : ℕ} (d : Fin (2 ^ N) → ℂ) (T : Finset (Wire N)) :
    PreservesWires (Matrix.diagonal d) T := by
  intro i j ⟨w, _, hij⟩
  have hne : i ≠ j := fun h ↦ hij (h ▸ rfl)
  simp [hne]

theorem preservesWires_embedMatrix_of_disjoint {N k : ℕ} (r : QRegister k N)
    (M : Operator (2 ^ k)) (T : Finset (Wire N)) (hDisj : Disjoint r.image T) :
    PreservesWires (r.embedMatrix M) T := by
  intro i j ⟨w, hw, hij⟩
  have hcol : (r.embedMatrix M) i j = ((r.embedMatrix M) *ᵥ ket (basisBits N j)) i := by
    simp [ket, basisState]
  rw [hcol, embedMatrix_mulVec_ket, Finset.sum_apply]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  have hwNot : w ∉ Set.range r.wires := by
    rintro ⟨u, rfl⟩
    exact Finset.disjoint_left.mp hDisj ((QRegister.mem_image r _).mpr ⟨u, rfl⟩) hw
  have hne : (basisBits N).symm (writeReg (basisBits N j) r (basisBits k l)) ≠ i := by
    intro heq
    apply hij
    have hwEq := congrFun (congrArg (basisBits N) heq) w
    rw [basisBits_symm_apply, writeReg_apply_of_not_mem _ _ _ w hwNot] at hwEq
    exact hwEq.symm
  simp [ket, basisState, hne.symm]

theorem preservesWires_conj_embedBitPerm {N k : ℕ} {A : Operator (2 ^ N)} {T : Finset (Wire N)}
    (hA : PreservesWires A T) (rSub : QRegister k N) (hSub : rSub.image ⊆ T)
    (perm : Equiv.Perm (BitAssignment k)) (hInvol : Function.Involutive perm) :
    PreservesWires
      ((rSub.embedUnitary (bitPermUnitary perm)).1 * A *
        (rSub.embedUnitary (bitPermUnitary perm)).1) T := by
  let W := rSub.embedUnitary (bitPermUnitary perm)
  let gN (β : BitAssignment N) : BitAssignment N := writeReg β rSub (perm (fun u ↦ β (rSub u)))
  have hgInvol (β : BitAssignment N) : gN (gN β) = β := by
    have hloc : (fun u ↦ gN β (rSub u)) = perm (fun u ↦ β (rSub u)) := by
      funext u; simp [gN]
    funext q
    by_cases hq : q ∈ Set.range rSub.wires
    · obtain ⟨u, rfl⟩ := hq
      dsimp only [gN]
      rw [writeReg_apply_reg, hloc, hInvol]
    · dsimp only [gN]
      rw [writeReg_apply_of_not_mem _ _ _ q hq, writeReg_apply_of_not_mem _ _ _ q hq]
  have hW_vec (v : Fin (2 ^ N) → ℂ) (i : Fin (2 ^ N)) :
      (W.1 *ᵥ v) i = v ((basisBits N).symm (gN (basisBits N i))) := by
    have hv : v = ∑ m : Fin (2 ^ N), v m • ket (basisBits N m) := by
      funext x; simp [ket, basisState, Pi.single_apply]
    conv_lhs => rw [hv, Matrix.mulVec_sum]
    rw [Finset.sum_apply, Finset.sum_eq_single ((basisBits N).symm (gN (basisBits N i)))]
    · rw [Matrix.mulVec_smul, embedUnitary_bitPermUnitary_mulVec_ket]
      change (v _ • ket (gN (basisBits N ((basisBits N).symm (gN (basisBits N i)))))) i = _
      rw [basisBits_symm_apply, hgInvol]
      simp [ket, basisState]
    · intro m _ hm
      rw [Matrix.mulVec_smul, embedUnitary_bitPermUnitary_mulVec_ket]
      change (v m • ket (gN (basisBits N m))) i = 0
      have hne : (basisBits N).symm (gN (basisBits N m)) ≠ i := by
        intro heq
        apply hm
        have h1 := congrArg (fun x ↦ (basisBits N).symm (gN (basisBits N x))) heq
        simpa only [basisBits_symm_apply, hgInvol, symm_basisBits_apply] using h1
      simp [ket, basisState, hne.symm]
    · simp
  intro i j ⟨w, hw, hij⟩
  have hentry : (W.1 * A * W.1) i j =
      A ((basisBits N).symm (gN (basisBits N i)))
        ((basisBits N).symm (gN (basisBits N j))) := by
    have hcol : (W.1 * A * W.1) i j = ((W.1 * A * W.1) *ᵥ ket (basisBits N j)) i := by
      simp [ket, basisState]
    rw [hcol, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hW_vec, embedUnitary_bitPermUnitary_mulVec_ket]
    change (A *ᵥ ket (gN (basisBits N j))) _ = _
    simp [ket, basisState]
  rw [hentry]
  apply hA
  simp only [basisBits_symm_apply]
  by_contra hall
  push Not at hall
  apply hij
  have hlocEq : (fun u ↦ gN (basisBits N i) (rSub u)) =
      fun u ↦ gN (basisBits N j) (rSub u) := by
    funext u
    exact hall (rSub u) (hSub ((QRegister.mem_image rSub _).mpr ⟨u, rfl⟩))
  have hgEq : gN (gN (basisBits N i)) w = gN (gN (basisBits N j)) w := by
    by_cases hwR : w ∈ Set.range rSub.wires
    · obtain ⟨u, rfl⟩ := hwR
      dsimp only [gN]
      rw [writeReg_apply_reg, writeReg_apply_reg, hlocEq]
    · change writeReg (gN (basisBits N i)) rSub _ w = writeReg (gN (basisBits N j)) rSub _ w
      rw [writeReg_apply_of_not_mem _ _ _ w hwR, writeReg_apply_of_not_mem _ _ _ w hwR]
      exact hall w hw
  rwa [hgInvol, hgInvol] at hgEq

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasPrep
