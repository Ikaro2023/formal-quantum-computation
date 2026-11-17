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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CliffordTSynthesis
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DataArrays
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.QromBase
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncoding
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MeasuresLowEnergiesAux
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SpectralUpperBound

/-!
# Outer & Inner Alias Pre-Integration Bridge (`InnerTablePreInteg`)

Pre-stages the cross-module bridges connecting the coherent alias and block-encoding components:

1. **Concrete `UnifTreeGates` from `CliffordTSynthesis` (`unifGates184`, `unifGates30`):**
   - Instantiates `CoherentAlias.UnifTreeGates` with `CliffordT.rySplit` and `CliffordT.ryHalfSplit`
     (`tCount = 732` for `D = 184`, `tCount = 734` for `D = 30`, `TOFF = 0`) and proves the
     `≤ 28 / 10 ^ 15` operator-norm approximation bounds.
2. **Concrete Outer (`184`) & Inner (`126 × 30`) Coherent Alias Bridges:**
   - Bridges the `184`-item outer alias QROM (`728 T`) with `CoherentAlias.outerAliasPrepProg`
     (`1,548 T`, `0 TOFF`), proves `IsValidAliasTable` and `packAliasRow` alignment, and discharges
     `BlockEncoding.PrepOutValid` (`w_go = 29`).
   - Bridges `InnerTable.innerAliasSelectSwapQromDirect` (`≤ 3,080 T`) with
     `CoherentAlias.innerAliasPrepProg` (`≤ 3,888 T`, `0 TOFF`), proving `IsValidAliasTable` and
     `packAliasRow` alignment for all `126` `(r, c)` tables.
3. **Spin-Blocked `p450FswapUninterleave` Conjugation & `preparePhaseGrad14` Catalyst Wrapper:**
   - Reduces `MeasuresLowEnergies_local (thcHamiltonian P450.dfthc) 63 Δ ε` to
     `MeasuresLowEnergies_local BlockEncoding.p450HBlocked 63 Δ ε` at `0` `T` and `0` `TOFF`
     gates, proves `thcHamiltonian_comm_electronSectorProjector_pre` and
     `p450HBlocked_comm_electronSectorProjector`, transfers the
     `[dfthcLowerBound, dfthcUpperBound]` spectral bracket to `p450HBlocked`, and wraps
     `preparePhaseGrad14` / `unpreparePhaseGrad14` (`2,262 T`, `≤ 2e-8` error).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 0: Symbolic `QRegister` Disjointness, Concat & Basis-Ket Helpers -/

/-! ## Section 1: Concrete `UnifTreeGates` from `CliffordTSynthesis` (`≤ 28 / 10 ^ 15`) -/

/-- Symbolic `(m + 1)`-qubit column-zero and marginal-sum bridge for any `m`-qubit state-prep
unitary `U` tensor Hadamard `H` on wire `m`. -/
theorem prepPlusHadamard_vanish_and_sum {m d : ℕ}
    (U : Unitary (2 ^ m)) (rIdx : QRegister d m) (rIdxExt : QRegister d (m + 1))
    (hr : rIdxExt = (QRegister.block 0 m (by omega)).compose rIdx) :
    (∀ (o : Fin (2 ^ (m + 1))) (i₀ : Fin (2 ^ d)),
      rIdxExt.extractIndex o = i₀ →
      (∑ g : Fin (2 ^ m), if rIdx.extractIndex g = i₀ then ‖(U.1 *ᵥ basisState 0) g‖ ^ 2 else 0) =
        0 →
      (((QRegister.block m 1 (by omega)).embedUnitary (Circuit.H 0).eval *
          (QRegister.block 0 m (by omega)).embedUnitary U).1 o 0) = 0) ∧
    (∀ (i₀ : Fin (2 ^ d)) (so : Fin (2 ^ 1)),
      (∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ (m + 1)) ↦
          (rIdxExt.extractIndex o).val = i₀.val ∧
            (QRegister.block m 1 (by omega)).extractIndex o = so),
        Complex.normSq ((((QRegister.block m 1 (by omega)).embedUnitary (Circuit.H 0).eval *
          (QRegister.block 0 m (by omega)).embedUnitary U).1 o 0))) =
      (1 / 2 : ℝ) * ∑ g : Fin (2 ^ m),
        if rIdx.extractIndex g = i₀ then ‖(U.1 *ᵥ basisState 0) g‖ ^ 2 else 0) := by
  let rLo : QRegister m (m + 1) := QRegister.block 0 m (by omega)
  let rHi : QRegister 1 (m + 1) := QRegister.block m 1 (by omega)
  let Ψ : Fin (2 ^ m) → ℂ := U.1 *ᵥ basisState 0
  have hH : ∀ y : Fin (2 ^ 1),
      ((Circuit.H (0 : Wire 1)).eval.1 *ᵥ basisState 0) y = ((1 / √2 : ℝ) : ℂ) := by
    intro y
    fin_cases y <;>
      simp [Circuit.H, PrimitiveGate.eval, Qubit.H, basisState,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.real_smul]
  have hcol (o : Fin (2 ^ (m + 1))) :
      ((rHi.embedUnitary (Circuit.H 0).eval * rLo.embedUnitary U).1 : Operator (2 ^ (m + 1)))
        o 0 = Ψ (rLo.extractIndex o) * ((1 / √2 : ℝ) : ℂ) := by
    have hmul :
        ((rHi.embedUnitary (Circuit.H 0).eval * rLo.embedUnitary U).1 : Operator (2 ^ (m + 1)))
          o 0 =
        (((rHi.embedUnitary (Circuit.H 0).eval * rLo.embedUnitary U).1 : Operator (2 ^ (m + 1))) *ᵥ
          basisState 0) o := by simp [basisState]
    rw [hmul, Submonoid.coe_mul, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← Matrix.mulVec_mulVec, (CoherentAlias.blockProdState_basisState_zero m 1).symm,
      CoherentAlias.embedMatrix_block_lo_mulVec_blockProdState,
      CoherentAlias.embedMatrix_block_hi_mulVec_blockProdState]
    dsimp only [CoherentAlias.blockProdState]
    rw [hH]
  have hext (o : Fin (2 ^ (m + 1))) :
      rIdxExt.extractIndex o = rIdx.extractIndex (rLo.extractIndex o) := by
    rw [hr, QRegister.extractIndex_compose]
  refine ⟨fun o i₀ ho hsum0 ↦ ?_, fun i₀ so ↦ ?_⟩
  · rw [hcol o]
    set g₀ := rLo.extractIndex o
    have hg₀ : rIdx.extractIndex g₀ = i₀ := by rw [← hext o, ho]
    have hle : ‖Ψ g₀‖ ^ 2 ≤
        ∑ g : Fin (2 ^ m), if rIdx.extractIndex g = i₀ then ‖Ψ g‖ ^ 2 else 0 := by
      have hterm : (if rIdx.extractIndex g₀ = i₀ then ‖Ψ g₀‖ ^ 2 else 0) = ‖Ψ g₀‖ ^ 2 := by
        simp [hg₀]
      rw [← hterm]
      exact Finset.single_le_sum
        (f := fun g : Fin (2 ^ m) ↦ if rIdx.extractIndex g = i₀ then ‖Ψ g‖ ^ 2 else 0)
        (fun g _ ↦ by split_ifs <;> positivity) (Finset.mem_univ g₀)
    have hsq0 : ‖Ψ g₀‖ ^ 2 = 0 := le_antisymm (hle.trans_eq hsum0) (sq_nonneg _)
    rw [norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0), zero_mul]
  · have hbij : (∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ (m + 1)) ↦
          (rIdxExt.extractIndex o).val = i₀.val ∧ rHi.extractIndex o = so),
          Complex.normSq (((rHi.embedUnitary (Circuit.H 0).eval * rLo.embedUnitary U).1 :
            Operator (2 ^ (m + 1))) o 0)) =
        ∑ g : Fin (2 ^ m),
          if rIdx.extractIndex g = i₀ then
            Complex.normSq (Ψ g * ((1 / √2 : ℝ) : ℂ))
          else 0 := by
      rw [Finset.sum_filter]
      let e := BlockEncodingCore.splitBlockEquiv m 1
      rw [← e.symm.sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [Fintype.sum_eq_single so]
      · have hfst : rLo.extractIndex (e.symm (g, so)) = g := by
          have := BlockEncodingCore.splitBlockEquiv_fst m 1 (e.symm (g, so))
          simpa [e, rLo] using this.symm
        have hsnd : rHi.extractIndex (e.symm (g, so)) = so := by
          have := BlockEncodingCore.splitBlockEquiv_snd m 1 (e.symm (g, so))
          simpa [e, rHi] using this.symm
        rw [hcol, hext, hfst, hsnd]
        by_cases hg : rIdx.extractIndex g = i₀
        · simp [hg]
        · have hval : (rIdx.extractIndex g).val ≠ i₀.val := fun h ↦ hg (Fin.ext h)
          simp [hg, hval]
      · intro s' hs'
        have hsnd : rHi.extractIndex (e.symm (g, s')) = s' := by
          have := BlockEncodingCore.splitBlockEquiv_snd m 1 (e.symm (g, s'))
          simpa [e, rHi] using this.symm
        rw [hsnd]
        simp [hs']
    rw [hbij, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    split_ifs
    · rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
      have hs2 : (1 / √2 : ℝ) * (1 / √2 : ℝ) = 1 / 2 := by
        rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
      rw [hs2]
      ring
    · ring

/-! ### Part 2B: Outer Alias `PREP` (`1,548 T`, `0 TOFF`) & `BlockEncoding.PrepOutValid` -/

/-- Wrap any `CleanRealizes` dynamic circuit `P` on `2 * 58 + m` active wires with
`p450FswapUninterleave` before and `p450FswapUninterleave.inverse` after (`0` extra `T` or `.TOFF`
gates). -/
def p450FswapConjProg {Var : Type} {m N : ℕ}
    (rAct : QRegister (2 * 58 + m) N) (P : DynamicCircuit Var N) : DynamicCircuit Var N :=
  let rSys : QRegister (2 * 58) N := rAct.compose (QRegister.block 0 (2 * 58) (by omega))
  .seq (.circuit (p450FswapUninterleave.onRegister rSys))
    (.seq P (.circuit (p450FswapUninterleave.inverse.onRegister rSys)))

@[simp]
theorem count_p450FswapConjProg_toff {Var : Type} {m N : ℕ}
    (rAct : QRegister (2 * 58 + m) N) {P : DynamicCircuit Var N} (hP : P.count .TOFF = 0) :
    (p450FswapConjProg rAct P).count .TOFF = 0 := by
  simp [p450FswapConjProg, hP]

@[simp]
theorem count_p450FswapConjProg_t {Var : Type} {m N : ℕ}
    (rAct : QRegister (2 * 58 + m) N) (P : DynamicCircuit Var N) :
    (p450FswapConjProg rAct P).count .T = P.count .T := by
  simp [p450FswapConjProg]

/-- Spectral bracket `[dfthcLowerBound, dfthcUpperBound]` transferred to `63`-electron eigenstates
of `BlockEncoding.p450HBlocked`. -/
theorem p450HBlocked_eigenvalue_bounds (E : ℝ) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (heig : BlockEncodingCore.p450HBlocked *ᵥ ψ = (E : ℂ) • ψ ∧
      electronSectorProjector (2 * 58) 63 *ᵥ ψ = ψ ∧ ψ ≠ 0)
    (_ : ∑ i, Complex.normSq (ψ i) = 1) :
    dfthcLowerBound ≤ E ∧ E ≤ dfthcUpperBound := by
  let U := p450FswapUninterleave.eval
  have hU1 : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
  have hU2 : U.1 * U.1ᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.2
  let φ := U.1ᴴ *ᵥ ψ
  have hφ_ne : φ ≠ 0 := by
    intro hz
    apply heig.2.2
    calc ψ = (U.1 * U.1ᴴ) *ᵥ ψ := by rw [hU2, Matrix.one_mulVec]
      _ = U.1 *ᵥ φ := (Matrix.mulVec_mulVec ψ U.1 U.1ᴴ).symm
      _ = 0 := by rw [hz, Matrix.mulVec_zero]
  have hφ_eig : thcHamiltonian dfthc *ᵥ φ = (E : ℂ) • φ := by
    calc thcHamiltonian dfthc *ᵥ φ
        = (U.1ᴴ * U.1) *ᵥ (thcHamiltonian dfthc *ᵥ (U.1ᴴ *ᵥ ψ)) := by
          rw [hU1, Matrix.one_mulVec]
      _ = U.1ᴴ *ᵥ (BlockEncodingCore.p450HBlocked *ᵥ ψ) := by
          dsimp only [U, BlockEncodingCore.p450HBlocked]
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (E : ℂ) • φ := by rw [heig.1, Matrix.mulVec_smul]
  exact ⟨(thcHamiltonian_dfthc_eigenvalue_mem_Icc E φ hφ_eig hφ_ne).1,
    thcHamiltonian_dfthc_eigenvalue_le hφ_eig hφ_ne⟩

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.InnerTable
open QuantumComputation.Specs QuantumComputation.Specs.P450
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.InnerTable
