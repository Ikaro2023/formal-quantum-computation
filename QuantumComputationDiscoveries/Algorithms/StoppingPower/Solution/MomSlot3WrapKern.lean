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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.NucTwistCatLem

@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section MomSlots35Slot3Helpers_aux
local instance (priority := 1000000) instNeZeroTwoPow_MomSlots35Slot3Helpers_aux (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Slot 3 (`U_pn(cfg)`, Coin `c = 6`) Concrete Clean-Workspace `DynamicCircuit` Oracle
(`MomSlots35Slot3ProjNuclear`)

Complete verified concrete
clean-workspace `DynamicCircuit` oracle, 48-wire phase-gradient catalyst intertwining proof,
Hadamard top-block extraction, spectral-norm cap `alphaSlot3 ≤ 20150 ≤ 20310` Ha, `permElectron`
symmetry proof, and fermionic-sector intrinsic error bound `≤ 3 / 10 ^ 6 ≤ 5 / 1000000` Ha for
**Slot 3 (`U_pn(cfg)`, `fullSysCoinIdx 3 = 6 = (0, 1, 1)_LSB`)**.
-/

public section

namespace MomSlots35Slot3ProjNuclear

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open MomSlots35Coulomb
open ModWrapCoarse8PureMomentum
open Slot5MatrixAndScaleCert
open SpecsAux.DyadicSubgridToeplitz512AndShift
open TwosCompAndWire0Cancel
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 2: 17-Wire Uniform Nucleus Bijection (`216 * 606 = 130896 ≤ 2 ^ 17`, `wt_3 = 1`) -/

/-! ## Section 3: Scale Cap (`alphaSlot3 ≤ 20150`), Hardware Two's-Complement `bTwosSlot3`,
`‖bUnitTwosSlot3‖ ≤ 1`, `permElectron` & `3 × 10⁻⁶` Ha Error -/

section ScaleAndOperatorBridge

attribute [local irreducible] box3D nonzeroBox3D

theorem dampedModWrapKernelApprox_38_36_127_eq (ν_true : Fin 3 → ℤ) :
    dampedModWrapKernelApprox 38 36 127 (2 / 42) 2 ν_true =
      2 * modWrapRadKernelApprox 38 127 (1 / 42) 1 ν_true := by
  unfold dampedModWrapKernelApprox
  rw [dampCoinConst_36_two_div_42_eq]
  push_cast
  ring

/-- Hardware two's-complement unnormalized Slot 3 operator `bTwosSlot3 cfg` on `systemQubits = 3948`
acting ONLY on the 24 projectile wires (`elecAxisField x i w = elecAxisField y i w`). -/
noncomputable def bTwosSlot3 (cfg : SpecsAux.SpecMirror.Configuration) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  open Classical in
  Matrix.of fun x y ↦
    if ProjTwosGridState x ∧ ProjTwosGridState y ∧
        (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
          elecAxisField x i w = elecAxisField y i w) then
      quantizedStructureFactorNearest 42 cfg
        (twosMomentum x .projectile - twosMomentum y .projectile) *
      (dampedModWrapKernelApprox 38 36 127 (2 / 42) 2
        (twosMomentum x .projectile - twosMomentum y .projectile) : ℂ)
    else 0

lemma fine38_le_two_pow_30_coarseEnv8 {ν Δ : Fin 3 → ℤ}
    (hν_mem : ν ∈ nonzeroBox3D (127 : ℤ)) (hbox : Δ ∈ box3D (2 * (127 : ℤ)))
    (hfold : modFold3D 127 Δ = ν) :
    dampedModWrapKernelApprox 38 36 127 (2 / 42) 2 Δ ≤ 2 * coarseBoxRadKernel8 ν := by
  have hnu_ne : ν ≠ 0 := (ne_zero_of_mem_nonzeroBox3D3 hν_mem)
  rw [dampedModWrapKernelApprox_38_36_127_eq]
  unfold modWrapRadKernelApprox coarseBoxRadKernel8
  rw [hfold]
  have hμ7 : shellIndex ν < 7 := shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν_mem
  have hs_pos : 0 < sumNatAbsSq ν := sumNatAbsSq_pos_of_ne_zero hnu_ne
  have hdom : sumNatAbsSq ν ≤ sumNatAbsSq Δ := by
    rw [← hfold]
    exact sumNatAbsSq_modFold3D_le 127 hbox
  set E := coarseEnv8Count (boxRadConst 36 (1 / 42) 1 (shellIndex ν)) (sumNatAbsSq ν)
  have hq_le : boxRadConst 38 (1 / 42) 1 (shellIndex ν) / sumNatAbsSq Δ ≤ 2 ^ 30 * E := by
    by_contra hgt
    have hlt_q : 0 + 2 ^ 30 * E < boxRadConst 38 (1 / 42) 1 (shellIndex ν) / sumNatAbsSq Δ := by
      omega
    have hcontr := fine38_imp_coarseEnv8_lt hμ7 hs_pos hdom hlt_q
    omega
  have hq_real : ((boxRadConst 38 (1 / 42) 1 (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 30 * (E : ℝ) := by exact_mod_cast hq_le
  have hpow : (2 : ℝ) ^ (2 * shellIndex ν + 38) =
      (2 : ℝ) ^ 30 * (2 : ℝ) ^ (2 * shellIndex ν + 8) := by
    rw [← pow_add]; congr 1; omega
  calc 2 * ((1 / 42 : ℝ) *
        ((boxRadConst 38 (1 / 42) 1 (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ) /
        (2 : ℝ) ^ (2 * shellIndex ν + 38))
      ≤ 2 * ((1 / 42 : ℝ) * ((2 : ℝ) ^ 30 * (E : ℝ)) /
        ((2 : ℝ) ^ 30 * (2 : ℝ) ^ (2 * shellIndex ν + 8))) := by
          rw [hpow]
          gcongr
    _ = 2 * ((1 / 42 : ℝ) * (E : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν + 8)) := by
          field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- Exact grid-state entry agreement between
`smToTwosSysUnitary * bTwosSlot3 cfg * smToTwosSysUnitary` and
`modWrapProjNucOp cfg 38 36 42 (2 / 42) 1` on ALL `(x, y)` with `IsGridState x ∧ IsGridState y`. -/
theorem smToTwosSysUnitary_conj_bTwosSlot3_on_grid (cfg : SpecsAux.SpecMirror.Configuration)
    {x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)} (hx : IsGridState x) (hy : IsGridState y) :
    (smToTwosSysUnitary.1 * bTwosSlot3 cfg * smToTwosSysUnitary.1) x y =
      modWrapProjNucOp cfg 38 36 42 (2 / 42) 1 x y := by
  classical
  have hentry : ∀ a b, (fwdPermUnitary smToTwosSysPerm).1 a b = if smToTwosSysPerm b = a then
      1 else 0 := fwdPermUnitary_apply smToTwosSysPerm
  change ((fwdPermUnitary smToTwosSysPerm).1 * bTwosSlot3 cfg *
      (fwdPermUnitary smToTwosSysPerm).1) x y = _
  rw [Matrix.mul_apply, Finset.sum_eq_single (smToTwosSysPerm y)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (smToTwosSysPerm x)]
    · have h1 : (fwdPermUnitary smToTwosSysPerm).1 x (smToTwosSysPerm x) = 1 := by
        rw [hentry, ite_true_eq (smToTwosSysPerm_self x)]
      have h2 : (fwdPermUnitary smToTwosSysPerm).1 (smToTwosSysPerm y) y = 1 := by
        rw [hentry, ite_true_eq rfl]
      rw [h1, h2, one_mul, mul_one]
      have hpx : ProjTwosGridState (smToTwosSysPerm x) :=
        ((isTwosGridState_smToTwosSysPerm_iff x).mpr hx).2
      have hpy : ProjTwosGridState (smToTwosSysPerm y) :=
        ((isTwosGridState_smToTwosSysPerm_iff y).mpr hy).2
      have hmx : ∀ d, twosMomentum (smToTwosSysPerm x) d = SpecsAux.SpecMirror.momentum x d :=
        twosMomentum_smToTwosSysPerm hx
      have hmy : ∀ d, twosMomentum (smToTwosSysPerm y) d = SpecsAux.SpecMirror.momentum y d :=
        twosMomentum_smToTwosSysPerm hy
      have he_iff : (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3, elecAxisField
          (smToTwosSysPerm x) i w = elecAxisField (smToTwosSysPerm y) i w) ↔ (∀ b ≠
          SpecsAux.SpecMirror.Particle.projectile, SpecsAux.SpecMirror.momentum x b =
          SpecsAux.SpecMirror.momentum y b) := by
        constructor
        · intro he b hb
          cases b with
          | projectile => exact (hb rfl).elim
          | electron i =>
              rw [← hmx (.electron i), ← hmy (.electron i)]
              ext w
              dsimp [twosMomentum]
              rw [he i w]
        · intro hm i w
          have hmi : twosMomentum (smToTwosSysPerm x) (.electron i) =
              twosMomentum (smToTwosSysPerm y) (.electron i) := by
            rw [hmx, hmy]
            exact hm (.electron i) (fun h ↦ SpecsAux.SpecMirror.Particle.noConfusion h)
          exact twosComp6Int_injective (congrFun hmi w)
      unfold bTwosSlot3 modWrapProjNucOp
      rw [Matrix.of_apply, Matrix.of_apply]
      by_cases he : ∀ b ≠ SpecsAux.SpecMirror.Particle.projectile,
          SpecsAux.SpecMirror.momentum x b = SpecsAux.SpecMirror.momentum y b
      · rw [ite_true_eq ⟨hpx, hpy, he_iff.mpr he⟩, ite_true_eq ⟨hx, hy, he⟩,
          hmx .projectile, hmy .projectile, Complex.ofReal_one, one_mul]
      · have hnotL : ¬(ProjTwosGridState (smToTwosSysPerm x) ∧ ProjTwosGridState
          (smToTwosSysPerm y) ∧ ∀ i w, elecAxisField (smToTwosSysPerm x) i w = elecAxisField
          (smToTwosSysPerm y) i w) := fun hc ↦ he (he_iff.mp hc.2.2)
        have hnotR : ¬(IsGridState x ∧ IsGridState y ∧
            ∀ b ≠ SpecsAux.SpecMirror.Particle.projectile,
              SpecsAux.SpecMirror.momentum x b = SpecsAux.SpecMirror.momentum y b) := fun hc ↦
                he hc.2.2
        rw [ite_false_eq hnotL, ite_false_eq hnotR]
    · intro a _ ha
      have hne : ¬(smToTwosSysPerm a = x) := fun heq ↦
        ha (by rw [← heq, smToTwosSysPerm_self a])
      rw [hentry, ite_false_eq hne, zero_mul]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  · intro b _ hb
    rw [hentry, ite_false_eq hb.symm, mul_zero]
  · intro hm; exact (hm (Finset.mem_univ _)).elim

attribute [local irreducible] bTwosSlot3

end ScaleAndOperatorBridge

end MomSlots35Slot3ProjNuclear
end
end MomSlots35Slot3Helpers_aux

end QuantumComputation.Specs.StoppingPowerSolution
