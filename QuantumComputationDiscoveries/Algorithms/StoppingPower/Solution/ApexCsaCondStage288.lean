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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosSlot4FermBridge

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModJunctionApexCSA288
@[expose] public section
namespace JunctionApexCSA288
section ConfigJunctionApexCSA288
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64Engine
open PosMomSelectSandwich
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open ProjZ512QftAndTwist288 hiding basisBits_symm_apply
  fullSysCoreWires_eq_add
open FusedVepCore288
local instance (priority := 1000000) instNeZeroTwoPowJunction (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
lemma fullSysCoreWires_eq_3954_add (mPayload : ℕ) : fullSysCoreWires mPayload = 3954 + mPayload :=
  by
  unfold fullSysCoreWires SpecsAux.SpecMirror.systemQubits SpecsAux.SpecMirror.numElectrons
    SpecsAux.SpecMirror.electronBits SpecsAux.SpecMirror.projectileBits
  omega
lemma bitsVal_basisBits_eq_val {q : ℕ} (v : Fin (2 ^ q)) : bitsVal (basisBits q v) = v.val :=
  _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal_basisBits v
@[scoped simp] lemma symm_bitsVal_eq {q : ℕ} (γ : BitAssignment q) :
    ((basisBitsEquiv q).symm γ).val = bitsVal γ :=
      (_root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal_eq_symm_val γ).symm
lemma zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by revert b; decide
lemma regVal_flipRegBits_add {k n : ℕ} (r : QRegister k n) (ξ : BitAssignment n) :
    regVal r (flipRegBits r ξ) + regVal r ξ = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ m ih =>
      have hhead : (flipRegBits r ξ (r 0)).val + (ξ (r 0)).val = 1 := by
        rw [show flipRegBits r ξ (r 0) = ξ (r 0) + 1 by
          simp [flipRegBits, (QRegister.mem_image r _).mpr ⟨0, rfl⟩]]
        generalize ξ (r 0) = b; revert b; decide
      have htail : regVal (r.slice 1 m (by omega)) (flipRegBits r ξ) =
          regVal (r.slice 1 m (by omega)) (flipRegBits (r.slice 1 m (by omega)) ξ) :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun j ↦ by
          simp [flipRegBits]
      have := ih (r.slice 1 m (by omega)); have := Nat.one_le_two_pow (n := m)
      rw [_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_head_tail r,
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_head_tail r, htail,
        pow_succ]; omega
lemma slice_apply_eq {m a l n : ℕ} (r : QRegister m n) (h : a + l ≤ m) (j : Fin l) :
    (r.slice a l h) j = r ⟨a + j.val, by omega⟩ := r.slice_apply a l h j
def intModFinPow2 (W : ℕ) (z : ℤ) : Fin (2 ^ W) :=
  ⟨(z % (2 ^ W : ℤ)).toNat, by
    have hpos : (0 : ℤ) < (2 ^ W : ℤ) := by positivity
    have hlt : ((z % (2 ^ W : ℤ)).toNat : ℤ) < ((2 ^ W : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg z (ne_of_gt hpos))]
      simpa using Int.emod_lt_of_pos z hpos
    exact_mod_cast hlt⟩
@[simp] lemma intModFinPow2_coe (W : ℕ) (z : ℤ) : ((intModFinPow2 W z).val : ℤ) = z % (2 ^ W : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (ne_of_gt (by positivity)))
lemma ediv_mul_add_intModFinPow2 (W : ℕ) (z : ℤ) :
    (2 ^ W : ℤ) * (z / (2 ^ W : ℤ)) + ((intModFinPow2 W z).val : ℤ) = z := by
  rw [intModFinPow2_coe]; exact Int.mul_ediv_add_emod z (2 ^ W : ℤ)
lemma intModFinPow2_nat_lt {W k : ℕ} (hk : k < 2 ^ W) : intModFinPow2 W (k : ℤ) = ⟨k, hk⟩ := by
  apply Fin.ext; zify; rw [intModFinPow2_coe]
  exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hk)
lemma intModFinPow2_add_right (W : ℕ) (z d : ℤ) :
    intModFinPow2 W (((intModFinPow2 W z).val : ℤ) + d) = intModFinPow2 W (z + d) := by
  apply Fin.ext; zify; simp only [intModFinPow2_coe, Int.emod_add_emod]
def winValA (A W : ℕ) (hW : W ≤ A) (γ : BitAssignment (A + 3)) : ℕ :=
  bitsVal (fun j : Fin W ↦ γ ⟨A - W + j.val, by omega⟩)
lemma winValA_lt (A W : ℕ) (hW : W ≤ A) (γ : BitAssignment (A + 3)) :
    winValA A W hW γ < 2 ^ W := bitsVal_lt_two_pow _
def replaceWinA (A W : ℕ) (_hW : W ≤ A) (γ : BitAssignment (A + 3)) (v : Fin (2 ^ W)) :
    BitAssignment (A + 3) := fun k ↦
  if hk : A - W ≤ k.val ∧ k.val < A then basisBits W v ⟨k.val - (A - W), by omega⟩ else γ k
lemma winValA_replaceWinA (A W : ℕ) (hW : W ≤ A) (γ : BitAssignment (A + 3)) (v : Fin (2 ^ W)) :
    winValA A W hW (replaceWinA A W hW γ v) = v.val := by
  unfold winValA replaceWinA
  rw [show (fun j : Fin W ↦ if hk : A - W ≤ A - W + j.val ∧ A - W + j.val < A then
      basisBits W v ⟨A - W + j.val - (A - W), by omega⟩ else γ ⟨A - W + j.val, by omega⟩) =
      basisBits W v from funext fun j ↦ by
    rw [dite_eq_left_of_eq_true (eq_true ⟨by omega, by have := j.isLt; omega⟩)]
    exact congrArg (basisBits W v) (Fin.ext (by dsimp; omega)), bitsVal_basisBits_eq_val]
lemma bitsVal_replaceWinA_add (A W : ℕ) (hW : W ≤ A) (γ : BitAssignment (A + 3)) (v : Fin (2 ^ W)) :
    bitsVal
    (replaceWinA A W hW γ v) + 2 ^ (A - W) * winValA A W hW γ = bitsVal γ + 2 ^ (A - W) * v.val :=
      by
  let P : Fin (A + 3) → Prop := fun k ↦ A - W ≤ k.val ∧ k.val < A
  have hOut : ∑ k ∈ Finset.univ.filter (fun k : Fin (A + 3) ↦ ¬P k),
      (replaceWinA A W hW γ v k).val * 2 ^ k.val =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (A + 3) ↦ ¬P k), (γ k).val * 2 ^ k.val :=
    Finset.sum_congr rfl fun k hk ↦ by
      unfold replaceWinA
      rw [dite_eq_right_of_eq_false (eq_false (Finset.mem_filter.mp hk).2)]
  have hBij (f : Fin (A + 3) → ℕ) : (∑ k ∈ Finset.univ.filter P, f k * 2 ^ k.val) =
      2 ^ (A - W) * ∑ j : Fin W, f ⟨A - W + j.val, by omega⟩ * 2 ^ j.val := by
    rw [Finset.mul_sum]
    refine (Finset.sum_bij (fun (j : Fin W) _ ↦ (⟨A - W + j.val, by omega⟩ : Fin (A + 3)))
      (fun j _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        show A - W ≤ A - W + j.val ∧ A - W + j.val < A by omega⟩)
      (fun j₁ _ j₂ _ hEq ↦ Fin.ext (Nat.add_left_cancel (Fin.mk.inj hEq)))
      (fun k hk ↦ ⟨⟨k.val - (A - W), by
          have h := (Finset.mem_filter.mp hk).2
          omega⟩,
        Finset.mem_univ _, Fin.ext (by
          have h := (Finset.mem_filter.mp hk).2
          dsimp
          omega)⟩)
      (fun j _ ↦ by
        dsimp only
        rw [pow_add]
        ring)).symm
  change (∑ k : Fin (A + 3), (replaceWinA A W hW γ v k).val * 2 ^ k.val) + _ =
    (∑ k : Fin (A + 3), (γ k).val * 2 ^ k.val) + _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P (fun k ↦ (replaceWinA A W hW γ v k).val *
    2 ^ k.val),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ P (fun k ↦ (γ k).val * 2 ^ k.val),
    hOut, hBij (fun k ↦ (replaceWinA A W hW γ v k).val), hBij (fun k ↦ (γ k).val)]
  change 2 ^ (A - W) * winValA A W hW (replaceWinA A W hW γ v) + _ + _ = 2 ^ (A - W) * winValA A W
    hW γ + _ + _
  rw [winValA_replaceWinA A W hW γ v]
  ring
def stepWinAFin (A W : ℕ) (hW : W ≤ A) (d : ℤ) (m : Fin (2 ^ (A + 3))) : Fin (2 ^ (A + 3)) :=
  (basisBitsEquiv (A + 3)).symm (replaceWinA A W hW (basisBits (A + 3) m)
    (intModFinPow2 W ((winValA A W hW (basisBits (A + 3) m) : ℤ) + d)))
lemma stepWinAFin_zero (A W : ℕ) (hW : W ≤ A) (m : Fin (2 ^ (A + 3))) : stepWinAFin A W hW 0 m =
    m := by
  let γ := basisBits (A + 3) m
  unfold stepWinAFin
  rw [add_zero, intModFinPow2_nat_lt (winValA_lt A W hW γ),
    show (⟨winValA A W hW γ, winValA_lt A W hW γ⟩ : Fin (2 ^ W)) =
      (basisBitsEquiv W).symm (fun j : Fin W ↦ γ ⟨A - W + j.val, by omega⟩) from
      Fin.ext (by rw [symm_bitsVal_eq]; rfl),
    show replaceWinA A W hW γ ((basisBitsEquiv W).symm (fun j : Fin W ↦ γ ⟨A - W + j.val,
      by omega⟩)) = γ from
      funext fun k ↦ by
        unfold replaceWinA; split_ifs with hk
        · change (basisBitsEquiv W) ((basisBitsEquiv W).symm _) _ = γ k
          rw [(basisBitsEquiv W).apply_symm_apply]; exact congrArg γ (Fin.ext (by dsimp; omega))
        · rfl,
    basisBitsEquiv_symm_basisBits_eq]
lemma stepWinAFin_step (A W : ℕ) (hW : W ≤ A) (d₁ d₂ : ℤ) (m : Fin (2 ^ (A + 3))) :
    stepWinAFin A W hW d₂ (stepWinAFin A W hW d₁ m) = stepWinAFin A W hW (d₁ + d₂) m := by
  unfold stepWinAFin
  rw [basisBits_basisBitsEquiv_symm_eq, winValA_replaceWinA,
    show ∀ (γ : BitAssignment (A + 3)) (v₁ v₂ : Fin (2 ^ W)),
      replaceWinA A W hW (replaceWinA A W hW γ v₁) v₂ = replaceWinA A W hW γ v₂ from
      fun _ _ _ ↦ funext fun _ ↦ by dsimp only [replaceWinA]; split_ifs <;> rfl,
    intModFinPow2_add_right, add_assoc]
def apexWinMidPermA (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys → ℤ) :
    Equiv.Perm (BitAssignment kSys × Fin (2 ^ (A + 3))) where
  toFun p := (p.1, stepWinAFin A W hW (δ p.1) p.2)
  invFun p := (p.1, stepWinAFin A W hW (-δ p.1) p.2)
  left_inv p := Prod.ext rfl (by dsimp; rw [stepWinAFin_step, add_neg_cancel, stepWinAFin_zero])
  right_inv p := Prod.ext rfl (by dsimp; rw [stepWinAFin_step, neg_add_cancel, stepWinAFin_zero])
def apexWinPermA (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys → ℤ) : Equiv.Perm (Fin (2 ^
    (kSys + (A + 3)))) :=
  (splitSysCatEquiv kSys (A + 3)).trans ((apexWinMidPermA kSys A W hW δ).trans (splitSysCatEquiv
    kSys (A + 3)).symm)
lemma apexWinPermA_apply (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys → ℤ) (x : Fin (2 ^
    (kSys + (A + 3)))) :
    apexWinPermA kSys A W hW δ x = (splitSysCatEquiv kSys (A + 3)).symm ((splitSysCatEquiv kSys (A +
      3) x).1,
    stepWinAFin A W hW (δ (splitSysCatEquiv kSys (A + 3) x).1) (splitSysCatEquiv kSys (A +
      3) x).2) := by
  unfold apexWinPermA apexWinMidPermA; simp only [Equiv.trans_apply, Equiv.coe_fn_mk]
lemma apexWinPermA_symm_apply (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys →
    ℤ) (γ : BitAssignment kSys) (m : Fin
    (2 ^ (A + 3))) : apexWinPermA kSys A W hW δ ((splitSysCatEquiv kSys (A + 3)).symm (γ, m)) =
      (splitSysCatEquiv kSys
    (A + 3)).symm (γ, stepWinAFin A W hW (δ γ) m) := by
  unfold apexWinPermA apexWinMidPermA
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.coe_fn_mk]
def apexCarryExpA (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys → ℤ) :
    BitAssignment (kSys + (A + 3)) → ℤ := fun β ↦
  ((winValA A W hW (fun k ↦ β (Fin.natAdd kSys k)) : ℤ) + δ (fun i ↦ β (Fin.castAdd (A +
    3) i))) / (2 ^ W : ℤ)
noncomputable def uApexShiftA (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys → ℤ) :
    Unitary (2 ^ (kSys + (A + 3))) :=
  Operator.permutationUnitary (apexWinPermA kSys A W hW δ) *
    DyadicQft64.dyadicDiagUnitary (kSys + (A + 3)) 3 (apexCarryExpA kSys A W hW δ)
lemma basisBits_splitSysCatEquiv_symm_castAdd {kSys B : ℕ} (γ : BitAssignment kSys) (m : Fin (2 ^
    B)) (i : Fin kSys) :
    basisBits (kSys + B) ((splitSysCatEquiv kSys B).symm (γ, m)) (Fin.castAdd B i) = γ i := by
  change (basisBitsEquiv (kSys + B)) ((splitSysCatEquiv kSys B).symm (γ, m)) (Fin.castAdd B i) = γ i
  simp [splitSysCatEquiv]
lemma basisBits_splitSysCatEquiv_symm_natAdd {kSys B : ℕ} (γ : BitAssignment kSys) (m : Fin (2 ^ B))
    (j : Fin B) :
    basisBits (kSys + B) ((splitSysCatEquiv kSys B).symm (γ, m)) (Fin.natAdd kSys j) = basisBits B m
      j := by
  change (basisBitsEquiv (kSys + B)) ((splitSysCatEquiv kSys B).symm (γ, m)) (Fin.natAdd kSys j) =
    basisBits B m j
  simp [splitSysCatEquiv]
lemma uApexShiftA_mulVec_single {kSys A W : ℕ} (hW : W ≤ A) (δ : BitAssignment kSys → ℤ) (x : Fin (2
    ^ (kSys + (A +
    3)))) : (uApexShiftA kSys A W hW δ).1.mulVec (Pi.single x (1 : ℂ)) = DyadicQft64.dyadicTurn 3
      (apexCarryExpA kSys A
    W hW δ (basisBits (kSys + (A + 3)) x)) • Pi.single (apexWinPermA kSys A W hW δ x) (1 : ℂ) := by
  have hdiag : (DyadicQft64.dyadicDiagUnitary (kSys + (A + 3)) 3 (apexCarryExpA kSys A W hW
    δ)).1.mulVec
      (Pi.single x (1 : ℂ)) = DyadicQft64.dyadicTurn 3
        (apexCarryExpA kSys A W hW δ (basisBits (kSys + (A + 3)) x)) • Pi.single x (1 : ℂ) := by
    have hemb := embedUnitary_dyadicDiagUnitary_mulVec_basisKet
      (QRegExt.idReg (kSys + (A + 3))) 3 (apexCarryExpA kSys A W hW δ) (basisBits (kSys + (A +
        3)) x)
    rw [embedUnitary_idReg_eq] at hemb
    rw [pi_single_eq_basisKet x, hemb]; rfl
  rw [uApexShiftA, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul,
    Operator.permutationUnitary_mulVec_single]
lemma uApexShiftA_zero (kSys A W : ℕ) (hW : W ≤ A) :
    uApexShiftA kSys A W hW (fun _ ↦ 0) = 1 := by
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  let x := (basisBitsEquiv (kSys + (A + 3))).symm β
  rw [show basisKet β = Pi.single x (1 : ℂ) from rfl, uApexShiftA_mulVec_single,
    Submonoid.coe_one, Matrix.one_mulVec, apexWinPermA_apply, stepWinAFin_zero,
    Prod.mk.eta, Equiv.symm_apply_apply,
    show apexCarryExpA kSys A W hW (fun _ ↦ 0) (basisBits (kSys + (A + 3)) x) = 0 from by
      unfold apexCarryExpA
      rw [add_zero]
      exact Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast winValA_lt A W hW _),
    DyadicQft64.dyadicTurn_zero, one_smul]
lemma uApexShiftA_mul (kSys A W : ℕ) (hW : W ≤ A) (δ₁ δ₂ : BitAssignment kSys → ℤ) :
    uApexShiftA kSys A W hW δ₂ * uApexShiftA kSys A W hW δ₁ =
      uApexShiftA kSys A W hW (fun γ ↦ δ₁ γ + δ₂ γ) := by
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  let x := (basisBitsEquiv (kSys + (A + 3))).symm β
  let p := splitSysCatEquiv kSys (A + 3) x
  have hx : x = (splitSysCatEquiv kSys (A + 3)).symm (p.1, p.2) := by
    dsimp only [p]
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  have hExp (δ : BitAssignment kSys → ℤ) (m : Fin (2 ^ (A + 3))) :
      apexCarryExpA kSys A W hW δ
        (basisBits (kSys + (A + 3)) ((splitSysCatEquiv kSys (A + 3)).symm (p.1, m))) =
        ((winValA A W hW (basisBits (A + 3) m) : ℤ) + δ p.1) / (2 ^ W : ℤ) := by
    unfold apexCarryExpA
    rw [show (fun k ↦ basisBits (kSys + (A + 3)) ((splitSysCatEquiv kSys (A + 3)).symm (p.1, m))
          (Fin.natAdd kSys k)) = basisBits (A + 3) m from
          funext (basisBits_splitSysCatEquiv_symm_natAdd p.1 m),
        show (fun i ↦ basisBits (kSys + (A + 3)) ((splitSysCatEquiv kSys (A + 3)).symm (p.1, m))
          (Fin.castAdd (A + 3) i)) = p.1 from
          funext (basisBits_splitSysCatEquiv_symm_castAdd p.1 m)]
  rw [Submonoid.coe_mul, show basisKet β = Pi.single x (1 : ℂ) from rfl, ← Matrix.mulVec_mulVec, hx,
      uApexShiftA_mulVec_single, Matrix.mulVec_smul, apexWinPermA_symm_apply,
        uApexShiftA_mulVec_single,
      uApexShiftA_mulVec_single, apexWinPermA_symm_apply, apexWinPermA_symm_apply, stepWinAFin_step,
        smul_smul,
      DyadicQft64.dyadicTurn_add, hExp, hExp, hExp]
  congr 2
  let K : ℤ := (winValA A W hW (basisBits (A + 3) p.2) : ℤ)
  let r₁ := intModFinPow2 W (K + δ₁ p.1)
  rw [show (winValA A W hW (basisBits (A + 3) (stepWinAFin A W hW (δ₁ p.1) p.2)) : ℤ) =
      (r₁.val : ℤ) from by
        unfold stepWinAFin
        rw [basisBits_basisBitsEquiv_symm_eq, winValA_replaceWinA]]
  have hr_coe : ((intModFinPow2 W ((r₁.val : ℤ) + δ₂ p.1)).val : ℤ) =
      ((intModFinPow2 W (K + (δ₁ p.1 + δ₂ p.1))).val : ℤ) := by
    dsimp only [r₁]
    rw [intModFinPow2_add_right, add_assoc]
  have hmul : (2 ^ W : ℤ) * (((r₁.val : ℤ) + δ₂ p.1) / (2 ^ W : ℤ) + (K + δ₁ p.1) / (2 ^ W : ℤ) -
      (K + (δ₁ p.1 + δ₂ p.1)) / (2 ^ W : ℤ)) = 0 := by
    linear_combination ediv_mul_add_intModFinPow2 W (K + δ₁ p.1) +
      ediv_mul_add_intModFinPow2 W ((r₁.val : ℤ) + δ₂ p.1) -
      ediv_mul_add_intModFinPow2 W (K + (δ₁ p.1 + δ₂ p.1)) - hr_coe
  have hsub := (mul_eq_zero.mp hmul).resolve_left (by positivity : (2 ^ W : ℤ) ≠ 0)
  linarith
lemma uApexShiftA_inv (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys → ℤ) :
    (uApexShiftA kSys A W hW δ)⁻¹ = uApexShiftA kSys A W hW (fun γ ↦ -δ γ) := by
  apply inv_eq_of_mul_eq_one_left
  rw [uApexShiftA_mul, show (fun γ ↦ δ γ + -δ γ) = fun _ ↦ (0 : ℤ) from funext fun _ ↦
    add_neg_cancel _,
    uApexShiftA_zero]
lemma uApexShiftA_comm_coreDiag (kSys A W : ℕ) (hW : W ≤ A) (B : ℕ)
    (e : BitAssignment kSys → ℤ) (δ : BitAssignment kSys → ℤ) :
    (QRegister.block 0 kSys (by omega : 0 + kSys ≤ kSys + (A + 3))).embedUnitary
        (DyadicQft64.dyadicDiagUnitary kSys B e) * uApexShiftA kSys A W hW δ =
      uApexShiftA kSys A W hW δ *
        (QRegister.block 0 kSys (by omega : 0 + kSys ≤ kSys + (A + 3))).embedUnitary
          (DyadicQft64.dyadicDiagUnitary kSys B e) := by
  let rSys0 : QRegister kSys (kSys + (A + 3)) := QRegister.block 0 kSys (by omega)
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  let x := (basisBitsEquiv (kSys + (A + 3))).symm β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul,
    show basisKet β = Pi.single x (1 : ℂ) from rfl, uApexShiftA_mulVec_single, Matrix.mulVec_smul,
    smul_smul, pi_single_eq_basisKet, embedUnitary_dyadicDiagUnitary_mulVec_basisKet, smul_smul]
  refine congrArg (· • _) ?_
  rw [show (fun i ↦ basisBits (kSys + (A + 3)) (apexWinPermA kSys A W hW δ x) (rSys0 i)) =
      (fun i ↦ β (rSys0 i)) from funext fun i ↦ by
        have hr : rSys0 i = Fin.castAdd (A + 3) i := Fin.ext (by simp [rSys0])
        rw [hr, apexWinPermA_apply, basisBits_splitSysCatEquiv_symm_castAdd]
        change basisBits (kSys + (A + 3)) x (Fin.castAdd (A + 3) i) = _
        simp [x], mul_comm]
noncomputable def phaseGradNorm (b : ℕ) : ℂ := phaseGradKet b ⟨0, Nat.two_pow_pos b⟩
lemma phaseGradKet_eq_norm_dyadicTurn (b : ℕ) (m : Fin (2 ^ b)) :
    phaseGradKet b m = phaseGradNorm b * DyadicQft64.dyadicTurn b (-(m.val : ℤ)) := by
  unfold phaseGradNorm phaseGradKet DyadicQft64.dyadicTurn; dsimp only
  simp only [Nat.cast_zero, mul_zero, neg_zero, zero_div, Complex.exp_zero, mul_one]
  congr 2; push_cast; ring
lemma dyadicTurn3_eq_dyadicTurnA3_mul (A : ℕ) (z : ℤ) :
    DyadicQft64.dyadicTurn 3 z = DyadicQft64.dyadicTurn (A + 3) ((2 ^ A : ℤ) * z) :=
  (DyadicQft64Engine.turnPow2_scale_pow A 3 z).symm
theorem uApexShiftA_intertwinesLocal (kSys A W : ℕ) (hW : W ≤ A) (δ : BitAssignment kSys → ℤ)
    (U_cat : Unitary (2 ^ (A + 3))) (hcol0 : U_cat.1.mulVec (Pi.single 0 1) = phaseGradKet (A +
      3)) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat (uApexShiftA kSys A W hW δ)
      (DyadicQft64.dyadicDiagUnitary kSys (A + 3) (fun γ ↦ (2 ^ (A - W) : ℤ) * δ γ)) := by
  let rAct0 : QRegister kSys (kSys + (A + 3)) := .block 0 kSys (by omega)
  let rCat0 : QRegister (A + 3) (kSys + (A + 3)) := .block kSys (A + 3) le_rfl
  have hdisj : rAct0.DisjointWires rCat0 := QRegExt.disjointWires_of_finset
    (Finset.disjoint_left.mpr fun u hu1 hu2 ↦ by
    rcases (QRegister.mem_image rAct0 u).mp hu1 with ⟨i, rfl⟩
    rcases (QRegister.mem_image rCat0 _).mp hu2 with ⟨j, hj⟩
    have hv := congrArg Fin.val hj; simp [rAct0, rCat0] at hv; omega)
  refine ⟨?_, rAct0.embedMatrix_comm_of_disjoint rCat0 hdisj _ _,
    rAct0.embedMatrix_comm_of_disjoint rCat0 hdisj _ (compProj 0)⟩
  apply matrix_ext_basisKet; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, reg_zero_proj_mulVec_basisKet]
  split_ifs with hzero
  · let idx₀ := (basisBitsEquiv (kSys + (A + 3))).symm β
    let γ : BitAssignment kSys := fun i ↦ β (rAct0 i)
    have hext0 : rCat0.extractIndex idx₀ = 0 := by
      unfold QRegister.extractIndex
      rw [show (fun j ↦ basisBits (kSys + (A + 3)) idx₀ (rCat0 j)) = basisBits (A + 3) 0 from funext
        fun j ↦ by
        rw [basisBits_zero_at]; change basisBits _ ((basisBitsEquiv _).symm β) _ = 0
        rw [basisBits_basisBitsEquiv_symm_eq]; exact hzero j, basisBitsEquiv_symm_basisBits_eq]
    have hprep : (rCat0.embedUnitary U_cat).1.mulVec (basisKet β) = ∑ m : Fin (2 ^ (A + 3)),
        phaseGradKet (A + 3) m • Pi.single (rCat0.replaceIndex idx₀ m) (1 : ℂ) := by
      conv_lhs =>
        rw [QRegister.embedUnitary_val, basisKet, basisState,
          rCat0.embedMatrix_mulVec_single_factors,
        hext0, hcol0, show phaseGradKet (A + 3) = ∑ m : Fin (2 ^ (A + 3)), phaseGradKet (A +
          3) m • Pi.single m (1 : ℂ) from
          funext fun x ↦ by
            rw [Finset.sum_apply, Finset.sum_eq_single x (fun m _ hmx ↦ by
              simp [Pi.single_eq_of_ne hmx.symm])
            (fun hx ↦ absurd (Finset.mem_univ x) hx)]; simp, rCat0.tensorState_sum_left]
      exact Finset.sum_congr rfl fun m _ ↦ by
        rw [rCat0.tensorState_smul_left, rCat0.tensorState_single_replaceIndex]
    rw [embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul, hprep,
      Matrix.mulVec_sum, Finset.smul_sum]
    have hSplitIdx (m : Fin (2 ^ (A + 3))) : rCat0.replaceIndex idx₀ m = (splitSysCatEquiv kSys (A +
      3)).symm (γ, m) :=
      (basisBitsEquiv (kSys + (A + 3))).injective (funext fun w ↦ Fin.addCases
        (fun i ↦ by
          change basisBits _ _ _ = basisBits _ _ _; rw [basisBits_splitSysCatEquiv_symm_castAdd,
            show Fin.castAdd (A + 3) i = rAct0 i from Fin.ext (by simp [rAct0]),
            rCat0.basisBits_replaceIndex_of_not_mem idx₀ m (rAct0 i) fun ⟨k, hk⟩ ↦ hdisj.ne i k
              hk.symm]; simp [γ, idx₀])
        (fun j ↦ by
          change basisBits _ _ _ = basisBits _ _ _; rw [basisBits_splitSysCatEquiv_symm_natAdd,
            show Fin.natAdd kSys j = rCat0 j from Fin.ext (by simp [rCat0])]
          exact rCat0.basisBits_replaceIndex_apply idx₀ m j) w)
    let e_m : Equiv.Perm (Fin (2 ^ (A + 3))) := ⟨stepWinAFin A W hW (δ γ), stepWinAFin A W hW (-δ
      γ),
      fun _ ↦ by rw [stepWinAFin_step, add_neg_cancel, stepWinAFin_zero],
      fun _ ↦ by rw [stepWinAFin_step, neg_add_cancel, stepWinAFin_zero]⟩
    have hstep (m : Fin (2 ^ (A + 3))) : (uApexShiftA kSys A W hW δ).1.mulVec (Pi.single
      (rCat0.replaceIndex idx₀ m) (1 : ℂ)) =
        DyadicQft64.dyadicTurn 3 (((winValA A W hW (basisBits (A + 3) m) : ℤ) + δ γ) / (2 ^ W : ℤ))
          •
          Pi.single (rCat0.replaceIndex idx₀ (e_m m)) (1 : ℂ) := by
      rw [uApexShiftA_mulVec_single, show apexWinPermA kSys A W hW δ (rCat0.replaceIndex idx₀ m) =
        rCat0.replaceIndex idx₀ (e_m m) by
          rw [hSplitIdx m, hSplitIdx (e_m m)]; exact apexWinPermA_symm_apply kSys A W hW δ γ m,
        show apexCarryExpA kSys A W hW δ (basisBits (kSys + (A + 3)) (rCat0.replaceIndex idx₀ m)) =
            ((winValA A W hW (basisBits (A + 3) m) : ℤ) + δ γ) / (2 ^ W : ℤ) by
          rw [hSplitIdx m]; unfold apexCarryExpA
          rw [funext (basisBits_splitSysCatEquiv_symm_natAdd γ m),
            funext (basisBits_splitSysCatEquiv_symm_castAdd γ m)]]
    simp_rw [Matrix.mulVec_smul, hstep, smul_smul]; rw [← e_m.symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    let m := e_m.symm k
    have hmk : e_m m = k := e_m.apply_symm_apply k
    let K_m : ℕ := winValA A W hW (basisBits (A + 3) m)
    let q_m : ℤ := ((K_m : ℤ) + δ γ) / (2 ^ W : ℤ)
    let r_m : Fin (2 ^ W) := intModFinPow2 W ((K_m : ℤ) + δ γ)
    change (phaseGradKet (A + 3) m * DyadicQft64.dyadicTurn 3 q_m) • Pi.single (rCat0.replaceIndex
      idx₀ (e_m m)) (1 : ℂ) =
      (DyadicQft64.dyadicTurn (A + 3) ((2 ^ (A - W) : ℤ) * δ γ) * phaseGradKet (A +
        3) k) • Pi.single (rCat0.replaceIndex idx₀ k) (1 : ℂ)
    rw [hmk]; congr 1
    have hbits_add := bitsVal_replaceWinA_add A W hW (basisBits (A + 3) m) r_m
    rw [← (show k.val = bitsVal (replaceWinA A W hW (basisBits (A + 3) m) r_m) by
      rw [← (show stepWinAFin A W hW (δ γ) m = k from hmk)]; unfold stepWinAFin
      rw [symm_bitsVal_eq]),
      bitsVal_basisBits_eq_val] at hbits_add
    have hbits_z : (k.val : ℤ) + (2 ^ (A - W) : ℤ) * (K_m : ℤ) = (m.val : ℤ) + (2 ^ (A - W) : ℤ) *
      (r_m.val : ℤ) := by
      exact_mod_cast hbits_add
    have hexp_eq : -(m.val : ℤ) + (2 ^ A : ℤ) * q_m = (2 ^ (A - W) : ℤ) * δ γ + -(k.val : ℤ) := by
      rw [← show (2 ^ (A - W) : ℤ) * (2 ^ W : ℤ) = (2 ^ A : ℤ) by rw [← pow_add]; congr 1; omega]
      linear_combination (2 ^ (A - W) : ℤ) * ediv_mul_add_intModFinPow2 W ((K_m : ℤ) + δ γ) +
        hbits_z
    rw [phaseGradKet_eq_norm_dyadicTurn (A + 3) m, phaseGradKet_eq_norm_dyadicTurn (A + 3) k,
      dyadicTurn3_eq_dyadicTurnA3_mul A, mul_assoc, DyadicQft64.dyadicTurn_add, hexp_eq,
        ← DyadicQft64.dyadicTurn_add]
    ring
  · simp
noncomputable def shiftRegInt {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) (d : ℤ) :
    BitAssignment n := fun w ↦
  if hw : ∃ j : Fin W, rT j = w then basisBits W (intModFinPow2 W ((regVal rT ξ : ℤ) + d)) hw.choose
    else ξ w
noncomputable def apexCarryPhase {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) (d : ℤ) : ℂ :=
  DyadicQft64.dyadicTurn 3 (((regVal rT ξ : ℤ) + d) / (2 ^ W : ℤ))
lemma shiftRegInt_outside {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) (d : ℤ)
    {w : Wire n} (hw : w ∉ rT.image) : shiftRegInt rT ξ d w = ξ w :=
  dite_eq_right_of_eq_false (eq_false fun ⟨j, hj⟩ ↦ hw ((QRegister.mem_image rT w).mpr ⟨j, hj⟩))
@[simp] lemma shiftRegInt_apply_reg {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) (d : ℤ)
    (j : Fin W) : shiftRegInt rT ξ d (rT j) = basisBits W (intModFinPow2 W ((regVal rT ξ : ℤ) +
      d)) j := by
  unfold shiftRegInt; have hex : ∃ k : Fin W, rT k = rT j := ⟨j, rfl⟩
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg (basisBits _ _) (rT.wires.injective hex.choose_spec)
lemma regVal_shiftRegInt {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) (d : ℤ) :
    regVal rT (shiftRegInt rT ξ d) = (intModFinPow2 W ((regVal rT ξ : ℤ) + d)).val := by
  conv_lhs => unfold regVal
  rw [funext (shiftRegInt_apply_reg rT ξ d), bitsVal_basisBits_eq_val]
lemma eq_shiftRegInt_of_outside_and_regVal {W n : ℕ} (rT : QRegister W n)
    (α ξ : BitAssignment n) (d : ℤ) (hout : ∀ w, w ∉ rT.image → α w = ξ w)
    (hval : regVal rT α = (intModFinPow2 W ((regVal rT ξ : ℤ) + d)).val) : α = shiftRegInt rT ξ d :=
      by
  funext w; by_cases hw : w ∈ rT.image
  · rcases (QRegister.mem_image rT w).mp hw with ⟨j, rfl⟩
    rw [shiftRegInt_apply_reg, show intModFinPow2 W ((regVal rT ξ : ℤ) + d) =
      (basisBitsEquiv W).symm (fun k ↦ α (rT k)) from Fin.ext (by
        rw [symm_bitsVal_eq]; exact hval.symm),
      basisBits_basisBitsEquiv_symm_eq]
  · rw [hout w hw, shiftRegInt_outside rT ξ d hw]
theorem embed_uApexShiftA_mulVec_basisKet {kSys A W n : ℕ} (hW : W ≤ A)
    (rSys : QRegister kSys n) (rCat : QRegister (A + 3) n) (hdisj : rSys.DisjointWires rCat)
    (δ : BitAssignment kSys → ℤ) (ξ : BitAssignment n) :
    ((rSys.concat rCat hdisj).embedUnitary (uApexShiftA kSys A W hW δ)).1.mulVec (basisKet ξ) =
      apexCarryPhase (rCat.slice (A - W) W (by omega)) ξ (δ (fun i ↦ ξ (rSys i))) •
        basisKet (shiftRegInt (rCat.slice (A - W) W (by omega)) ξ (δ (fun i ↦ ξ (rSys i)))) := by
  let rSC := rSys.concat rCat hdisj
  let rWin := rCat.slice (A - W) W (by omega)
  let idx₀ := (basisBitsEquiv n).symm ξ
  let x₀ := rSC.extractIndex idx₀
  have hext_sys : (fun i ↦ basisBits (kSys + (A + 3)) x₀ (Fin.castAdd (A + 3) i)) =
      fun i ↦ ξ (rSys i) := funext fun i ↦ by simp [x₀, rSC, idx₀]
  have hext_cat : (fun k ↦ basisBits (kSys + (A + 3)) x₀ (Fin.natAdd kSys k)) =
      fun k ↦ ξ (rCat k) := funext fun k ↦ by simp [x₀, rSC, idx₀]
  rw [QRegister.embedUnitary_val, show basisKet ξ = Pi.single idx₀ (1 : ℂ) from rfl,
    rSC.embedMatrix_mulVec_single_factors, uApexShiftA_mulVec_single, rSC.tensorState_smul_left,
    rSC.tensorState_single_replaceIndex,
    show DyadicQft64.dyadicTurn 3 (apexCarryExpA kSys A W hW δ (basisBits (kSys + (A + 3)) x₀)) =
      apexCarryPhase rWin ξ (δ (fun i ↦ ξ (rSys i))) from by
        unfold apexCarryExpA apexCarryPhase
        rw [hext_cat, hext_sys]
        rfl,
    pi_single_eq_basisKet]
  congr 1
  congr 1
  let p₀ := splitSysCatEquiv kSys (A + 3) x₀
  have hp1 : p₀.1 = fun i ↦ ξ (rSys i) := hext_sys
  have hp2 : basisBits (A + 3) p₀.2 = fun k ↦ ξ (rCat k) := by
    change basisBits (A + 3) ((basisBitsEquiv (A + 3)).symm _) = _
    rw [basisBits_basisBitsEquiv_symm_eq]
    exact hext_cat
  have hperm := apexWinPermA_apply kSys A W hW δ x₀
  apply eq_shiftRegInt_of_outside_and_regVal rWin _ ξ (δ (fun i ↦ ξ (rSys i)))
  · intro w hwNotWin
    by_cases hwSC : w ∈ Set.range rSC.wires
    · rcases hwSC with ⟨idx, rfl⟩
      rw [rSC.basisBits_replaceIndex_apply, hperm]
      revert hwNotWin
      refine Fin.addCases (fun i _ ↦ ?_) (fun k hwNotWin ↦ ?_) idx
      · rw [QRegister.concat_apply_left, basisBits_splitSysCatEquiv_symm_castAdd, hp1]
      · rw [QRegister.concat_apply_right, basisBits_splitSysCatEquiv_symm_natAdd]
        unfold stepWinAFin replaceWinA
        rw [basisBits_basisBitsEquiv_symm_eq, dite_eq_right_of_eq_false (eq_false fun hkIn ↦
          hwNotWin
          ((QRegister.mem_image rWin _).mpr ⟨⟨k.val - (A - W), by omega⟩, by
            dsimp only [rWin, rSC]
            rw [slice_apply_eq, QRegister.concat_apply_right]
            exact congrArg rCat (Fin.ext (by
              dsimp
              omega))⟩)), hp2]
    · rw [rSC.basisBits_replaceIndex_of_not_mem idx₀ _ w hwSC]
      simp [idx₀]
  · conv_lhs => unfold regVal
    rw [show (fun j : Fin W ↦ basisBits n (rSC.replaceIndex idx₀ (apexWinPermA kSys A W hW δ x₀))
      (rWin j)) =
        basisBits W (intModFinPow2 W ((regVal rWin ξ : ℤ) + δ (fun i ↦ ξ (rSys i)))) from funext
          fun j ↦ by
      let k : Fin (A + 3) := ⟨A - W + j.val, by omega⟩
      rw [show rWin j = rSC (Fin.natAdd kSys k) from by
            dsimp only [rWin, rSC]
            rw [slice_apply_eq, QRegister.concat_apply_right],
          rSC.basisBits_replaceIndex_apply, hperm, basisBits_splitSysCatEquiv_symm_natAdd]
      unfold stepWinAFin replaceWinA
      rw [basisBits_basisBitsEquiv_symm_eq,
        dite_eq_left_of_eq_true (eq_true (show A - W ≤ k.val ∧ k.val < A by
          dsimp [k]
          omega)),
        hp2, hp1]
      exact congrArg (basisBits _ _) (Fin.ext (by
        dsimp [k]
        omega)),
      bitsVal_basisBits_eq_val]
noncomputable abbrev uApexShift45 (kSys W : ℕ) (hW : W ≤ 45) (δ : BitAssignment kSys → ℤ) :
    Unitary (2 ^ (kSys + 48)) := uApexShiftA kSys 45 W hW δ
lemma uApexShift45_inv (kSys W : ℕ) (hW : W ≤ 45) (δ : BitAssignment kSys → ℤ) :
    (uApexShift45 kSys W hW δ)⁻¹ = uApexShift45 kSys W hW (fun γ ↦ -δ γ) := uApexShiftA_inv kSys 45
      W hW δ
lemma uApexShift45_comm_coreDiag (kSys W : ℕ) (hW : W ≤ 45) (B : ℕ)
    (e δ : BitAssignment kSys → ℤ) :
    (QRegister.block 0 kSys (by omega : 0 + kSys ≤ kSys + 48)).embedUnitary
        (DyadicQft64.dyadicDiagUnitary kSys B e) * uApexShift45 kSys W hW δ =
      uApexShift45 kSys W hW δ * (QRegister.block 0 kSys (by
        omega : 0 + kSys ≤ kSys + 48)).embedUnitary
        (DyadicQft64.dyadicDiagUnitary kSys B e) := uApexShiftA_comm_coreDiag kSys 45 W hW B e δ
theorem uApexShift45_intertwinesLocal (kSys W : ℕ) (hW : W ≤ 45) (δ : BitAssignment kSys → ℤ)
    (U_cat_48 : Unitary (2 ^ 48)) (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48 (uApexShift45 kSys W hW δ)
      (DyadicQft64.dyadicDiagUnitary kSys 48 (fun γ ↦ (2 ^ (45 - W) : ℤ) * δ γ)) :=
  uApexShiftA_intertwinesLocal kSys 45 W hW δ U_cat_48 hcol0
theorem embed_uApexShift45_mulVec_basisKet {kSys W n : ℕ} (hW : W ≤ 45)
    (rSys : QRegister kSys n) (rCat : QRegister 48 n) (hdisj : rSys.DisjointWires rCat)
    (δ : BitAssignment kSys → ℤ) (ξ : BitAssignment n) :
    ((rSys.concat rCat hdisj).embedUnitary (uApexShift45 kSys W hW δ)).1.mulVec (basisKet ξ) =
      apexCarryPhase (rCat.slice (45 - W) W (by omega)) ξ (δ (fun i ↦ ξ (rSys i))) •
        basisKet (shiftRegInt (rCat.slice (45 - W) W (by omega)) ξ (δ (fun i ↦ ξ (rSys i)))) :=
  embed_uApexShiftA_mulVec_basisKet (A := 45) hW rSys rCat hdisj δ ξ
structure PreservesReg {W n : ℕ} (rT : QRegister W n) (c : Circuit n) (f : BitAssignment n →
    BitAssignment n) : Prop where
  evolve : ∀ ξ : BitAssignment n, c.eval.1.mulVec (basisKet ξ) = basisKet (f ξ)
  comm_shift : ∀ (ξ : BitAssignment n) (d : ℤ), f (shiftRegInt rT ξ d) = shiftRegInt rT (f ξ) d
  pres_reg : ∀ (ξ : BitAssignment n) (j : Fin W), f ξ (rT j) = ξ (rT j)
lemma PreservesReg.regVal_eq {W n : ℕ} {rT : QRegister W n} {c : Circuit n}
    {f : BitAssignment n → BitAssignment n} (hc : PreservesReg rT c f) (ξ : BitAssignment n) :
    regVal rT (f ξ) = regVal rT ξ :=
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rT (hc.pres_reg ξ)
lemma PreservesReg.of_update {W n : ℕ} {rT : QRegister W n} {c : Circuit n} (t : Wire n) (ht : t ∉
    rT.image) (g :
    BitAssignment n → ZMod 2) (hev : ∀ ξ, c.eval.1.mulVec (basisKet ξ) = basisKet (Function.update ξ
      t (g ξ)))
    (hg : ∀ ξ d, g (shiftRegInt rT ξ d) = g ξ) :
    PreservesReg rT c (fun ξ ↦ Function.update ξ t (g ξ)) :=
  ⟨hev, fun ξ d ↦ by
    have hval : regVal rT (Function.update ξ t (g ξ)) = regVal rT ξ := regVal_congr rT fun j ↦ by
      rw [Function.update_of_ne (by rintro rfl; exact ht ((QRegister.mem_image rT _).mpr ⟨j, rfl⟩))]
    funext w
    by_cases hw : w = t
    · subst hw
      rw [Function.update_self, shiftRegInt_outside rT _ d ht, Function.update_self, hg ξ d]
    · rw [Function.update_of_ne hw]
      by_cases hwT : w ∈ rT.image
      · rcases (QRegister.mem_image rT w).mp hwT with ⟨j, rfl⟩
        rw [shiftRegInt_apply_reg, shiftRegInt_apply_reg, hval]
      · rw [shiftRegInt_outside rT _ d hwT, shiftRegInt_outside rT _ d hwT, Function.update_of_ne
          hw],
   fun ξ j ↦ by
    rw [Function.update_of_ne (by rintro rfl; exact ht ((QRegister.mem_image rT _).mpr ⟨j, rfl⟩))]⟩
lemma PreservesReg.identity {W n : ℕ} (rT : QRegister W n) : PreservesReg rT (Circuit.identity :
    Circuit n) id :=
  ⟨fun ξ ↦ by simpa only [one_smul] using (PhasePerm.identity (∅ : Finset (Wire n))).evolve ξ,
   fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
lemma PreservesReg.seq {W n : ℕ} {rT : QRegister W n} {c₁ c₂ : Circuit n} {f₁ f₂ : BitAssignment n →
    BitAssignment n}
    (h₁ : PreservesReg rT c₁ f₁) (h₂ : PreservesReg rT c₂ f₂) :
    PreservesReg rT (c₁ ;;ᶜ c₂) (f₂ ∘ f₁) :=
  ⟨fun ξ ↦ by
     rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₁.evolve, h₂.evolve]
     rfl,
   fun ξ d ↦ by
     dsimp
     rw [h₁.comm_shift, h₂.comm_shift],
   fun ξ j ↦ by
     dsimp
     rw [h₂.pres_reg, h₁.pres_reg]⟩
lemma PreservesReg.X {W n : ℕ} {rT : QRegister W n} (a : Wire n) (ha : a ∉ rT.image) :
    PreservesReg rT (Circuit.X a) (fun ξ ↦ Function.update ξ a (ξ a + 1)) :=
  PreservesReg.of_update a ha _ (evolve_X_basisKet a) fun ξ d ↦
    by rw [shiftRegInt_outside rT ξ d ha]
lemma PreservesReg.CNOT {W n : ℕ} {rT : QRegister W n} (a b : Wire n) (hab : a ≠ b)
    (ha : a ∉ rT.image) (hb : b ∉ rT.image) :
    PreservesReg rT (Circuit.CNOT a b hab) (fun ξ ↦ Function.update ξ b (ξ b + ξ a)) :=
  PreservesReg.of_update b hb _ (evolve_CNOT_basisKet a b hab) fun ξ d ↦
    by rw [shiftRegInt_outside rT ξ d hb, shiftRegInt_outside rT ξ d ha]
lemma PreservesReg.TOFF {W n : ℕ} {rT : QRegister W n} (a b t : Wire n) (h₁ : a ≠ b) (h₂ : a ≠ t)
    (h₃ : b ≠ t) (ha : a ∉
    rT.image) (hb : b ∉ rT.image) (ht : t ∉ rT.image) : PreservesReg rT (Circuit.TOFF a b t h₁ h₂
      h₃)
      (fun ξ ↦ Function.update ξ t (ξ t + ξ a * ξ b)) :=
  PreservesReg.of_update t ht _ (evolve_TOFF_basisKet a b t h₁ h₂ h₃) fun ξ d ↦
    by
      rw [shiftRegInt_outside rT ξ d ht, shiftRegInt_outside rT ξ d ha, shiftRegInt_outside rT ξ d
        hb]
lemma rProjAxis_disjoint_of_ne {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    {w₁ w₂ : Fin 3} (hne
    : w₁ ≠ w₂) : (rProjAxis rCore w₁).DisjointWires (rProjAxis rCore w₂) := by
  refine QRegExt.disjointWires_of_finset (Finset.disjoint_left.mpr fun u hu1 hu2 ↦ ?_)
  rcases (QRegister.mem_image _ u).mp hu1 with ⟨i, rfl⟩
  rcases (QRegister.mem_image _ _).mp hu2 with ⟨j, hj⟩
  unfold rProjAxis at hj; rw [slice_apply_eq, slice_apply_eq] at hj
  have hv := congrArg Fin.val (rCore.wires.injective hj); dsimp at hv
  have := i.isLt; have := j.isLt; have := w₁.isLt; have := w₂.isLt
  exact hne (Fin.ext (by omega))
lemma disj_symm {k₁ k₂ n : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    (h : r₁.DisjointWires r₂) : r₂.DisjointWires r₁ := QRegister.disjoint_comm.mp h
lemma disj_tail {k n : ℕ} {r₁ r₂ : QRegister (k + 1) n} (h : r₁.DisjointWires r₂) :
    (r₁.slice 1 k (by omega)).DisjointWires (r₂.slice 1 k (by omega)) :=
  (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h)
    (QRegister.image_compose_subset r₁ _))) (QRegister.image_compose_subset r₂
    _)
lemma qreg_image_concat {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (h : r₁.DisjointWires r₂) : (r₁.concat r₂ h).image = r₁.image ∪ r₂.image := by
  ext w; simp only [QRegister.mem_image, Finset.mem_union]
  refine ⟨?_, fun h' ↦ h'.elim (fun ⟨i, hi⟩ ↦ ⟨Fin.castAdd k₂ i, hi ▸ QRegister.concat_apply_left r₁
    r₂ h i⟩)
    (fun ⟨j, hj⟩ ↦ ⟨Fin.natAdd k₁ j, hj ▸ QRegister.concat_apply_right r₁ r₂ h j⟩)⟩
  rintro ⟨idx, rfl⟩; by_cases hlt : idx.val < k₁
  · exact Or.inl ⟨⟨idx.val, hlt⟩, (QRegister.concat_apply_left r₁ r₂ h ⟨idx.val, hlt⟩).symm⟩
  · let j : Fin k₂ := ⟨idx.val - k₁, by have := idx.isLt; omega⟩
    have hidx : idx = Fin.natAdd k₁ j := Fin.ext (by dsimp [j]; omega)
    refine Or.inr ⟨j, ?_⟩
    rw [hidx]; exact (QRegister.concat_apply_right r₁ r₂ h j).symm
lemma evolve_identity_basisKet {n : ℕ} (ξ : BitAssignment n) :
    (Circuit.identity : Circuit n).eval.1.mulVec (basisKet ξ) = basisKet ξ := by
  simpa only [one_smul, id_eq] using (PhasePerm.identity (∅ : Finset (Wire n))).evolve ξ
lemma halfAdder_val_eq (a b : ZMod 2) : 2 * (a * b).val + (b + a).val = a.val + b.val := by
  revert a b; decide
lemma CleanUnitaryWp.circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {mW n : ℕ} (rW : QRegister mW n) (c : Circuit n) : CleanUnitaryWp (Var := Var) rW c.eval
      (.circuit c) := by
  have hw := CleanUnitaryWp.of_realizesClean
    (DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
    (Var := Var) (QRegExt.idReg n) rW c.eval c (embedUnitary_idReg_eq c.eval).symm)
  rwa [embedUnitary_idReg_eq] at hw
lemma PreservesReg.conj_shift {W n : ℕ} {rT : QRegister W n} {c : Circuit n} {f : BitAssignment n →
    BitAssignment n} (hc
    : PreservesReg rT c f) {U : Unitary (2 ^ n)} {ξ : BitAssignment n} {φ : ℂ} {d : ℤ} (hU :
      U.1.mulVec (basisKet (f ξ))
    = φ • basisKet (shiftRegInt rT (f ξ) d)) : (c.inverse.eval * U * c.eval).1.mulVec (basisKet ξ) =
      φ • basisKet
    (shiftRegInt rT ξ d) := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hc.evolve ξ, hU, Matrix.mulVec_smul,
    circuit_inverse_evolve_of_evolve (by rw [hc.evolve (shiftRegInt rT ξ d), hc.comm_shift ξ d])]
lemma shiftRegInt_congr_mod {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) {d₁ d₂ : ℤ} (hmod :
    d₁ % (2 ^ W : ℤ) =
    d₂ % (2 ^ W : ℤ)) : shiftRegInt rT ξ d₁ = shiftRegInt rT ξ d₂ := by
  funext w; by_cases hw : w ∈ rT.image
  · rcases (QRegister.mem_image rT w).mp hw with ⟨j, rfl⟩
    rw [shiftRegInt_apply_reg, shiftRegInt_apply_reg, show intModFinPow2 W ((regVal rT ξ : ℤ) +
      d₁) =
      intModFinPow2 W ((regVal rT ξ : ℤ) + d₂) from Fin.ext (by
        zify; rw [intModFinPow2_coe, intModFinPow2_coe, Int.add_emod, hmod, ← Int.add_emod])]
  · rw [shiftRegInt_outside _ _ _ hw, shiftRegInt_outside _ _ _ hw]
lemma diagOn_of_diag_ket {n : ℕ} (S : Finset (Wire n)) {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (φ : BitAssignment n →
    ℂ) (hKet : ∀ ξ : BitAssignment n, M.mulVec (basisKet ξ) = φ ξ • basisKet ξ) : DiagOn S M :=
  DiagOn.of_mulVec_basisKet fun ξ i hne _ _ ↦ by
    rw [hKet ξ] at hne
    rw [show i = (basisBitsEquiv n).symm ξ by
      by_contra hne_i; apply hne
      change φ ξ * Pi.single (M := fun _ ↦ ℂ) ((basisBitsEquiv n).symm ξ) (1 : ℂ) i = 0
      rw [Pi.single_eq_of_ne hne_i, mul_zero], basisBits_basisBitsEquiv_symm_eq]
lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide
lemma zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a := by revert a b; decide
lemma eval_inverse_of_invol {n : ℕ} (c : Circuit n) (f : BitAssignment n → BitAssignment n)
    (hevolve : ∀ ξ,
    c.eval.1.mulVec (basisKet ξ) = basisKet (f ξ)) (hinvol : ∀ ξ, f (f ξ) = ξ) : c.inverse.eval =
      c.eval := by
  rw [Circuit.eval_inverse]
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext; apply matrix_ext_basisKet; intro ξ
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hevolve, hevolve, hinvol, OneMemClass.coe_one,
    Matrix.one_mulVec]
@[scoped simp] lemma eval_X_inverse {n : ℕ} (a : Wire n) : (Circuit.X a).inverse.eval =
    (Circuit.X a).eval :=
  eval_inverse_of_invol _ _ (evolve_X_basisKet a) fun ξ ↦ by
    funext u; by_cases hu : u = a
    · subst hu; simp
    · simp [Function.update_of_ne hu]
@[scoped simp] lemma eval_CNOT_inverse {n : ℕ} (a b : Wire n) (hab : a ≠ b) :
    (Circuit.CNOT a b hab).inverse.eval = (Circuit.CNOT a b hab).eval :=
  eval_inverse_of_invol _ _ (evolve_CNOT_basisKet a b hab) fun ξ ↦ by
    funext u; by_cases hu : u = b
    · subst hu; simp [Function.update_of_ne hab]
    · simp [Function.update_of_ne hu]
@[scoped simp] lemma eval_TOFF_inverse {n : ℕ} (a b t : Wire n) (h₁ : a ≠ b) (h₂ : a ≠ t) (h₃ : b ≠
    t) : (Circuit.TOFF a
    b t h₁ h₂ h₃).inverse.eval = (Circuit.TOFF a b t h₁ h₂ h₃).eval :=
  eval_inverse_of_invol _ _ (evolve_TOFF_basisKet a b t h₁ h₂ h₃) fun ξ ↦ by
    funext u; by_cases hu : u = t
    · subst hu; simp [Function.update_of_ne h₂, Function.update_of_ne h₃]
    · simp [Function.update_of_ne hu]
lemma support_X_sub {n : ℕ} {S : Finset (Wire n)} (a : Wire n) (ha : a ∈ S) :
    (Circuit.X a).support ⊆ S := fun u hu ↦ by
  suffices u = a from this ▸ ha
  simpa [Circuit.support] using hu
lemma support_seq_sub {n : ℕ} {S : Finset (Wire n)} {c₁ c₂ : Circuit n}
    (h₁ : c₁.support ⊆ S) (h₂ : c₂.support ⊆ S) : (c₁ ;;ᶜ c₂).support ⊆ S := by
  rw [Circuit.support_seq]; exact Finset.union_subset h₁ h₂
lemma disj_support_X {n : ℕ} {S : Finset (Wire n)} (a : Wire n) (ha : a ∉ S) : Disjoint (Circuit.X
    a).support S :=
  Finset.disjoint_left.mpr fun _ hu hS ↦ ha ((Finset.mem_singleton.mp (support_X_sub a
    (Finset.mem_singleton_self a) hu)) ▸ hS)
lemma disj_support_CNOT {n : ℕ} {S : Finset (Wire n)} (a b : Wire n) (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) : Disjoint (Circuit.CNOT a b hab).support S :=
  Finset.disjoint_left.mpr fun u hu hS ↦ by
    suffices u = a ∨ u = b by
      rcases this with rfl | rfl
      · exact ha hS
      · exact hb hS
    simpa [Circuit.support] using hu
lemma disj_support_seq {n : ℕ} {S : Finset (Wire n)} {c₁ c₂ : Circuit n}
    (h₁ : Disjoint c₁.support S) (h₂ : Disjoint c₂.support S) : Disjoint (c₁ ;;ᶜ c₂).support S := by
  rw [Circuit.support_seq]; exact Finset.disjoint_union_left.mpr ⟨h₁, h₂⟩
lemma diagOn_CNOT_of_not_mem {n : ℕ} {S : Finset (Wire n)} (a b : Wire n) (hab : a ≠ b)
    (hb : b ∉ S) : DiagOn S (Circuit.CNOT a b hab).eval.1 :=
  DiagOn.of_mulVec_basisKet fun ξ i hne u huS ↦ by
    rw [evolve_CNOT_basisKet] at hne
    rw [show i = (basisBitsEquiv n).symm (Function.update ξ b (ξ b + ξ a)) by
      by_contra hne_i; apply hne; rw [basisKet_eq_single, Pi.single_eq_of_ne hne_i],
      basisBits_basisBitsEquiv_symm_eq, Function.update_of_ne (fun hEq ↦ hb (by rwa [← hEq]))]
def optX {n : ℕ} (b : Bool) (w : Wire n) : Circuit n := if b then Circuit.X w else .identity
@[simp] lemma count_optX_toff {n : ℕ} (b : Bool) (w : Wire n) : (optX b w).count .TOFF = 0 := by
  cases b <;> rfl
@[simp] lemma count_optX_t {n : ℕ} (b : Bool) (w : Wire n) : (optX b w).count .T = 0 := by
  cases b <;> rfl
@[simp] lemma eval_optX_inverse {n : ℕ} (b : Bool) (w : Wire n) :
    (optX b w).inverse.eval = (optX b w).eval := by
  cases b
  · exact rfl
  · exact eval_X_inverse w
lemma disj_support_optX {n : ℕ} {S : Finset (Wire n)} (b : Bool) (w : Wire n) (hw : w ∉ S) :
    Disjoint (optX b w).support S := by
  cases b
  · simp [optX]
  · exact disj_support_X w hw
lemma evolve_optX_basisKet {n : ℕ} (b : Bool) (w : Wire n) (ξ : BitAssignment n) :
    (optX b w).eval.1.mulVec (basisKet ξ) = basisKet (Function.update ξ w (ξ w + if b then 1 else
      0)) := by
  cases b
  · simp [optX]
  · simp only [optX, ↓reduceIte, evolve_X_basisKet]
lemma DiagOn.conj_optX {n : ℕ} {S : Finset (Wire n)} (b : Bool) (w : Wire n) {M : Matrix (Fin (2 ^
    n)) (Fin (2 ^ n)) ℂ}
    (hM : DiagOn S M) : DiagOn S ((optX b w).eval.1 * M * (optX b w).eval.1) := by
  cases b
  · simpa [optX] using hM
  · exact DiagOn.conj_X w hM
def genBoolBit (b₁ b₂ bOut : Bool) (x₁ x₂ : ZMod 2) : ZMod 2 :=
  (if bOut then 1 else 0) + (x₁ + if b₁ then 1 else 0) * (x₂ + if b₂ then 1 else 0)
def dGenBoolWrap {Var : Type} {n : ℕ} (b₁ b₂ bOut : Bool) (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠
    c₂) (h₁a : c₁ ≠
    anc) (h₂a : c₂ ≠ anc) (dInner : DynamicCircuit Var n) : DynamicCircuit Var n :=
  dPureConj (optX b₁ c₁ ;;ᶜ optX b₂ c₂) (dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a
    (dPureConj (optX b₁ c₁ ;;ᶜ optX b₂ c₂ ;;ᶜ optX bOut anc) dInner))
@[simp] lemma count_dGenBoolWrap_toff {Var : Type} {n : ℕ} (b₁ b₂ bOut : Bool) (v : Var) (c₁ c₂
    anc : Wire n) (h₁₂ : c₁
    ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dInner : DynamicCircuit Var n) : (dGenBoolWrap b₁ b₂
      bOut v c₁ c₂ anc h₁₂
    h₁a h₂a dInner).count .TOFF = dInner.count .TOFF := by
  unfold dGenBoolWrap
  rw [count_dPureConj_toff _ (by simp [Circuit.count_seq]), count_dAndSandwich_toff,
    count_dPureConj_toff _ (by simp [Circuit.count_seq])]
@[simp] lemma count_dGenBoolWrap_t {Var : Type} {n : ℕ} (b₁ b₂ bOut : Bool) (v : Var) (c₁ c₂ anc :
    Wire n) (h₁₂ : c₁ ≠
    c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dInner : DynamicCircuit Var n) : (dGenBoolWrap b₁ b₂ bOut
      v c₁ c₂ anc h₁₂ h₁a
    h₂a dInner).count .T = 4 + dInner.count .T := by
  unfold dGenBoolWrap
  rw [count_dPureConj_t _ (by simp [Circuit.count_seq]), count_dAndSandwich_t,
    count_dPureConj_t _ (by simp [Circuit.count_seq])]
def cGenBoolStep {n : ℕ} (b₁ b₂ bOut : Bool) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : Circuit n :=
  (optX b₁ c₁ ;;ᶜ optX b₂ c₂) ;;ᶜ (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ (optX b₁ c₁ ;;ᶜ
    optX b₂ c₂ ;;ᶜ optX bOut anc))
lemma cGenBoolStep_evolve {n : ℕ} (b₁ b₂ bOut : Bool) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁
    ≠ anc) (h₂a : c₂ ≠
    anc) (ξ : BitAssignment n) : (cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a).eval.1.mulVec
      (basisKet ξ) = basisKet
    (Function.update ξ anc (ξ anc + genBoolBit b₁ b₂ bOut (ξ c₁) (ξ c₂))) := by
  unfold cGenBoolStep
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_optX_basisKet,
    evolve_TOFF_basisKet]
  congr 1; funext u; by_cases hua : u = anc
  · subst hua
    simp only [Function.update_self, Function.update_of_ne h₁a.symm, Function.update_of_ne h₂a.symm,
      Function.update_of_ne h₁₂, Function.update_of_ne h₁₂.symm, genBoolBit]; ring
  · by_cases hu1 : u = c₁
    · subst hu1
      simp [Function.update_of_ne hua, Function.update_of_ne h₁₂, Function.update_of_ne h₁₂.symm]
    · by_cases hu2 : u = c₂
      · subst hu2
        simp [Function.update_of_ne hua, Function.update_of_ne hu1, Function.update_of_ne h₁₂]
      · simp [Function.update_of_ne hua, Function.update_of_ne hu1, Function.update_of_ne hu2]
@[simp] lemma eval_cGenBoolStep_inverse {n : ℕ} (b₁ b₂ bOut : Bool) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠
    c₂) (h₁a : c₁ ≠
    anc) (h₂a : c₂ ≠ anc) : (cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a).inverse.eval =
      (cGenBoolStep b₁ b₂ bOut c₁
    c₂ anc h₁₂ h₁a h₂a).eval :=
  eval_inverse_of_invol _ _ (cGenBoolStep_evolve b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a) fun ξ ↦ by
    funext u; by_cases hu : u = anc
    · subst hu; simp [Function.update_of_ne h₁a, Function.update_of_ne h₂a]
    · simp [Function.update_of_ne hu]
theorem CleanUnitaryWp.dGenBoolWrap {Var : Type} [Fintype Var] [DecidableEq Var] {mSub mTot n : ℕ}
    (b₁ b₂ bOut : Bool)
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (rSub :
      QRegister mSub n) (rTot :
    QRegister mTot n) (hSubTot : rSub.image ⊆ rTot.image) (hAncTot : anc ∈ rTot.image) (hc1Tot : c₁
      ∉ rTot.image)
    (hc2Tot : c₂ ∉ rTot.image) (hancSub : anc ∉ rSub.image) {uInner : Unitary (2 ^ n)} {dInner :
      DynamicCircuit Var n}
    (hDiag : DiagOn ({c₁, c₂, anc} : Finset (Wire n)) uInner.1) (hwInner : CleanUnitaryWp rSub
      uInner dInner) :
    CleanUnitaryWp rTot ((cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a).inverse.eval * uInner *
      (cGenBoolStep b₁ b₂
    bOut c₁ c₂ anc h₁₂ h₁a h₂a).eval) (JunctionApexCSA288.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ anc h₁₂
      h₁a
      h₂a dInner) := by
  have hc1Sub : c₁ ∉ rSub.image := fun h ↦ hc1Tot (hSubTot h)
  have hc2Sub : c₂ ∉ rSub.image := fun h ↦ hc2Tot (hSubTot h)
  let cIn := optX b₁ c₁ ;;ᶜ optX b₂ c₂ ;;ᶜ optX bOut anc
  let cOut := optX b₁ c₁ ;;ᶜ optX b₂ c₂
  have hDiag1 : DiagOn ({c₁, c₂, anc} : Finset (Wire n)) (cIn.inverse.eval * uInner * cIn.eval).1 :=
    by
    simp only [cIn, Circuit.inverse_seq, Circuit.eval_seq, eval_optX_inverse, Submonoid.coe_mul,
      Matrix.mul_assoc]
    simpa only [Matrix.mul_assoc] using DiagOn.conj_optX b₁ c₁ (DiagOn.conj_optX b₂ c₂
      (DiagOn.conj_optX bOut anc hDiag))
  refine (CleanUnitaryWp.dPureConj cOut rTot (disj_support_seq (disj_support_optX b₁ c₁ hc1Tot)
    (disj_support_optX b₂ c₂
      hc2Tot)) (CleanUnitaryWp.dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a rSub rTot hSubTot hAncTot hc1Sub
        hc2Sub hancSub
      hDiag1 (CleanUnitaryWp.dPureConj cIn rSub (disj_support_seq (disj_support_optX b₁ c₁ hc1Sub)
        (disj_support_seq
      (disj_support_optX b₂ c₂ hc2Sub) (disj_support_optX bOut anc hancSub)))
        hwInner))).congr_unitary ?_
  simp only [cGenBoolStep, cIn, cOut, Circuit.inverse_seq, Circuit.eval_seq, eval_TOFF_inverse,
    mul_assoc]
lemma DiagOn.conj_cGenBoolStep {n : ℕ} {S : Finset (Wire n)} (b₁ b₂ bOut : Bool) (c₁ c₂ anc : Wire
    n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hc1 : c₁ ∈ S) (hc2 : c₂ ∈ S) {M : Matrix (Fin (2 ^ n)) (Fin
      (2 ^ n)) ℂ} (hM :
    DiagOn S M) : DiagOn S ((cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a).inverse.eval.1 * M *
      (cGenBoolStep b₁ b₂
    bOut c₁ c₂ anc h₁₂ h₁a h₂a).eval.1) := by
  simp only [cGenBoolStep, Circuit.inverse_seq, Circuit.eval_seq, eval_optX_inverse,
    eval_TOFF_inverse, Submonoid.coe_mul, Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc] using DiagOn.conj_optX b₁ c₁ (DiagOn.conj_optX b₂ c₂
    (DiagOn.conj_TOFF c₁ c₂ anc h₁₂ h₁a h₂a hc1 hc2
      (DiagOn.conj_optX b₁ c₁ (DiagOn.conj_optX b₂ c₂ (DiagOn.conj_optX bOut anc hM)))))
lemma PreservesReg.cGenBoolStep {W n : ℕ} {rT : QRegister W n} (b₁ b₂ bOut : Bool) (c₁ c₂ anc : Wire
    n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hc1 : c₁ ∉ rT.image) (hc2 : c₂ ∉ rT.image) (hanc : anc ∉
      rT.image) : PreservesReg
    rT (JunctionApexCSA288.cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a)
      (fun ξ ↦ Function.update ξ anc (ξ anc + genBoolBit b₁ b₂ bOut (ξ c₁) (ξ c₂))) :=
  PreservesReg.of_update anc hanc _ (cGenBoolStep_evolve b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a) fun ξ d ↦
    by
      rw [shiftRegInt_outside rT ξ d hanc, shiftRegInt_outside rT ξ d hc1, shiftRegInt_outside rT ξ
        d hc2]
lemma qreg_slice_zero_eq {k n : ℕ} (r : QRegister (k + 1) n) (j : Fin k) : (r.slice 1 k (by omega))
    j = r j.succ := by
  rw [slice_apply_eq]
  exact congrArg r (Fin.ext (Nat.one_add j.val))
lemma qreg_slice_init_eq {k n : ℕ} (r : QRegister (k + 1) n) (j : Fin k) :
    (r.slice 0 k (by omega)) j = r j.castSucc := by
  rw [slice_apply_eq]
  exact congrArg r (Fin.ext (Nat.zero_add j.val))
lemma qreg_zero_not_mem_tail {k n : ℕ} (r : QRegister (k + 1) n) :
    r 0 ∉ (r.slice 1 k (by omega)).image := fun hm ↦ by
  rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
  rw [qreg_slice_zero_eq] at hj
  exact Fin.succ_ne_zero j (r.wires.injective hj)
lemma regVal_zero {n : ℕ} (r : QRegister 0 n) (ξ : BitAssignment n) : regVal r ξ = 0 := rfl
lemma regVal_succ {k n : ℕ} (r : QRegister (k + 1) n) (ξ : BitAssignment n) :
    regVal r ξ = (ξ (r 0)).val + 2 * regVal (r.slice 1 k (by omega)) ξ :=
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_head_tail r
      ξ
lemma regVal_split_last {k n : ℕ} (r : QRegister (k + 1) n) (ξ : BitAssignment n) :
    regVal r ξ = regVal (r.slice 0 k (by omega)) ξ + 2 ^ k * (ξ (r ⟨k, by omega⟩)).val := by
  unfold regVal bitsVal
  rw [Fin.sum_univ_castSucc, show (Fin.last k : Fin (k + 1)) = ⟨k, by omega⟩ from rfl]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    change (ξ (r j.castSucc)).val * 2 ^ j.castSucc.val = (ξ ((r.slice 0 k (by omega)) j)).val *
      2 ^ j.val
    rw [qreg_slice_init_eq r j]; rfl
  · dsimp; ring
lemma zero_on_sub {k m n : ℕ} {rSub : QRegister k n} {rSup : QRegister m n} (hsub : rSub.image ⊆
    rSup.image) {ξ :
    BitAssignment n} (hz : ∀ i : Fin m, ξ (rSup i) = 0) (j : Fin k) : ξ (rSub j) = 0 := by
  rcases (QRegister.mem_image rSup _).mp (hsub ((QRegister.mem_image rSub _).mpr ⟨j, rfl⟩)) with ⟨i,
    hi⟩
  exact hi ▸ hz i
lemma eq_shiftRegInt_succ_step {k n : ℕ} (rT : QRegister (k + 1) n) (α ξ : BitAssignment n) (d' d :
    ℤ) (hne : ∀ w, w ≠
    rT 0 → α w = shiftRegInt (rT.slice 1 k (by omega)) ξ d' w) (hstep : ((α (rT 0)).val : ℤ) + 2 *
      d' = ((ξ (rT 0)).val
    : ℤ) + d) : α = shiftRegInt rT ξ d := by
  let rT' := rT.slice 1 k (by omega)
  apply eq_shiftRegInt_of_outside_and_regVal rT α ξ d
  · intro w hwNotT
    rw [hne w (fun h ↦ hwNotT (h ▸ (QRegister.mem_image rT _).mpr ⟨0, rfl⟩))]
    exact shiftRegInt_outside rT' ξ d' (fun hm ↦ hwNotT (QRegister.image_compose_subset rT _ hm))
  · rw [regVal_succ rT α]
    have hα_T' : regVal rT' α = regVal rT' (shiftRegInt rT' ξ d') :=
      regVal_congr rT' fun j ↦ hne (rT' j)
        (fun h ↦ qreg_zero_not_mem_tail rT ((QRegister.mem_image rT' _).mpr ⟨j, h⟩))
    change (α (rT 0)).val + 2 * regVal rT' α = _
    rw [hα_T', regVal_shiftRegInt rT' ξ d']
    zify; rw [intModFinPow2_coe, intModFinPow2_coe]
    have hbit_lt : (α (rT 0)).val < 2 := ZMod.val_lt _
    have hrem_nn : (0 : ℤ) ≤ ((regVal rT' ξ : ℤ) + d') % (2 ^ k : ℤ) := Int.emod_nonneg _ (by
      positivity)
    have hrem_lt : ((regVal rT' ξ : ℤ) + d') % (2 ^ k : ℤ) < (2 ^ k : ℤ) := Int.emod_lt_of_pos _ (by
      positivity)
    have hlt_tot : ((α (rT 0)).val : ℤ) + 2 * (((regVal rT' ξ : ℤ) + d') % (2 ^ k : ℤ)) < (2 ^ (k +
      1) : ℤ) := by
      rw [pow_succ']; linarith
    have hnn_tot : (0 : ℤ) ≤ ((α (rT 0)).val : ℤ) + 2 * (((regVal rT' ξ : ℤ) + d') % (2 ^ k : ℤ)) :=
      by positivity
    rw [← Int.emod_eq_of_lt hnn_tot hlt_tot]
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    obtain ⟨q, hq⟩ : (2 ^ k : ℤ) ∣ ((((regVal rT' ξ : ℤ) + d') % (2 ^ k : ℤ)) - ((regVal rT' ξ : ℤ)
      + d')) :=
      Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod])
    refine Int.emod_eq_zero_of_dvd ⟨q, ?_⟩
    have hT_z : (regVal rT ξ : ℤ) = ((ξ (rT 0)).val : ℤ) + 2 * (regVal rT' ξ : ℤ) := by
      exact_mod_cast regVal_succ rT ξ
    rw [pow_succ', mul_assoc]; linarith
def xAllCircuit {n : ℕ} : {W : ℕ} → (r : QRegister W n) → Circuit n
  | 0, _ => .identity
  | k + 1, r => Circuit.X (r 0) ;;ᶜ xAllCircuit (r.slice 1 k (by omega))
@[simp] lemma count_xAllCircuit_toff {W n : ℕ} (r : QRegister W n) : (xAllCircuit r).count .TOFF =
    0 := by
  induction W with
  | zero => rfl
  | succ k ih => simp [xAllCircuit, Circuit.count_seq, ih (r.slice 1 k (by omega))]
@[simp] lemma count_xAllCircuit_t {W n : ℕ} (r : QRegister W n) : (xAllCircuit r).count .T = 0 := by
  induction W with
  | zero => rfl
  | succ k ih => simp [xAllCircuit, Circuit.count_seq, ih (r.slice 1 k (by omega))]
lemma support_xAllCircuit_sub {W n : ℕ} (r : QRegister W n) : (xAllCircuit r).support ⊆ r.image :=
  by
  induction W with
  | zero => simp [xAllCircuit]
  | succ k ih =>
      exact support_seq_sub (support_X_sub (r 0) ((QRegister.mem_image r _).mpr ⟨0, rfl⟩))
        ((ih (r.slice 1 k (by omega))).trans (QRegister.image_compose_subset r _))
lemma xAllCircuit_evolve {W n : ℕ} (r : QRegister W n) (ξ : BitAssignment n) :
    (xAllCircuit r).eval.1.mulVec (basisKet ξ) = basisKet (flipRegBits r ξ) := by
  induction W generalizing ξ with
  | zero =>
      rw [show flipRegBits r ξ = ξ from funext fun w ↦ flipRegBits_outside r ξ fun hm ↦ by
        rcases (QRegister.mem_image r w).mp hm with ⟨i, _⟩
        exact Fin.elim0 i]
      exact evolve_identity_basisKet ξ
  | succ k ih =>
      let r' := r.slice 1 k (by omega)
      unfold xAllCircuit
      rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_X_basisKet, ih r']
      congr 1
      funext w
      by_cases hw0 : w = r 0
      · subst hw0
        rw [flipRegBits_outside r' _ (qreg_zero_not_mem_tail r), Function.update_self]
        simp [flipRegBits, (QRegister.mem_image r _).mpr ⟨0, rfl⟩]
      · by_cases hw' : w ∈ r'.image
        · simp [flipRegBits, hw', QRegister.image_compose_subset r _ hw', Function.update_of_ne hw0]
        · have hnot : w ∉ r.image := fun hm ↦ by
            rcases (QRegister.mem_image r w).mp hm with ⟨i, rfl⟩
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
            · exact hw0 rfl
            · exact hw' ((QRegister.mem_image r' _).mpr ⟨j, qreg_slice_zero_eq r j⟩)
          simp [flipRegBits, hw', hnot, Function.update_of_ne hw0]
@[simp] lemma eval_xAllCircuit_inverse {W n : ℕ} (r : QRegister W n) :
    (xAllCircuit r).inverse.eval = (xAllCircuit r).eval := by
  rw [Circuit.eval_inverse]
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro ξ
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, xAllCircuit_evolve, xAllCircuit_evolve,
    flipRegBits_self_inv, OneMemClass.coe_one, Matrix.one_mulVec]
lemma DiagOn.conj_xAllCircuit {W n : ℕ} {S : Finset (Wire n)} (r : QRegister W n) {M : Matrix (Fin
    (2 ^ n)) (Fin (2 ^
    n)) ℂ} (hM : DiagOn S M) : DiagOn S ((xAllCircuit r).eval.1 * M * (xAllCircuit r).eval.1) := by
  induction W with
  | zero => simpa [xAllCircuit] using hM
  | succ k ih =>
      nth_rw 1 [congrArg Subtype.val (eval_xAllCircuit_inverse r).symm]
      simp only [xAllCircuit, Circuit.inverse_seq, Circuit.eval_seq, eval_X_inverse,
        eval_xAllCircuit_inverse, Submonoid.coe_mul, Matrix.mul_assoc]
      simpa only [Matrix.mul_assoc] using DiagOn.conj_X (r 0) (ih (r.slice 1 k (by omega)))
def carryBitZMod2 (c u t : ZMod 2) : ZMod 2 := c + (u + c) * (t + c)
lemma carryBitZMod2_val_eq (c u t : ZMod 2) :
    2 * (carryBitZMod2 c u t).val + (t + c + u).val = c.val + u.val + t.val := by
  rcases zmod2_eq_zero_or_one c with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one t with rfl | rfl <;> decide
lemma zmod2_ofNat_val (b : ZMod 2) : ((b.val : ℕ) : ZMod 2) = b := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide
noncomputable def dApexTail {Var : Type} {n : ℕ} :
    (m : ℕ) → (v : Var) → (cApex : Wire n → Circuit n) → (cin : Wire n) →
    (rU rT rC : QRegister m n) →
    (hcinU : cin ∉ rU.image) → (hcinT : cin ∉ rT.image) → (hcinC : cin ∉ rC.image) →
    (hUT : rU.DisjointWires rT) → (hUC : rU.DisjointWires rC) → (hTC : rT.DisjointWires rC) →
    DynamicCircuit Var n
  | 0, _, cApex, cin, _, _, _, _, _, _, _, _, _ => .circuit (cApex cin)
  | k + 1, v, cApex, cin, rU, rT, rC, hcinU, hcinT, hcinC, hUT, hUC, hTC =>
      let h_cin_u0 : cin ≠ rU 0 := fun h ↦ hcinU (h ▸ (QRegister.mem_image rU _).mpr ⟨0, rfl⟩)
      let h_cin_t0 : cin ≠ rT 0 := fun h ↦ hcinT (h ▸ (QRegister.mem_image rT _).mpr ⟨0, rfl⟩)
      let h_cin_c0 : cin ≠ rC 0 := fun h ↦ hcinC (h ▸ (QRegister.mem_image rC _).mpr ⟨0, rfl⟩)
      let h_u0_t0 : rU 0 ≠ rT 0 := disj_wire_ne hUT 0 0
      .seq
        (dPureConj (Circuit.CNOT cin (rU 0) h_cin_u0 ;;ᶜ Circuit.CNOT cin (rT 0) h_cin_t0)
          (dAndSandwich v (rU 0) (rT 0) (rC 0) h_u0_t0 (disj_wire_ne hUC 0 0) (disj_wire_ne hTC 0 0)
            (dPureConj (Circuit.CNOT cin (rC 0) h_cin_c0)
              (dApexTail k v cApex (rC 0) (rU.slice 1 k (by omega)) (rT.slice 1 k (by omega))
                (rC.slice 1 k (by omega))
                (fun hm ↦ (disj_symm hUC).apply_not_mem_right 0 (QRegister.image_compose_subset rU _
                  hm))
                (fun hm ↦ (disj_symm hTC).apply_not_mem_right 0 (QRegister.image_compose_subset rT _
                  hm))
                (qreg_zero_not_mem_tail rC) (disj_tail hUT) (disj_tail hUC) (disj_tail hTC)))))
        (.circuit (Circuit.CNOT cin (rT 0) h_cin_t0 ;;ᶜ Circuit.CNOT (rU 0) (rT 0) h_u0_t0))
lemma count_dApexTail_toff {Var : Type} {n : ℕ} (m : ℕ) (v : Var) (cApex : Wire n →
    Circuit n) (hcToff : ∀ w, (cApex
    w).count .TOFF = 0) (cin : Wire n) (rU rT rC : QRegister m n) (hcinU : cin ∉ rU.image) (hcinT :
      cin ∉ rT.image)
    (hcinC : cin ∉ rC.image) (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC) (hTC :
      rT.DisjointWires rC) :
    (dApexTail m v cApex cin rU rT rC hcinU hcinT hcinC hUT hUC hTC).count .TOFF = 0 := by
  induction m generalizing cin with
  | zero => exact hcToff cin
  | succ k ih =>
      unfold dApexTail; dsimp only
      rw [count_dyn_seq, count_dPureConj_toff _ (by simp [Circuit.CNOT, Circuit.count_seq]),
        count_dAndSandwich_toff, count_dPureConj_toff _ (by simp [Circuit.CNOT]), ih]
      simp [DynamicCircuit.count, Circuit.CNOT, Circuit.count_seq]
lemma count_dApexTail_t_mem {Var : Type} {n : ℕ} (m : ℕ) (v : Var) (cApex : Wire n →
    Circuit n) (tApex : ℕ) (cin : Wire
    n) (rU rT rC : QRegister m n) (hcT : ∀ w ∈ insert cin rC.image, (cApex w).count .T =
      tApex) (hcinU : cin ∉ rU.image)
    (hcinT : cin ∉ rT.image) (hcinC : cin ∉ rC.image) (hUT : rU.DisjointWires rT) (hUC :
      rU.DisjointWires rC) (hTC :
    rT.DisjointWires rC) : (dApexTail m v cApex cin rU rT rC hcinU hcinT hcinC hUT hUC hTC).count
      .T = 4 * m + tApex :=
    by
  induction m generalizing cin with
  | zero =>
      unfold dApexTail; simpa [DynamicCircuit.count] using hcT cin (Finset.mem_insert_self _ _)
  | succ k ih =>
      unfold dApexTail; dsimp only
      rw [count_dyn_seq, count_dPureConj_t _ (by simp [Circuit.CNOT, Circuit.count_seq]),
        count_dAndSandwich_t, count_dPureConj_t _ (by simp [Circuit.CNOT]),
        ih (rC 0) _ _ _ (fun w hw ↦ hcT w (Finset.mem_insert_of_mem (by
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · exact (QRegister.mem_image rC _).mpr ⟨0, rfl⟩
          · exact QRegister.image_compose_subset rC _ hw')))]
      have h0 : (DynamicCircuit.circuit
          (Circuit.CNOT cin (rT 0) (fun h ↦ hcinT (h ▸ (QRegister.mem_image rT _).mpr ⟨0, rfl⟩)) ;;ᶜ
            Circuit.CNOT (rU 0) (rT 0) (disj_wire_ne hUT 0 0)) : DynamicCircuit Var n).count .T =
              0 := by
        simp [DynamicCircuit.count, Circuit.CNOT, Circuit.count_seq]
      rw [h0]; omega
lemma count_dApexTail_t {Var : Type} {n : ℕ} (m : ℕ) (v : Var) (cApex : Wire n → Circuit n) (tApex :
    ℕ) (hcT : ∀ w,
    (cApex w).count .T = tApex) (cin : Wire n) (rU rT rC : QRegister m n) (hcinU : cin ∉ rU.image)
      (hcinT : cin ∉
    rT.image) (hcinC : cin ∉ rC.image) (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC)
      (hTC : rT.DisjointWires
    rC) : (dApexTail m v cApex cin rU rT rC hcinU hcinT hcinC hUT hUC hTC).count .T = 4 * m +
      tApex :=
  count_dApexTail_t_mem m v cApex tApex cin rU rT rC (fun w _ ↦ hcT w) hcinU hcinT hcinC hUT hUC hTC
theorem dApexTail_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (m : ℕ) (v : Var)
    (cApex : Wire n → Circuit
    n) (S_ctrl : Finset (Wire n)) (φ : BitAssignment n → ZMod 2 → ℂ) (hφ_congr : ∀ ξ₁ ξ₂ b,
      (∀ u ∈ S_ctrl, ξ₁ u = ξ₂ u)
    → φ ξ₁ b = φ ξ₂ b) (hApexKet : ∀ (c : Wire n) (ξ : BitAssignment n), (cApex c).eval.1.mulVec
      (basisKet ξ) = φ ξ (ξ
    c) • basisKet ξ) (cin : Wire n) (rU rT rC : QRegister m n) (hcinU : cin ∉ rU.image) (hcinT : cin
      ∉ rT.image) (hcinC
    : cin ∉ rC.image) (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC) (hTC :
      rT.DisjointWires rC) (hcinS : cin ∉
    S_ctrl) (hUS : Disjoint rU.image S_ctrl) (hTS : Disjoint rT.image S_ctrl) (hCS : Disjoint
      rC.image S_ctrl) : ∃ u :
    Unitary (2 ^ n), CleanUnitaryWp rC u (dApexTail m v cApex cin rU rT rC hcinU hcinT hcinC hUT hUC
      hTC) ∧ DiagOn
    (Finset.univ \ rT.image) u.1 ∧ ∀ ξ : BitAssignment n, (∀ i : Fin m, ξ (rC i) = 0) →
      u.1.mulVec (basisKet ξ) = φ ξ
    ((((ξ cin).val + regVal rU ξ + regVal rT ξ) / 2 ^ m : ℕ) : ZMod 2) • basisKet (shiftRegInt rT ξ
      (((ξ cin).val +
    regVal rU ξ : ℕ) : ℤ)) := by
  induction m generalizing cin with
  | zero =>
      refine ⟨(cApex cin).eval, CleanUnitaryWp.circuit rC (cApex cin),
        diagOn_of_diag_ket _ (fun ξ ↦ φ ξ (ξ cin)) (hApexKet cin), fun ξ _ ↦ ?_⟩
      have hU0 : regVal rU ξ = 0 := rfl
      have hT0 : regVal rT ξ = 0 := rfl
      rw [hApexKet cin ξ, show shiftRegInt rT ξ (((ξ cin).val + regVal rU ξ : ℕ) : ℤ) = ξ from
        funext fun w ↦ shiftRegInt_outside rT ξ _ fun hm ↦ by
          rcases (QRegister.mem_image rT w).mp hm with ⟨i, _⟩; exact Fin.elim0 i, hU0, hT0]
      simp only [add_zero, _root_.pow_zero, Nat.div_one, zmod2_ofNat_val]
  | succ k ih =>
      let u₀ := rU 0; let t₀ := rT 0; let c₀ := rC 0
      let rU' := rU.slice 1 k (by omega);
        let rT' := rT.slice 1 k (by omega); let rC' := rC.slice 1 k (by omega)
      have hU'_sub : rU'.image ⊆ rU.image := QRegister.image_compose_subset rU _
      have hT'_sub : rT'.image ⊆ rT.image := QRegister.image_compose_subset rT _
      have hC'_sub : rC'.image ⊆ rC.image := QRegister.image_compose_subset rC _
      have h_cin_u0 : cin ≠ u₀ := fun h ↦ hcinU (h ▸ (QRegister.mem_image rU _).mpr ⟨0, rfl⟩)
      have h_cin_t0 : cin ≠ t₀ := fun h ↦ hcinT (h ▸ (QRegister.mem_image rT _).mpr ⟨0, rfl⟩)
      have h_cin_c0 : cin ≠ c₀ := fun h ↦ hcinC (h ▸ (QRegister.mem_image rC _).mpr ⟨0, rfl⟩)
      have h_u0_t0 : u₀ ≠ t₀ := disj_wire_ne hUT 0 0
      have h_u0_c0 : u₀ ≠ c₀ := disj_wire_ne hUC 0 0
      have h_t0_c0 : t₀ ≠ c₀ := disj_wire_ne hTC 0 0
      have hc0U' : c₀ ∉ rU'.image := fun hm ↦ (disj_symm hUC).apply_not_mem_right 0 (hU'_sub hm)
      have hc0T' : c₀ ∉ rT'.image := fun hm ↦ (disj_symm hTC).apply_not_mem_right 0 (hT'_sub hm)
      have hc0C' : c₀ ∉ rC'.image := qreg_zero_not_mem_tail rC
      have hu0T' : u₀ ∉ rT'.image := fun hm ↦ hUT.apply_not_mem_right 0 (hT'_sub hm)
      have ht0T' : t₀ ∉ rT'.image := qreg_zero_not_mem_tail rT
      have hcinT' : cin ∉ rT'.image := fun hm ↦ hcinT (hT'_sub hm)
      have hcinC' : cin ∉ rC'.image := fun hm ↦ hcinC (hC'_sub hm)
      have hu0C : u₀ ∉ rC.image := hUC.apply_not_mem_right 0
      have ht0C : t₀ ∉ rC.image := hTC.apply_not_mem_right 0
      have hc0S : c₀ ∉ S_ctrl := Finset.disjoint_left.mp hCS ((QRegister.mem_image rC _).mpr ⟨0,
        rfl⟩)
      have hu0S : u₀ ∉ S_ctrl := Finset.disjoint_left.mp hUS ((QRegister.mem_image rU _).mpr ⟨0,
        rfl⟩)
      have ht0S : t₀ ∉ S_ctrl := Finset.disjoint_left.mp hTS ((QRegister.mem_image rT _).mpr ⟨0,
        rfl⟩)
      obtain ⟨uTail, hwTail, hDiagTail, hKetTail⟩ := ih c₀ rU' rT' rC' hc0U' hc0T' hc0C'
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hUT) hU'_sub)) hT'_sub)
          ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hUC) hU'_sub))
          hC'_sub)
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hTC) hT'_sub)) hC'_sub)
          hc0S (Finset.disjoint_of_subset_left hU'_sub
          hUS)
        (Finset.disjoint_of_subset_left hT'_sub hTS) (Finset.disjoint_of_subset_left hC'_sub hCS)
      let cIn := Circuit.CNOT cin c₀ h_cin_c0
      let cOut := Circuit.CNOT cin u₀ h_cin_u0 ;;ᶜ Circuit.CNOT cin t₀ h_cin_t0
      let cPost := Circuit.CNOT cin t₀ h_cin_t0 ;;ᶜ Circuit.CNOT u₀ t₀ h_u0_t0
      have hw1 := CleanUnitaryWp.dPureConj cIn rC' (disj_support_CNOT cin c₀ h_cin_c0 hcinC' hc0C')
        hwTail
      have hDiag1 : DiagOn (Finset.univ \ rT'.image) (cIn.inverse.eval * uTail * cIn.eval).1 := by
        simp only [cIn, eval_CNOT_inverse, Submonoid.coe_mul]
        exact DiagOn.conj_CNOT cin c₀ h_cin_c0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          hcinT'⟩) hDiagTail
      have hDiag1_3 : DiagOn ({u₀, t₀, c₀} : Finset (Wire n)) (cIn.inverse.eval * uTail *
        cIn.eval).1 :=
        DiagOn.anti (fun w hw ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> assumption⟩) hDiag1
      have hw2 := CleanUnitaryWp.dAndSandwich v u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0 rC' rC hC'_sub
        ((QRegister.mem_image rC _).mpr ⟨0, rfl⟩) (fun hm ↦ hu0C (hC'_sub hm)) (fun hm ↦
          ht0C (hC'_sub hm)) hc0C' hDiag1_3 hw1
      have hDiag2 : DiagOn (Finset.univ \ rT'.image) ((Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0
        h_t0_c0).eval *
          (cIn.inverse.eval * uTail * cIn.eval) * (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0
            h_t0_c0).eval).1 := by
        simp only [Submonoid.coe_mul]
        exact DiagOn.conj_TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu0T'⟩) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ
            _, ht0T'⟩) hDiag1
      have hw3 := CleanUnitaryWp.dPureConj cOut rC
        (disj_support_seq (disj_support_CNOT cin u₀ h_cin_u0 hcinC hu0C) (disj_support_CNOT cin t₀
          h_cin_t0 hcinC ht0C)) hw2
      let u3 := cOut.inverse.eval * ((Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0).eval *
        (cIn.inverse.eval * uTail * cIn.eval) * (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0
          h_t0_c0).eval) * cOut.eval
      have hDiag3 : DiagOn (Finset.univ \ rT'.image) u3.1 := by
        have hEq : u3.1 = (Circuit.CNOT cin u₀ h_cin_u0).eval.1 * ((Circuit.CNOT cin t₀
          h_cin_t0).eval.1 *
            ((Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0).eval * (cIn.inverse.eval * uTail *
              cIn.eval) *
              (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0).eval).1 *
            (Circuit.CNOT cin t₀ h_cin_t0).eval.1) * (Circuit.CNOT cin u₀ h_cin_u0).eval.1 := by
          simp only [u3, cOut, Circuit.inverse_seq, Circuit.eval_seq, eval_CNOT_inverse,
            Submonoid.coe_mul, Matrix.mul_assoc]
        rw [hEq]
        exact DiagOn.conj_CNOT cin u₀ h_cin_u0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcinT'⟩)
          (DiagOn.conj_CNOT cin t₀ h_cin_t0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
            hcinT'⟩) hDiag2)
      have hwFull := CleanUnitaryWp.seq_of_diag hw3 (CleanUnitaryWp.circuit rC cPost)
        (DiagOn.anti (fun w hw ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hwT' ↦
          Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTC) (hT'_sub hwT') hw⟩) hDiag3)
      have ht0Not : t₀ ∉ Finset.univ \ rT.image := fun hm ↦
        (Finset.mem_sdiff.mp hm).2 ((QRegister.mem_image rT _).mpr ⟨0, rfl⟩)
      have hDiagFull : DiagOn (Finset.univ \ rT.image) (cPost.eval * u3).1 := by
        simp only [cPost, Circuit.eval_seq, Submonoid.coe_mul]
        exact DiagOn.mul (DiagOn.mul (diagOn_CNOT_of_not_mem u₀ t₀ h_u0_t0 ht0Not)
          (diagOn_CNOT_of_not_mem cin t₀ h_cin_t0 ht0Not))
          (DiagOn.anti (fun w hw ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm ↦
            (Finset.mem_sdiff.mp hw).2 (hT'_sub hm)⟩) hDiag3)
      refine ⟨cPost.eval * u3, by unfold dApexTail; exact hwFull, hDiagFull, fun ξ hzC ↦ ?_⟩
      let cPreAll := cOut ;;ᶜ (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0 ;;ᶜ cIn)
      have hpAll := ((PreservesReg.CNOT cin u₀ h_cin_u0 hcinT' hu0T').seq
        (PreservesReg.CNOT cin t₀ h_cin_t0 hcinT' ht0T')).seq
        ((PreservesReg.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0 hu0T' ht0T' hc0T').seq
          (PreservesReg.CNOT cin c₀ h_cin_c0 hcinT' hc0T'))
      let η := (((fun γ ↦ Function.update γ c₀ (γ c₀ + γ cin)) ∘
        fun γ ↦ Function.update γ c₀ (γ c₀ + γ u₀ * γ t₀)) ∘
        (fun γ ↦ Function.update γ t₀ (γ t₀ + γ cin)) ∘
        fun γ ↦ Function.update γ u₀ (γ u₀ + γ cin)) ξ
      have hη_c0 : η c₀ = carryBitZMod2 (ξ cin) (ξ u₀) (ξ t₀) := by
        have hz0 : ξ c₀ = 0 := hzC 0
        dsimp only [η, carryBitZMod2, Function.comp_apply]
        simp only [Function.update_self, Function.update_of_ne h_cin_u0, Function.update_of_ne
          h_cin_t0,
          Function.update_of_ne h_u0_t0, Function.update_of_ne h_u0_t0.symm, Function.update_of_ne
            h_u0_c0.symm,
          Function.update_of_ne h_t0_c0.symm, Function.update_of_ne h_cin_c0, hz0]
        ring
      have hη_out : ∀ w, w ≠ u₀ → w ≠ t₀ → w ≠ c₀ → η w = ξ w := fun w h1 h2 h3 ↦ by
        dsimp only [η, Function.comp_apply]
        simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
      have hzC' : ∀ j : Fin k, η (rC' j) = 0 := fun j ↦ by
        rw [hη_out _ (fun h ↦ hu0C (hC'_sub ((QRegister.mem_image rC' _).mpr ⟨j, h⟩)))
          (fun h ↦ ht0C (hC'_sub ((QRegister.mem_image rC' _).mpr ⟨j, h⟩)))
          (fun h ↦ hc0C' ((QRegister.mem_image rC' _).mpr ⟨j, h⟩)), qreg_slice_zero_eq]
        exact hzC j.succ
      have hU'_eq : regVal rU' η = regVal rU' ξ := regVal_congr rU' fun j ↦ hη_out _
        (by rw [qreg_slice_zero_eq]; exact fun h ↦ Fin.succ_ne_zero j (rU.wires.injective h))
        (fun h ↦ (disj_wire_ne hUT j.succ 0) ((qreg_slice_zero_eq rU j).symm.trans h))
        (fun h ↦ hc0U' ((QRegister.mem_image rU' _).mpr ⟨j, h⟩))
      have hφ_eq : ∀ b, φ η b = φ ξ b := fun b ↦ hφ_congr η ξ b fun w hwS ↦ hη_out w
        (fun h ↦ hu0S (h ▸ hwS)) (fun h ↦ ht0S (h ▸ hwS)) (fun h ↦ hc0S (h ▸ hwS))
      have hTailAt := hKetTail η hzC'
      rw [hφ_eq, hη_c0, hU'_eq, hpAll.regVal_eq ξ] at hTailAt
      have hu3At : u3.1.mulVec (basisKet ξ) =
          φ ξ ((((carryBitZMod2 (ξ cin) (ξ u₀) (ξ t₀)).val + regVal rU' ξ + regVal rT' ξ) / 2 ^ k :
            ℕ) : ZMod 2) •
            basisKet (shiftRegInt rT' ξ (((carryBitZMod2 (ξ cin) (ξ u₀) (ξ t₀)).val + regVal rU' ξ :
              ℕ) : ℤ)) := by
        rw [show u3 = cPreAll.inverse.eval * uTail * cPreAll.eval by
          simp only [u3, cPreAll, Circuit.inverse_seq, Circuit.eval_seq, eval_TOFF_inverse,
            mul_assoc]]
        exact hpAll.conj_shift hTailAt
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hu3At, Matrix.mulVec_smul]
      let car0 := (carryBitZMod2 (ξ cin) (ξ u₀) (ξ t₀)).val
      have hsum_bit := carryBitZMod2_val_eq (ξ cin) (ξ u₀) (ξ t₀)
      have hU_sp : regVal rU ξ = (ξ u₀).val + 2 * regVal rU' ξ := regVal_succ rU ξ
      have hT_sp : regVal rT ξ = (ξ t₀).val + 2 * regVal rT' ξ := regVal_succ rT ξ
      have hdiv : (car0 + regVal rU' ξ + regVal rT' ξ) / 2 ^ k = ((ξ cin).val + regVal rU ξ +
        regVal rT ξ) / 2 ^ (k + 1) := by
        have hbit_lt : (ξ t₀ + ξ cin + ξ u₀).val < 2 := ZMod.val_lt _
        rw [pow_succ', ← Nat.div_div_eq_div_mul, show ((ξ cin).val + regVal rU ξ + regVal rT ξ) /
          2 =
          car0 + regVal rU' ξ + regVal rT' ξ by
            rw [hU_sp, hT_sp]; dsimp [car0] at hsum_bit ⊢; omega]
      rw [hdiv]; congr 1
      let ξ' := shiftRegInt rT' ξ ((car0 + regVal rU' ξ : ℕ) : ℤ)
      simp only [cPost, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        evolve_CNOT_basisKet]
      congr 1
      let α := Function.update (Function.update ξ' t₀ (ξ' t₀ + ξ' cin)) t₀
        (Function.update ξ' t₀ (ξ' t₀ + ξ' cin) t₀ + Function.update ξ' t₀ (ξ' t₀ + ξ' cin) u₀)
      have hα_t0 : α t₀ = ξ t₀ + ξ cin + ξ u₀ := by
        have h1 : ξ' cin = ξ cin := shiftRegInt_outside rT' ξ _ hcinT'
        have h2 : ξ' u₀ = ξ u₀ := shiftRegInt_outside rT' ξ _ hu0T'
        have h3 : ξ' t₀ = ξ t₀ := shiftRegInt_outside rT' ξ _ ht0T'
        dsimp only [α]
        simp [Function.update_of_ne h_u0_t0, h1, h2, h3]
      refine eq_shiftRegInt_succ_step rT α ξ ((car0 + regVal rU' ξ : ℕ) : ℤ)
        (((ξ cin).val + regVal rU ξ : ℕ) : ℤ)
        (fun w hw ↦ by dsimp only [α, t₀]; rw [Function.update_of_ne hw, Function.update_of_ne hw])
          ?_
      change ((α t₀).val : ℤ) + _ = ((ξ t₀).val : ℤ) + _
      rw [hα_t0]; exact_mod_cast (by rw [hU_sp]; dsimp [car0] at hsum_bit ⊢; omega :
        (ξ t₀ + ξ cin + ξ u₀).val + 2 * (car0 + regVal rU' ξ) = (ξ t₀).val + ((ξ cin).val +
          regVal rU ξ))
noncomputable def dApexCarryChain {Var : Type} {n : ℕ} (m : ℕ) (v : Var)
    (cApex : Wire n → Circuit n) (rU rT rC : QRegister (m + 1) n) (hUT : rU.DisjointWires rT)
    (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) : DynamicCircuit Var n :=
  .seq
    (dAndSandwich v (rU 0) (rT 0) (rC 0) (disj_wire_ne hUT 0 0) (disj_wire_ne hUC 0 0) (disj_wire_ne
      hTC 0 0)
      (dApexTail m v cApex (rC 0) (rU.slice 1 m (by omega)) (rT.slice 1 m (by omega)) (rC.slice 1 m
        (by omega))
        (fun hm ↦ (disj_symm hUC).apply_not_mem_right 0 (QRegister.image_compose_subset rU _ hm))
        (fun hm ↦ (disj_symm hTC).apply_not_mem_right 0 (QRegister.image_compose_subset rT _ hm))
        (qreg_zero_not_mem_tail rC)
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hUT)
          (QRegister.image_compose_subset rU _)))
          (QRegister.image_compose_subset rT _))
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hUC)
          (QRegister.image_compose_subset rU _)))
          (QRegister.image_compose_subset rC _))
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hTC)
          (QRegister.image_compose_subset rT _)))
          (QRegister.image_compose_subset rC _))))
    (.circuit (Circuit.CNOT (rU 0) (rT 0) (disj_wire_ne hUT 0 0)))
lemma count_dApexCarryChain_toff {Var : Type} {n : ℕ} (m : ℕ) (v : Var) (cApex : Wire n →
    Circuit n) (hcToff : ∀ w,
    (cApex w).count .TOFF = 0) (rU rT rC : QRegister (m + 1) n) (hUT : rU.DisjointWires rT) (hUC :
      rU.DisjointWires rC)
    (hTC : rT.DisjointWires rC) : (dApexCarryChain m v cApex rU rT rC hUT hUC hTC).count .TOFF =
      0 := by
  unfold dApexCarryChain
  rw [count_dyn_seq, count_dAndSandwich_toff, count_dApexTail_toff m v cApex hcToff]
  simp [DynamicCircuit.count, Circuit.CNOT]
lemma count_dApexCarryChain_t_mem {Var : Type} {n : ℕ} (m : ℕ) (v : Var) (cApex : Wire n →
    Circuit n) (tApex : ℕ) (rU rT
    rC : QRegister (m + 1) n) (hcT : ∀ w ∈ rC.image, (cApex w).count .T = tApex) (hUT :
      rU.DisjointWires rT) (hUC :
    rU.DisjointWires rC) (hTC : rT.DisjointWires rC) : (dApexCarryChain m v cApex rU rT rC hUT hUC
      hTC).count .T = 4 *
    (m + 1) + tApex := by
  unfold dApexCarryChain
  rw [count_dyn_seq, count_dAndSandwich_t, count_dApexTail_t_mem m v cApex tApex (rC 0) _ _ _
    (fun w hw ↦ hcT w (by
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact (QRegister.mem_image rC _).mpr ⟨0, rfl⟩
      · exact QRegister.image_compose_subset rC _ hw'))]
  have h0 : (DynamicCircuit.circuit (Circuit.CNOT (rU 0) (rT 0) (disj_wire_ne hUT 0 0)) :
      DynamicCircuit Var n).count .T = 0 := by simp [DynamicCircuit.count, Circuit.CNOT]
  rw [h0]; omega
lemma count_dApexCarryChain_t {Var : Type} {n : ℕ} (m : ℕ) (v : Var) (cApex : Wire n →
    Circuit n) (tApex : ℕ) (hcT : ∀
    w, (cApex w).count .T = tApex) (rU rT rC : QRegister (m + 1) n) (hUT : rU.DisjointWires rT)
      (hUC : rU.DisjointWires
    rC) (hTC : rT.DisjointWires rC) : (dApexCarryChain m v cApex rU rT rC hUT hUC hTC).count .T =
      4 * (m + 1) + tApex :=
  count_dApexCarryChain_t_mem m v cApex tApex rU rT rC (fun w _ ↦ hcT w) hUT hUC hTC
theorem dApexCarryChain_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (m : ℕ) (v : Var)
    (cApex : Wire n →
    Circuit n) (S_ctrl : Finset (Wire n)) (φ : BitAssignment n → ZMod 2 → ℂ) (hφ_congr : ∀ ξ₁ ξ₂ b,
      (∀ u ∈ S_ctrl, ξ₁ u
    = ξ₂ u) → φ ξ₁ b = φ ξ₂ b) (hApexKet : ∀ (c : Wire n) (ξ : BitAssignment n),
      (cApex c).eval.1.mulVec (basisKet ξ) =
    φ ξ (ξ c) • basisKet ξ) (rU rT rC : QRegister (m + 1) n) (hUT : rU.DisjointWires rT) (hUC :
      rU.DisjointWires rC)
    (hTC : rT.DisjointWires rC) (hUS : Disjoint rU.image S_ctrl) (hTS : Disjoint rT.image S_ctrl)
      (hCS : Disjoint
    rC.image S_ctrl) : ∃ u : Unitary (2 ^ n), CleanUnitaryWp rC u (dApexCarryChain m v cApex rU rT
      rC hUT hUC hTC) ∧
    DiagOn (Finset.univ \ rT.image) u.1 ∧ ∀ ξ : BitAssignment n, (∀ i : Fin (m + 1), ξ (rC i) = 0) →
      u.1.mulVec
    (basisKet ξ) = φ ξ (((regVal rU ξ + regVal rT ξ) / 2 ^ (m + 1) : ℕ) : ZMod 2) • basisKet
      (shiftRegInt rT ξ (regVal
    rU ξ : ℤ)) := by
  let u₀ := rU 0; let t₀ := rT 0; let c₀ := rC 0
  let rU' := rU.slice 1 m (by omega);
    let rT' := rT.slice 1 m (by omega); let rC' := rC.slice 1 m (by omega)
  have hU'_sub : rU'.image ⊆ rU.image := QRegister.image_compose_subset rU _
  have hT'_sub : rT'.image ⊆ rT.image := QRegister.image_compose_subset rT _
  have hC'_sub : rC'.image ⊆ rC.image := QRegister.image_compose_subset rC _
  have h_u0_t0 : u₀ ≠ t₀ := disj_wire_ne hUT 0 0
  have h_u0_c0 : u₀ ≠ c₀ := disj_wire_ne hUC 0 0
  have h_t0_c0 : t₀ ≠ c₀ := disj_wire_ne hTC 0 0
  have hc0U' : c₀ ∉ rU'.image := fun hm ↦ (disj_symm hUC).apply_not_mem_right 0 (hU'_sub hm)
  have hc0T' : c₀ ∉ rT'.image := fun hm ↦ (disj_symm hTC).apply_not_mem_right 0 (hT'_sub hm)
  have hc0C' : c₀ ∉ rC'.image := qreg_zero_not_mem_tail rC
  have hu0T' : u₀ ∉ rT'.image := fun hm ↦ hUT.apply_not_mem_right 0 (hT'_sub hm)
  have ht0T' : t₀ ∉ rT'.image := qreg_zero_not_mem_tail rT
  have hc0S : c₀ ∉ S_ctrl := Finset.disjoint_left.mp hCS ((QRegister.mem_image rC _).mpr ⟨0, rfl⟩)
  obtain ⟨uTail, hwTail, hDiagTail, hKetTail⟩ := dApexTail_spec m v cApex S_ctrl φ hφ_congr hApexKet
    c₀ rU' rT' rC'
      hc0U' hc0T' hc0C' ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hUT)
        hU'_sub)) hT'_sub) ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hUC)
        hU'_sub)) hC'_sub)
      ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hTC) hT'_sub)) hC'_sub)
        hc0S (Finset.disjoint_of_subset_left hU'_sub hUS)
      (Finset.disjoint_of_subset_left hT'_sub hTS) (Finset.disjoint_of_subset_left hC'_sub hCS)
  have hDiag3 : DiagOn ({u₀, t₀, c₀} : Finset (Wire n)) uTail.1 :=
    DiagOn.anti (fun w hw ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption⟩) hDiagTail
  have hwSand := CleanUnitaryWp.dAndSandwich v u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0 rC' rC hC'_sub
    ((QRegister.mem_image rC _).mpr ⟨0, rfl⟩) (fun hm ↦ hUC.apply_not_mem_right 0 (hC'_sub hm))
    (fun hm ↦ hTC.apply_not_mem_right 0 (hC'_sub hm)) hc0C' hDiag3 hwTail
  let uSand := (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0).eval * uTail *
    (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0).eval
  have hDiagSand : DiagOn (Finset.univ \ rT'.image) uSand.1 := by
    simp only [uSand, Submonoid.coe_mul]
    exact DiagOn.conj_TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu0T'⟩) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        ht0T'⟩) hDiagTail
  have hwFull := CleanUnitaryWp.seq_of_diag hwSand (CleanUnitaryWp.circuit rC (Circuit.CNOT u₀ t₀
    h_u0_t0))
    (DiagOn.anti (fun w hw ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hwT' ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTC) (hT'_sub hwT') hw⟩) hDiagSand)
  have hDiagFull : DiagOn (Finset.univ \ rT.image) ((Circuit.CNOT u₀ t₀ h_u0_t0).eval * uSand).1 :=
    by
    simp only [Submonoid.coe_mul]
    exact DiagOn.mul (diagOn_CNOT_of_not_mem u₀ t₀ h_u0_t0 fun hm ↦
      (Finset.mem_sdiff.mp hm).2 ((QRegister.mem_image rT _).mpr ⟨0, rfl⟩))
      (DiagOn.anti (fun w hw ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm ↦
        (Finset.mem_sdiff.mp hw).2 (hT'_sub hm)⟩) hDiagSand)
  refine ⟨(Circuit.CNOT u₀ t₀ h_u0_t0).eval * uSand, by unfold dApexCarryChain; exact hwFull,
    hDiagFull, fun ξ hzC ↦ ?_⟩
  have hpToff := PreservesReg.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0 hu0T' ht0T' hc0T'
  let η := Function.update ξ c₀ (ξ c₀ + ξ u₀ * ξ t₀)
  have hTailAt := hKetTail η fun j ↦ by
    dsimp only [η]
    rw [Function.update_of_ne (fun h ↦ hc0C' ((QRegister.mem_image rC' _).mpr ⟨j, h⟩))]
    exact zero_on_sub hC'_sub hzC j
  rw [show ∀ b, φ η b = φ ξ b from fun b ↦ hφ_congr η ξ b fun w hwS ↦ by
      dsimp only [η]; rw [Function.update_of_ne (by rintro rfl; exact hc0S hwS)],
    show η c₀ = ξ u₀ * ξ t₀ by simp [η, c₀, hzC 0],
    show regVal rU' η = regVal rU' ξ from regVal_congr rU' (fun j ↦ by
      dsimp only [η]
      rw [Function.update_of_ne (fun h ↦ hc0U' ((QRegister.mem_image rU' _).mpr ⟨j, h⟩))]),
    hpToff.regVal_eq ξ] at hTailAt
  have hSandAt : uSand.1.mulVec (basisKet ξ) =
      φ ξ ((((ξ u₀ * ξ t₀).val + regVal rU' ξ + regVal rT' ξ) / 2 ^ m : ℕ) : ZMod 2) •
        basisKet (shiftRegInt rT' ξ (((ξ u₀ * ξ t₀).val + regVal rU' ξ : ℕ) : ℤ)) := by
    rw [show uSand = (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0).inverse.eval * uTail *
      (Circuit.TOFF u₀ t₀ c₀ h_u0_t0 h_u0_c0 h_t0_c0).eval by simp only [uSand, eval_TOFF_inverse]]
    exact hpToff.conj_shift hTailAt
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hSandAt, Matrix.mulVec_smul, evolve_CNOT_basisKet]
  have hbit0 := halfAdder_val_eq (ξ u₀) (ξ t₀)
  have hU_sp : regVal rU ξ = (ξ u₀).val + 2 * regVal rU' ξ := regVal_succ rU ξ
  have hT_sp : regVal rT ξ = (ξ t₀).val + 2 * regVal rT' ξ := regVal_succ rT ξ
  have hdiv : ((ξ u₀ * ξ t₀).val + regVal rU' ξ + regVal rT' ξ) / 2 ^ m = (regVal rU ξ +
    regVal rT ξ) / 2 ^ (m + 1) := by
    have hlt2 : (ξ t₀ + ξ u₀).val < 2 := ZMod.val_lt _
    rw [pow_succ', ← Nat.div_div_eq_div_mul, show (regVal rU ξ + regVal rT ξ) / 2 =
      (ξ u₀ * ξ t₀).val + regVal rU' ξ + regVal rT' ξ by rw [hU_sp, hT_sp]; omega]
  rw [hdiv]; congr 1; congr 1
  let ξ' := shiftRegInt rT' ξ (((ξ u₀ * ξ t₀).val + regVal rU' ξ : ℕ) : ℤ)
  refine eq_shiftRegInt_succ_step rT (Function.update ξ' t₀ (ξ' t₀ + ξ' u₀)) ξ
    (((ξ u₀ * ξ t₀).val + regVal rU' ξ : ℕ) : ℤ) (regVal rU ξ : ℤ)
    (fun w hw ↦ by rw [Function.update_of_ne hw]) ?_
  change ((Function.update ξ' t₀ (ξ' t₀ + ξ' u₀) t₀).val : ℤ) + _ = ((ξ t₀).val : ℤ) + _
  rw [Function.update_self]
  dsimp only [ξ']
  rw [shiftRegInt_outside rT' ξ _ ht0T', shiftRegInt_outside rT' ξ _ hu0T']
  exact_mod_cast (by rw [hU_sp]; omega :
    (ξ t₀ + ξ u₀).val + 2 * ((ξ u₀ * ξ t₀).val + regVal rU' ξ) = (ξ t₀).val + regVal rU ξ)
lemma dyadicTurn7_16_eq_3 (k : ℤ) : DyadicQft64.dyadicTurn 7 (16 * k) = DyadicQft64.dyadicTurn 3
    k := by
  have h := turnPow2_scale_pow 4 3 k
  change turnPow2 7 (16 * k) = turnPow2 3 k
  simpa using h
lemma ones_comp_carry_eq {W K U : ℕ} (hK : K < 2 ^ W) (hU : U < 2 ^ W) :
    -(((U + (2 ^ W - 1 - K)) / 2 ^ W : ℕ) : ℤ) = ((K : ℤ) - (U : ℤ)) / (2 ^ W : ℤ) := by
  set P := 2 ^ W
  have hPpos : 0 < P := Nat.two_pow_pos W
  have hKP : K < P := hK
  have hUP : U < P := hU
  by_cases hKU : U ≤ K
  · rw [Nat.div_eq_of_lt (by omega : U + (P - 1 - K) < P)]
    change -((0 : ℕ) : ℤ) = ((K : ℤ) - (U : ℤ)) / (P : ℤ)
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    rfl
  · rw [show (U + (P - 1 - K)) / P = 1 from Nat.le_antisymm
        (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hPpos).mpr (by omega)))
        ((Nat.le_div_iff_mul_le hPpos).mpr (by omega))]
    change (-1 : ℤ) = ((K : ℤ) - (U : ℤ)) / (P : ℤ)
    have hEq : (K : ℤ) - (U : ℤ) = ((P + K - U : ℕ) : ℤ) + (-1 : ℤ) * (P : ℤ) := by omega
    have hrem_lt : (P + K - U : ℕ) < P := by omega
    rw [hEq, Int.add_mul_ediv_right _ _ (by positivity : (P : ℤ) ≠ 0),
      Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hrem_lt), zero_add]
lemma flipRegBits_shiftRegInt_ones_comp {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) {U : ℕ}
    (hU : U < 2 ^ W) :
    flipRegBits rT (shiftRegInt rT (flipRegBits rT ξ) (U : ℤ)) = shiftRegInt rT ξ (-(U : ℤ)) := by
  let ξ₁ := flipRegBits rT ξ
  let α := flipRegBits rT (shiftRegInt rT ξ₁ (U : ℤ))
  have hK : regVal rT ξ < 2 ^ W := regVal_lt_two_pow rT ξ
  have hK₁ : regVal rT ξ₁ = 2 ^ W - 1 - regVal rT ξ := by
    have h : regVal rT ξ₁ + regVal rT ξ = 2 ^ W - 1 := regVal_flipRegBits_add rT ξ
    omega
  apply eq_shiftRegInt_of_outside_and_regVal rT α ξ (-(U : ℤ))
  · intro w hwNot
    dsimp [α, ξ₁]
    rw [flipRegBits_outside rT _ hwNot, shiftRegInt_outside rT _ _ hwNot, flipRegBits_outside rT _
      hwNot]
  · have hα : regVal rT α + regVal rT (shiftRegInt rT ξ₁ (U : ℤ)) = 2 ^ W - 1 :=
      regVal_flipRegBits_add rT (shiftRegInt rT ξ₁ (U : ℤ))
    have hK₁_sum : regVal rT ξ₁ + regVal rT ξ = 2 ^ W - 1 := regVal_flipRegBits_add rT ξ
    rw [regVal_shiftRegInt rT ξ₁ (U : ℤ)] at hα
    have hpow : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    zify [hpow] at hK₁_sum hα ⊢
    rw [intModFinPow2_coe] at hα ⊢
    have h1 := ones_comp_carry_eq (regVal_lt_two_pow rT ξ) hU
    have hE1 := Int.mul_ediv_add_emod ((regVal rT ξ₁ : ℤ) + (U : ℤ)) (2 ^ W : ℤ)
    have hE2 := Int.mul_ediv_add_emod ((regVal rT ξ : ℤ) + -(U : ℤ)) (2 ^ W : ℤ)
    rw [show ((regVal rT ξ₁ : ℤ) + (U : ℤ)) / (2 ^ W : ℤ) =
        (((U + (2 ^ W - 1 - regVal rT ξ)) / 2 ^ W : ℕ) : ℤ) by
          rw [hK₁, add_comm]
          exact (Int.natCast_ediv _ _).symm] at hE1
    have hE2' : (2 ^ W : ℤ) * (((regVal rT ξ : ℤ) - (U : ℤ)) / (2 ^ W : ℤ)) +
        (((regVal rT ξ : ℤ) - (U : ℤ)) % (2 ^ W : ℤ)) = (regVal rT ξ : ℤ) - (U : ℤ) := by
      simpa [sub_eq_add_neg] using hE2
    rw [← h1] at hE2'
    change (regVal rT α : ℤ) = ((regVal rT ξ : ℤ) - (U : ℤ)) % (2 ^ W : ℤ)
    linarith
def cApexSign {n : ℕ} (isInv : Bool) (c : Wire n) : Circuit n :=
  if isInv then (Circuit.T c).inverse else Circuit.T c
@[simp] lemma count_cApexSign_toff {n : ℕ} (isInv : Bool) (c : Wire n) :
    (cApexSign isInv c).count .TOFF = 0 := by cases isInv <;> rfl
@[simp] lemma count_cApexSign_t {n : ℕ} (isInv : Bool) (c : Wire n) :
    (cApexSign isInv c).count .T = 1 := by cases isInv <;> rfl
lemma cApexSign_evolve {n : ℕ} (isInv : Bool) (c : Wire n) (ξ : BitAssignment n) :
    (cApexSign isInv c).eval.1.mulVec (basisKet ξ) =
      DyadicQft64.dyadicTurn 3 ((if isInv then (-1 : ℤ) else 1) * ((ξ c).val : ℤ)) • basisKet ξ :=
        by
  cases isInv
  · simp only [cApexSign, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [(PhasePerm.gateT c).evolve ξ, dyadicTurn7_16_eq_3]; rfl
  · simp only [cApexSign, ↓reduceIte, neg_one_mul]
    rw [(PhasePerm.gateTDag c).evolve ξ, show (-16 * ((ξ c).val : ℤ)) = 16 * -((ξ c).val : ℤ)
      by ring, dyadicTurn7_16_eq_3]; rfl
noncomputable def dApexTAdder {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ) (v : Var) (rU rT rC :
    QRegister (m + 1) n)
    (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) :
      DynamicCircuit Var n :=
  if isInv then dPureConj (xAllCircuit rT) (dApexCarryChain m v (cApexSign true) rU rT rC hUT hUC
    hTC)
  else dApexCarryChain m v (cApexSign false) rU rT rC hUT hUC hTC
@[simp] lemma count_dApexTAdder_toff {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ) (v : Var)
    (rU rT rC : QRegister (m + 1) n) (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC)
    (hTC : rT.DisjointWires rC) : (dApexTAdder isInv m v rU rT rC hUT hUC hTC).count .TOFF = 0 := by
  cases isInv
  · exact count_dApexCarryChain_toff m v _ (count_cApexSign_toff false) rU rT rC hUT hUC hTC
  · simp only [dApexTAdder, ↓reduceIte]; rw [count_dPureConj_toff _ (count_xAllCircuit_toff rT)]
    exact count_dApexCarryChain_toff m v _ (count_cApexSign_toff true) rU rT rC hUT hUC hTC
@[simp] lemma count_dApexTAdder_t {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ) (v : Var)
    (rU rT rC : QRegister (m + 1) n) (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC)
    (hTC : rT.DisjointWires rC) : (dApexTAdder isInv m v rU rT rC hUT hUC hTC).count .T = 4 * (m +
      1) + 1 := by
  cases isInv
  · exact count_dApexCarryChain_t m v _ 1 (count_cApexSign_t false) rU rT rC hUT hUC hTC
  · simp only [dApexTAdder, ↓reduceIte]; rw [count_dPureConj_t _ (count_xAllCircuit_t rT)]
    exact count_dApexCarryChain_t m v _ 1 (count_cApexSign_t true) rU rT rC hUT hUC hTC
lemma div_two_pow_zmod2_val {W U T : ℕ} (hU : U < 2 ^ W) (hT : T < 2 ^ W) :
    ((((U + T) / 2 ^ W : ℕ) : ZMod 2).val : ℤ) = ((T : ℤ) + (U : ℤ)) / (2 ^ W : ℤ) := by
  rw [ZMod.val_natCast_of_lt ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos W)).mpr (by omega)),
    add_comm U T]
  exact (Int.natCast_ediv (T + U) (2 ^ W)).symm
theorem dApexTAdder_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (isInv : Bool)
    (m : ℕ) (v : Var) (rU rT rC : QRegister (m + 1) n) (hUT : rU.DisjointWires rT)
    (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) : ∃ u : Unitary (2 ^ n),
    CleanUnitaryWp rC u (dApexTAdder isInv m v rU rT rC hUT hUC hTC) ∧ DiagOn
    (Finset.univ \ rT.image) u.1 ∧ ∀ ξ : BitAssignment n, (∀ i : Fin (m + 1), ξ (rC i) = 0) →
    u.1.mulVec (basisKet ξ) = apexCarryPhase rT ξ
    ((if isInv then (-1 : ℤ) else 1) * (regVal rU ξ : ℤ)) • basisKet (shiftRegInt rT ξ ((if
    isInv then (-1 : ℤ) else 1) * (regVal rU ξ : ℤ))) := by
  cases isInv
  · obtain ⟨u, hw, hDiag, hKet⟩ := dApexCarryChain_spec m v (cApexSign false) ∅
      (fun _ b ↦ DyadicQft64.dyadicTurn 3 (b.val : ℤ)) (fun _ _ _ _ ↦ rfl)
      (fun c ξ ↦ by simpa using cApexSign_evolve false c ξ) rU rT rC hUT hUC hTC
      (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right
        _)
    refine ⟨u, hw, hDiag, fun ξ hzC ↦ ?_⟩
    rw [hKet ξ hzC]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact congrArg (· • _) (congrArg (DyadicQft64.dyadicTurn 3)
      (div_two_pow_zmod2_val (regVal_lt_two_pow rU ξ) (regVal_lt_two_pow rT ξ)))
  · obtain ⟨u₀, hw₀, hDiag₀, hKet₀⟩ := dApexCarryChain_spec m v (cApexSign true) ∅
      (fun _ b ↦ DyadicQft64.dyadicTurn 3 (-(b.val : ℤ))) (fun _ _ _ _ ↦ rfl)
      (fun c ξ ↦ by simpa using cApexSign_evolve true c ξ) rU rT rC hUT hUC hTC
      (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right
        _)
    let u := (xAllCircuit rT).inverse.eval * u₀ * (xAllCircuit rT).eval
    refine ⟨u, by
        unfold dApexTAdder
        simp only [↓reduceIte]
        exact CleanUnitaryWp.dPureConj (xAllCircuit rT) rC
          (Finset.disjoint_of_subset_left (support_xAllCircuit_sub rT)
            (QRegExt.disjointWires_to_finset hTC)) hw₀,
      by
        simp only [u, eval_xAllCircuit_inverse, Submonoid.coe_mul]
        exact DiagOn.conj_xAllCircuit rT hDiag₀,
      fun ξ hzC ↦ ?_⟩
    simp only [u, eval_xAllCircuit_inverse, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      xAllCircuit_evolve]
    let ξ₁ := flipRegBits rT ξ
    have hzC₁ : ∀ i : Fin (m + 1), ξ₁ (rC i) = 0 := fun i ↦ by
      dsimp only [ξ₁]
      rw [flipRegBits_outside rT ξ ((disj_symm hTC).apply_not_mem_right i), hzC i]
    have hU₁ : regVal rU ξ₁ = regVal rU ξ :=
      regVal_congr rU fun i ↦ flipRegBits_outside rT ξ (hUT.apply_not_mem_right i)
    have hT₁ : regVal rT ξ₁ = 2 ^ (m + 1) - 1 - regVal rT ξ := by
      have h : regVal rT ξ₁ + regVal rT ξ = 2 ^ (m + 1) - 1 := regVal_flipRegBits_add rT ξ
      omega
    rw [hKet₀ ξ₁ hzC₁, Matrix.mulVec_smul, xAllCircuit_evolve, hU₁,
      flipRegBits_shiftRegInt_ones_comp rT ξ (regVal_lt_two_pow rU ξ)]
    simp only [↓reduceIte, neg_one_mul]
    congr 1
    rw [ZMod.val_natCast_of_lt ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (m + 1))).mpr (by
        have := regVal_lt_two_pow rU ξ
        have := regVal_lt_two_pow rT ξ₁
        omega)), hT₁]
    unfold apexCarryPhase
    congr 1
    simpa [sub_eq_add_neg] using ones_comp_carry_eq (regVal_lt_two_pow rT ξ) (regVal_lt_two_pow rU
      ξ)
def cApexXorT {n : ℕ} (wNeg c : Wire n) : Circuit n :=
  if h : wNeg ≠ c then Circuit.CNOT wNeg c h ;;ᶜ Circuit.T c ;;ᶜ Circuit.CNOT wNeg c h else
    .identity
@[simp] lemma count_cApexXorT_toff {n : ℕ} (wNeg c : Wire n) : (cApexXorT wNeg c).count .TOFF = 0 :=
  by
  unfold cApexXorT
  by_cases h : wNeg ≠ c
  · simp [h, Circuit.CNOT, Circuit.T, Circuit.count_seq]
  · simp [h]
lemma count_cApexXorT_t {n : ℕ} {wNeg c : Wire n} (hne : wNeg ≠ c) : (cApexXorT wNeg c).count .T =
    1 := by
  unfold cApexXorT
  rw [dite_eq_left hne]
  rfl
noncomputable def dApexTAdderCtrlSign {Var : Type} {n : ℕ} (v : Var) (wNeg : Wire n)
    (rU rT rC : QRegister 4 n) (hwNegT : ∀ i : Fin 4, wNeg ≠ rT i) (hUT : rU.DisjointWires rT)
    (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) : DynamicCircuit Var n :=
  dPureConj (cnotAllCircuit wNeg rT hwNegT) (dApexCarryChain 3 v (cApexXorT wNeg) rU rT rC hUT hUC
    hTC)
@[simp] lemma count_dApexTAdderCtrlSign_toff {Var : Type} {n : ℕ} (v : Var) (wNeg : Wire n) (rU rT
    rC : QRegister 4 n)
    (hwNegT : ∀ i : Fin 4, wNeg ≠ rT i) (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC)
      (hTC : rT.DisjointWires
    rC) : (dApexTAdderCtrlSign v wNeg rU rT rC hwNegT hUT hUC hTC).count .TOFF = 0 := by
  unfold dApexTAdderCtrlSign
  rw [count_dPureConj_toff _ (count_cnotAllCircuit_toff wNeg rT hwNegT)]
  exact count_dApexCarryChain_toff 3 v (cApexXorT wNeg) (count_cApexXorT_toff wNeg) rU rT rC hUT hUC
    hTC
lemma count_dApexTAdderCtrlSign_t {Var : Type} {n : ℕ} (v : Var) (wNeg : Wire n) (rU rT rC :
    QRegister 4 n) (hwNegT : ∀
    i : Fin 4, wNeg ≠ rT i) (hwNegC : wNeg ∉ rC.image) (hUT : rU.DisjointWires rT) (hUC :
      rU.DisjointWires rC) (hTC :
    rT.DisjointWires rC) : (dApexTAdderCtrlSign v wNeg rU rT rC hwNegT hUT hUC hTC).count .T = 17 :=
      by
  unfold dApexTAdderCtrlSign
  rw [count_dPureConj_t _ (count_cnotAllCircuit_t wNeg rT hwNegT),
    count_dApexCarryChain_t_mem 3 v (cApexXorT wNeg) 1 rU rT rC
      (fun w hw ↦ count_cApexXorT_t (by
        rintro rfl
        exact hwNegC hw)) hUT hUC hTC]
lemma cApexXorT_evolve_any {n : ℕ} (wNeg c : Wire n) (ξ : BitAssignment n) : (cApexXorT wNeg
    c).eval.1.mulVec (basisKet
    ξ) = DyadicQft64.dyadicTurn 3 (((ξ c + ξ wNeg).val : ℤ)) • basisKet ξ := by
  unfold cApexXorT
  by_cases hne : wNeg ≠ c
  · rw [dite_eq_left hne]
    simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_CNOT_basisKet]
    rw [(PhasePerm.gateT c).evolve, Matrix.mulVec_smul, evolve_CNOT_basisKet, dyadicTurn7_16_eq_3,
      Function.update_self]
    congr 2
    funext u
    by_cases hu : u = c
    · subst hu
      simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hu]
  · rcases Decidable.of_not_not hne with rfl
    rw [dite_eq_right (not_not.mpr rfl), zmod2_add_self]
    change (Circuit.identity : Circuit n).eval.1.mulVec (basisKet ξ) = DyadicQft64.dyadicTurn 3 0 •
      basisKet ξ
    rw [DyadicQft64.dyadicTurn_zero, one_smul]
    exact evolve_identity_basisKet ξ
lemma zmod2_natCast_add_one_val {q : ℕ} (hq : q < 2) : ((((q : ZMod 2) + 1).val : ℤ)) = 1 +
    -(q : ℤ) := by
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · decide
  · decide
theorem dApexTAdderCtrlSign_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (wNeg : Wire n) (rU rT
    rC : QRegister 4 n) (hwNegU : wNeg ∉ rU.image) (hwNegT : ∀ i : Fin 4, wNeg ≠ rT i) (hwNegC :
      wNeg ∉ rC.image)
    (hUT : rU.DisjointWires rT) (hUC : rU.DisjointWires rC) (hTC : rT.DisjointWires rC) :
    ∃ u : Unitary (2 ^ n),
      CleanUnitaryWp rC u (dApexTAdderCtrlSign v wNeg rU rT rC hwNegT hUT hUC hTC) ∧
      DiagOn (Finset.univ \ rT.image) u.1 ∧
      ∀ ξ : BitAssignment n, (∀ i : Fin 4, ξ (rC i) = 0) →
        let sgn : ℤ := 1 - 2 * ((ξ wNeg).val : ℤ)
        u.1.mulVec (basisKet ξ) =
          (DyadicQft64.dyadicTurn 3 ((ξ wNeg).val : ℤ) *
            apexCarryPhase rT ξ (sgn * (regVal rU ξ : ℤ))) •
            basisKet (shiftRegInt rT ξ (sgn * (regVal rU ξ : ℤ))) := by
  have hwNegT_not : wNeg ∉ rT.image := fun hm ↦ by
    rcases (QRegister.mem_image rT wNeg).mp hm with ⟨i, hi⟩
    exact hwNegT i hi.symm
  obtain ⟨u₀, hw₀, hDiag₀, hKet₀⟩ := dApexCarryChain_spec 3 v (cApexXorT wNeg) ({wNeg} : Finset
    (Wire n))
    (fun ξ b ↦ DyadicQft64.dyadicTurn 3 (((b + ξ wNeg).val : ℤ)))
    (fun ξ₁ ξ₂ b hEq ↦ by simp [hEq wNeg (Finset.mem_singleton_self wNeg)]) (cApexXorT_evolve_any
      wNeg) rU rT rC hUT hUC hTC
    (Finset.disjoint_singleton_right.mpr hwNegU) (Finset.disjoint_singleton_right.mpr hwNegT_not)
      (Finset.disjoint_singleton_right.mpr hwNegC)
  let u := (cnotAllCircuit wNeg rT hwNegT).inverse.eval * u₀ * (cnotAllCircuit wNeg rT hwNegT).eval
  refine ⟨u, CleanUnitaryWp.dPureConj (cnotAllCircuit wNeg rT hwNegT) rC
      (Finset.disjoint_of_subset_left (support_cnotAllCircuit_sub wNeg rT hwNegT)
        (Finset.disjoint_insert_left.mpr ⟨hwNegC, (QRegExt.disjointWires_to_finset hTC)⟩)) hw₀,
    DiagOn.conj_cnotAllCircuit wNeg rT hwNegT disjoint_sdiff_self_right hDiag₀, fun ξ hzC ↦ ?_⟩
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    cnotAllCircuit_evolve]
  rcases zmod2_eq_zero_or_one (ξ wNeg) with hw0 | hw1
  · have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp only [hw0, h01, ↓reduceIte]
    rw [hKet₀ ξ hzC, Matrix.mulVec_smul, cnotAllCircuit_inverse_evolve, shiftRegInt_outside rT ξ _
      hwNegT_not]
    simp only [hw0, h01, ↓reduceIte, ZMod.val_zero, CharP.cast_eq_zero, mul_zero, sub_zero, one_mul,
      add_zero, DyadicQft64.dyadicTurn_zero]
    exact congrArg (· • _) (congrArg (DyadicQft64.dyadicTurn 3)
      (div_two_pow_zmod2_val (W := 4) (regVal_lt_two_pow rU ξ) (regVal_lt_two_pow rT ξ)))
  · simp only [hw1, ↓reduceIte]
    let ξ₁ := flipRegBits rT ξ
    have hzC₁ : ∀ i : Fin 4, ξ₁ (rC i) = 0 := fun i ↦ by
      dsimp only [ξ₁]
      rw [flipRegBits_outside rT ξ ((disj_symm hTC).apply_not_mem_right i), hzC i]
    have hU₁ : regVal rU ξ₁ = regVal rU ξ := regVal_congr rU fun i ↦ flipRegBits_outside rT ξ
      (hUT.apply_not_mem_right i)
    have hw₁ : ξ₁ wNeg = 1 := by
      dsimp only [ξ₁]
      rw [flipRegBits_outside rT ξ hwNegT_not, hw1]
    have hT₁ : regVal rT ξ₁ = 2 ^ 4 - 1 - regVal rT ξ := by
      have h : regVal rT ξ₁ + regVal rT ξ = 2 ^ 4 - 1 := regVal_flipRegBits_add rT ξ
      omega
    rw [hKet₀ ξ₁ hzC₁, Matrix.mulVec_smul, cnotAllCircuit_inverse_evolve,
      ite_eq_left (by rw [shiftRegInt_outside rT ξ₁ _ hwNegT_not, hw₁]), hU₁,
      flipRegBits_shiftRegInt_ones_comp rT ξ (regVal_lt_two_pow rU ξ), hw₁,
      show (1 - 2 * ((1 : ZMod 2).val : ℤ)) = -1 by decide, neg_one_mul]
    congr 1
    change DyadicQft64.dyadicTurn 3 ((((((regVal rU ξ + regVal rT ξ₁) / 2 ^ 4 : ℕ) : ZMod 2) +
      1).val : ℤ)) =
      DyadicQft64.dyadicTurn 3 ((1 : ZMod 2).val : ℤ) * apexCarryPhase rT ξ (-(regVal rU ξ : ℤ))
    rw [show ((1 : ZMod 2).val : ℤ) = 1 by decide, zmod2_natCast_add_one_val (by
        have := regVal_lt_two_pow rU ξ
        have := regVal_lt_two_pow rT ξ₁
        omega), ← DyadicQft64.dyadicTurn_add]
    congr 1
    rw [hT₁]
    unfold apexCarryPhase
    congr 1
    simpa [sub_eq_add_neg] using ones_comp_carry_eq (regVal_lt_two_pow rT ξ) (regVal_lt_two_pow rU
      ξ)
structure ClassicalAncBank {n : ℕ} (S_ctrl S_anc : Finset (Wire n))
    (c : Circuit n) (f fInv : BitAssignment n → BitAssignment n) : Prop where
  evolve : ∀ γ : BitAssignment n, c.eval.1.mulVec (basisKet γ) = basisKet (f γ)
  inv_evolve : ∀ γ : BitAssignment n, c.inverse.eval.1.mulVec (basisKet γ) = basisKet (fInv γ)
  left_inv : ∀ γ : BitAssignment n, fInv (f γ) = γ
  fwd_outside : ∀ (γ : BitAssignment n) (w : Wire n), w ∉ S_anc → f γ w = γ w
  inv_outside : ∀ (γ : BitAssignment n) (w : Wire n), w ∉ S_anc → fInv γ w = γ w
  inv_congr : ∀ γ₁ γ₂ : BitAssignment n, (∀ u ∈ S_ctrl ∪ S_anc, γ₁ u = γ₂ u) → ∀ u ∈ S_anc,
    fInv γ₁ u = fInv γ₂ u
lemma ClassicalAncBank.seq {n : ℕ} {S_ctrl S_anc : Finset (Wire n)} (hDisj : Disjoint S_ctrl S_anc)
    {c₁ c₂ : Circuit n} {f₁ fInv₁ f₂ fInv₂ : BitAssignment n → BitAssignment n}
    (h₁ : ClassicalAncBank S_ctrl S_anc c₁ f₁ fInv₁) (h₂ : ClassicalAncBank S_ctrl S_anc c₂ f₂
      fInv₂) :
    ClassicalAncBank S_ctrl S_anc (c₁ ;;ᶜ c₂) (fun γ ↦ f₂ (f₁ γ)) (fun γ ↦ fInv₁ (fInv₂ γ)) where
  evolve γ := by
    rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₁.evolve, h₂.evolve]
  inv_evolve γ := by
    rw [Circuit.inverse_seq, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      h₂.inv_evolve, h₁.inv_evolve]
  left_inv γ := by rw [h₂.left_inv, h₁.left_inv]
  fwd_outside γ w hw := by rw [h₂.fwd_outside _ w hw, h₁.fwd_outside _ w hw]
  inv_outside γ w hw := by rw [h₁.inv_outside _ w hw, h₂.inv_outside _ w hw]
  inv_congr γ₁ γ₂ hEq u huAnc := h₁.inv_congr _ _ (fun w hwU ↦ (Finset.mem_union.mp hwU).elim
    (fun hwC ↦ by
      have hwN := Finset.disjoint_left.mp hDisj hwC
      rw [h₂.inv_outside _ w hwN, h₂.inv_outside _ w hwN, hEq w hwU])
    (h₂.inv_congr γ₁ γ₂ hEq w)) u huAnc
lemma ClassicalAncBank.of_self_inv_update {n : ℕ} {S_ctrl S_anc : Finset (Wire n)} (c : Circuit n)
    (anc : Wire n) (δ :
    BitAssignment n → ZMod 2) (hanc : anc ∈ S_anc) (hevolve : ∀ γ, c.eval.1.mulVec (basisKet γ) =
      basisKet
    (Function.update γ anc (γ anc + δ γ))) (hinv : c.inverse.eval = c.eval) (hδ_anc : ∀ γ,
      δ (Function.update γ anc (γ
    anc + δ γ)) = δ γ)
    (hδ_congr : ∀ γ₁ γ₂, (∀ w ∈ S_ctrl ∪ S_anc, γ₁ w = γ₂ w) → δ γ₁ = δ γ₂) :
    ClassicalAncBank S_ctrl S_anc c
      (fun γ ↦ Function.update γ anc (γ anc + δ γ))
      (fun γ ↦ Function.update γ anc (γ anc + δ γ)) where
  evolve := hevolve
  inv_evolve γ := by rw [hinv]; exact hevolve γ
  left_inv γ := by
    funext w; by_cases hw : w = anc
    · subst hw; simp [hδ_anc γ]
    · simp [Function.update_of_ne hw]
  fwd_outside γ w hw := by rw [Function.update_of_ne (by rintro rfl; exact hw hanc)]
  inv_outside γ w hw := by rw [Function.update_of_ne (by rintro rfl; exact hw hanc)]
  inv_congr γ₁ γ₂ hEq u huAnc := by
    by_cases hu : u = anc
    · rw [hu]; simp [hEq anc (Finset.mem_union_right _ hanc), hδ_congr γ₁ γ₂ hEq]
    · simp [Function.update_of_ne hu, hEq u (Finset.mem_union_right _ huAnc)]
lemma ClassicalAncBank.cGenBoolStep {n : ℕ} {S_ctrl S_anc : Finset (Wire n)} (b₁ b₂ bOut : Bool) (c₁
    c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hc1 : c₁ ∈ S_ctrl ∪ S_anc) (hc2 : c₂ ∈ S_ctrl
      ∪ S_anc) (hanc :
    anc ∈ S_anc) : ClassicalAncBank S_ctrl S_anc (JunctionApexCSA288.cGenBoolStep b₁ b₂ bOut c₁ c₂
      anc
      h₁₂ h₁a h₂a)
      (fun γ ↦ Function.update γ anc (γ anc + genBoolBit b₁ b₂ bOut (γ c₁) (γ c₂)))
      (fun γ ↦ Function.update γ anc (γ anc + genBoolBit b₁ b₂ bOut (γ c₁) (γ c₂))) :=
  ClassicalAncBank.of_self_inv_update _ anc _ hanc
    (cGenBoolStep_evolve b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a) (eval_cGenBoolStep_inverse _ _ _ _ _ _ _
      _ _)
    (fun γ ↦ by simp [Function.update_of_ne h₁a, Function.update_of_ne h₂a])
    (fun _ _ hEq ↦ by simp [hEq c₁ hc1, hEq c₂ hc2])
lemma ClassicalAncBank.CNOT {n : ℕ} {S_ctrl S_anc : Finset (Wire n)} (c₁ anc : Wire n) (h₁a : c₁ ≠
    anc) (hc1 : c₁ ∈
    S_ctrl ∪ S_anc) (hanc : anc ∈ S_anc) : ClassicalAncBank S_ctrl S_anc (Circuit.CNOT c₁ anc h₁a)
      (fun γ ↦ Function.update γ anc (γ anc + γ c₁))
      (fun γ ↦ Function.update γ anc (γ anc + γ c₁)) :=
  ClassicalAncBank.of_self_inv_update _ anc _ hanc (evolve_CNOT_basisKet c₁ anc h₁a)
    (eval_CNOT_inverse _ _ _) (fun γ ↦ by simp [Function.update_of_ne h₁a])
    (fun _ _ hEq ↦ hEq c₁ hc1)
lemma vec_decomp_basisKet {n : ℕ} (v : Fin (2 ^ n) → ℂ) : v = ∑ i : Fin (2 ^ n), v i • basisKet
    (basisBits n i) := by
  funext j
  rw [Finset.sum_apply]
  have hterm : ∀ i : Fin (2 ^ n),(v i • basisKet (basisBits n i)) j =
      if i = j then v j else 0 := by
    intro i
    rw [← pi_single_eq_basisKet i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  simp [hterm]
theorem ClassicalAncBank.conj_elim_embed {mSys n : ℕ} {S_ctrl S_anc : Finset (Wire n)} {cBank :
    Circuit n} {f fInv :
    BitAssignment n → BitAssignment n} (hBank : ClassicalAncBank S_ctrl S_anc cBank f fInv) (rSys :
      QRegister mSys n)
    (hSysAnc : Disjoint rSys.image S_anc) (U : Unitary (2 ^ n)) (U₀ : Unitary (2 ^ mSys)) (hDiag :
      DiagOn (S_ctrl ∪
    S_anc) U.1) (ξ : BitAssignment n) (hAct : U.1.mulVec (basisKet (f ξ)) = (rSys.embedUnitary
      U₀).1.mulVec (basisKet (f
    ξ))) : (cBank.inverse.eval * U * cBank.eval).1.mulVec (basisKet ξ) = (rSys.embedUnitary
      U₀).1.mulVec (basisKet ξ) :=
    by
  let g : BitAssignment n → BitAssignment n := fun β w ↦
    if w ∈ S_anc then β w + (f ξ w + ξ w) else β w
  have hg_eq : ∀ i : Fin (2 ^ n), (U.1.mulVec (basisKet (f ξ))) i ≠ 0 →
      fInv (basisBits n i) = g (basisBits n i) := fun i hne ↦ by
    have hMatNe : U.1 i ((basisBitsEquiv n).symm (f ξ)) ≠ 0 := by
      rwa [basisKet_eq_single, Matrix.mulVec_single_one] at hne
    have hAgree : ∀ u ∈ S_ctrl ∪ S_anc, basisBits n i u = f ξ u := fun u hu ↦ by
      simpa [basisBits_basisBitsEquiv_symm_eq] using hDiag i ((basisBitsEquiv n).symm (f ξ)) hMatNe
        u hu
    funext w; by_cases hw : w ∈ S_anc
    · dsimp [g]; rw [hBank.inv_congr _ _ hAgree w hw, hBank.left_inv ξ, ite_eq_left hw,
        hAgree w (Finset.mem_union_right _ hw), ← add_assoc, zmod2_add_self, zero_add]
    · dsimp [g]; rw [hBank.inv_outside _ w hw, ite_eq_right hw]
  have hg_write : ∀ b : BitAssignment mSys, g (vepWriteReg (f ξ) rSys b) = vepWriteReg ξ rSys b :=
    fun b ↦ by
    funext w; by_cases hwSys : w ∈ Set.range rSys.wires
    · rcases hwSys with ⟨j, rfl⟩
      dsimp [g]
      rw [ite_eq_right (Finset.disjoint_left.mp hSysAnc ((QRegister.mem_image rSys _).mpr ⟨j,
        rfl⟩)),
        vepWriteReg_mem, vepWriteReg_mem]
    · dsimp [g]; rw [vepWriteReg_not_mem _ _ _ _ hwSys, vepWriteReg_not_mem _ _ _ _ hwSys]
      by_cases hwAnc : w ∈ S_anc
      · rw [ite_eq_left hwAnc, ← add_assoc, zmod2_add_self, zero_add]
      · rw [ite_eq_right hwAnc, hBank.fwd_outside ξ w hwAnc]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hBank.evolve ξ]
  let ψ := U.1.mulVec (basisKet (f ξ))
  let Lg : (Fin (2 ^ n) → ℂ) → (Fin (2 ^ n) → ℂ) := fun v ↦ ∑ i : Fin (2 ^ n), v i • basisKet (g
    (basisBits n i))
  have hLHS : cBank.inverse.eval.1.mulVec ψ = Lg ψ := by
    conv_lhs => rw [vec_decomp_basisKet ψ]
    rw [Matrix.mulVec_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Matrix.mulVec_smul, hBank.inv_evolve]
    by_cases h0 : ψ i = 0
    · simp [h0]
    · rw [hg_eq i h0]
  have hLg_ket : ∀ β : BitAssignment n, Lg (basisKet β) = basisKet (g β) := fun β ↦ by
    dsimp [Lg]; rw [Finset.sum_eq_single ((basisBitsEquiv n).symm β)]
    · rw [basisKet_eq_single, Pi.single_eq_same, one_smul, basisBits_basisBitsEquiv_symm_eq]
    · intro i _ hne; rw [basisKet_eq_single, Pi.single_eq_of_ne hne, zero_smul]
    · intro hAbs; exact absurd (Finset.mem_univ _) hAbs
  have hLg_sum : ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (β : ι → BitAssignment n),
      Lg (∑ l ∈ s, c l • basisKet (β l)) = ∑ l ∈ s, c l • basisKet (g (β l)) := fun s c β ↦ by
    dsimp [Lg]; simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← hLg_ket]; dsimp [Lg]; rw [Finset.smul_sum]; simp_rw [smul_smul]
  change cBank.inverse.eval.1.mulVec ψ = (rSys.embedMatrix U₀.1).mulVec (basisKet ξ)
  rw [hLHS, show ψ = (rSys.embedMatrix U₀.1).mulVec (basisKet (f ξ)) from hAct,
    vepEmbedMatrix_mulVec_basisKet, hLg_sum,
    show (fun j : Fin mSys ↦ f ξ (rSys j)) = (fun j : Fin mSys ↦ ξ (rSys j)) from funext fun j ↦
      hBank.fwd_outside ξ (rSys j) (Finset.disjoint_left.mp hSysAnc ((QRegister.mem_image rSys
        _).mpr ⟨j, rfl⟩)),
    vepEmbedMatrix_mulVec_basisKet]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [hg_write]
lemma slice_disjoint_of_le {m n : ℕ} (r : QRegister m n) (a₁ k₁ a₂ k₂ : ℕ) (h₁ : a₁ + k₁ ≤ m) (h₂ :
    a₂ + k₂ ≤ m) (hle :
    a₁ + k₁ ≤ a₂) : (r.slice a₁ k₁ h₁).DisjointWires (r.slice a₂ k₂ h₂) :=
  QRegExt.disjointWires_of_finset (Finset.disjoint_left.mpr fun w hw1 hw2 ↦ by
    rcases (QRegister.mem_image _ w).mp hw1 with ⟨i, rfl⟩
    rcases (QRegister.mem_image _ _).mp hw2 with ⟨j, hj⟩
    rw [slice_apply_eq, slice_apply_eq] at hj
    have hEq := congrArg Fin.val (r.wires.injective hj); dsimp at hEq; omega)
lemma shiftRegInt_add_mul_two_pow {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) (sgn M Q :
    ℤ) :
    shiftRegInt rT ξ (sgn * M) = shiftRegInt rT ξ (sgn * (M + (2 ^ W : ℤ) * Q)) :=
  shiftRegInt_congr_mod rT ξ (by
    rw [show sgn * (M + (2 ^ W : ℤ) * Q) = sgn * M + (2 ^ W : ℤ) * (sgn * Q) by
      ring, Int.add_mul_emod_self_left])
lemma apexCarryPhase_add_mul_two_pow {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n) (sgn M Q :
    ℤ) :
    DyadicQft64.dyadicTurn 3 (sgn * Q) * apexCarryPhase rT ξ (sgn * M) =
      apexCarryPhase rT ξ (sgn * (M + (2 ^ W : ℤ) * Q)) := by
  unfold apexCarryPhase; rw [DyadicQft64.dyadicTurn_add]; congr 1
  rw [show (regVal rT ξ : ℤ) + sgn * (M + (2 ^ W : ℤ) * Q) =
    ((regVal rT ξ : ℤ) + sgn * M) + (2 ^ W : ℤ) * (sgn * Q) by ring,
    Int.add_mul_ediv_left _ _ (by positivity : (2 ^ W : ℤ) ≠ 0), add_comm]
def dFaWrap {Var : Type} {n : ℕ} (v : Var) (a b c car : Wire n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b
    ≠ c) (hacar : a ≠
    car) (hbcar : b ≠ car) (hccar : c ≠ car) (dInner : DynamicCircuit Var n) : DynamicCircuit Var
      n :=
  dPureConj (Circuit.CNOT c a hac.symm ;;ᶜ Circuit.CNOT c b hbc.symm)
    (dAndSandwich v a b car hab hacar hbcar
      (dPureConj (Circuit.CNOT c car hccar ;;ᶜ Circuit.CNOT c a hac.symm ;;ᶜ Circuit.CNOT a b hab)
        dInner))
@[simp] lemma count_dFaWrap_toff {Var : Type} {n : ℕ} (v : Var) (a b c car : Wire n) (hab : a ≠ b)
    (hac : a ≠ c) (hbc :
    b ≠ c) (hacar : a ≠ car) (hbcar : b ≠ car) (hccar : c ≠ car) (dInner : DynamicCircuit Var n) :
      (dFaWrap v a b c car
    hab hac hbc hacar hbcar hccar dInner).count .TOFF = dInner.count .TOFF := by
  unfold dFaWrap
  rw [count_dPureConj_toff _ (by simp [Circuit.CNOT, Circuit.count_seq]), count_dAndSandwich_toff,
    count_dPureConj_toff _ (by simp [Circuit.CNOT, Circuit.count_seq])]
@[simp] lemma count_dFaWrap_t {Var : Type} {n : ℕ} (v : Var) (a b c car : Wire n) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠
    c) (hacar : a ≠ car) (hbcar : b ≠ car) (hccar : c ≠ car) (dInner : DynamicCircuit Var n) :
      (dFaWrap v a b c car hab
    hac hbc hacar hbcar hccar dInner).count .T = 4 + dInner.count .T := by
  unfold dFaWrap
  rw [count_dPureConj_t _ (by simp [Circuit.CNOT, Circuit.count_seq]), count_dAndSandwich_t,
    count_dPureConj_t _ (by simp [Circuit.CNOT, Circuit.count_seq])]
lemma pair3_sub_sdiff {W n : ℕ} {rT : QRegister W n} {a b c : Wire n}
    (ha : a ∉ rT.image) (hb : b ∉ rT.image) (hc : c ∉ rT.image) :
    ({a, b, c} : Finset (Wire n)) ⊆ Finset.univ \ rT.image := fun w hw ↦
  Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, by
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ha
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hb
      · exact Finset.mem_singleton.mp hw ▸ hc⟩
theorem dFaWrap_spec {Var : Type} [Fintype Var] [DecidableEq Var] {W mSub mTot n : ℕ} (v : Var)
    (rT : QRegister W n)
    (rSub : QRegister mSub n) (rTot : QRegister mTot n) (a b c car : Wire n) (hab : a ≠ b) (hac : a
      ≠ c) (hbc : b ≠ c)
    (hacar : a ≠ car) (hbcar : b ≠ car) (hccar : c ≠ car) (hSubTot : rSub.image ⊆ rTot.image)
      (hcarTot : car ∈
    rTot.image) (hcarSub : car ∉ rSub.image) (haTot : a ∉ rTot.image) (hbTot : b ∉ rTot.image)
      (hcTot : c ∉ rTot.image)
    (haT : a ∉ rT.image) (hbT : b ∉ rT.image) (hcT : c ∉ rT.image) (hcarT : car ∉ rT.image)
      {uInner : Unitary (2 ^ n)}
    {dInner : DynamicCircuit Var n} (hwInner : CleanUnitaryWp rSub uInner dInner)
    (hDiagInner : DiagOn (Finset.univ \ rT.image) uInner.1) :
    ∃ u : Unitary (2 ^ n),
      CleanUnitaryWp rTot u (dFaWrap v a b c car hab hac hbc hacar hbcar hccar dInner) ∧
      DiagOn (Finset.univ \ rT.image) u.1 ∧
      ∀ (ξ : BitAssignment n) {φ : ℂ} {d : ℤ}, ξ car = 0 →
        let η := Function.update (Function.update ξ b (ξ b + ξ c + ξ a)) car
            (carryBitZMod2 (ξ c) (ξ a) (ξ b))
        uInner.1.mulVec (basisKet η) = φ • basisKet (shiftRegInt rT η d) →
        u.1.mulVec (basisKet ξ) = φ • basisKet (shiftRegInt rT ξ d) := by
  have haSub : a ∉ rSub.image := fun h ↦ haTot (hSubTot h)
  have hbSub : b ∉ rSub.image := fun h ↦ hbTot (hSubTot h)
  have hcSub : c ∉ rSub.image := fun h ↦ hcTot (hSubTot h)
  let cIn := Circuit.CNOT c car hccar ;;ᶜ Circuit.CNOT c a hac.symm ;;ᶜ Circuit.CNOT a b hab
  let cOut := Circuit.CNOT c a hac.symm ;;ᶜ Circuit.CNOT c b hbc.symm
  have hDiag1 : DiagOn (Finset.univ \ rT.image) (cIn.inverse.eval * uInner * cIn.eval).1 := by
    simp only [cIn, Circuit.inverse_seq, Circuit.eval_seq, eval_CNOT_inverse, Submonoid.coe_mul,
      Matrix.mul_assoc]
    simpa only [Matrix.mul_assoc] using
      DiagOn.conj_CNOT c car hccar (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcT⟩)
        (DiagOn.conj_CNOT c a hac.symm (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcT⟩)
          (DiagOn.conj_CNOT a b hab (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haT⟩) hDiagInner))
  let u2 := (Circuit.TOFF a b car hab hacar hbcar).eval *
      (cIn.inverse.eval * uInner * cIn.eval) * (Circuit.TOFF a b car hab hacar hbcar).eval
  have hDiag2 : DiagOn (Finset.univ \ rT.image) u2.1 :=
    DiagOn.conj_TOFF a b car hab hacar hbcar (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haT⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbT⟩) hDiag1
  let u := cOut.inverse.eval * u2 * cOut.eval
  have hDiag3 : DiagOn (Finset.univ \ rT.image) u.1 := by
    simp only [u, cOut, Circuit.inverse_seq, Circuit.eval_seq, eval_CNOT_inverse, Submonoid.coe_mul,
      Matrix.mul_assoc]
    simpa only [Matrix.mul_assoc] using
      DiagOn.conj_CNOT c a hac.symm (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcT⟩)
        (DiagOn.conj_CNOT c b hbc.symm (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcT⟩) hDiag2)
  refine ⟨u, CleanUnitaryWp.dPureConj cOut rTot
      (disj_support_seq (disj_support_CNOT c a hac.symm hcTot haTot) (disj_support_CNOT c b hbc.symm
        hcTot hbTot))
      (CleanUnitaryWp.dAndSandwich v a b car hab hacar hbcar rSub rTot hSubTot hcarTot haSub hbSub
        hcarSub
        (DiagOn.anti (pair3_sub_sdiff haT hbT hcarT) hDiag1)
        (CleanUnitaryWp.dPureConj cIn rSub
          (disj_support_seq (disj_support_CNOT c car hccar hcSub hcarSub)
            (disj_support_seq (disj_support_CNOT c a hac.symm hcSub haSub) (disj_support_CNOT a b
              hab haSub hbSub)))
          hwInner)),
    hDiag3, fun ξ {φ d} hzCar hAct ↦ ?_⟩
  let cPreAll := cOut ;;ᶜ (Circuit.TOFF a b car hab hacar hbcar ;;ᶜ cIn)
  rw [show u = cPreAll.inverse.eval * uInner * cPreAll.eval by
    simp only [u, u2, cPreAll, Circuit.inverse_seq, Circuit.eval_seq, eval_TOFF_inverse, mul_assoc]]
  apply (((PreservesReg.CNOT c a hac.symm hcT haT).seq (PreservesReg.CNOT c b hbc.symm hcT hbT)).seq
    ((PreservesReg.TOFF
      a b car hab hacar hbcar haT hbT hcarT).seq ((PreservesReg.CNOT c car hccar hcT hcarT).seq
        ((PreservesReg.CNOT c a
      hac.symm hcT haT).seq (PreservesReg.CNOT a b hab haT hbT))))).conj_shift
  have hGoal : ∀ ζ, ζ = Function.update (Function.update ξ b (ξ b + ξ c + ξ a))
      car (carryBitZMod2 (ξ c) (ξ a) (ξ b)) →
      uInner.1.mulVec (basisKet ζ) = φ • basisKet (shiftRegInt rT ζ d) := by
    rintro _ rfl
    exact hAct
  apply hGoal
  funext w
  by_cases hwb : w = b
  · subst hwb
    simp only [Function.comp_apply, Function.update_self, Function.update_of_ne, hab, hab.symm,
      hac.symm,
        hbc.symm, hacar, hacar.symm, hbcar, hbcar.symm, hccar, ne_eq, not_false_eq_true]
    rw [zmod2_add_cancel_right]
  · by_cases hwcar : w = car
    · subst hwcar
      simp only [carryBitZMod2, hzCar, Function.comp_apply, Function.update_self,
        Function.update_of_ne,
        hab, hab.symm, hac.symm, hbc.symm, hacar, hacar.symm, hbcar, hbcar.symm,
        hccar, ne_eq, not_false_eq_true]
      ring
    · by_cases hwa : w = a
      · subst hwa
        simp only [Function.comp_apply, Function.update_self, Function.update_of_ne, hwb, hwcar,
          hab.symm,
            hac.symm, hbc.symm, hacar.symm, hbcar, hbcar.symm, hccar, ne_eq, not_false_eq_true]
        exact zmod2_add_cancel_right (ξ w) (ξ c)
      · simp [Function.update_of_ne hwb, Function.update_of_ne hwcar, Function.update_of_ne hwa]
def dHaWrap {Var : Type} {n : ℕ} (v : Var) (b a car : Wire n) (hba : b ≠ a) (hbcar : b ≠ car)
    (hacar : a ≠ car) (dInner : DynamicCircuit Var n) : DynamicCircuit Var n :=
  dAndSandwich v b a car hba hbcar hacar (dPureConj (Circuit.CNOT a b hba.symm) dInner)
@[simp] lemma count_dHaWrap_toff {Var : Type} {n : ℕ} (v : Var) (b a car : Wire n)
    (hba : b ≠ a) (hbcar : b ≠ car) (hacar : a ≠ car) (dInner : DynamicCircuit Var n) :
    (dHaWrap v b a car hba hbcar hacar dInner).count .TOFF = dInner.count .TOFF := by
  unfold dHaWrap
  rw [count_dAndSandwich_toff, count_dPureConj_toff _ (by simp [Circuit.CNOT])]
@[simp] lemma count_dHaWrap_t {Var : Type} {n : ℕ} (v : Var) (b a car : Wire n) (hba : b ≠ a)
    (hbcar : b ≠ car) (hacar : a ≠ car) (dInner : DynamicCircuit Var n) :
    (dHaWrap v b a car hba hbcar hacar dInner).count .T = 4 + dInner.count .T := by
  unfold dHaWrap
  rw [count_dAndSandwich_t, count_dPureConj_t _ (by simp [Circuit.CNOT])]
theorem dHaWrap_spec {Var : Type} [Fintype Var] [DecidableEq Var] {W mSub mTot n : ℕ} (v : Var)
    (rT : QRegister W n)
    (rSub : QRegister mSub n) (rTot : QRegister mTot n) (b a car : Wire n) (hba : b ≠ a) (hbcar : b
      ≠ car) (hacar : a ≠
    car) (hSubTot : rSub.image ⊆ rTot.image) (hcarTot : car ∈ rTot.image) (hcarSub : car ∉
      rSub.image) (hbTot : b ∉
    rTot.image) (haTot : a ∉ rTot.image) (hbT : b ∉ rT.image) (haT : a ∉ rT.image) (hcarT : car ∉
      rT.image) {uInner :
    Unitary (2 ^ n)} {dInner : DynamicCircuit Var n} (hwInner : CleanUnitaryWp rSub uInner dInner)
    (hDiagInner : DiagOn (Finset.univ \ rT.image) uInner.1) :
    ∃ u : Unitary (2 ^ n),
      CleanUnitaryWp rTot u (dHaWrap v b a car hba hbcar hacar dInner) ∧
      DiagOn (Finset.univ \ rT.image) u.1 ∧
      ∀ (ξ : BitAssignment n) {φ : ℂ} {d : ℤ}, ξ car = 0 →
        let η := Function.update (Function.update ξ b (ξ b + ξ a)) car (ξ b * ξ a)
        uInner.1.mulVec (basisKet η) = φ • basisKet (shiftRegInt rT η d) →
        u.1.mulVec (basisKet ξ) = φ • basisKet (shiftRegInt rT ξ d) := by
  have hbSub : b ∉ rSub.image := fun h ↦ hbTot (hSubTot h)
  have haSub : a ∉ rSub.image := fun h ↦ haTot (hSubTot h)
  let cIn := Circuit.CNOT a b hba.symm
  have hDiag1 : DiagOn (Finset.univ \ rT.image) (cIn.inverse.eval * uInner * cIn.eval).1 := by
    simp only [cIn, eval_CNOT_inverse, Submonoid.coe_mul]
    exact DiagOn.conj_CNOT a b hba.symm (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haT⟩) hDiagInner
  let u := (Circuit.TOFF b a car hba hbcar hacar).eval *
      (cIn.inverse.eval * uInner * cIn.eval) * (Circuit.TOFF b a car hba hbcar hacar).eval
  refine ⟨u, CleanUnitaryWp.dAndSandwich v b a car hba hbcar hacar rSub rTot hSubTot hcarTot hbSub
    haSub hcarSub
      (DiagOn.anti (pair3_sub_sdiff hbT haT hcarT) hDiag1)
      (CleanUnitaryWp.dPureConj cIn rSub (disj_support_CNOT a b hba.symm haSub hbSub) hwInner),
    DiagOn.conj_TOFF b a car hba hbcar hacar (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbT⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haT⟩) hDiag1,
    fun ξ {φ d} hzCar hAct ↦ ?_⟩
  let cPreAll := Circuit.TOFF b a car hba hbcar hacar ;;ᶜ cIn
  rw [show u = cPreAll.inverse.eval * uInner * cPreAll.eval by
    simp only [u, cPreAll, Circuit.inverse_seq, Circuit.eval_seq, eval_TOFF_inverse, mul_assoc]]
  apply ((PreservesReg.TOFF b a car hba hbcar hacar hbT haT hcarT).seq
    (PreservesReg.CNOT a b hba.symm haT hbT)).conj_shift
  have hGoal : ∀ ζ, ζ = Function.update (Function.update ξ b (ξ b + ξ a)) car (ξ b * ξ a) →
      uInner.1.mulVec (basisKet ζ) = φ • basisKet (shiftRegInt rT ζ d) := by
    rintro _ rfl
    exact hAct
  apply hGoal
  funext w
  by_cases hwb : w = b
  · subst hwb
    simp [Function.update_of_ne hbcar, Function.update_of_ne hacar]
  · by_cases hwcar : w = car
    · subst hwcar
      simp [hzCar, Function.update_of_ne hbcar.symm]
    · simp [Function.update_of_ne hwb, Function.update_of_ne hwcar]
noncomputable def dCsaLayer1 {Var : Type} {n : ℕ} :
    (w : ℕ) → (v : Var) → (rM0 rM1 rM2 rC1 : QRegister w n) →
    (h01 : rM0.DisjointWires rM1) → (h02 : rM0.DisjointWires rM2) → (h12 : rM1.DisjointWires rM2) →
    (h0c : rM0.DisjointWires rC1) → (h1c : rM1.DisjointWires rC1) → (h2c : rM2.DisjointWires rC1) →
    DynamicCircuit Var n → DynamicCircuit Var n
  | 0, _, _, _, _, _, _, _, _, _, _, _, dInner => dInner
  | k + 1, v, rM0, rM1, rM2, rC1, h01, h02, h12, h0c, h1c, h2c, dInner =>
      dFaWrap v (rM0 0) (rM1 0) (rM2 0) (rC1 0)
        (disj_wire_ne h01 0 0) (disj_wire_ne h02 0 0) (disj_wire_ne h12 0 0)
        (disj_wire_ne h0c 0 0) (disj_wire_ne h1c 0 0) (disj_wire_ne h2c 0 0)
        (dCsaLayer1 k v (rM0.slice 1 k (by omega)) (rM1.slice 1 k (by omega))
          (rM2.slice 1 k (by omega)) (rC1.slice 1 k (by omega))
          (disj_tail h01) (disj_tail h02) (disj_tail h12) (disj_tail h0c) (disj_tail h1c) (disj_tail
            h2c) dInner)
lemma count_dCsaLayer1_toff {Var : Type} {n : ℕ} (w : ℕ) (v : Var) (rM0 rM1 rM2 rC1 : QRegister w n)
    (h01 :
    rM0.DisjointWires rM1) (h02 : rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h0c :
      rM0.DisjointWires rC1)
    (h1c : rM1.DisjointWires rC1) (h2c : rM2.DisjointWires rC1) (dInner : DynamicCircuit Var n) :
      (dCsaLayer1 w v rM0
    rM1 rM2 rC1 h01 h02 h12 h0c h1c h2c dInner).count .TOFF = dInner.count .TOFF := by
  induction w with
  | zero => rfl
  | succ k ih => unfold dCsaLayer1; rw [count_dFaWrap_toff, ih]
lemma count_dCsaLayer1_t {Var : Type} {n : ℕ} (w : ℕ) (v : Var) (rM0 rM1 rM2 rC1 : QRegister w n)
    (h01 :
    rM0.DisjointWires rM1) (h02 : rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h0c :
      rM0.DisjointWires rC1)
    (h1c : rM1.DisjointWires rC1) (h2c : rM2.DisjointWires rC1) (dInner : DynamicCircuit Var n) :
      (dCsaLayer1 w v rM0
    rM1 rM2 rC1 h01 h02 h12 h0c h1c h2c dInner).count .T = 4 * w + dInner.count .T := by
  induction w with
  | zero => simp [dCsaLayer1]
  | succ k ih => unfold dCsaLayer1; rw [count_dFaWrap_t, ih]; omega
theorem dCsaLayer1_spec {Var : Type} [Fintype Var] [DecidableEq Var] {W mRest n : ℕ} (w : ℕ) (v :
    Var) (rT : QRegister W
    n) (rRest : QRegister mRest n) (rM0 rM1 rM2 rC1 : QRegister w n) (h01 : rM0.DisjointWires rM1)
      (h02 :
    rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h0c : rM0.DisjointWires rC1) (h1c :
      rM1.DisjointWires rC1)
    (h2c : rM2.DisjointWires rC1) (h0T : rM0.DisjointWires rT) (h1T : rM1.DisjointWires rT) (h2T :
      rM2.DisjointWires rT)
    (hcT : rC1.DisjointWires rT) (h0R : rM0.DisjointWires rRest) (h1R : rM1.DisjointWires rRest)
      (h2R :
    rM2.DisjointWires rRest) (hcR : rC1.DisjointWires rRest) {uInner : Unitary (2 ^ n)} {dInner :
      DynamicCircuit Var n}
    (hwInner : CleanUnitaryWp rRest uInner dInner) (hDiagInner : DiagOn (Finset.univ \ rT.image)
      uInner.1) (φ_ket :
    BitAssignment n → ℂ) (d_ket : BitAssignment n → ℤ) (hKetInner : ∀ η : BitAssignment n,
      (∀ j : Fin mRest, η (rRest j)
    = 0) → uInner.1.mulVec (basisKet η) = φ_ket η • basisKet (shiftRegInt rT η (d_ket η))) : ∃ u :
      Unitary (2 ^ n),
    CleanUnitaryWp (rC1.concat rRest hcR) u (dCsaLayer1 w v rM0 rM1 rM2 rC1 h01 h02 h12 h0c h1c h2c
      dInner) ∧ DiagOn
    (Finset.univ \ rT.image) u.1 ∧ ∀ ξ : BitAssignment n, (∀ i : Fin w, ξ (rC1 i) = 0) →
      (∀ j : Fin mRest, ξ (rRest j) =
    0) → ∃ η : BitAssignment n, (∀ u, u ∉ rM1.image → u ∉ rC1.image → η u = ξ u) ∧ (∀ j : Fin mRest,
      η (rRest j) = 0) ∧
    regVal rM1 η + 2 * regVal rC1 η = regVal rM0 ξ + regVal rM1 ξ + regVal rM2 ξ ∧
      u.1.mulVec (basisKet ξ) = φ_ket η •
    basisKet (shiftRegInt rT ξ (d_ket η)) := by
  induction w with
  | zero =>
      refine ⟨uInner, hwInner.mono_workspace (by
        intro x hx; rw [qreg_image_concat]; exact Finset.mem_union_right _ hx),
        hDiagInner, fun ξ _ hzR ↦ ⟨ξ, fun _ _ _ ↦ rfl, hzR, rfl, hKetInner ξ hzR⟩⟩
  | succ k ih =>
      let rM0' := rM0.slice 1 k (by omega); let rM1' := rM1.slice 1 k (by omega)
      let rM2' := rM2.slice 1 k (by omega); let rC1' := rC1.slice 1 k (by omega)
      have h0'_sub : rM0'.image ⊆ rM0.image := QRegister.image_compose_subset rM0 _
      have h1'_sub : rM1'.image ⊆ rM1.image := QRegister.image_compose_subset rM1 _
      have h2'_sub : rM2'.image ⊆ rM2.image := QRegister.image_compose_subset rM2 _
      have hc'_sub : rC1'.image ⊆ rC1.image := QRegister.image_compose_subset rC1 _
      obtain ⟨uSub, hwSub, hDiagSub, hKetSub⟩ :=
        ih rM0' rM1' rM2' rC1' ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left
        h01)
        h0'_sub)) h1'_sub)
          ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h02) h0'_sub))
            h2'_sub) ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h12)
            h1'_sub)) h2'_sub)
            ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h0c)
          h0'_sub)) hc'_sub) ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left
            h1c) h1'_sub)) hc'_sub) ((QRegExt.disjointWires_mono_right
            ((QRegExt.disjointWires_mono_left h2c)
            h2'_sub))
          hc'_sub) ((QRegExt.disjointWires_mono_left h0T) h0'_sub) ((QRegExt.disjointWires_mono_left
            h1T) h1'_sub) ((QRegExt.disjointWires_mono_left h2T) h2'_sub)
            ((QRegExt.disjointWires_mono_left hcT) hc'_sub)
          ((QRegExt.disjointWires_mono_left h0R) h0'_sub) ((QRegExt.disjointWires_mono_left h1R)
            h1'_sub) ((QRegExt.disjointWires_mono_left h2R) h2'_sub)
            ((QRegExt.disjointWires_mono_left hcR)
            hc'_sub)
      let rSubW := rC1'.concat rRest ((QRegExt.disjointWires_mono_left hcR) hc'_sub); let rTotW :=
        rC1.concat rRest hcR
      obtain ⟨u, hw, hDiag, hFa⟩ := dFaWrap_spec v rT rSubW rTotW (rM0 0) (rM1 0) (rM2 0) (rC1 0)
        (disj_wire_ne h01 0 0) (disj_wire_ne h02 0 0) (disj_wire_ne h12 0 0)
        (disj_wire_ne h0c 0 0) (disj_wire_ne h1c 0 0) (disj_wire_ne h2c 0 0)
        (by
          simp only [rSubW, rTotW, qreg_image_concat]; exact Finset.union_subset_union_left hc'_sub)
        (by
          simp only [rTotW, qreg_image_concat]
          exact Finset.mem_union_left _ ((QRegister.mem_image rC1 _).mpr ⟨0, rfl⟩))
        (by
          simp only [rSubW, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨qreg_zero_not_mem_tail rC1, hcR.apply_not_mem_right 0⟩)
        (by
          simp only [rTotW, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨h0c.apply_not_mem_right 0, h0R.apply_not_mem_right 0⟩)
        (by
          simp only [rTotW, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨h1c.apply_not_mem_right 0, h1R.apply_not_mem_right 0⟩)
        (by
          simp only [rTotW, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨h2c.apply_not_mem_right 0, h2R.apply_not_mem_right 0⟩)
        (h0T.apply_not_mem_right 0) (h1T.apply_not_mem_right 0) (h2T.apply_not_mem_right 0)
        (hcT.apply_not_mem_right 0) hwSub hDiagSub
      refine ⟨u, hw, hDiag, fun ξ hzC1 hzR ↦ ?_⟩
      let ξ₁ := Function.update (Function.update ξ (rM1 0) (ξ (rM1 0) + ξ (rM2 0) + ξ (rM0 0)))
        (rC1 0) (carryBitZMod2 (ξ (rM2 0)) (ξ (rM0 0)) (ξ (rM1 0)))
      have hξ₁_out : ∀ w, w ≠ rM1 0 → w ≠ rC1 0 → ξ₁ w = ξ w := fun w h1 h2 ↦ by
        dsimp [ξ₁]; simp [Function.update_of_ne h1, Function.update_of_ne h2]
      obtain ⟨η, hη_out, hη_R, hη_sum, hη_ket⟩ := hKetSub ξ₁
        (fun j ↦ by
          rw [hξ₁_out _ (fun h ↦ h1c.apply_not_mem_right 0 (hc'_sub ((QRegister.mem_image rC1'
            _).mpr ⟨j, h⟩)))
            (fun h ↦ qreg_zero_not_mem_tail rC1 ((QRegister.mem_image rC1' _).mpr ⟨j, h⟩)),
              qreg_slice_zero_eq]
          exact hzC1 j.succ)
        (fun j ↦ by
          rw [hξ₁_out _ (disj_wire_ne h1R 0 j).symm (disj_wire_ne hcR 0 j).symm]; exact hzR j)
      refine ⟨η, fun w hw1 hw2 ↦ (hη_out w (fun h ↦ hw1 (h1'_sub h)) (fun h ↦ hw2 (hc'_sub
        h))).trans
        (hξ₁_out w (fun h ↦ hw1 (h ▸ (QRegister.mem_image rM1 _).mpr ⟨0, rfl⟩))
          (fun h ↦ hw2 (h ▸ (QRegister.mem_image rC1 _).mpr ⟨0, rfl⟩))), hη_R, ?_, hFa ξ (hzC1 0)
            hη_ket⟩
      rw [regVal_congr rM0' (fun j ↦ hξ₁_out _
          (fun h ↦ (disj_symm h01).apply_not_mem_right 0 (h ▸ h0'_sub ((QRegister.mem_image rM0'
            _).mpr ⟨j, rfl⟩)))
          (fun h ↦ (disj_symm h0c).apply_not_mem_right 0 (h ▸ h0'_sub ((QRegister.mem_image rM0'
            _).mpr ⟨j, rfl⟩)))),
        regVal_congr rM1' (fun j ↦ hξ₁_out _ (fun h ↦ qreg_zero_not_mem_tail rM1
          ((QRegister.mem_image rM1' _).mpr ⟨j, h⟩))
          (fun h ↦ (disj_symm h1c).apply_not_mem_right 0 (h ▸ h1'_sub ((QRegister.mem_image rM1'
            _).mpr ⟨j, rfl⟩)))),
        regVal_congr rM2' (fun j ↦ hξ₁_out _ (fun h ↦ h12.apply_not_mem_right 0 (h ▸ h2'_sub
          ((QRegister.mem_image rM2' _).mpr ⟨j, rfl⟩)))
          (fun h ↦ (disj_symm h2c).apply_not_mem_right 0 (h ▸ h2'_sub ((QRegister.mem_image rM2'
            _).mpr ⟨j, rfl⟩))))] at hη_sum
      have hbit := carryBitZMod2_val_eq (ξ (rM2 0)) (ξ (rM0 0)) (ξ (rM1 0))
      rw [regVal_succ rM1 η, regVal_succ rC1 η, regVal_succ rM0 ξ, regVal_succ rM1 ξ, regVal_succ
        rM2 ξ,
        show η (rM1 0) = ξ (rM1 0) + ξ (rM2 0) + ξ (rM0 0) by
          rw [hη_out (rM1 0) (qreg_zero_not_mem_tail rM1) (fun h ↦ h1c.apply_not_mem_right 0
            (hc'_sub h))]
          dsimp [ξ₁]; simp [Function.update_of_ne (disj_wire_ne h1c 0 0)],
        show η (rC1 0) = carryBitZMod2 (ξ (rM2 0)) (ξ (rM0 0)) (ξ (rM1 0)) by
          rw [hη_out (rC1 0) (fun h ↦ (disj_symm h1c).apply_not_mem_right 0 (h1'_sub h))
            (qreg_zero_not_mem_tail rC1)]
          dsimp [ξ₁]; simp]
      change (ξ (rM1 0) + ξ (rM2 0) + ξ (rM0 0)).val + 2 * regVal rM1' η +
          2 * ((carryBitZMod2 (ξ (rM2 0)) (ξ (rM0 0)) (ξ (rM1 0))).val + 2 * regVal rC1' η) =
        ((ξ (rM0 0)).val + 2 * regVal rM0' ξ) + ((ξ (rM1 0)).val + 2 * regVal rM1' ξ) +
          ((ξ (rM2 0)).val + 2 * regVal rM2' ξ)
      omega
noncomputable def dFaChain {Var : Type} {n : ℕ} (isInv : Bool) :
    (q : ℕ) → (v : Var) → (cin : Wire n) → (rA rB rD : QRegister q n) →
    (hcinA : cin ∉ rA.image) → (hcinB : cin ∉ rB.image) → (hcinD : cin ∉ rD.image) →
    (hAB : rA.DisjointWires rB) → (hAD : rA.DisjointWires rD) → (hBD : rB.DisjointWires rD) →
    DynamicCircuit Var n → DynamicCircuit Var n
  | 0, _, cin, _, _, _, _, _, _, _, _, _, dAdder => .seq (.circuit (cApexSign isInv cin)) dAdder
  | k + 1, v, cin, rA, rB, rD, hcinA, hcinB, hcinD, hAB, hAD, hBD, dAdder =>
      dFaWrap v (rA 0) (rB 0) cin (rD 0)
        (disj_wire_ne hAB 0 0)
        (fun h ↦ hcinA (h ▸ (QRegister.mem_image rA _).mpr ⟨0, rfl⟩))
        (fun h ↦ hcinB (h ▸ (QRegister.mem_image rB _).mpr ⟨0, rfl⟩))
        (disj_wire_ne hAD 0 0) (disj_wire_ne hBD 0 0)
        (fun h ↦ hcinD (h ▸ (QRegister.mem_image rD _).mpr ⟨0, rfl⟩))
        (dFaChain isInv k v (rD 0) (rA.slice 1 k (by omega)) (rB.slice 1 k (by omega)) (rD.slice 1 k
          (by omega))
          (fun hm ↦ (disj_symm hAD).apply_not_mem_right 0 (QRegister.image_compose_subset rA _ hm))
          (fun hm ↦ (disj_symm hBD).apply_not_mem_right 0 (QRegister.image_compose_subset rB _ hm))
          (qreg_zero_not_mem_tail rD) (disj_tail hAB) (disj_tail hAD) (disj_tail hBD) dAdder)
lemma count_dFaChain_toff {Var : Type} {n : ℕ} (isInv : Bool) (q : ℕ) (v : Var) (cin : Wire n) (rA
    rB rD : QRegister q
    n) (hcinA : cin ∉ rA.image) (hcinB : cin ∉ rB.image) (hcinD : cin ∉ rD.image) (hAB :
      rA.DisjointWires rB) (hAD :
    rA.DisjointWires rD) (hBD : rB.DisjointWires rD) (dAdder : DynamicCircuit Var n) : (dFaChain
      isInv q v cin rA rB rD
    hcinA hcinB hcinD hAB hAD hBD dAdder).count .TOFF = dAdder.count .TOFF := by
  induction q generalizing cin with
  | zero => simp [dFaChain, DynamicCircuit.count]
  | succ k ih => unfold dFaChain; rw [count_dFaWrap_toff, ih]
lemma count_dFaChain_t {Var : Type} {n : ℕ} (isInv : Bool) (q : ℕ) (v : Var) (cin : Wire n) (rA rB
    rD : QRegister q n)
    (hcinA : cin ∉ rA.image) (hcinB : cin ∉ rB.image) (hcinD : cin ∉ rD.image) (hAB :
      rA.DisjointWires rB) (hAD :
    rA.DisjointWires rD) (hBD : rB.DisjointWires rD) (dAdder : DynamicCircuit Var n) : (dFaChain
      isInv q v cin rA rB rD
    hcinA hcinB hcinD hAB hAD hBD dAdder).count .T = 4 * q + 1 + dAdder.count .T := by
  induction q generalizing cin with
  | zero =>
      unfold dFaChain; rw [count_dyn_seq, show (DynamicCircuit.circuit (cApexSign isInv cin) :
        DynamicCircuit Var n).count .T = 1 from count_cApexSign_t isInv cin]
  | succ k ih => unfold dFaChain; rw [count_dFaWrap_t, ih]; omega
theorem dFaChain_spec {Var : Type} [Fintype Var] [DecidableEq Var] {W mRest n : ℕ} (isInv : Bool)
    (q : ℕ) (v : Var) (rT
    : QRegister W n) (rRest : QRegister mRest n) (cin : Wire n) (rA rB rD : QRegister q n) (hcinA :
      cin ∉ rA.image)
    (hcinB : cin ∉ rB.image) (hcinD : cin ∉ rD.image) (hAB : rA.DisjointWires rB) (hAD :
      rA.DisjointWires rD) (hBD :
    rB.DisjointWires rD) (hcinT : cin ∉ rT.image) (hAT : rA.DisjointWires rT) (hBT :
      rB.DisjointWires rT) (hDT :
    rD.DisjointWires rT) (hcinR : cin ∉ rRest.image) (hAR : rA.DisjointWires rRest) (hBR :
      rB.DisjointWires rRest) (hDR
    : rD.DisjointWires rRest) {uAdder : Unitary (2 ^ n)} {dAdder : DynamicCircuit Var n} (hwAdder :
      CleanUnitaryWp rRest
    uAdder dAdder) (hDiagAdder : DiagOn (Finset.univ \ rT.image) uAdder.1) (φ_add : BitAssignment n
      → ℂ) (d_add :
    BitAssignment n → ℤ)
    (hKetAdder : ∀ γ : BitAssignment n, (∀ j : Fin mRest, γ (rRest j) = 0) →
      uAdder.1.mulVec (basisKet γ) = φ_add γ • basisKet (shiftRegInt rT γ (d_add γ))) :
    let sgn : ℤ := if isInv then -1 else 1
    ∃ u : Unitary (2 ^ n),
      CleanUnitaryWp (rD.concat rRest hDR) u
        (dFaChain isInv q v cin rA rB rD hcinA hcinB hcinD hAB hAD hBD dAdder) ∧
      DiagOn (Finset.univ \ rT.image) u.1 ∧
      ∀ ξ : BitAssignment n,
        (∀ i : Fin q, ξ (rD i) = 0) → (∀ j : Fin mRest, ξ (rRest j) = 0) →
        ∃ (γ : BitAssignment n) (coutBit : ℕ),
          (∀ u, u ∉ rB.image → u ∉ rD.image → γ u = ξ u) ∧
          (∀ j : Fin mRest, γ (rRest j) = 0) ∧
          regVal rB γ + 2 ^ q * coutBit = (ξ cin).val + regVal rA ξ + regVal rB ξ ∧
          u.1.mulVec (basisKet ξ) =
            (DyadicQft64.dyadicTurn 3 (sgn * (coutBit : ℤ)) * φ_add γ) •
              basisKet (shiftRegInt rT ξ (d_add γ)) := by
  intro sgn; induction q generalizing cin with
  | zero =>
      refine ⟨uAdder * (cApexSign isInv cin).eval,
        (CleanUnitaryWp.seq_of_diag (CleanUnitaryWp.circuit rRest (cApexSign isInv cin)) hwAdder
          (diagOn_of_diag_ket _ _ (cApexSign_evolve isInv cin))).mono_workspace
          (by intro x hx; rw [qreg_image_concat]; exact Finset.mem_union_right _ hx),
        DiagOn.mul hDiagAdder (diagOn_of_diag_ket _ _ (cApexSign_evolve isInv cin)), fun ξ _ hzR ↦
          ⟨ξ, (ξ cin).val, fun _ _ _ ↦ rfl, hzR, by change 0 + _ = (ξ cin).val + 0 + 0; simp, by
            rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, cApexSign_evolve,
              Matrix.mulVec_smul, hKetAdder ξ hzR, smul_smul]⟩⟩
  | succ k ih =>
      let rA' := rA.slice 1 k (by omega);
        let rB' := rB.slice 1 k (by omega); let rD' := rD.slice 1 k (by omega)
      have hA'_sub : rA'.image ⊆ rA.image := QRegister.image_compose_subset rA _
      have hB'_sub : rB'.image ⊆ rB.image := QRegister.image_compose_subset rB _
      have hD'_sub : rD'.image ⊆ rD.image := QRegister.image_compose_subset rD _
      obtain ⟨uSub, hwSub, hDiagSub, hKetSub⟩ := ih (rD 0) rA' rB' rD'
        (fun hm ↦ (disj_symm hAD).apply_not_mem_right 0 (hA'_sub hm))
        (fun hm ↦ (disj_symm hBD).apply_not_mem_right 0 (hB'_sub hm))
        (qreg_zero_not_mem_tail rD) ((QRegExt.disjointWires_mono_right
          ((QRegExt.disjointWires_mono_left hAB) hA'_sub)) hB'_sub)
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hAD) hA'_sub)) hD'_sub)
          ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hBD) hB'_sub))
          hD'_sub)
        (hDT.apply_not_mem_right 0) ((QRegExt.disjointWires_mono_left hAT) hA'_sub)
          ((QRegExt.disjointWires_mono_left hBT) hB'_sub) ((QRegExt.disjointWires_mono_left hDT)
          hD'_sub)
        (hDR.apply_not_mem_right 0) ((QRegExt.disjointWires_mono_left hAR) hA'_sub)
          ((QRegExt.disjointWires_mono_left hBR) hB'_sub) ((QRegExt.disjointWires_mono_left hDR)
          hD'_sub)
      let rSubW := rD'.concat rRest ((QRegExt.disjointWires_mono_left hDR) hD'_sub); let rTotW :=
        rD.concat rRest hDR
      obtain ⟨u, hw, hDiag, hFa⟩ := dFaWrap_spec v rT rSubW rTotW (rA 0) (rB 0) cin (rD 0)
        (disj_wire_ne hAB 0 0) (fun h ↦ hcinA (h ▸ (QRegister.mem_image rA _).mpr ⟨0, rfl⟩))
        (fun h ↦ hcinB (h ▸ (QRegister.mem_image rB _).mpr ⟨0, rfl⟩))
        (disj_wire_ne hAD 0 0) (disj_wire_ne hBD 0 0)
        (fun h ↦ hcinD (h ▸ (QRegister.mem_image rD _).mpr ⟨0, rfl⟩))
        (by
          simp only [rSubW, rTotW, qreg_image_concat]; exact Finset.union_subset_union_left hD'_sub)
        (by
          simp only [rTotW, qreg_image_concat]
          exact Finset.mem_union_left _ ((QRegister.mem_image rD _).mpr ⟨0, rfl⟩))
        (by
          simp only [rSubW, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨qreg_zero_not_mem_tail rD, hDR.apply_not_mem_right 0⟩)
        (by
          simp only [rTotW, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨hAD.apply_not_mem_right 0, hAR.apply_not_mem_right 0⟩)
        (by
          simp only [rTotW, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨hBD.apply_not_mem_right 0, hBR.apply_not_mem_right 0⟩)
        (by simp only [rTotW, qreg_image_concat, Finset.mem_union, not_or]; exact ⟨hcinD, hcinR⟩)
        (hAT.apply_not_mem_right 0) (hBT.apply_not_mem_right 0) hcinT (hDT.apply_not_mem_right 0)
          hwSub hDiagSub
      refine ⟨u, hw, hDiag, fun ξ hzD hzR ↦ ?_⟩
      let ξ₁ := Function.update (Function.update ξ (rB 0) (ξ (rB 0) + ξ cin + ξ (rA 0)))
        (rD 0) (carryBitZMod2 (ξ cin) (ξ (rA 0)) (ξ (rB 0)))
      have hξ₁_out : ∀ w, w ≠ rB 0 → w ≠ rD 0 → ξ₁ w = ξ w := fun w h1 h2 ↦ by
        dsimp [ξ₁]; simp [Function.update_of_ne h1, Function.update_of_ne h2]
      obtain ⟨γ, coutBit, hγ_out, hγ_R, hγ_sum, hγ_ket⟩ := hKetSub ξ₁
        (fun j ↦ by
          rw [hξ₁_out _ (fun h ↦ hBD.apply_not_mem_right 0 (hD'_sub ((QRegister.mem_image rD' _).mpr
            ⟨j, h⟩)))
            (fun h ↦ qreg_zero_not_mem_tail rD ((QRegister.mem_image rD' _).mpr ⟨j, h⟩)),
              qreg_slice_zero_eq]
          exact hzD j.succ)
        (fun j ↦ by
          rw [hξ₁_out _ (disj_wire_ne hBR 0 j).symm (disj_wire_ne hDR 0 j).symm]; exact hzR j)
      refine ⟨γ, coutBit, fun w hwB hwD ↦ (hγ_out w (fun h ↦ hwB (hB'_sub h)) (fun h ↦ hwD (hD'_sub
        h))).trans
        (hξ₁_out w (fun h ↦ hwB (h ▸ (QRegister.mem_image rB _).mpr ⟨0, rfl⟩))
          (fun h ↦ hwD (h ▸ (QRegister.mem_image rD _).mpr ⟨0, rfl⟩))), hγ_R, ?_, hFa ξ (hzD 0)
            hγ_ket⟩
      rw [regVal_congr rA' (fun j ↦ hξ₁_out _
          (fun h ↦ (disj_symm hAB).apply_not_mem_right 0 (h ▸ hA'_sub ((QRegister.mem_image rA'
            _).mpr ⟨j, rfl⟩)))
          (fun h ↦ (disj_symm hAD).apply_not_mem_right 0 (h ▸ hA'_sub ((QRegister.mem_image rA'
            _).mpr ⟨j, rfl⟩)))),
        regVal_congr rB' (fun j ↦ hξ₁_out _ (fun h ↦ qreg_zero_not_mem_tail rB ((QRegister.mem_image
          rB' _).mpr ⟨j, h⟩))
          (fun h ↦ (disj_symm hBD).apply_not_mem_right 0 (h ▸ hB'_sub ((QRegister.mem_image rB'
            _).mpr ⟨j, rfl⟩)))),
        show ξ₁ (rD 0) = carryBitZMod2 (ξ cin) (ξ (rA 0)) (ξ (rB 0)) by dsimp [ξ₁]; simp] at hγ_sum
      have hbit := carryBitZMod2_val_eq (ξ cin) (ξ (rA 0)) (ξ (rB 0))
      rw [regVal_succ rB γ, regVal_succ rA ξ, regVal_succ rB ξ,
        show γ (rB 0) = ξ (rB 0) + ξ cin + ξ (rA 0) by
          rw [hγ_out (rB 0) (qreg_zero_not_mem_tail rB) (fun h ↦ hBD.apply_not_mem_right 0 (hD'_sub
            h))]
          dsimp [ξ₁]; simp [Function.update_of_ne (disj_wire_ne hBD 0 0)],
        pow_succ', mul_assoc 2 (2 ^ k) coutBit]
      change (ξ (rB 0) + ξ cin + ξ (rA 0)).val + 2 * regVal rB' γ + 2 * (2 ^ k * coutBit) =
        (ξ cin).val + ((ξ (rA 0)).val + 2 * regVal rA' ξ) + ((ξ (rB 0)).val + 2 * regVal rB' ξ)
      omega
abbrev csaScratchWidth (m : ℕ) : ℕ :=
  match m with
  | 0 => 2
  | q + 1 => 3 * (q + 2) - 1
abbrev csaTCount (m : ℕ) : ℕ :=
  match m with
  | 0 => 10
  | q + 1 => 12 * (q + 2) - 1
noncomputable def dCsa3AxisApex {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ) (v : Var) (rM0 rM1 rM2
    rT : QRegister (m +
    1) n) (rScr : QRegister (csaScratchWidth m) n) (h01 : rM0.DisjointWires rM1) (h02 :
      rM0.DisjointWires rM2) (h12 :
    rM1.DisjointWires rM2) (h1T : rM1.DisjointWires rT) (h0S : rM0.DisjointWires rScr) (h1S :
      rM1.DisjointWires rScr)
    (h2S : rM2.DisjointWires rScr) (hTS : rT.DisjointWires rScr) : DynamicCircuit Var n :=
  match m with
  | 0 =>
      let rC1 := rScr.slice 0 1 (by decide); let rCApex := rScr.slice 1 1 (by decide)
      dCsaLayer1 1 v rM0 rM1 rM2 rC1 h01 h02 h12
        ((QRegExt.disjointWires_mono_right h0S) (QRegister.image_compose_subset rScr _))
        ((QRegExt.disjointWires_mono_right h1S) (QRegister.image_compose_subset rScr _))
        ((QRegExt.disjointWires_mono_right h2S) (QRegister.image_compose_subset rScr _))
        (.seq (.circuit (cApexSign isInv (rC1 0)))
          (dApexTAdder isInv 0 v rM1 rT rCApex h1T
            ((QRegExt.disjointWires_mono_right h1S) (QRegister.image_compose_subset rScr _))
            ((QRegExt.disjointWires_mono_right hTS) (QRegister.image_compose_subset rScr _))))
  | q + 1 =>
      let rC1 := rScr.slice 0 (q + 2) (by dsimp [csaScratchWidth]; omega)
      let rD2 := rScr.slice (q + 2) (q + 1) (by dsimp [csaScratchWidth]; omega)
      let rCApex := rScr.slice (2 * q + 3) (q + 2) (by dsimp [csaScratchWidth]; omega)
      let hC1_sub : rC1.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      let hD2_sub : rD2.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      let hCA_sub : rCApex.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      let rA := rC1.slice 0 (q + 1) (by omega); let rB := rM1.slice 1 (q + 1) (by omega)
      let hA_sub : rA.image ⊆ rC1.image := QRegister.image_compose_subset rC1 _
      let hB_sub : rB.image ⊆ rM1.image := QRegister.image_compose_subset rM1 _
      let hBA : rB.DisjointWires rA :=
        (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left
        ((QRegExt.disjointWires_mono_right h1S) hC1_sub)) hB_sub)) hA_sub
      let hAD2 : rA.DisjointWires rD2 :=
        (QRegExt.disjointWires_mono_left (slice_disjoint_of_le rScr 0 (q + 2) (q + 2) (q +
        1) _ _ (by omega))) hA_sub
      let hBD2 : rB.DisjointWires rD2 :=
        (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h1S) hB_sub)) hD2_sub
      dCsaLayer1 (q + 2) v rM0 rM1 rM2 rC1 h01 h02 h12
        ((QRegExt.disjointWires_mono_right h0S) hC1_sub) ((QRegExt.disjointWires_mono_right h1S)
          hC1_sub) ((QRegExt.disjointWires_mono_right h2S) hC1_sub)
        (.seq (.circuit (cApexSign isInv (rC1 ⟨q + 1, by omega⟩)))
          (dHaWrap v (rB 0) (rA 0) (rD2 0) (disj_wire_ne hBA 0 0) (disj_wire_ne hBD2 0 0)
            (disj_wire_ne hAD2 0 0)
            (dFaChain isInv q v (rD2 0) (rA.slice 1 q (by omega)) (rB.slice 1 q (by omega))
              (rD2.slice 1 q (by omega))
              (fun hm ↦ (disj_symm hAD2).apply_not_mem_right 0 (QRegister.image_compose_subset rA _
                hm))
              (fun hm ↦ (disj_symm hBD2).apply_not_mem_right 0 (QRegister.image_compose_subset rB _
                hm))
              (qreg_zero_not_mem_tail rD2)
              ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hBA))
                (QRegister.image_compose_subset rA _)))
                (QRegister.image_compose_subset rB _))
              ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hAD2)
                (QRegister.image_compose_subset rA _)))
                (QRegister.image_compose_subset rD2 _))
              ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hBD2)
                (QRegister.image_compose_subset rB _)))
                (QRegister.image_compose_subset rD2 _))
              (dApexTAdder isInv (q +
                1) v rM1 rT rCApex h1T ((QRegExt.disjointWires_mono_right h1S) hCA_sub)
                ((QRegExt.disjointWires_mono_right hTS) hCA_sub)))))
@[simp] lemma count_dCsa3AxisApex_toff {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ) (v : Var) (rM0
    rM1 rM2 rT : QRegister
    (m + 1) n) (rScr : QRegister (csaScratchWidth m) n) (h01 : rM0.DisjointWires rM1) (h02 :
      rM0.DisjointWires rM2) (h12
    : rM1.DisjointWires rM2) (h1T : rM1.DisjointWires rT) (h0S : rM0.DisjointWires rScr) (h1S :
      rM1.DisjointWires rScr)
    (h2S : rM2.DisjointWires rScr) (hTS : rT.DisjointWires rScr) : (dCsa3AxisApex isInv m v rM0 rM1
      rM2 rT rScr h01 h02
    h12 h1T h0S h1S h2S hTS).count .TOFF = 0 := by
  cases m
  · unfold dCsa3AxisApex; rw [count_dCsaLayer1_toff, count_dyn_seq, count_dApexTAdder_toff]
    simp [DynamicCircuit.count]
  · unfold dCsa3AxisApex
    rw [count_dCsaLayer1_toff, count_dyn_seq, count_dHaWrap_toff, count_dFaChain_toff,
      count_dApexTAdder_toff]
    simp [DynamicCircuit.count]
@[simp] lemma count_dCsa3AxisApex_t {Var : Type} {n : ℕ} (isInv : Bool) (m : ℕ) (v : Var) (rM0 rM1
    rM2 rT : QRegister (m
    + 1) n) (rScr : QRegister (csaScratchWidth m) n) (h01 : rM0.DisjointWires rM1) (h02 :
      rM0.DisjointWires rM2) (h12 :
    rM1.DisjointWires rM2) (h1T : rM1.DisjointWires rT) (h0S : rM0.DisjointWires rScr) (h1S :
      rM1.DisjointWires rScr)
    (h2S : rM2.DisjointWires rScr) (hTS : rT.DisjointWires rScr) : (dCsa3AxisApex isInv m v rM0 rM1
      rM2 rT rScr h01 h02
    h12 h1T h0S h1S h2S hTS).count .T = csaTCount m := by
  cases m with
  | zero =>
      unfold dCsa3AxisApex csaTCount
      rw [count_dCsaLayer1_t, count_dyn_seq, count_dApexTAdder_t,
        show (DynamicCircuit.circuit (cApexSign isInv ((rScr.slice 0 1 (by decide)) 0)) :
          DynamicCircuit Var n).count .T = 1 from
          count_cApexSign_t isInv _]
  | succ q =>
      dsimp only [dCsa3AxisApex, csaTCount]
      rw [count_dCsaLayer1_t, count_dyn_seq, count_dHaWrap_t, count_dFaChain_t, count_dApexTAdder_t,
        show (DynamicCircuit.circuit (cApexSign isInv ((rScr.slice 0 (q + 2) (by
          dsimp [csaScratchWidth]; omega)) ⟨q + 1, by omega⟩)) :
          DynamicCircuit Var n).count .T = 1 from count_cApexSign_t isInv _]
      omega
theorem dCsa3AxisApex_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (isInv : Bool) (m :
    ℕ) (v : Var) (rM0
    rM1 rM2 rT : QRegister (m + 1) n) (rScr : QRegister (csaScratchWidth m) n) (h01 :
      rM0.DisjointWires rM1) (h02 :
    rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h0T : rM0.DisjointWires rT) (h1T :
      rM1.DisjointWires rT) (h2T
    : rM2.DisjointWires rT) (h0S : rM0.DisjointWires rScr) (h1S : rM1.DisjointWires rScr)
    (h2S : rM2.DisjointWires rScr) (hTS : rT.DisjointWires rScr) :
    let sgn : ℤ := if isInv then -1 else 1
    ∃ u : Unitary (2 ^ n), CleanUnitaryWp rScr u
      (dCsa3AxisApex isInv m v rM0 rM1 rM2 rT rScr h01 h02 h12 h1T h0S h1S h2S hTS) ∧
      DiagOn (Finset.univ \ rT.image) u.1 ∧
      ∀ ξ : BitAssignment n, (∀ i : Fin (csaScratchWidth m), ξ (rScr i) = 0) →
        let S : ℤ := ((regVal rM0 ξ + regVal rM1 ξ + regVal rM2 ξ : ℕ) : ℤ)
        u.1.mulVec (basisKet ξ) = apexCarryPhase rT ξ (sgn * S) • basisKet (shiftRegInt rT ξ (sgn *
          S)) := by
  intro sgn; cases m with
  | zero =>
      let rC1 := rScr.slice 0 1 (by decide); let rCApex := rScr.slice 1 1 (by decide)
      have hC1_sub : rC1.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      have hCA_sub : rCApex.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      obtain ⟨uAdd, hwAdd, hDiagAdd, hKetAdd⟩ := dApexTAdder_spec isInv 0 v rM1 rT rCApex h1T
        ((QRegExt.disjointWires_mono_right h1S) hCA_sub) ((QRegExt.disjointWires_mono_right hTS)
          hCA_sub)
      obtain ⟨u, hw, hDiag, hLayer1⟩ := dCsaLayer1_spec 1 v rT rCApex rM0 rM1 rM2 rC1
        h01 h02 h12 ((QRegExt.disjointWires_mono_right h0S) hC1_sub)
          ((QRegExt.disjointWires_mono_right h1S) hC1_sub) ((QRegExt.disjointWires_mono_right h2S)
          hC1_sub)
        h0T h1T h2T ((QRegExt.disjointWires_mono_left (disj_symm hTS)) hC1_sub)
        ((QRegExt.disjointWires_mono_right h0S) hCA_sub) ((QRegExt.disjointWires_mono_right h1S)
          hCA_sub) ((QRegExt.disjointWires_mono_right h2S) hCA_sub)
        (slice_disjoint_of_le rScr 0 1 1 1 (by decide) (by decide) (by decide))
        (CleanUnitaryWp.seq_of_diag (CleanUnitaryWp.circuit rCApex (cApexSign isInv (rC1 0))) hwAdd
          (diagOn_of_diag_ket _ _ (cApexSign_evolve isInv (rC1 0))))
        (DiagOn.mul hDiagAdd (diagOn_of_diag_ket _ _ (cApexSign_evolve isInv (rC1 0))))
        (fun η ↦ DyadicQft64.dyadicTurn 3 (sgn * ((η (rC1 0)).val : ℤ)) * apexCarryPhase rT η (sgn *
          (regVal rM1 η : ℤ)))
        (fun η ↦ sgn * (regVal rM1 η : ℤ))
        (fun η hzCA ↦ by
          change (uAdd.1 * (cApexSign isInv (rC1 0)).eval.1).mulVec (basisKet η) = _
          rw [← Matrix.mulVec_mulVec, cApexSign_evolve, Matrix.mulVec_smul, hKetAdd η hzCA,
            smul_smul])
      refine ⟨u, hw.mono_workspace (by
        rw [qreg_image_concat]; exact Finset.union_subset hC1_sub hCA_sub),
        hDiag, fun ξ hzScr ↦ ?_⟩
      obtain ⟨η, hη_out, _, hη_sum, hη_ket⟩ := hLayer1 ξ (zero_on_sub hC1_sub hzScr) (zero_on_sub
        hCA_sub hzScr)
      have hT_eq : regVal rT η = regVal rT ξ := regVal_congr rT fun j ↦
        hη_out (rT j) ((disj_symm h1T).apply_not_mem_right j) (((QRegExt.disjointWires_mono_right
          hTS)
          hC1_sub).apply_not_mem_right j)
      rw [show regVal rC1 η = (η (rC1 0)).val by rw [regVal_succ rC1 η]; simp [regVal_zero]]
        at hη_sum
      rw [hη_ket, show apexCarryPhase rT η (sgn * (regVal rM1 η : ℤ)) =
          apexCarryPhase rT ξ (sgn * (regVal rM1 η : ℤ)) by unfold apexCarryPhase; rw [hT_eq],
        apexCarryPhase_add_mul_two_pow, shiftRegInt_add_mul_two_pow,
        ← (show ((regVal rM0 ξ + regVal rM1 ξ + regVal rM2 ξ : ℕ) : ℤ) =
          (regVal rM1 η : ℤ) + (2 ^ 1 : ℤ) * ((η (rC1 0)).val : ℤ) by exact_mod_cast hη_sum.symm)]
  | succ q =>
      let rC1 := rScr.slice 0 (q + 2) (by dsimp [csaScratchWidth]; omega)
      let rD2 := rScr.slice (q + 2) (q + 1) (by dsimp [csaScratchWidth]; omega)
      let rCApex := rScr.slice (2 * q + 3) (q + 2) (by dsimp [csaScratchWidth]; omega)
      have hC1_sub : rC1.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      have hD2_sub : rD2.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      have hCA_sub : rCApex.image ⊆ rScr.image := QRegister.image_compose_subset rScr _
      have hC1D2 : rC1.DisjointWires rD2 := slice_disjoint_of_le rScr 0 (q + 2) (q + 2) (q +
        1) _ _ (by omega)
      have hC1CA : rC1.DisjointWires rCApex := slice_disjoint_of_le rScr 0 (q + 2) (2 * q + 3) (q +
        2) _ _ (by omega)
      have hD2CA : rD2.DisjointWires rCApex := slice_disjoint_of_le rScr (q + 2) (q + 1) (2 * q +
        3) (q + 2) _ _ (by omega)
      let rA := rC1.slice 0 (q + 1) (by omega); let rB := rM1.slice 1 (q + 1) (by omega)
      have hA_sub : rA.image ⊆ rC1.image := QRegister.image_compose_subset rC1 _
      have hB_sub : rB.image ⊆ rM1.image := QRegister.image_compose_subset rM1 _
      have hBA : rB.DisjointWires rA :=
        (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left
        ((QRegExt.disjointWires_mono_right h1S) hC1_sub)) hB_sub))
        hA_sub
      have hAD2 : rA.DisjointWires rD2 := (QRegExt.disjointWires_mono_left hC1D2) hA_sub
      have hBD2 : rB.DisjointWires rD2 :=
        (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left h1S) hB_sub)) hD2_sub
      let rA' := rA.slice 1 q (by omega);
        let rB' := rB.slice 1 q (by omega); let rD2' := rD2.slice 1 q (by omega)
      have hA'_sub : rA'.image ⊆ rA.image := QRegister.image_compose_subset rA _
      have hB'_sub : rB'.image ⊆ rB.image := QRegister.image_compose_subset rB _
      have hD2'_sub : rD2'.image ⊆ rD2.image := QRegister.image_compose_subset rD2 _
      obtain ⟨uAdd, hwAdd, hDiagAdd, hKetAdd⟩ := dApexTAdder_spec isInv (q + 1) v rM1 rT rCApex
        h1T ((QRegExt.disjointWires_mono_right h1S) hCA_sub) ((QRegExt.disjointWires_mono_right hTS)
          hCA_sub)
      obtain ⟨uChain, hwChain, hDiagChain, hKetChain⟩ := dFaChain_spec isInv q v rT rCApex
        (rD2 0) rA' rB' rD2' (fun hm ↦ (disj_symm hAD2).apply_not_mem_right 0 (hA'_sub hm))
        (fun hm ↦ (disj_symm hBD2).apply_not_mem_right 0 (hB'_sub hm)) (qreg_zero_not_mem_tail rD2)
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hBA))
          hA'_sub)) hB'_sub)
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hAD2) hA'_sub))
          hD2'_sub) ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hBD2)
          hB'_sub))
          hD2'_sub)
        (((QRegExt.disjointWires_mono_left (disj_symm hTS)) hD2_sub).apply_not_mem_right 0)
        ((QRegExt.disjointWires_mono_left ((QRegExt.disjointWires_mono_left (disj_symm hTS))
          hC1_sub)) (hA'_sub.trans hA_sub))
        ((QRegExt.disjointWires_mono_left h1T) (hB'_sub.trans hB_sub))
          ((QRegExt.disjointWires_mono_left ((QRegExt.disjointWires_mono_left (disj_symm hTS))
          hD2_sub))
          hD2'_sub)
        (hD2CA.apply_not_mem_right 0) ((QRegExt.disjointWires_mono_left hC1CA) (hA'_sub.trans
          hA_sub))
        ((QRegExt.disjointWires_mono_left ((QRegExt.disjointWires_mono_right h1S) hCA_sub))
          (hB'_sub.trans hB_sub)) ((QRegExt.disjointWires_mono_left hD2CA) hD2'_sub)
        hwAdd hDiagAdd (fun γ ↦ apexCarryPhase rT γ (sgn * (regVal rM1 γ : ℤ)))
        (fun γ ↦ sgn * (regVal rM1 γ : ℤ)) hKetAdd
      let rD2'CA := rD2'.concat rCApex ((QRegExt.disjointWires_mono_left hD2CA) hD2'_sub)
      let rD2CA := rD2.concat rCApex hD2CA
      obtain ⟨uHa, hwHa, hDiagHa, hKetHa⟩ := dHaWrap_spec v rT rD2'CA rD2CA (rB 0) (rA 0) (rD2 0)
        (disj_wire_ne hBA 0 0) (disj_wire_ne hBD2 0 0) (disj_wire_ne hAD2 0 0)
        (by
          simp only [rD2'CA, rD2CA, qreg_image_concat]
          exact Finset.union_subset_union_left hD2'_sub)
        (by
          simp only [rD2CA, qreg_image_concat]
          exact Finset.mem_union_left _ ((QRegister.mem_image rD2 _).mpr ⟨0, rfl⟩))
        (by
          simp only [rD2'CA, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨qreg_zero_not_mem_tail rD2, hD2CA.apply_not_mem_right 0⟩)
        (by
          simp only [rD2CA, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨hBD2.apply_not_mem_right 0,
            ((QRegExt.disjointWires_mono_left ((QRegExt.disjointWires_mono_right h1S) hCA_sub))
            hB_sub).apply_not_mem_right 0⟩)
        (by
          simp only [rD2CA, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨hAD2.apply_not_mem_right 0,
            ((QRegExt.disjointWires_mono_left hC1CA) hA_sub).apply_not_mem_right 0⟩)
        (((QRegExt.disjointWires_mono_left h1T) hB_sub).apply_not_mem_right 0)
        (((QRegExt.disjointWires_mono_left ((QRegExt.disjointWires_mono_left (disj_symm hTS))
          hC1_sub)) hA_sub).apply_not_mem_right 0)
        (((QRegExt.disjointWires_mono_left (disj_symm hTS)) hD2_sub).apply_not_mem_right 0) hwChain
          hDiagChain
      let c1Top := rC1 ⟨q + 1, by omega⟩
      have hKetMid : ∀ η : BitAssignment n, (∀ j : Fin ((q + 1) + (q + 2)), η (rD2CA j) = 0) →
          (uHa * (cApexSign isInv c1Top).eval).1.mulVec (basisKet η) =
            apexCarryPhase rT η (sgn * ((regVal rM1 η + 2 * regVal rC1 η : ℕ) : ℤ)) •
              basisKet (shiftRegInt rT η (sgn * ((regVal rM1 η + 2 * regVal rC1 η : ℕ) : ℤ))) := by
        intro η hzD2CA
        have hzD2 : ∀ i : Fin (q + 1), η (rD2 i) = 0 :=
          zero_on_sub (by rw [qreg_image_concat]; exact Finset.subset_union_left) hzD2CA
        have hzCA : ∀ i : Fin (q + 2), η (rCApex i) = 0 :=
          zero_on_sub (by rw [qreg_image_concat]; exact Finset.subset_union_right) hzD2CA
        let η₁ := Function.update (Function.update η (rB 0) (η (rB 0) + η (rA 0))) (rD2 0) (η (rB 0)
          * η (rA 0))
        have hη₁_out : ∀ w, w ≠ rB 0 → w ≠ rD2 0 → η₁ w = η w := fun w h1 h2 ↦ by
          dsimp [η₁]; simp [Function.update_of_ne h1, Function.update_of_ne h2]
        obtain ⟨γ, coutBit, hγ_out, _, hγ_sum, hγ_ket⟩ := hKetChain η₁
          (fun j ↦ by
            rw [hη₁_out _ (fun h ↦ hBD2.apply_not_mem_right 0 (hD2'_sub ((QRegister.mem_image rD2'
              _).mpr ⟨j, h⟩)))
              (fun h ↦ qreg_zero_not_mem_tail rD2 ((QRegister.mem_image rD2' _).mpr ⟨j, h⟩))]
            exact zero_on_sub hD2'_sub hzD2 j)
          (fun j ↦ by
            rw [hη₁_out _ (fun h ↦
              ((QRegExt.disjointWires_mono_left ((QRegExt.disjointWires_mono_right h1S) hCA_sub))
              hB_sub).apply_not_mem_right 0
              ((QRegister.mem_image rCApex _).mpr ⟨j, h⟩))
              (disj_wire_ne hD2CA 0 j).symm]
            exact hzCA j)
        have hT_γ : regVal rT γ = regVal rT η := regVal_congr rT fun j ↦
          (hγ_out (rT j) ((disj_symm ((QRegExt.disjointWires_mono_left h1T) (hB'_sub.trans
            hB_sub))).apply_not_mem_right j)
            (((QRegExt.disjointWires_mono_right hTS) (hD2'_sub.trans hD2_sub)).apply_not_mem_right
              j)).trans
            (hη₁_out (rT j) (disj_wire_ne ((QRegExt.disjointWires_mono_left h1T) hB_sub) 0 j).symm
              (disj_wire_ne
              ((QRegExt.disjointWires_mono_right hTS) hD2_sub) j 0))
        rw [show apexCarryPhase rT γ (sgn * (regVal rM1 γ : ℤ)) =
          apexCarryPhase rT η (sgn * (regVal rM1 γ : ℤ)) by
            unfold apexCarryPhase; rw [hT_γ]] at hγ_ket
        change (uHa.1 * (cApexSign isInv c1Top).eval.1).mulVec (basisKet η) = _
        rw [← Matrix.mulVec_mulVec, cApexSign_evolve, Matrix.mulVec_smul, hKetHa η (hzD2 0) hγ_ket,
          smul_smul, ← mul_assoc, DyadicQft64.dyadicTurn_add]
        rw [regVal_congr rA' (fun j ↦ hη₁_out _
            (fun h ↦ hBA.apply_not_mem_right 0 (h ▸ hA'_sub ((QRegister.mem_image rA' _).mpr ⟨j,
              rfl⟩)))
            (fun h ↦ (disj_symm hAD2).apply_not_mem_right 0 (h ▸ hA'_sub ((QRegister.mem_image rA'
              _).mpr ⟨j, rfl⟩)))),
          regVal_congr rB' (fun j ↦ hη₁_out _
            (fun h ↦ qreg_zero_not_mem_tail rB ((QRegister.mem_image rB' _).mpr ⟨j, h⟩))
            (fun h ↦ (disj_symm hBD2).apply_not_mem_right 0 (h ▸ hB'_sub ((QRegister.mem_image rB'
              _).mpr ⟨j, rfl⟩)))),
          show η₁ (rD2 0) = η (rB 0) * η (rA 0) by dsimp [η₁]; simp] at hγ_sum
        have hha_bit := halfAdder_val_eq (η (rB 0)) (η (rA 0))
        rw [add_comm (η (rA 0)) (η (rB 0))] at hha_bit
        have hB_sum : regVal rB γ + 2 ^ (q + 1) * coutBit = regVal rA η + regVal rB η := by
          rw [regVal_succ rB γ, regVal_succ rA η, regVal_succ rB η,
            show γ (rB 0) = η (rB 0) + η (rA 0) by
              rw [hγ_out (rB 0) (qreg_zero_not_mem_tail rB) (fun h ↦ hBD2.apply_not_mem_right 0
                (hD2'_sub h))]
              dsimp [η₁]; simp [Function.update_of_ne (disj_wire_ne hBD2 0 0)],
            pow_succ', mul_assoc 2 (2 ^ q) coutBit]
          change (η (rB 0) + η (rA 0)).val + 2 * regVal rB' γ + 2 * (2 ^ q * coutBit) =
            ((η (rA 0)).val + 2 * regVal rA' η) + ((η (rB 0)).val + 2 * regVal rB' η)
          omega
        have hFull_sum : regVal rM1 η + 2 * regVal rC1 η = regVal rM1 γ + 2 ^ (q + 2) *
          ((η c1Top).val + coutBit) := by
          have hC1_sp := regVal_split_last rC1 η;
            have hM1_η := regVal_succ rM1 η; have hM1_γ := regVal_succ rM1 γ
          have hm0_notB : rM1 0 ∉ rB.image := qreg_zero_not_mem_tail rM1
          have hm0_notD2 : rM1 0 ∉ rD2.image :=
            ((QRegExt.disjointWires_mono_right h1S) hD2_sub).apply_not_mem_right 0
          rw [(hγ_out (rM1 0) (fun h ↦ hm0_notB (hB'_sub h)) (fun h ↦ hm0_notD2 (hD2'_sub h))).trans
            (hη₁_out (rM1 0) (fun h ↦ hm0_notB (h ▸ (QRegister.mem_image rB _).mpr ⟨0, rfl⟩))
              (fun h ↦ hm0_notD2 (h ▸ (QRegister.mem_image rD2 _).mpr ⟨0, rfl⟩)))] at hM1_γ
          change regVal rC1 η = regVal rA η + 2 ^ (q + 1) * (η c1Top).val at hC1_sp
          change regVal rM1 η = (η (rM1 0)).val + 2 * regVal rB η at hM1_η
          change regVal rM1 γ = (η (rM1 0)).val + 2 * regVal rB γ at hM1_γ
          rw [pow_succ', mul_assoc 2 (2 ^ (q + 1)) ((η c1Top).val + coutBit), Nat.mul_add]; omega
        rw [show (if isInv = true then -1 else 1) * ((η c1Top).val : ℤ) +
            (if isInv = true then -1 else 1) * (coutBit : ℤ) = sgn * (((η c1Top).val +
              coutBit : ℕ) : ℤ) by
              dsimp [sgn]; ring,
          apexCarryPhase_add_mul_two_pow, shiftRegInt_add_mul_two_pow,
          ← (show ((regVal rM1 η + 2 * regVal rC1 η : ℕ) : ℤ) =
            (regVal rM1 γ : ℤ) + (2 ^ (q + 2) : ℤ) * (((η c1Top).val + coutBit : ℕ) : ℤ)
              by exact_mod_cast hFull_sum)]
      obtain ⟨u, hw, hDiag, hLayer1⟩ := dCsaLayer1_spec (q + 2) v rT rD2CA rM0 rM1 rM2 rC1 h01 h02
        h12 ((QRegExt.disjointWires_mono_right h0S)
          hC1_sub) ((QRegExt.disjointWires_mono_right h1S) hC1_sub)
            ((QRegExt.disjointWires_mono_right h2S) hC1_sub) h0T h1T h2T
            ((QRegExt.disjointWires_mono_left (disj_symm
            hTS)) hC1_sub)
          (QRegExt.disjointWires_concat_right (h₁₂ :=
            hD2CA) ((QRegExt.disjointWires_mono_right h0S) hD2_sub)
            ((QRegExt.disjointWires_mono_right h0S) hCA_sub))
          (QRegExt.disjointWires_concat_right (h₁₂ :=
            hD2CA) ((QRegExt.disjointWires_mono_right h1S) hD2_sub)
            ((QRegExt.disjointWires_mono_right h1S) hCA_sub))
          (QRegExt.disjointWires_concat_right (h₁₂ :=
            hD2CA) ((QRegExt.disjointWires_mono_right h2S) hD2_sub)
            ((QRegExt.disjointWires_mono_right h2S) hCA_sub))
          (QRegExt.disjointWires_concat_right (h₁₂ := hD2CA) hC1D2 hC1CA)
            (CleanUnitaryWp.seq_of_diag
          (CleanUnitaryWp.circuit rD2CA (cApexSign isInv c1Top)) hwHa (diagOn_of_diag_ket _ _
            (cApexSign_evolve isInv
          c1Top))) (DiagOn.mul hDiagHa (diagOn_of_diag_ket _ _ (cApexSign_evolve isInv c1Top))) _ _
            hKetMid
      refine ⟨u, hw.mono_workspace (by
        rw [qreg_image_concat, qreg_image_concat]
        exact Finset.union_subset hC1_sub (Finset.union_subset hD2_sub hCA_sub)),
        hDiag, fun ξ hzScr ↦ ?_⟩
      obtain ⟨η, hη_out, _, hη_sum, hη_ket⟩ := hLayer1 ξ (zero_on_sub hC1_sub hzScr)
        (zero_on_sub (by rw [qreg_image_concat]; exact Finset.union_subset hD2_sub hCA_sub) hzScr)
      have hT_eq : regVal rT η = regVal rT ξ := regVal_congr rT fun j ↦
        hη_out (rT j) ((disj_symm h1T).apply_not_mem_right j) (((QRegExt.disjointWires_mono_right
          hTS)
          hC1_sub).apply_not_mem_right j)
      rw [hη_ket, show ∀ d : ℤ, apexCarryPhase rT η d = apexCarryPhase rT ξ d from
        fun d ↦ by unfold apexCarryPhase; rw [hT_eq], hη_sum]
lemma qreg_ext_local {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
lemma embedUnitary_diagonal_mulVec_basisKet {k n : ℕ} (r : QRegister k n)
    (U : Unitary (2 ^ k)) (d : Fin (2 ^ k) → ℂ) (hU : U.1 = Matrix.diagonal d)
    (ξ : BitAssignment n) :
    (r.embedUnitary U).1.mulVec (basisKet ξ) = d ((basisBitsEquiv k).symm (fun i ↦ ξ (r i))) •
      basisKet ξ := by
  rw [QRegister.embedUnitary_val, hU, vepEmbedMatrix_mulVec_basisKet,
    Finset.sum_eq_single ((basisBitsEquiv k).symm (fun i ↦ ξ (r i)))]
  · rw [Matrix.diagonal_apply_eq]; congr 2; funext w
    by_cases hw : w ∈ Set.range r.wires
    · rcases hw with ⟨i, rfl⟩; rw [vepWriteReg_mem, basisBits_basisBitsEquiv_symm_eq]
    · exact vepWriteReg_not_mem ξ r _ w hw
  · intro l _ hne; rw [Matrix.diagonal_apply_ne _ hne, zero_smul]
  · intro hAbs; exact absurd (Finset.mem_univ _) hAbs
lemma dyadicTurn_eq_turnPow2 (B : ℕ) (k : ℤ) : DyadicQft64.dyadicTurn B k = turnPow2 B k := rfl
lemma dyadicTurn_scale_pow (a b : ℕ) (k : ℤ) :
    DyadicQft64.dyadicTurn (a + b) ((2 ^ a : ℤ) * k) = DyadicQft64.dyadicTurn b k :=
  turnPow2_scale_pow a b k
lemma zmod2_add_val_int (a b : ZMod 2) :
    ((a + b).val : ℤ) = (a.val : ℤ) + (b.val : ℤ) - 2 * (a.val : ℤ) * (b.val : ℤ) := by
      revert a b; decide
lemma zmod2_mul_val_int (a b : ZMod 2) : ((a * b).val : ℤ) = (a.val : ℤ) * (b.val : ℤ) := by
  revert a b; decide
lemma entry_eq_of_comm_slotBitProj {k : ℕ} {A : Operator (2 ^ k)} (q : Wire k) (hcomm : A *
    slotBitProj q 0 =
    slotBitProj q 0 * A) {i j : Fin (2 ^ k)} (hne : A i j ≠ 0) : basisBits k i q = basisBits k j
      q := by
  have hent := congrFun (congrFun hcomm i) j
  unfold slotBitProj at hent; rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hent
  by_cases hi0 : (basisBits k i q).val = 0
  · by_cases hj0 : (basisBits k j q).val = 0
    · exact ZMod.val_injective 2 (hi0.trans hj0.symm)
    · suffices 0 = A i j from False.elim (hne this.symm)
      simpa [hi0, hj0] using hent
  · by_cases hj0 : (basisBits k j q).val = 0
    · suffices A i j = 0 from False.elim (hne this)
      simpa [hi0, hj0] using hent
    · have := ZMod.val_lt (basisBits k i q); have := ZMod.val_lt (basisBits k j q)
      exact ZMod.val_injective 2 (by omega)
structure CondStageSpec {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mW n : ℕ} (rAct : QRegister mAct n) (rW : QRegister mW n)
    (S_pres : Finset (Wire n)) (H : BitAssignment n → Prop)
    (U : Unitary (2 ^ mAct)) (d : DynamicCircuit Var n) : Prop where
  exists_u : ∃ u : Unitary (2 ^ n), CleanUnitaryWp rW u d ∧ DiagOn (S_pres ∪ rW.image) u.1 ∧
    ∀ ξ : BitAssignment n, (∀ i : Fin mW, ξ (rW i) = 0) → H ξ →
      u.1.mulVec (basisKet ξ) = (rAct.embedUnitary U).1.mulVec (basisKet ξ)
lemma CondStageSpec.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ}
    {rAct : QRegister mAct n} {rW : QRegister mW n} {S_pres : Finset (Wire n)}
    {H : BitAssignment n → Prop} {U₁ U₂ : Unitary (2 ^ mAct)} {d : DynamicCircuit Var n}
    (hs : CondStageSpec rAct rW S_pres H U₁ d) (hU : U₁ = U₂) : CondStageSpec rAct rW S_pres H U₂
      d := hU ▸ hs
lemma CondStageSpec.weaken_H {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ} {rAct :
    QRegister mAct n} {rW
    : QRegister mW n} {S_pres : Finset (Wire n)} {H₁ H₂ : BitAssignment n → Prop} {U : Unitary (2 ^
      mAct)} {d :
    DynamicCircuit Var n} (hs : CondStageSpec rAct rW S_pres H₁ U d) (hImp : ∀ ξ, H₂ ξ →
      H₁ ξ) : CondStageSpec rAct rW
    S_pres H₂ U d :=
  let ⟨u, hw, hD, hK⟩ := hs.exists_u; ⟨⟨u, hw, hD, fun ξ hz h2 ↦ hK ξ hz (hImp ξ h2)⟩⟩
lemma CondStageSpec.to_realizesClean {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ}
    {rAct : QRegister mAct
    n} {rW : QRegister mW n} {S_pres : Finset (Wire n)} {U : Unitary (2 ^ mAct)} {d : DynamicCircuit
      Var n}
    (hs : CondStageSpec rAct rW S_pres (fun _ ↦ True) U d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rW U d :=
  let ⟨_, hw, _, hK⟩ := hs.exists_u; (hw.congr_cleanKet fun ξ hz ↦ hK ξ hz trivial).to_realizesClean
lemma CondStageSpec.widen_workspace {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mSub mTot n :
    ℕ} {rAct :
    QRegister mAct n} {rSub : QRegister mSub n} {rTot : QRegister mTot n} {S_sub S_tot : Finset
      (Wire n)} {H :
    BitAssignment n → Prop} {U : Unitary (2 ^ mAct)} {d : DynamicCircuit Var n} (hSubTot :
      rSub.image ⊆ rTot.image)
    (hCov : S_tot ∪ rTot.image ⊆ S_sub ∪ rSub.image) (hs : CondStageSpec rAct rSub S_sub H U d) :
      CondStageSpec rAct
    rTot S_tot H U d :=
  let ⟨u, hw, hD, hK⟩ := hs.exists_u
  ⟨⟨u, hw.mono_workspace hSubTot, DiagOn.anti hCov hD, fun ξ hzTot hH ↦ hK ξ (zero_on_sub hSubTot
    hzTot) hH⟩⟩
lemma CondStageSpec.seq {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ} {rAct :
    QRegister mAct n} {rW :
    QRegister mW n} {S_pres : Finset (Wire n)} {H : BitAssignment n → Prop} {U₁ U₂ : Unitary (2 ^
      mAct)} {d₁ d₂ :
    DynamicCircuit Var n} (hActW : rAct.DisjointWires rW) (hH : ∀ ξ₁ ξ₂, (∀ w ∈ S_pres, ξ₁ w =
      ξ₂ w) → (H ξ₁ ↔ H ξ₂))
    (hs₁ : CondStageSpec rAct rW S_pres H U₁ d₁) (hs₂ : CondStageSpec rAct rW S_pres H U₂ d₂) :
      CondStageSpec rAct rW
    S_pres H (U₂ * U₁) (.seq d₁ d₂) := by
  rcases hs₁.exists_u with ⟨u₁, hw₁, hD₁, hK₁⟩
  rcases hs₂.exists_u with ⟨u₂, hw₂, hD₂, hK₂⟩
  refine ⟨⟨u₂ * u₁, CleanUnitaryWp.seq_of_diag hw₁ hw₂ (DiagOn.anti Finset.subset_union_right hD₁),
    DiagOn.mul hD₂ hD₁, fun ξ hzW hHξ ↦ ?_⟩⟩
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hK₁ ξ hzW hHξ,
    QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  let x₀ := (basisBitsEquiv mAct).symm (fun i ↦ ξ (rAct i))
  let ξ_l : Fin (2 ^ mAct) → BitAssignment n := fun l ↦ vepWriteReg ξ rAct (basisBits mAct l)
  have hξ_inj : Function.Injective ξ_l := fun l₁ l₂ hEq ↦
    (basisBitsEquiv mAct).injective (funext fun i ↦ by
      have hi := congrFun hEq (rAct i)
      dsimp [ξ_l] at hi
      rwa [vepWriteReg_mem, vepWriteReg_mem] at hi)
  have hexp : (rAct.embedUnitary U₁).1.mulVec (basisKet ξ) =
      ∑ l : Fin (2 ^ mAct), U₁.1 l x₀ • basisKet (ξ_l l) := vepEmbedMatrix_mulVec_basisKet rAct U₁.1
        ξ
  rw [hexp, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  by_cases h0 : U₁.1 l x₀ = 0
  · simp [h0]
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    congr 1
    let idx_l := (basisBitsEquiv n).symm (ξ_l l)
    have hu1_ne : u₁.1 idx_l ((basisBitsEquiv n).symm ξ) ≠ 0 := by
      rw [show u₁.1 idx_l ((basisBitsEquiv n).symm ξ) = (u₁.1.mulVec (basisKet ξ)) idx_l by
            rw [basisKet_eq_single, Matrix.mulVec_single_one]
            rfl,
          hK₁ ξ hzW hHξ, hexp, Finset.sum_apply, Finset.sum_eq_single l
            (fun l' _ hne' ↦ by
              rw [Pi.smul_apply, basisKet_eq_single,
                Pi.single_eq_of_ne fun h ↦ hne' (hξ_inj ((basisBitsEquiv n).symm.injective h)).symm,
                smul_zero])
            (fun hAbs ↦ False.elim (hAbs (Finset.mem_univ l))),
          Pi.smul_apply, basisKet_eq_single, Pi.single_eq_same, smul_eq_mul, mul_one]
      exact h0
    refine hK₂ (ξ_l l) (fun i ↦ ?_) ((hH _ _ fun w hwS ↦ ?_).mpr hHξ)
    · dsimp [ξ_l]
      rw [vepWriteReg_not_mem]
      · exact hzW i
      · rintro ⟨j, hj⟩
        exact disj_wire_ne hActW j i hj
    · simpa [idx_l] using hD₁ idx_l ((basisBitsEquiv n).symm ξ) hu1_ne w (Finset.mem_union_left _
        hwS)
lemma CondStageSpec.dGenBoolWrap {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mSub mTot n : ℕ}
    (b₁ b₂ bOut : Bool)
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) {rAct :
      QRegister mAct n} (rSub :
    QRegister mSub n) (rTot : QRegister mTot n) {S_inner S_outer : Finset (Wire n)} {H_outer :
      BitAssignment n → Prop}
    {U : Unitary (2 ^ mAct)} {dInner : DynamicCircuit Var n} (hSubTot : rSub.image ⊆ rTot.image)
      (hAncTot : anc ∈
    rTot.image) (hc1Tot : c₁ ∉ rTot.image) (hc2Tot : c₂ ∉ rTot.image) (hancSub : anc ∉ rSub.image)
      (hancAct : anc ∉
    rAct.image) (hc1S : c₁ ∈ S_outer) (hc2S : c₂ ∈ S_outer) (hCov : S_outer ∪ rTot.image ⊆ S_inner ∪
      rSub.image) (hH_anc
    : ∀ ξ₁ ξ₂, (∀ w, w ≠ anc → ξ₁ w = ξ₂ w) → H_outer ξ₁ → H_outer ξ₂)
    (hsInner : CondStageSpec rAct rSub S_inner
      (fun η ↦ H_outer η ∧ η anc = genBoolBit b₁ b₂ bOut (η c₁) (η c₂)) U dInner) :
    CondStageSpec rAct rTot S_outer H_outer U
      (JunctionApexCSA288.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ anc h₁₂ h₁a h₂a dInner) := by
  rcases hsInner.exists_u with ⟨uInner, hwInner, hDiagInner, hKetInner⟩
  have hDiagOutInner : DiagOn (S_outer ∪ rTot.image) uInner.1 := DiagOn.anti hCov hDiagInner
  have hSub3 : ({c₁, c₂, anc} : Finset (Wire n)) ⊆ S_outer ∪ rTot.image :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hc1S,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hc2S,
        Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ hAncTot)⟩⟩
  let cStep := cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a
  refine ⟨⟨cStep.inverse.eval * uInner * cStep.eval,
    CleanUnitaryWp.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ anc h₁₂ h₁a h₂a rSub rTot
      hSubTot hAncTot hc1Tot hc2Tot hancSub (DiagOn.anti hSub3 hDiagOutInner) hwInner,
    DiagOn.conj_cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a
      (Finset.mem_union_left _ hc1S) (Finset.mem_union_left _ hc2S) hDiagOutInner,
    fun ξ hzTot hHξ ↦ ?_⟩⟩
  apply (ClassicalAncBank.cGenBoolStep (S_ctrl := {c₁, c₂}) (S_anc := {anc})
      b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a (by simp) (by simp) (Finset.mem_singleton_self
        anc)).conj_elim_embed
    rAct (Finset.disjoint_singleton_right.mpr hancAct) uInner U
    (DiagOn.anti (Finset.union_subset
      (Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hc1S,
        Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ hc2S)⟩)
      (Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ hAncTot))) hDiagOutInner) ξ
  refine hKetInner _ (fun j ↦ ?_) ⟨hH_anc ξ _ (fun w hw ↦ by rw [Function.update_of_ne hw]) hHξ, ?_⟩
  · rw [Function.update_of_ne (by
      rintro rfl; exact hancSub ((QRegister.mem_image rSub _).mpr ⟨j, rfl⟩))]
    exact zero_on_sub hSubTot hzTot j
  · rcases (QRegister.mem_image rTot anc).mp hAncTot with ⟨iAnc, hiAnc⟩
    simp [Function.update_of_ne h₁a, Function.update_of_ne h₂a, hiAnc ▸ hzTot iAnc]
lemma CondStageSpec.dPureConjCNOT {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ} (c
    t : Wire n) (hct : c ≠
    t) {rAct : QRegister mAct n} {rW : QRegister mW n} {S_pres : Finset (Wire n)} {H_outer H_inner :
      BitAssignment n →
    Prop} {U : Unitary (2 ^ mAct)} {dInner : DynamicCircuit Var n} (hcW : c ∉ rW.image) (htW : t ∉
      rW.image) (htAct : t
    ∉ rAct.image) (hcS : c ∈ S_pres) (htS : t ∈ S_pres) (hH_step : ∀ ξ, H_outer ξ →
      H_inner (Function.update ξ t (ξ t +
    ξ c))) (hsInner : CondStageSpec rAct rW S_pres H_inner U dInner) : CondStageSpec rAct rW S_pres
      H_outer U (dPureConj
    (Circuit.CNOT c t hct) dInner) := by
  rcases hsInner.exists_u with ⟨uInner, hwInner, hDiagInner, hKetInner⟩
  let uOuter := (Circuit.CNOT c t hct).inverse.eval * uInner * (Circuit.CNOT c t hct).eval
  refine ⟨⟨uOuter, CleanUnitaryWp.dPureConj (Circuit.CNOT c t hct) rW (disj_support_CNOT c t hct hcW
    htW) hwInner,
    by
      simp only [uOuter, eval_CNOT_inverse, Submonoid.coe_mul]
      exact DiagOn.conj_CNOT c t hct (Finset.mem_union_left _ hcS) hDiagInner,
    fun ξ hzW hHξ ↦ ?_⟩⟩
  apply (ClassicalAncBank.CNOT (S_ctrl := {c}) (S_anc := {t}) c t hct
      (Finset.mem_union_left _ (Finset.mem_singleton_self c)) (Finset.mem_singleton_self
        t)).conj_elim_embed
    rAct (Finset.disjoint_singleton_right.mpr htAct) uInner U
    (DiagOn.anti (Finset.union_subset (Finset.singleton_subset_iff.mpr (Finset.mem_union_left _
      hcS))
      (Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ htS))) hDiagInner) ξ
  refine hKetInner _ (fun i ↦ ?_) (hH_step ξ hHξ)
  rw [Function.update_of_ne (by rintro rfl; exact htW ((QRegister.mem_image rW _).mpr ⟨i, rfl⟩))]
  exact hzW i
def dXorAndWrap {Var : Type} {n : ℕ} (v : Var) (wCoin wb0 wb1 wAct : Wire n) (h_b0_b1 : wb0 ≠ wb1)
    (h_c_b1 : wCoin ≠
    wb1) (h_c_act : wCoin ≠ wAct) (h_b1_act : wb1 ≠ wAct) (dBody : DynamicCircuit Var n) :
      DynamicCircuit Var n :=
  dPureConj (Circuit.CNOT wb0 wb1 h_b0_b1)
    (dAndSandwich v wCoin wb1 wAct h_c_b1 h_c_act h_b1_act (dPureConj (Circuit.CNOT wb0 wb1 h_b0_b1)
      dBody))
@[simp] lemma count_dXorAndWrap_toff {Var : Type} {n : ℕ} (v : Var) (wCoin wb0 wb1 wAct : Wire n)
    (h_b0_b1 : wb0 ≠ wb1)
    (h_c_b1 : wCoin ≠ wb1) (h_c_act : wCoin ≠ wAct) (h_b1_act : wb1 ≠ wAct) (dBody : DynamicCircuit
      Var n) :
    (dXorAndWrap v wCoin wb0 wb1 wAct h_b0_b1 h_c_b1 h_c_act h_b1_act dBody).count .TOFF =
      dBody.count .TOFF := by
  unfold dXorAndWrap
  rw [count_dPureConj_toff _ (by simp [Circuit.CNOT]), count_dAndSandwich_toff,
    count_dPureConj_toff _ (by simp [Circuit.CNOT])]
@[simp] lemma count_dXorAndWrap_t {Var : Type} {n : ℕ} (v : Var) (wCoin wb0 wb1 wAct : Wire n)
    (h_b0_b1 : wb0 ≠ wb1)
    (h_c_b1 : wCoin ≠ wb1) (h_c_act : wCoin ≠ wAct) (h_b1_act : wb1 ≠ wAct) (dBody : DynamicCircuit
      Var n) :
    (dXorAndWrap v wCoin wb0 wb1 wAct h_b0_b1 h_c_b1 h_c_act h_b1_act dBody).count .T = 4 +
      dBody.count .T := by
  unfold dXorAndWrap
  rw [count_dPureConj_t _ (by simp [Circuit.CNOT]), count_dAndSandwich_t,
    count_dPureConj_t _ (by simp [Circuit.CNOT])]
lemma CondStageSpec.dXorAndWrap {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mSub mTot n : ℕ}
    (v : Var) (wCoin wb0
    wb1 wAct : Wire n) (h_b0_b1 : wb0 ≠ wb1) (h_c_b1 : wCoin ≠ wb1) (h_c_b0 : wCoin ≠ wb0)
      (h_c_act : wCoin ≠ wAct)
    (h_b1_act : wb1 ≠ wAct) (h_b0_act : wb0 ≠ wAct) {rAct : QRegister mAct n} (rSub : QRegister mSub
      n) (rTot :
    QRegister mTot n) {S_inner S_outer : Finset (Wire n)} {H_outer : BitAssignment n →
      Prop} {U : Unitary (2 ^ mAct)}
    {dBody : DynamicCircuit Var n} (hSubTot : rSub.image ⊆ rTot.image) (hActTot : wAct ∈ rTot.image)
      (hActSub : wAct ∉
    rSub.image) (hcTot : wCoin ∉ rTot.image) (hb0Tot : wb0 ∉ rTot.image) (hb1Tot : wb1 ∉ rTot.image)
      (hActNotSys : wAct
    ∉ rAct.image) (hcS : wCoin ∈ S_outer) (hb0S : wb0 ∈ S_outer) (hb1S : wb1 ∈ S_outer) (hCov :
      S_outer ∪ rTot.image ⊆
    S_inner ∪ rSub.image) (hH_act : ∀ ξ₁ ξ₂, (∀ w, w ≠ wAct → ξ₁ w = ξ₂ w) → H_outer ξ₁ →
      H_outer ξ₂)
    (hsBody : CondStageSpec rAct rSub S_inner (fun η ↦ H_outer η ∧ η wAct = η wCoin * (η wb1 +
      η wb0)) U dBody) :
    CondStageSpec rAct rTot S_outer H_outer U
      (JunctionApexCSA288.dXorAndWrap v wCoin wb0 wb1 wAct h_b0_b1 h_c_b1 h_c_act h_b1_act dBody) :=
        by
  rcases hsBody.exists_u with ⟨uBody, hwBody, hDiagBody, hKetBody⟩
  have hDiagOut : DiagOn (S_outer ∪ rTot.image) uBody.1 := DiagOn.anti hCov hDiagBody
  let cCnot := Circuit.CNOT wb0 wb1 h_b0_b1
  let cToff := Circuit.TOFF wCoin wb1 wAct h_c_b1 h_c_act h_b1_act
  have hw1 := CleanUnitaryWp.dPureConj cCnot rSub
    (disj_support_CNOT wb0 wb1 h_b0_b1 (fun h ↦ hb0Tot (hSubTot h)) (fun h ↦ hb1Tot (hSubTot h)))
      hwBody
  have hDiag1 : DiagOn (S_outer ∪ rTot.image) (cCnot.inverse.eval * uBody * cCnot.eval).1 := by
    rw [show (cCnot.inverse.eval * uBody * cCnot.eval).1 = cCnot.eval.1 * uBody.1 * cCnot.eval.1 by
      dsimp only [cCnot]; rw [eval_CNOT_inverse]; rfl]
    exact DiagOn.conj_CNOT wb0 wb1 h_b0_b1 (Finset.mem_union_left _ hb0S) hDiagOut
  have hw2 := CleanUnitaryWp.dAndSandwich v wCoin wb1 wAct h_c_b1 h_c_act h_b1_act rSub rTot hSubTot
    hActTot (fun h ↦ hcTot (hSubTot h)) (fun h ↦ hb1Tot (hSubTot h)) hActSub
    (DiagOn.anti (fun w hw ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact Finset.mem_union_left _ hcS
      · exact Finset.mem_union_left _ hb1S
      · exact Finset.mem_union_right _ hActTot) hDiag1) hw1
  have hDiag2 : DiagOn (S_outer ∪ rTot.image)
      (cToff.eval * (cCnot.inverse.eval * uBody * cCnot.eval) * cToff.eval).1 :=
    DiagOn.conj_TOFF wCoin wb1 wAct h_c_b1 h_c_act h_b1_act
      (Finset.mem_union_left _ hcS) (Finset.mem_union_left _ hb1S) hDiag1
  let u3 := cCnot.inverse.eval * (cToff.eval * (cCnot.inverse.eval * uBody * cCnot.eval) *
    cToff.eval) * cCnot.eval
  have hDiag3 : DiagOn (S_outer ∪ rTot.image) u3.1 := by
    rw [show u3.1 = cCnot.eval.1 * (cToff.eval * (cCnot.inverse.eval * uBody * cCnot.eval) *
      cToff.eval).1 * cCnot.eval.1 by
      dsimp only [u3, cCnot]; rw [eval_CNOT_inverse]; rfl]
    exact DiagOn.conj_CNOT wb0 wb1 h_b0_b1 (Finset.mem_union_left _ hb0S) hDiag2
  refine ⟨⟨u3, CleanUnitaryWp.dPureConj cCnot rTot (disj_support_CNOT wb0 wb1 h_b0_b1 hb0Tot hb1Tot)
    hw2,
    hDiag3, fun ξ hzTot hHξ ↦ ?_⟩⟩
  let cBank := cCnot ;;ᶜ (cToff ;;ᶜ cCnot)
  rw [show u3 = cBank.inverse.eval * uBody * cBank.eval by
    dsimp only [u3, cBank, cCnot, cToff]
    simp only [Circuit.inverse_seq, Circuit.eval_seq, eval_CNOT_inverse, eval_TOFF_inverse,
      mul_assoc]]
  have hBank : ClassicalAncBank ({wCoin, wb0, wb1} : Finset (Wire n)) ({wAct} : Finset (Wire n))
    cBank
      (fun γ ↦ Function.update γ wAct (γ wAct + γ wCoin * (γ wb1 + γ wb0)))
      (fun γ ↦ Function.update γ wAct (γ wAct + γ wCoin * (γ wb1 + γ wb0))) :=
    ClassicalAncBank.of_self_inv_update cBank wAct (fun γ ↦ γ wCoin * (γ wb1 + γ wb0))
      (Finset.mem_singleton_self _)
      (fun γ ↦ by
        dsimp only [cBank, cCnot, cToff]
        rw [Circuit.eval_seq, Circuit.eval_seq, Submonoid.coe_mul, Submonoid.coe_mul,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, evolve_CNOT_basisKet,
            evolve_TOFF_basisKet, evolve_CNOT_basisKet]
        congr 1; funext u; by_cases hu : u = wAct
        · subst hu; simp [Function.update_of_ne h_b1_act.symm, Function.update_of_ne h_c_b1]
        · by_cases hub1 : u = wb1
          · subst hub1; simp [Function.update_of_ne h_b1_act, Function.update_of_ne h_b0_act,
              Function.update_of_ne h_b0_b1]
          · simp [Function.update_of_ne hu, Function.update_of_ne hub1])
      (by dsimp only [cBank, cCnot, cToff]
          simp only [Circuit.inverse_seq, Circuit.eval_seq, eval_CNOT_inverse, eval_TOFF_inverse,
            mul_assoc])
      (fun γ ↦ by
        simp [Function.update_of_ne h_c_act, Function.update_of_ne h_b1_act, Function.update_of_ne
          h_b0_act])
      (fun _ _ hEq ↦ by simp [hEq wCoin (Finset.mem_union_left _ (by simp)),
        hEq wb0 (Finset.mem_union_left _ (by simp)), hEq wb1 (Finset.mem_union_left _ (by simp))])
  refine hBank.conj_elim_embed rAct (Finset.disjoint_singleton_right.mpr hActNotSys) uBody U
    (DiagOn.anti (fun w hw ↦ by
      rcases Finset.mem_union.mp hw with h123 | ha
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h123
        rcases h123 with rfl | rfl | rfl
        · exact Finset.mem_union_left _ hcS
        · exact Finset.mem_union_left _ hb0S
        · exact Finset.mem_union_left _ hb1S
      · rw [Finset.mem_singleton.mp ha]; exact Finset.mem_union_right _ hActTot) hDiagOut) ξ
    (hKetBody _ (fun j ↦ ?_) ⟨hH_act ξ _ (fun w hw ↦ by rw [Function.update_of_ne hw]) hHξ, ?_⟩)
  · rw [Function.update_of_ne (by
      rintro rfl; exact hActSub ((QRegister.mem_image rSub _).mpr ⟨j, rfl⟩))]
    exact zero_on_sub hSubTot hzTot j
  · rcases (QRegister.mem_image rTot wAct).mp hActTot with ⟨iAct, hiAct⟩
    simp [Function.update_of_ne h_c_act, Function.update_of_ne h_b1_act,
      Function.update_of_ne h_b0_act, show ξ wAct = 0 from hiAct ▸ hzTot iAct]
def dMaskRegWrap {Var : Type} {n : ℕ} :
    (W : ℕ) → (v : Var) → (wCtrl : Wire n) → (rSrc rDst : QRegister W n) →
    (hcS : ∀ i : Fin W, wCtrl ≠ rSrc i) → (hcD : ∀ i : Fin W, wCtrl ≠ rDst i) →
    (hSD : rSrc.DisjointWires rDst) → DynamicCircuit Var n → DynamicCircuit Var n
  | 0, _, _, _, _, _, _, _, dInner => dInner
  | k + 1, v, wCtrl, rSrc, rDst, hcS, hcD, hSD, dInner =>
      dGenBoolWrap false false false v wCtrl (rSrc 0) (rDst 0) (hcS 0) (hcD 0) (disj_wire_ne hSD 0
        0)
        (dMaskRegWrap k v wCtrl (rSrc.slice 1 k (by omega)) (rDst.slice 1 k (by omega))
          (fun j ↦ by rw [qreg_slice_zero_eq]; exact hcS j.succ)
          (fun j ↦ by rw [qreg_slice_zero_eq]; exact hcD j.succ) (disj_tail hSD) dInner)
@[simp] lemma count_dMaskRegWrap_toff {Var : Type} {n : ℕ} (W : ℕ) (v : Var) (wCtrl : Wire n) (rSrc
    rDst : QRegister W
    n) (hcS : ∀ i : Fin W, wCtrl ≠ rSrc i) (hcD : ∀ i : Fin W, wCtrl ≠ rDst i) (hSD :
      rSrc.DisjointWires rDst) (dInner :
    DynamicCircuit Var n) : (dMaskRegWrap W v wCtrl rSrc rDst hcS hcD hSD dInner).count .TOFF =
      dInner.count .TOFF := by
  induction W with
  | zero => rfl
  | succ k ih => unfold dMaskRegWrap; rw [count_dGenBoolWrap_toff, ih]
@[simp] lemma count_dMaskRegWrap_t {Var : Type} {n : ℕ} (W : ℕ) (v : Var) (wCtrl : Wire n) (rSrc
    rDst : QRegister W n)
    (hcS : ∀ i : Fin W, wCtrl ≠ rSrc i) (hcD : ∀ i : Fin W, wCtrl ≠ rDst i) (hSD :
      rSrc.DisjointWires rDst) (dInner :
    DynamicCircuit Var n) : (dMaskRegWrap W v wCtrl rSrc rDst hcS hcD hSD dInner).count .T = 4 * W +
      dInner.count .T :=
    by
  induction W with
  | zero => simp [dMaskRegWrap]
  | succ k ih => unfold dMaskRegWrap; rw [count_dGenBoolWrap_t, ih]; omega
lemma regVal_masked_eq {W n : ℕ} (wCtrl : Wire n) (rSrc rDst : QRegister W n) (ξ : BitAssignment n)
    (h : ∀ i : Fin W, ξ
    (rDst i) = ξ wCtrl * ξ (rSrc i)) : (regVal rDst ξ : ℤ) = ((ξ wCtrl).val : ℤ) * (regVal rSrc ξ :
      ℤ) := by
  rcases zmod2_eq_zero_or_one (ξ wCtrl) with hc0 | hc1
  · rw [show regVal rDst ξ = 0 by unfold regVal bitsVal; simp [h, hc0]]; simp [hc0]
  · rw [show regVal rDst ξ = regVal rSrc ξ from congrArg bitsVal (funext fun i ↦ by
      simpa [hc1] using h i), hc1]; simp
lemma qreg_image_succ_eq {k n : ℕ} (r : QRegister (k + 1) n) :
    r.image = insert (r 0) (r.slice 1 k (by omega)).image := by
  ext w; simp only [Finset.mem_insert, QRegister.mem_image]
  refine ⟨?_, fun h ↦ h.elim (fun hw ↦ ⟨0, hw.symm⟩) fun ⟨j, hj⟩ ↦ ⟨j.succ, (qreg_slice_zero_eq r
    j).symm.trans hj⟩⟩
  rintro ⟨i, rfl⟩; exact Fin.cases (Or.inl rfl) (fun j ↦ Or.inr ⟨j, qreg_slice_zero_eq r j⟩) i
lemma CondStageSpec.dMaskRegWrap {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mSub n : ℕ} (W :
    ℕ) (v : Var) (wCtrl
    : Wire n) (rSrc rDst : QRegister W n) (hcS : ∀ i : Fin W, wCtrl ≠ rSrc i) (hcD : ∀ i : Fin W,
      wCtrl ≠ rDst i) (hSD :
    rSrc.DisjointWires rDst) {rAct : QRegister mAct n} (rSub : QRegister mSub n) (hDstSub :
      rDst.DisjointWires rSub)
    {S_outer : Finset (Wire n)} {H_outer : BitAssignment n → Prop} {U : Unitary (2 ^ mAct)}
      {dInner : DynamicCircuit Var
    n} (hcSub : wCtrl ∉ rSub.image) (hSrcSub : rSrc.DisjointWires rSub) (hActDst :
      rAct.DisjointWires rDst) (hcS_out :
    wCtrl ∈ S_outer) (hSrc_out : rSrc.image ⊆ S_outer) (hH_dst : ∀ ξ₁ ξ₂, (∀ w, w ∉ rDst.image →
      ξ₁ w = ξ₂ w) → H_outer
    ξ₁ → H_outer ξ₂)
    (hsInner : CondStageSpec rAct rSub (S_outer ∪ rDst.image)
      (fun η ↦ H_outer η ∧ ∀ i : Fin W, η (rDst i) = η wCtrl * η (rSrc i)) U dInner) :
    CondStageSpec rAct (rDst.concat rSub hDstSub) S_outer H_outer U
      (JunctionApexCSA288.dMaskRegWrap W v wCtrl rSrc rDst hcS hcD hSD dInner) := by
  induction W generalizing S_outer H_outer with
  | zero =>
      have hEmpty : rDst.image = ∅ := by
        ext w
        simp only [QRegister.mem_image, Finset.notMem_empty, iff_false]
        rintro ⟨i, _⟩
        exact Fin.elim0 i
      exact (hsInner.weaken_H fun ξ hH ↦ ⟨hH, fun i ↦ Fin.elim0 i⟩).widen_workspace
        (by rw [qreg_image_concat, hEmpty, Finset.empty_union])
        (by rw [qreg_image_concat, hEmpty, Finset.empty_union, Finset.union_empty])
  | succ k ih =>
      let rSrc' := rSrc.slice 1 k (by omega)
      let rDst' := rDst.slice 1 k (by omega)
      have hSrc'_sub : rSrc'.image ⊆ rSrc.image := QRegister.image_compose_subset rSrc _
      have hDst'_sub : rDst'.image ⊆ rDst.image := QRegister.image_compose_subset rDst _
      have hDst'Sub : rDst'.DisjointWires rSub :=
        (QRegExt.disjointWires_mono_left hDstSub) hDst'_sub
      let S_mid := insert (rDst 0) S_outer
      let H_mid : BitAssignment n → Prop := fun η ↦ H_outer η ∧ η (rDst 0) = η wCtrl * η (rSrc 0)
      have hS_eq : S_mid ∪ rDst'.image = S_outer ∪ rDst.image := by
        ext w
        simp only [S_mid, qreg_image_succ_eq rDst, Finset.mem_union, Finset.mem_insert]
        tauto
      have hsMid := ih (S_outer := S_mid) (H_outer := H_mid) rSrc' rDst'
        (fun j ↦ by
          rw [qreg_slice_zero_eq]
          exact hcS j.succ)
        (fun j ↦ by
          rw [qreg_slice_zero_eq]
          exact hcD j.succ)
        ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hSD) hSrc'_sub))
          hDst'_sub) hDst'Sub
        ((QRegExt.disjointWires_mono_left hSrcSub) hSrc'_sub) ((QRegExt.disjointWires_mono_right
          hActDst) hDst'_sub)
        (Finset.mem_insert_of_mem hcS_out)
        (Finset.Subset.trans hSrc'_sub (Finset.Subset.trans hSrc_out (Finset.subset_insert _ _)))
        (fun ξ₁ ξ₂ hOut ⟨hH0, hd0⟩ ↦
          ⟨hH_dst ξ₁ ξ₂ (fun w hw ↦ hOut w fun h ↦ hw (hDst'_sub h)) hH0, by
            rw [← hOut (rDst 0) (qreg_zero_not_mem_tail rDst),
              ← hOut wCtrl fun hm ↦ by
                rcases (QRegister.mem_image rDst' wCtrl).mp hm with ⟨j, hj⟩
                rw [qreg_slice_zero_eq] at hj
                exact hcD j.succ hj.symm,
              ← hOut (rSrc 0) fun hm ↦ hSD.apply_not_mem_right 0 (hDst'_sub hm)]
            exact hd0⟩)
        (by
          rw [hS_eq]
          refine hsInner.weaken_H fun η h ↦ ?_
          rcases h with ⟨⟨hH0, hd0⟩, hdk⟩
          refine ⟨hH0, Fin.cases hd0 fun j ↦ ?_⟩
          have h1 := hdk j
          rwa [qreg_slice_zero_eq, qreg_slice_zero_eq] at h1)
      let rMid := rDst'.concat rSub hDst'Sub
      let rTot := rDst.concat rSub hDstSub
      exact CondStageSpec.dGenBoolWrap false false false v wCtrl (rSrc 0) (rDst 0) (hcS 0)
        (hcD 0) (disj_wire_ne hSD 0 0) rMid rTot
        (by
          simp only [rMid, rTot, qreg_image_concat]
          exact Finset.union_subset_union_left hDst'_sub)
        (by
          simp only [rTot, qreg_image_concat]
          exact Finset.mem_union_left _ ((QRegister.mem_image rDst _).mpr ⟨0, rfl⟩))
        (by
          simp only [rTot, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨fun hm ↦ by
            rcases (QRegister.mem_image rDst wCtrl).mp hm with ⟨i, hi⟩
            exact hcD i hi.symm, hcSub⟩)
        (by
          simp only [rTot, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨hSD.apply_not_mem_right 0, hSrcSub.apply_not_mem_right 0⟩)
        (by
          simp only [rMid, qreg_image_concat, Finset.mem_union, not_or]
          exact ⟨qreg_zero_not_mem_tail rDst, hDstSub.apply_not_mem_right 0⟩)
        ((disj_symm hActDst).apply_not_mem_right 0) hcS_out
        (hSrc_out ((QRegister.mem_image rSrc _).mpr ⟨0, rfl⟩))
        (by
          simp only [S_mid, rMid, rTot, qreg_image_concat, qreg_image_succ_eq rDst]
          intro w hw
          simp only [Finset.mem_union, Finset.mem_insert] at hw ⊢
          tauto)
        (fun ξ₁ ξ₂ hOut hH0 ↦ hH_dst ξ₁ ξ₂
          (fun w hw ↦ hOut w fun h ↦ hw (h ▸ (QRegister.mem_image rDst _).mpr ⟨0, rfl⟩)) hH0)
        (hsMid.weaken_H
          (H₂ := fun η ↦ H_outer η ∧ η (rDst 0) = genBoolBit false false false (η wCtrl) (η (rSrc
            0)))
          fun η ⟨hH0, hgen⟩ ↦ ⟨hH0, by simpa [genBoolBit] using hgen⟩)
lemma compose_rCoreBlock48_eq {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister
    48 n) (hCP : rCore.DisjointWires rPGTwist) : (rCore.concat rPGTwist hCP).compose (rCoreBlock48
      mPayload) = rCore :=
  qreg_ext_local fun i ↦ by
    change (rCore.concat rPGTwist hCP) ⟨0 + i.val, _⟩ = rCore i
    rw [show (⟨0 + i.val, by have := i.isLt; omega⟩ : Fin (fullSysCoreWires mPayload + 48)) =
      Fin.castAdd 48 i from Fin.ext (Nat.zero_add i.val), QRegister.concat_apply_left]
lemma rProjAxis_sub_rCore {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (w : Fin 3) : (rProjAxis rCore w).image ⊆ rCore.image := QRegister.image_compose_subset rCore _
lemma rCosetB0_sub_rCore {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (rCosetB0 hm rCore).image ⊆ rCore.image := QRegister.image_compose_subset rCore _
lemma rCosetB1_sub_rCore {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (rCosetB1 hm rCore).image ⊆ rCore.image := QRegister.image_compose_subset rCore _
lemma rElecSlotAxis_sub_rCore {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (e : Fin numElectrons) (w : Fin 3) :
    (rElecSlotAxis rCore e w).image ⊆ rCore.image := QRegister.image_compose_subset rCore _
noncomputable def uCtrlProj3DStage {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (F : Fin 2 → Unitary 256) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uCtrlProj1DCore hm 0 F * (uCtrlProj1DCore hm 1 F * uCtrlProj1DCore hm 2 F)
lemma fin256_symm_val_eq_sum (f : BitAssignment 8) : ((basisBitsEquiv 8).symm f).val = (f 0).val +
    2 * (f 1).val + 4 *
    (f 2).val + 8 * (f 3).val + 16 * (f 4).val + 32 * (f 5).val + 64 * (f 6).val + 128 *
      (f 7).val := by
  rw [symm_bitsVal_eq]
  unfold bitsVal
  rw [Fin.sum_univ_eight]
  dsimp
  ring
lemma fin8_bits_lt (f : BitAssignment 8) : (f 0).val < 2 ∧ (f 1).val < 2 ∧ (f 2).val < 2 ∧
    (f 3).val < 2 ∧ (f 4).val < 2
    ∧ (f 5).val < 2 ∧ (f 6).val < 2 ∧ (f 7).val < 2 :=
  ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _,
   ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _⟩
lemma bit8_symm_eq (f : BitAssignment 8) (r : Fin 8) : bit8 ((basisBitsEquiv 8).symm f) r =
    (f r).val := by
  have := fin8_bits_lt f
  unfold bit8
  rw [fin256_symm_val_eq_sum f]
  fin_cases r <;> dsimp <;> omega
lemma projPreM9_decomp {n : ℕ} (rAx : QRegister 8 n) (ξ : BitAssignment n) :
    let u : Fin 256 := (basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))
    (projPreM9 u : ℤ) = (regVal (rAx.slice 0 6 (by decide)) ξ : ℤ) +
      64 * ((ξ (rAx 6)).val : ℤ) - 128 * ((ξ (rAx 7)).val : ℤ) + 512 * ((ξ (rAx 7)).val : ℤ) := by
  intro u
  unfold projPreM9
  rw [show bit8 u 7 = (ξ (rAx 7)).val from bit8_symm_eq (fun i ↦ ξ (rAx i)) 7,
    show u.val = _ from fin256_symm_val_eq_sum (fun i ↦ ξ (rAx i)),
    show regVal (rAx.slice 0 6 (by decide)) ξ = (ξ (rAx 0)).val + 2 * (ξ (rAx 1)).val +
      4 * (ξ (rAx 2)).val + 8 * (ξ (rAx 3)).val + 16 * (ξ (rAx 4)).val + 32 * (ξ (rAx 5)).val by
        unfold regVal bitsVal
        rw [Fin.sum_univ_six]
        simp only [slice_apply_eq]
        dsimp
        ring]
  push_cast
  ring
lemma stageRowExp512_m1 {n : ℕ} (rAx : QRegister 8 n) (ξ : BitAssignment n) :
    let u : Fin 256 := (basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))
    stageRowExp512 1 u = 128 * ((ξ (rAx 1)).val : ℤ) * ((ξ (rAx 0)).val : ℤ) := by
  intro u
  have := fin8_bits_lt (fun i ↦ ξ (rAx i))
  have hv := fin256_symm_val_eq_sum (fun i ↦ ξ (rAx i))
  have hb1 := bit8_symm_eq (fun i ↦ ξ (rAx i)) 1
  have hmod : (u.val : ℤ) % 2 = ((ξ (rAx 0)).val : ℤ) := by dsimp [u]; rw [hv]; omega
  unfold stageRowExp512
  dsimp [u] at hb1 hmod ⊢
  rw [hb1, hmod]
lemma stageRowExp512_m2 {n : ℕ} (rAx : QRegister 8 n) (ξ : BitAssignment n) :
    let u : Fin 256 := (basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))
    stageRowExp512 2 u = 128 * (((ξ (rAx 2)).val : ℤ) * ((ξ (rAx 1)).val : ℤ)) +
      64 * (((ξ (rAx 2)).val : ℤ) * ((ξ (rAx 0)).val : ℤ)) := by
  intro u
  have := fin8_bits_lt (fun i ↦ ξ (rAx i))
  have hv := fin256_symm_val_eq_sum (fun i ↦ ξ (rAx i))
  have hb2 := bit8_symm_eq (fun i ↦ ξ (rAx i)) 2
  have hmod : (u.val : ℤ) % 4 = ((ξ (rAx 0)).val : ℤ) + 2 * ((ξ (rAx 1)).val : ℤ) := by
    dsimp [u]; rw [hv]; omega
  unfold stageRowExp512
  dsimp [u] at hb2 hmod ⊢
  rw [hb2, hmod]
  ring
lemma stageRowExp512_ge3 {n : ℕ} (m : Fin 8) (hm3 : 3 ≤ m.val) (rAx : QRegister 8 n) (ξ :
    BitAssignment n) :
    let u : Fin 256 := (basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))
    let W : ℕ := m.val - 2
    stageRowExp512 m u =
      128 * (((ξ (rAx m)).val : ℤ) * ((ξ (rAx ⟨m.val - 1, by omega⟩)).val : ℤ)) +
        64 * (((ξ (rAx m)).val : ℤ) * ((ξ (rAx ⟨m.val - 2, by omega⟩)).val : ℤ)) +
        (2 ^ (6 - W) : ℤ) * (((ξ (rAx m)).val : ℤ) *
          (regVal (rAx.slice 0 W (by have := m.isLt; omega)) ξ : ℤ)) := by
  intro u W
  have h0 := ZMod.val_lt (ξ (rAx 0)); have h1 := ZMod.val_lt (ξ (rAx 1))
  have h2 := ZMod.val_lt (ξ (rAx 2)); have h3 := ZMod.val_lt (ξ (rAx 3))
  have h4 := ZMod.val_lt (ξ (rAx 4)); have h5 := ZMod.val_lt (ξ (rAx 5))
  have h6 := ZMod.val_lt (ξ (rAx 6)); have h7 := ZMod.val_lt (ξ (rAx 7))
  have hv := fin256_symm_val_eq_sum (fun i ↦ ξ (rAx i))
  have hbm := bit8_symm_eq (fun i ↦ ξ (rAx i)) m
  unfold stageRowExp512
  dsimp [u, W] at hv hbm ⊢
  revert hm3
  fin_cases m <;> intro hm3
  · dsimp at hm3; omega
  · dsimp at hm3; omega
  · dsimp at hm3; omega
  · dsimp at hbm ⊢
    have hmod : (((basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))).val : ℤ) % 8 =
        ((ξ (rAx 0)).val : ℤ) + 2 * ((ξ (rAx 1)).val : ℤ) + 4 * ((ξ (rAx 2)).val : ℤ) := by
          dsimp; rw [hv]; omega
    have hreg : regVal (rAx.slice 0 1 (by decide)) ξ = (ξ (rAx 0)).val := by
      unfold regVal bitsVal
      rw [Fin.sum_univ_one]
      simp_rw [slice_apply_eq]
      dsimp
      ring
    dsimp at hmod hreg
    rw [hbm, hmod, hreg]; ring
  · dsimp at hbm ⊢
    have hmod : (((basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))).val : ℤ) % 16 =
        ((ξ (rAx 0)).val : ℤ) + 2 * ((ξ (rAx 1)).val : ℤ) + 4 * ((ξ (rAx 2)).val : ℤ) + 8 *
          ((ξ (rAx 3)).val : ℤ) := by dsimp; rw [hv]; omega
    have hreg : regVal (rAx.slice 0 2 (by decide)) ξ = (ξ (rAx 0)).val + 2 * (ξ (rAx 1)).val := by
      unfold regVal bitsVal
      rw [Fin.sum_univ_two]
      simp_rw [slice_apply_eq]
      dsimp
      ring
    dsimp at hmod hreg
    rw [hbm, hmod, hreg]; push_cast; ring
  · dsimp at hbm ⊢
    have hmod : (((basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))).val : ℤ) % 32 =
        ((ξ (rAx 0)).val : ℤ) + 2 * ((ξ (rAx 1)).val : ℤ) + 4 * ((ξ (rAx 2)).val : ℤ) +
          8 * ((ξ (rAx 3)).val : ℤ) + 16 * ((ξ (rAx 4)).val : ℤ) := by dsimp; rw [hv]; omega
    have hreg : regVal (rAx.slice 0 3 (by decide)) ξ =
        (ξ (rAx 0)).val + 2 * (ξ (rAx 1)).val + 4 * (ξ (rAx 2)).val := by
      unfold regVal bitsVal
      rw [Fin.sum_univ_three]
      simp_rw [slice_apply_eq]
      dsimp
      ring
    dsimp at hmod hreg
    rw [hbm, hmod, hreg]; push_cast; ring
  · dsimp at hbm ⊢
    have hmod : (((basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))).val : ℤ) % 64 =
        ((ξ (rAx 0)).val : ℤ) + 2 * ((ξ (rAx 1)).val : ℤ) + 4 * ((ξ (rAx 2)).val : ℤ) +
          8 * ((ξ (rAx 3)).val : ℤ) + 16 * ((ξ (rAx 4)).val : ℤ) + 32 * ((ξ (rAx 5)).val : ℤ) := by
            dsimp; rw [hv]; omega
    have hreg : regVal (rAx.slice 0 4 (by decide)) ξ =
        (ξ (rAx 0)).val + 2 * (ξ (rAx 1)).val + 4 * (ξ (rAx 2)).val + 8 * (ξ (rAx 3)).val := by
      unfold regVal bitsVal
      rw [Fin.sum_univ_four]
      simp_rw [slice_apply_eq]
      dsimp
      ring
    dsimp at hmod hreg
    rw [hbm, hmod, hreg]; push_cast; ring
  · dsimp at hbm ⊢
    have hmod : (((basisBitsEquiv 8).symm (fun i ↦ ξ (rAx i))).val : ℤ) % 128 =
        ((ξ (rAx 0)).val : ℤ) + 2 * ((ξ (rAx 1)).val : ℤ) + 4 * ((ξ (rAx 2)).val : ℤ) +
          8 * ((ξ (rAx 3)).val : ℤ) + 16 * ((ξ (rAx 4)).val : ℤ) + 32 * ((ξ (rAx 5)).val : ℤ) + 64 *
            ((ξ (rAx 6)).val : ℤ) := by
      dsimp; rw [hv]; omega
    have hreg : regVal (rAx.slice 0 5 (by decide)) ξ =
        (ξ (rAx 0)).val + 2 * (ξ (rAx 1)).val + 4 * (ξ (rAx 2)).val +
          8 * (ξ (rAx 3)).val + 16 * (ξ (rAx 4)).val := by
      unfold regVal bitsVal
      rw [Fin.sum_univ_five]
      simp_rw [slice_apply_eq]
      dsimp
      ring
    dsimp at hmod hreg
    rw [hbm, hmod, hreg]; push_cast; ring
lemma dyadicTurn48_shift39_int_eq_omega512 (z : ℤ) : DyadicQft64.dyadicTurn 48 ((2 ^ 39 : ℤ) * z) =
    omega512 z := by
  lift (z % 512) to ℕ using Int.emod_nonneg z (by decide) with k hk
  rw [← show DyadicQft64.dyadicTurn 48 ((2 ^ 39 : ℤ) * (z % 512)) =
      DyadicQft64.dyadicTurn 48 ((2 ^ 39 : ℤ) * z) from DyadicQft64.dyadicTurn_eq_of_emod_eq 48 (by
    rw [show (2 ^ 48 : ℤ) = (2 ^ 39 : ℤ) * 512 by decide,
      Int.mul_emod_mul_of_pos (a := (2 ^ 39 : ℤ)) (z % 512) 512 (by decide),
      Int.mul_emod_mul_of_pos (a := (2 ^ 39 : ℤ)) z 512 (by decide), Int.emod_emod]),
    ← omega512_emod z, ← hk]
  simpa using dyadicTurn48_shift39_eq_omega512 k
def cWfPairXorT {n : ℕ} (isInv : Bool) (wf p : Wire n) (hne : wf ≠ p) : Circuit n :=
  if isInv then (Circuit.T p).inverse ;;ᶜ Circuit.CNOT wf p hne ;;ᶜ Circuit.T p ;;ᶜ Circuit.CNOT wf
    p hne
  else Circuit.T p ;;ᶜ Circuit.CNOT wf p hne ;;ᶜ (Circuit.T p).inverse ;;ᶜ Circuit.CNOT wf p hne
@[simp] lemma count_cWfPairXorT_toff {n : ℕ} (isInv : Bool) (wf p : Wire n) (hne : wf ≠ p) :
    (cWfPairXorT isInv wf p hne).count .TOFF = 0 := by cases isInv <;> rfl
@[simp] lemma count_cWfPairXorT_t {n : ℕ} (isInv : Bool) (wf p : Wire n) (hne : wf ≠ p) :
    (cWfPairXorT isInv wf p hne).count .T = 2 := by cases isInv <;> rfl
lemma cWfPairXorT_evolve {n : ℕ} (isInv : Bool) (wf p : Wire n) (hne : wf ≠ p)
    (ξ : BitAssignment n) : (cWfPairXorT isInv wf p hne).eval.1.mulVec (basisKet ξ) =
    DyadicQft64.dyadicTurn 7 ((if isInv then (-1 : ℤ) else 1) * (32 * ((ξ wf).val : ℤ) *
      ((ξ p).val : ℤ) - 16 * ((ξ wf).val : ℤ))) • basisKet ξ := by
  have hRestore : Function.update (Function.update ξ p (ξ p + ξ wf)) p
      (Function.update ξ p (ξ p + ξ wf) p + Function.update ξ p (ξ p + ξ wf) wf) = ξ := funext fun u
        ↦ by
    by_cases hu : u = p
    · subst hu
      simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hu]
  have hxor := zmod2_add_val_int (ξ p) (ξ wf)
  cases isInv
  · simp only [cWfPairXorT, Bool.false_eq_true, ↓reduceIte, one_mul, Circuit.eval_seq,
      Submonoid.coe_mul, ← Matrix.mulVec_mulVec, (PhasePerm.gateT p).evolve,
      (PhasePerm.gateTDag p).evolve, evolve_CNOT_basisKet, Matrix.mulVec_smul, smul_smul, id_eq]
    rw [hRestore, DyadicQft64.dyadicTurn_add]
    simp only [Function.update_self]
    exact congrArg (fun k ↦ DyadicQft64.dyadicTurn 7 k • basisKet ξ) (by linarith)
  · simp only [cWfPairXorT, ↓reduceIte, neg_one_mul, Circuit.eval_seq,
      Submonoid.coe_mul, ← Matrix.mulVec_mulVec, (PhasePerm.gateT p).evolve,
      (PhasePerm.gateTDag p).evolve, evolve_CNOT_basisKet, Matrix.mulVec_smul, smul_smul, id_eq]
    rw [hRestore, DyadicQft64.dyadicTurn_add]
    simp only [Function.update_self]
    exact congrArg (fun k ↦ DyadicQft64.dyadicTurn 7 k • basisKet ξ) (by linarith)
def cSharedWf3CsCore {n : ℕ} (isInv : Bool) (wf p0 p1 p2 : Wire n)
    (h0 : wf ≠ p0) (h1 : wf ≠ p1) (h2 : wf ≠ p2) : Circuit n :=
  (if isInv then (Circuit.T wf).inverse ;;ᶜ (Circuit.S wf).inverse else Circuit.T wf ;;ᶜ
    Circuit.S wf) ;;ᶜ
    cWfPairXorT isInv wf p0 h0 ;;ᶜ cWfPairXorT isInv wf p1 h1 ;;ᶜ cWfPairXorT isInv wf p2 h2
@[simp] lemma count_cSharedWf3CsCore_toff {n : ℕ} (isInv : Bool) (wf p0 p1 p2 : Wire n) (h0 : wf ≠
    p0) (h1 : wf ≠ p1)
    (h2 : wf ≠ p2) : (cSharedWf3CsCore isInv wf p0 p1 p2 h0 h1 h2).count .TOFF = 0 := by
  cases isInv
  · rfl
  · rfl
@[simp] lemma count_cSharedWf3CsCore_t {n : ℕ} (isInv : Bool) (wf p0 p1 p2 : Wire n) (h0 : wf ≠ p0)
    (h1 : wf ≠ p1) (h2 :
    wf ≠ p2) : (cSharedWf3CsCore isInv wf p0 p1 p2 h0 h1 h2).count .T = 7 := by
  cases isInv
  · rfl
  · rfl
lemma cSharedWf3CsCore_evolve {n : ℕ} (isInv : Bool) (wf p0 p1 p2 : Wire n) (h0 : wf ≠ p0)
    (h1 : wf ≠ p1) (h2 : wf ≠ p2) (ξ : BitAssignment n) :
    (cSharedWf3CsCore isInv wf p0 p1 p2 h0 h1 h2).eval.1.mulVec (basisKet ξ) =
    DyadicQft64.dyadicTurn 48 ((if isInv then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 128 *
      (((ξ wf).val : ℤ) * (((ξ p0).val : ℤ) + ((ξ p1).val : ℤ) + ((ξ p2).val : ℤ)))) • basisKet ξ :=
        by
  have hPre (η : BitAssignment n) :
      (if isInv then (Circuit.T wf).inverse ;;ᶜ (Circuit.S wf).inverse
       else Circuit.T wf ;;ᶜ Circuit.S wf).eval.1.mulVec (basisKet η) =
      DyadicQft64.dyadicTurn 7 ((if isInv then (-1 : ℤ) else 1) * (48 * ((η wf).val : ℤ))) •
        basisKet η := by
    cases isInv
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Circuit.eval_seq, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec, (PhasePerm.gateT wf).evolve, (PhasePerm.gateS wf).evolve,
        Matrix.mulVec_smul, smul_smul, id_eq, DyadicQft64.dyadicTurn_add]
      exact congrArg (fun k ↦ DyadicQft64.dyadicTurn 7 k • basisKet η) (by ring)
    · simp only [↓reduceIte, neg_one_mul, Circuit.eval_seq, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec, (PhasePerm.gateTDag wf).evolve, (PhasePerm.gateSDag wf).evolve,
        Matrix.mulVec_smul, smul_smul, id_eq, DyadicQft64.dyadicTurn_add]
      exact congrArg (fun k ↦ DyadicQft64.dyadicTurn 7 k • basisKet η) (by ring)
  unfold cSharedWf3CsCore
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    hPre, cWfPairXorT_evolve, Matrix.mulVec_smul, smul_smul, DyadicQft64.dyadicTurn_add]
  refine congrArg (· • basisKet ξ) ?_
  let sgn : ℤ := if isInv then -1 else 1
  rw [show sgn * (2 ^ 39 : ℤ) * 128 * (((ξ wf).val : ℤ) *
        (((ξ p0).val : ℤ) + ((ξ p1).val : ℤ) + ((ξ p2).val : ℤ))) =
      (2 ^ 41 : ℤ) * ((sgn * (32 * ((ξ wf).val : ℤ) * ((ξ p2).val : ℤ) - 16 * ((ξ wf).val : ℤ))) +
        ((sgn * (32 * ((ξ wf).val : ℤ) * ((ξ p1).val : ℤ) - 16 * ((ξ wf).val : ℤ))) +
          ((sgn * (32 * ((ξ wf).val : ℤ) * ((ξ p0).val : ℤ) - 16 * ((ξ wf).val : ℤ))) +
            sgn * (48 * ((ξ wf).val : ℤ))))) by ring,
    dyadicTurn_scale_pow 41 7]
  exact congrArg (DyadicQft64.dyadicTurn 7) (by ring)
lemma dyadicDiagUnitary_mulVec_basisKet {k : ℕ} [NeZero (2 ^ k)] (B : ℕ) (e : BitAssignment k →
    ℤ) (γ : BitAssignment k)
    : (DyadicQft64.dyadicDiagUnitary k B e).1.mulVec (basisKet γ) = DyadicQft64.dyadicTurn B (e γ) •
      basisKet γ := by
  have h := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg k) B e γ
  rwa [embedUnitary_idReg_eq] at h
def wfBitVal {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ := if vepHighNuc hm γ then 1 else 0
def preTopExp {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool) (γ : BitAssignment
    (fullSysCoreWires mPayload)) : ℤ :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (if isInv then -1 else 1) * (2 ^ 39 : ℤ) * wfBitVal hm γ * ∑ w : Fin 3, ((γ (rCosetB0 hm rId
    w)).val : ℤ) *
    (64 * ((γ (rProjAxis rId w 6)).val : ℤ) - 128 * ((γ (rProjAxis rId w 7)).val : ℤ))
def preLowShift {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (if isInv then -1 else 1) * wfBitVal hm γ * ∑ w : Fin 3, ((γ (rCosetB0 hm rId w)).val : ℤ) *
    (regVal ((rProjAxis rId w).slice 0 6 (by decide)) γ : ℤ)
noncomputable def uPre3DCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) (preLowShift hm isInv) *
    (rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (preTopExp hm isInv))
lemma dyadicDiagUnitary_eq_uCtrlProj3DStage {mPayload : ℕ} (hm : 22 ≤ mPayload) (F : Fin 2 →
    Unitary 256) (E :
    BitAssignment (fullSysCoreWires mPayload) → ℤ) (axExp : BitAssignment (fullSysCoreWires
      mPayload) → Fin 3 → ℤ) (h0
    : ∀ γ, wfBitVal hm γ = 0 → E γ = 0) (hAx : ∀ γ, vepHighNuc hm γ = true → ∀ w : Fin 3,
      (uCtrlProj1DCore hm w
    F).1.mulVec (basisKet γ) = omega512 (axExp γ w) • basisKet γ) (h1 : ∀ γ, wfBitVal hm γ = 1 →
      DyadicQft64.dyadicTurn
    48 (E γ) = DyadicQft64.dyadicTurn 48 ((2 ^ 39 : ℤ) * (axExp γ 0 + axExp γ 1 + axExp γ 2))) :
    DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 E = uCtrlProj3DStage hm F := by
  apply Subtype.ext; apply matrix_ext_basisKet; intro γ
  rw [dyadicDiagUnitary_mulVec_basisKet]; unfold uCtrlProj3DStage
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  cases hv : vepHighNuc hm γ
  · have hIdle : ∀ w : Fin 3, (uCtrlProj1DCore hm w F).1.mulVec (basisKet γ) = basisKet γ := fun w ↦
      by
      rw [uCtrlProj1DCore_mulVec_basisKet]; simp only [hv, Bool.false_eq_true, ↓reduceIte]
    rw [hIdle 2, hIdle 1, hIdle 0, h0 γ (by unfold wfBitVal; simp [hv]),
      DyadicQft64.dyadicTurn_zero, one_smul]
  · rw [hAx γ hv 2, Matrix.mulVec_smul, Matrix.mulVec_smul, hAx γ hv 1, Matrix.mulVec_smul,
      hAx γ hv 0, smul_smul, smul_smul]
    refine congrArg (· • basisKet γ) ?_
    rw [← omega512_add, ← omega512_add, h1 γ (by unfold wfBitVal; simp [hv]),
      dyadicTurn48_shift39_int_eq_omega512]
    congr 1; ring
lemma uPre3DCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload) (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 :
    U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
      NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
    (uPre3DCat hm false) (uCtrlProj3DStage hm preDiag8) := by
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  have hProd := (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (preTopExp hm false))).mul
    (uApexShift45_intertwinesLocal (fullSysCoreWires mPayload) 6 (by decide) (preLowShift hm false)
      U_cat_48 hcol0)
  suffices hEff : DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
        (fun γ ↦ (2 ^ (45 - 6) : ℤ) * preLowShift hm false γ) *
      DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (preTopExp hm false) =
      uCtrlProj3DStage hm preDiag8 by rwa [← hEff]
  rw [dyadicDiagUnitary_mul]
  refine dyadicDiagUnitary_eq_uCtrlProj3DStage hm preDiag8 _
    (fun γ w ↦ ((γ (rCosetB0 hm rId w)).val : ℤ) * (projPreM9 ((basisBitsEquiv 8).symm (fun i ↦
      γ (rProjAxis rId w i))) : ℤ))
    (fun γ hwf ↦ by unfold preTopExp preLowShift; simp [hwf])
    (fun γ hv w ↦ by
      rw [uCtrlProj1DCore_mulVec_basisKet]; simp only [hv, ↓reduceIte]
      exact embedUnitary_diagonal_mulVec_basisKet (rProjAxis rId w) (preDiag8 _) _ rfl γ)
    (fun γ hwf ↦ ?_)
  rw [← DyadicQft64.dyadicTurn_add_period 48 _ (((γ (rCosetB0 hm rId 0)).val : ℤ) * ((γ (rProjAxis
    rId 0 7)).val : ℤ) +
      ((γ (rCosetB0 hm rId 1)).val : ℤ) * ((γ (rProjAxis rId 1 7)).val : ℤ) + ((γ (rCosetB0 hm rId
        2)).val : ℤ) * ((γ
      (rProjAxis rId 2 7)).val : ℤ))]
  congr 1; unfold preTopExp preLowShift
  simp only [Bool.false_eq_true, ↓reduceIte, hwf, Fin.sum_univ_three]
  rw [projPreM9_decomp (rProjAxis rId 0) γ, projPreM9_decomp (rProjAxis rId 1) γ, projPreM9_decomp
    (rProjAxis rId 2) γ]
  ring
def stgTopExp {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let sgn : ℤ := if isInv then -1 else 1
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  if m.val = 0 then 0
  else if m.val = 1 then
    sgn * (2 ^ 39 : ℤ) * 128 * wfBitVal hm γ *
      ∑ w : Fin 3, ((γ (rProjAxis rId w 1)).val : ℤ) * ((γ (rProjAxis rId w 0)).val : ℤ)
  else
    sgn * (2 ^ 39 : ℤ) * wfBitVal hm γ * ∑ w : Fin 3, ((γ (rProjAxis rId w m)).val : ℤ) *
      (128 * ((γ (rProjAxis rId w ⟨m.val - 1, by omega⟩)).val : ℤ) +
        64 * ((γ (rProjAxis rId w ⟨m.val - 2, by omega⟩)).val : ℤ))
def stgLowShift {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) (hm3 : 3 ≤ m.val) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (if isInv then (-1 : ℤ) else 1) * wfBitVal hm γ * ∑ w : Fin 3, ((γ (rProjAxis rId w m)).val : ℤ) *
    (regVal ((rProjAxis rId w).slice 0 (m.val - 2) (by have := m.isLt; omega)) γ : ℤ)
noncomputable def uStg3DCat {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) (isInv : Bool) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  if hm3 : 3 ≤ m.val then
    uApexShift45 (fullSysCoreWires mPayload) (m.val - 2) (by have := m.isLt; omega) (stgLowShift hm
      m hm3 isInv) *
      (rCoreBlock48 mPayload).embedUnitary
        (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (stgTopExp hm m isInv))
  else
    (rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (stgTopExp hm m isInv))
lemma uStg3DCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) (hm1 : 1 ≤ m.val)
    (U_cat_48 : Unitary
    (2 ^ 48)) (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48 (uStg3DCat hm m false)
      (uCtrlProj3DStage hm (fun _ ↦ stageDiag8 m)) := by
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  have hAx : ∀ γ, vepHighNuc hm γ = true → ∀ w : Fin 3,
      (uCtrlProj1DCore hm w (fun _ ↦ stageDiag8 m)).1.mulVec (basisKet γ) =
        omega512 (stageRowExp512 m ((basisBitsEquiv 8).symm (fun i ↦ γ (rProjAxis rId w i)))) •
          basisKet γ :=
    fun γ hv w ↦ by
      rw [uCtrlProj1DCore_mulVec_basisKet]; simp only [hv, ↓reduceIte]
      exact embedUnitary_diagonal_mulVec_basisKet (rProjAxis rId w) (stageDiag8 m) _ rfl γ
  unfold uStg3DCat; by_cases hm3 : 3 ≤ m.val
  · simp only [hm3, ↓reduceDIte]
    have hProd := (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (stgTopExp hm m false))).mul
      (uApexShift45_intertwinesLocal (fullSysCoreWires mPayload) (m.val - 2) (by
        have := m.isLt; omega)
        (stgLowShift hm m hm3 false) U_cat_48 hcol0)
    suffices hEff : DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
          (fun γ ↦ (2 ^ (45 - (m.val - 2)) : ℤ) * stgLowShift hm m hm3 false γ) *
        DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (stgTopExp hm m false) =
        uCtrlProj3DStage hm (fun _ ↦ stageDiag8 m) by rwa [← hEff]
    rw [dyadicDiagUnitary_mul]
    refine dyadicDiagUnitary_eq_uCtrlProj3DStage hm _ _ _
      (fun γ hwf ↦ by unfold stgTopExp stgLowShift; dsimp only; split_ifs <;> simp [hwf]) hAx (fun γ
        hwf ↦ ?_)
    congr 1; unfold stgTopExp stgLowShift; dsimp only
    simp only [show m.val ≠ 0 by
      omega, show m.val ≠ 1 by omega, ↓reduceIte, Bool.false_eq_true, hwf,
      show (2 ^ (45 - (m.val - 2)) : ℤ) = (2 ^ 39 : ℤ) * (2 ^ (6 - (m.val - 2)) : ℤ) by
        rw [show 45 - (m.val - 2) = 39 + (6 - (m.val - 2)) by have := m.isLt; omega, pow_add],
      Fin.sum_univ_three]
    rw [stageRowExp512_ge3 m hm3 (rProjAxis rId 0) γ, stageRowExp512_ge3 m hm3 (rProjAxis rId 1) γ,
      stageRowExp512_ge3 m hm3 (rProjAxis rId 2) γ]; ring
  · simp only [hm3, ↓reduceDIte]
    suffices hEff : DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (stgTopExp hm m
      false) =
        uCtrlProj3DStage hm (fun _ ↦ stageDiag8 m) by
      rw [hEff]; exact NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48 _
    refine dyadicDiagUnitary_eq_uCtrlProj3DStage hm _ _ _
      (fun γ hwf ↦ by unfold stgTopExp; dsimp only; split_ifs <;> simp [hwf]) hAx (fun γ hwf ↦ ?_)
    congr 1
    rcases (by have := m.isLt; omega : m.val = 1 ∨ m.val = 2) with h | h
    · obtain rfl : m = 1 := Fin.ext h
      unfold stgTopExp; dsimp only
      simp only [Fin.val_one, one_ne_zero, ↓reduceIte, Bool.false_eq_true, hwf, Fin.sum_univ_three]
      rw [stageRowExp512_m1 (rProjAxis rId 0) γ, stageRowExp512_m1 (rProjAxis rId 1) γ,
        stageRowExp512_m1 (rProjAxis rId 2) γ]; ring
    · obtain rfl : m = 2 := Fin.ext h
      unfold stgTopExp; dsimp only
      simp only [show (2 : Fin 8).val ≠ 0 by decide, show (2 : Fin 8).val ≠ 1 by decide,
        ↓reduceIte, Bool.false_eq_true, hwf, Fin.sum_univ_three]
      have hs0 := stageRowExp512_m2 (rProjAxis rId 0) γ
      have hs1 := stageRowExp512_m2 (rProjAxis rId 1) γ
      have hs2 := stageRowExp512_m2 (rProjAxis rId 2) γ
      dsimp [rId] at hs0 hs1 hs2 ⊢; rw [hs0, hs1, hs2]; ring
lemma diagOn_embedMatrix_outside {k n : ℕ} (r : QRegister k n) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^
    k)) ℂ) {S : Finset
    (Wire n)} (hDisj : Disjoint r.image S) : DiagOn S (r.embedMatrix A) :=
  DiagOn.of_mulVec_basisKet fun ξ i hne u huS ↦ by
    rw [vepEmbedMatrix_mulVec_basisKet, Finset.sum_apply] at hne
    obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [show i = (basisBitsEquiv n).symm (vepWriteReg ξ r (basisBits k l)) by
      by_contra hne_i; apply hl
      rw [basisKet_eq_single, Pi.smul_apply, Pi.single_eq_of_ne hne_i, smul_zero],
      basisBits_basisBitsEquiv_symm_eq]
    exact vepWriteReg_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ Finset.disjoint_left.mp hDisj
      ((QRegister.mem_image r _).mpr ⟨j, hj⟩) huS
lemma reg_not_mem_slice {M s l n : ℕ} (r : QRegister M n) (hsl : s + l ≤ M) (a : Fin M)
    (ha : a.val < s ∨ s + l ≤ a.val) : r a ∉ (r.slice s l hsl).image := fun hm ↦ by
  rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
  rw [slice_apply_eq] at hj
  have hv := congrArg Fin.val (r.wires.injective hj); dsimp at hv; have := j.isLt; omega
lemma reg_mem_slice {M s l n : ℕ} (r : QRegister M n) (hsl : s + l ≤ M) (a : Fin M)
    (ha1 : s ≤ a.val) (ha2 : a.val < s + l) : r a ∈ (r.slice s l hsl).image :=
  (QRegister.mem_image _ _).mpr ⟨⟨a.val - s, by omega⟩, by
    rw [slice_apply_eq]; exact congrArg r (Fin.ext (by dsimp; omega))⟩
lemma slice_sub_slice {M s₁ l₁ s₂ l₂ n : ℕ} (r : QRegister M n) (h₁ : s₁ + l₁ ≤ M)
    (h₂ : s₂ + l₂ ≤ M) (hlo : s₂ ≤ s₁) (hhi : s₁ + l₁ ≤ s₂ + l₂) :
    (r.slice s₁ l₁ h₁).image ⊆ (r.slice s₂ l₂ h₂).image := fun u hu ↦ by
  rcases (QRegister.mem_image _ u).mp hu with ⟨i, rfl⟩
  rw [slice_apply_eq]; have := i.isLt
  exact reg_mem_slice r h₂ ⟨s₁ + i.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)
lemma slice_concat_image_eq {M s l₁ l₂ n : ℕ} (r : QRegister M n) (h₁ : s + l₁ ≤ M) (h₂ : (s + l₁) +
    l₂ ≤ M) (h₁₂ : s +
    (l₁ + l₂) ≤ M) (hd : (r.slice s l₁ h₁).DisjointWires (r.slice (s + l₁) l₂ h₂)) : ((r.slice s l₁
      h₁).concat (r.slice
    (s + l₁) l₂ h₂) hd).image = (r.slice s (l₁ + l₂) h₁₂).image := by
  rw [qreg_image_concat]
  refine Finset.Subset.antisymm
    (Finset.union_subset (slice_sub_slice r h₁ h₁₂ (by omega) (by omega))
      (slice_sub_slice r h₂ h₁₂ (by omega) (by omega))) fun u hu ↦ ?_
  rcases (QRegister.mem_image _ u).mp hu with ⟨k, rfl⟩
  rw [slice_apply_eq]
  have := k.isLt
  by_cases hk : k.val < l₁
  · exact Finset.mem_union_left _ (reg_mem_slice r h₁ ⟨s + k.val, by omega⟩ (by dsimp; omega) (by
      dsimp; omega))
  · exact Finset.mem_union_right _ (reg_mem_slice r h₂ ⟨s + k.val, by omega⟩ (by dsimp; omega) (by
      dsimp; omega))
lemma CondStageSpec.anti_S {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ} {rAct :
    QRegister mAct n} {rW :
    QRegister mW n} {S₁ S₂ : Finset (Wire n)} {H : BitAssignment n → Prop} {U : Unitary (2 ^ mAct)}
      {d : DynamicCircuit
    Var n} (hSub : S₁ ⊆ S₂) (hs : CondStageSpec rAct rW S₂ H U d) : CondStageSpec rAct rW S₁ H U
      d :=
    hs.widen_workspace Finset.Subset.rfl (Finset.union_subset_union_left hSub)
lemma CondStageSpec.of_diag_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {mPayload mW n : ℕ}
    (rCore : QRegister
    (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (hCP : rCore.DisjointWires rPGTwist)
      (rW : QRegister mW
    n) (S_pres : Finset (Wire n)) (H : BitAssignment n → Prop) (c : Circuit n) (e_n : BitAssignment
      n → ℤ) (e_core :
    BitAssignment (fullSysCoreWires mPayload) → ℤ) (hEv : ∀ ξ : BitAssignment n, c.eval.1.mulVec
      (basisKet ξ) =
    DyadicQft64.dyadicTurn 48 (e_n ξ) • basisKet ξ)
    (hEq : ∀ ξ : BitAssignment n, (∀ i : Fin mW, ξ (rW i) = 0) → H ξ → e_n ξ = e_core (fun i ↦
      ξ (rCore i))) :
    CondStageSpec (rCore.concat rPGTwist hCP) rW S_pres H
      ((rCoreBlock48 mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires
        mPayload) 48 e_core))
      (.circuit c : DynamicCircuit Var n) := by
  refine ⟨⟨c.eval, CleanUnitaryWp.circuit rW c, diagOn_of_diag_ket _ _ hEv, fun ξ hz hH ↦ ?_⟩⟩
  rw [hEv ξ, hEq ξ hz hH, ← QRegister.embedUnitary_compose, compose_rCoreBlock48_eq rCore rPGTwist
    hCP,
    embedUnitary_dyadicDiagUnitary_mulVec_basisKet]
lemma uApexShift45_congr {kSys W₁ W₂ : ℕ} (hW₁ : W₁ ≤ 45) (hW₂ : W₂ ≤ 45) (hEq : W₁ = W₂) {δ₁ δ₂ :
    BitAssignment kSys →
    ℤ} (hδ : ∀ γ, δ₁ γ = δ₂ γ) : uApexShift45 kSys W₁ hW₁ δ₁ = uApexShift45 kSys W₂ hW₂ δ₂ := by
  subst hEq; rw [funext hδ]
lemma regVal_slice_congr {M s l₁ l₂ n : ℕ} (r : QRegister M n)
    (h₁ : s + l₁ ≤ M) (h₂ : s + l₂ ≤ M) (hEq : l₁ = l₂) (ξ : BitAssignment n) :
    regVal (r.slice s l₁ h₁) ξ = regVal (r.slice s l₂ h₂) ξ := by subst hEq; rfl
lemma CondStageSpec.of_dCsa3AxisApex_pad {Var : Type} [Fintype Var] [DecidableEq Var] {mPayload mPad
    n : ℕ} (isInv :
    Bool) (q : ℕ) (hq : q + 1 ≤ 45) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
      (rPGTwist : QRegister
    48 n) (hCP : rCore.DisjointWires rPGTwist) (rM0 rM1 rM2 : QRegister (q + 1) n) (rScr : QRegister
      (csaScratchWidth q)
    n) (rPad : QRegister mPad n) (S_pres : Finset (Wire n)) (H : BitAssignment n →
      Prop) (δ : BitAssignment
    (fullSysCoreWires mPayload) → ℤ) (h01 : rM0.DisjointWires rM1) (h02 : rM0.DisjointWires rM2)
      (h12 :
    rM1.DisjointWires rM2) (h0T : rM0.DisjointWires (rPGTwist.slice (45 - (q + 1)) (q +
      1) (by omega))) (h1T :
    rM1.DisjointWires (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega))) (h2T : rM2.DisjointWires
      (rPGTwist.slice (45 -
    (q + 1)) (q + 1) (by omega))) (h0S : rM0.DisjointWires rScr) (h1S : rM1.DisjointWires rScr)
      (h2S : rM2.DisjointWires
    rScr) (hTS : (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega)).DisjointWires rScr) (hScrPad :
      rScr.image ⊆
    rPad.image)
    (hTPad : (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega)).DisjointWires rPad) (hDisjS :
    Disjoint S_pres (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega)).image) (hEq : ∀ ξ :
    BitAssignment n, (∀ i : Fin mPad, ξ (rPad i) = 0) → H ξ → (if isInv then (-1 : ℤ) else 1)
    * ((regVal rM0 ξ + regVal rM1 ξ + regVal rM2 ξ : ℕ) : ℤ) = δ (fun i ↦ ξ (rCore i))) :
    CondStageSpec (rCore.concat rPGTwist hCP) rPad S_pres H
      (uApexShift45 (fullSysCoreWires mPayload) (q + 1) hq δ)
      (dCsa3AxisApex isInv q v rM0 rM1 rM2 (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega)) rScr
        h01 h02 h12 h1T h0S h1S h2S hTS) := by
  let rT := rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega)
  obtain ⟨u, hw, hDiag, hKet⟩ := dCsa3AxisApex_spec isInv q v rM0 rM1 rM2 rT rScr h01 h02 h12 h0T
    h1T h2T h0S h1S h2S hTS
  refine ⟨⟨u, hw.mono_workspace hScrPad, DiagOn.anti (fun w hw' ↦ Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ w, by
    rcases Finset.mem_union.mp hw' with hwS | hwPad
    · exact Finset.disjoint_left.mp hDisjS hwS
    · exact Finset.disjoint_right.mp (QRegExt.disjointWires_to_finset hTPad) hwPad⟩) hDiag,
        fun ξ hzPad hH ↦ ?_⟩⟩
  rw [hKet ξ (zero_on_sub hScrPad hzPad), embed_uApexShift45_mulVec_basisKet hq rCore rPGTwist hCP δ
    ξ, hEq ξ hzPad hH]
lemma CondStageSpec.of_dCsa3AxisApex {Var : Type} [Fintype Var] [DecidableEq Var] {mPayload n : ℕ}
    (isInv : Bool) (q :
    ℕ) (hq : q + 1 ≤ 45) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist :
      QRegister 48 n) (hCP :
    rCore.DisjointWires rPGTwist) (rM0 rM1 rM2 : QRegister (q + 1) n) (rScr : QRegister
      (csaScratchWidth q) n) (S_pres :
    Finset (Wire n)) (H : BitAssignment n → Prop) (δ : BitAssignment (fullSysCoreWires mPayload) →
      ℤ) (h01 :
    rM0.DisjointWires rM1) (h02 : rM0.DisjointWires rM2) (h12 : rM1.DisjointWires rM2) (h0T :
      rM0.DisjointWires
    (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega))) (h1T : rM1.DisjointWires (rPGTwist.slice (45
      - (q + 1)) (q + 1)
    (by omega))) (h2T : rM2.DisjointWires (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega))) (h0S :
      rM0.DisjointWires
    rScr) (h1S : rM1.DisjointWires rScr) (h2S : rM2.DisjointWires rScr) (hTS : (rPGTwist.slice (45 -
      (q + 1)) (q + 1)
    (by omega)).DisjointWires rScr) (hDisjS : Disjoint S_pres (rPGTwist.slice (45 - (q + 1)) (q +
      1) (by omega)).image)
    (hEq : ∀ ξ : BitAssignment n, (∀ i : Fin (csaScratchWidth q), ξ (rScr i) = 0) → H ξ →
      (if isInv then (-1 : ℤ) else 1) * ((regVal rM0 ξ + regVal rM1 ξ + regVal rM2 ξ : ℕ) : ℤ) =
        δ (fun i ↦ ξ (rCore i))) :
    CondStageSpec (rCore.concat rPGTwist hCP) rScr S_pres H
      (uApexShift45 (fullSysCoreWires mPayload) (q + 1) hq δ)
      (dCsa3AxisApex isInv q v rM0 rM1 rM2 (rPGTwist.slice (45 - (q + 1)) (q + 1) (by omega)) rScr
        h01 h02 h12 h1T h0S h1S h2S hTS) :=
  CondStageSpec.of_dCsa3AxisApex_pad isInv q hq v rCore rPGTwist hCP rM0 rM1 rM2 rScr rScr
    S_pres H δ h01 h02 h12 h0T h1T h2T h0S h1S h2S hTS Finset.Subset.rfl hTS hDisjS hEq
def rHigh {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) : QRegister (6 +
    mPayload) n :=
  rCore.slice 3948 (6 + mPayload) (by rw [fullSysCoreWires_eq_3954_add]; omega)
lemma rHigh_sub_rCore {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (rHigh rCore).image ⊆ rCore.image := QRegister.image_compose_subset rCore _
lemma rCore_mem_rHigh {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (idx : Fin (fullSysCoreWires mPayload)) (hlo : 3948 ≤ idx.val) : rCore idx ∈ (rHigh
      rCore).image := by
  unfold rHigh
  exact reg_mem_slice rCore _ idx hlo (by
    have := idx.isLt; have := fullSysCoreWires_eq_3954_add mPayload; omega)
lemma wSlot0_mem_rHigh {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    wSlot0 rCore ∈ (rHigh rCore).image := rCore_mem_rHigh rCore _ (by dsimp; omega)
lemma wSlot1_mem_rHigh {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    wSlot1 rCore ∈ (rHigh rCore).image := rCore_mem_rHigh rCore _ (by dsimp; omega)
lemma wSlot2_mem_rHigh {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    wSlot2 rCore ∈ (rHigh rCore).image := rCore_mem_rHigh rCore _ (by dsimp; omega)
lemma rCosetB1_sub_rHigh {mPayload n : ℕ} (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires
    mPayload) n) :
    (rCosetB1 hm rCore).image ⊆ (rHigh rCore).image := by
  unfold rCosetB1 rHigh; refine slice_sub_slice rCore _ _ (by omega) (by omega)
lemma rCosetB0_sub_rHigh {mPayload n : ℕ} (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires
    mPayload) n) :
    (rCosetB0 hm rCore).image ⊆ (rHigh rCore).image := by
  unfold rCosetB0 rHigh; refine slice_sub_slice rCore _ _ (by omega) (by omega)
def HProjFlag {mPayload n : ℕ} (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires mPayload)
    n) (rWork :
    QRegister mWorkTwist n) (ξ : BitAssignment n) : Prop :=
  ξ (rWork 6) = if vepHighNuc hm (fun q ↦ ξ (rCore q)) then 1 else 0
lemma HProjFlag_congr_S {mPayload n : ℕ} (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires
    mPayload) n) (rWork
    : QRegister mWorkTwist n) {S : Finset (Wire n)} (hHigh : (rHigh rCore).image ⊆ S) (hwf : rWork 6
      ∈ S) : ∀ ξ₁ ξ₂ :
    BitAssignment n, (∀ w ∈ S, ξ₁ w = ξ₂ w) → (HProjFlag hm rCore rWork ξ₁ ↔ HProjFlag hm rCore
      rWork ξ₂) :=
  fun ξ₁ ξ₂ hEq ↦ by
    unfold HProjFlag
    rw [hEq (rWork 6) hwf, vepHighNuc_eq_of_high_eq hm fun q hq ↦ hEq (rCore q) (hHigh
      (rCore_mem_rHigh rCore q hq))]
lemma wfBitVal_of_HProjFlag {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWork : QRegister mWorkTwist n)
    {ξ : BitAssignment n} (hH : HProjFlag hm rCore rWork ξ) :
    ((ξ (rWork 6)).val : ℤ) = wfBitVal hm (fun q ↦ ξ (rCore q)) := by
  unfold HProjFlag at hH; unfold wfBitVal; rw [hH]
  cases vepHighNuc hm (fun q ↦ ξ (rCore q)) <;> decide

def dBiSeq {Var : Type} {n : ℕ} (isInv : Bool) (da db : DynamicCircuit Var n) :
    DynamicCircuit Var n := if isInv then .seq db da else .seq da db
lemma count_dBiSeq_toff {Var : Type} {n : ℕ} (isInv : Bool) {da db : DynamicCircuit Var n}
    (ha : da.count .TOFF = 0) (hb : db.count .TOFF = 0) : (dBiSeq isInv da db).count .TOFF = 0 := by
  cases isInv
  · exact dyn_seq_toff_zero ha hb
  · exact dyn_seq_toff_zero hb ha
@[simp] lemma count_dBiSeq_t {Var : Type} {n : ℕ} (isInv : Bool) (da db : DynamicCircuit Var n) :
    (dBiSeq isInv da db).count .T = da.count .T + db.count .T := by
  cases isInv <;> simp only [dBiSeq, ↓reduceIte, Bool.false_eq_true, count_dyn_seq]
  exact Nat.add_comm _ _
lemma CondStageSpec.dBiSeq {Var : Type} [Fintype Var] [DecidableEq Var] {mAct mW n : ℕ} {rAct :
    QRegister mAct n} {rW :
    QRegister mW n} {S_pres : Finset (Wire n)} {H : BitAssignment n → Prop} (hActW :
      rAct.DisjointWires rW) (hH : ∀ ξ₁
    ξ₂, (∀ w ∈ S_pres, ξ₁ w = ξ₂ w) → (H ξ₁ ↔ H ξ₂)) (isInv : Bool) {U₁ U₂ : Unitary (2 ^ mAct)} {da
      db : DynamicCircuit
    Var n}
    (ha : CondStageSpec rAct rW S_pres H (if isInv then U₁⁻¹ else U₁) da)
    (hb : CondStageSpec rAct rW S_pres H (if isInv then U₂⁻¹ else U₂) db) :
    CondStageSpec rAct rW S_pres H (if isInv then (U₂ * U₁)⁻¹ else U₂ * U₁)
      (JunctionApexCSA288.dBiSeq isInv da db) := by
  cases isInv
  · exact ha.seq hActW hH hb
  · simp only [↓reduceIte] at ha hb ⊢
    exact (hb.seq hActW hH ha).congr_unitary (_root_.mul_inv_rev U₂ U₁).symm
lemma mw256_b2 : mWorkTwist = 256 := rfl
lemma reg_not_mem_slice_b2 {M n : ℕ} (r : QRegister M n) (s l : ℕ) (hsl : s + l ≤ M)
    (a : Fin M) (ha : a.val < s ∨ s + l ≤ a.val) : r a ∉ (r.slice s l hsl).image :=
  reg_not_mem_slice r hsl a ha
lemma reg_mem_slice_b2 {M n : ℕ} (r : QRegister M n) (s l : ℕ) (hsl : s + l ≤ M) (a : Fin M)
    (ha1 : s ≤ a.val) (ha2 : a.val < s + l) : r a ∈ (r.slice s l hsl).image :=
  reg_mem_slice r hsl a ha1 ha2
lemma slice_sub_slice_b2 {M n : ℕ} (r : QRegister M n) (s₁ l₁ s₂ l₂ : ℕ) (h₁ : s₁ + l₁ ≤ M) (h₂ : s₂
    + l₂ ≤ M) (hlo : s₂
    ≤ s₁) (hhi : s₁ + l₁ ≤ s₂ + l₂) : (r.slice s₁ l₁ h₁).image ⊆ (r.slice s₂ l₂ h₂).image :=
  slice_sub_slice r h₁ h₂ hlo hhi
lemma slice_concat_image_eq_b2 {M n : ℕ} (r : QRegister M n) (s l₁ l₂ : ℕ) (h₁ : s + l₁ ≤ M) (h₂ :
    (s + l₁) + l₂ ≤ M)
    (h₁₂ : s + (l₁ + l₂) ≤ M) (hd : (r.slice s l₁ h₁).DisjointWires (r.slice (s + l₁) l₂ h₂)) :
      ((r.slice s l₁
    h₁).concat (r.slice (s + l₁) l₂ h₂) hd).image = (r.slice s (l₁ + l₂) h₁₂).image :=
  slice_concat_image_eq r h₁ h₂ h₁₂ hd
lemma embedUnitary_perm_mulVec_basisKet_b2 {k n : ℕ} (r : QRegister k n)
    (perm : Equiv.Perm (Fin (2 ^ k))) (β β_out : BitAssignment n)
    (h_in : ∀ q : Fin k, β_out (r q) = basisBits k (perm ((basisBitsEquiv k).symm (fun q' ↦
      β (r q')))) q)
    (h_out : ∀ z : Wire n, z ∉ r.image → β_out z = β z) :
    (r.embedUnitary (Operator.permutationUnitary perm)).1.mulVec (basisKet β) = basisKet β_out := by
  rw [show basisKet β = Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) from rfl,
    QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
    Operator.permutationUnitary_mulVec_single, r.tensorState_single_replaceIndex,
    show r.extractIndex ((basisBitsEquiv n).symm β) = (basisBitsEquiv k).symm (fun q' ↦
      β (r q')) from
      (basisBitsEquiv k).injective (funext fun q ↦ by
        change basisBits k _ q = basisBits k _ q
        rw [r.basisBits_extractIndex, basisBits_symm_apply, basisBits_symm_apply])]
  refine congrArg (Pi.single · (1 : ℂ)) ((basisBitsEquiv n).injective (funext fun z ↦ ?_))
  change basisBits n _ z = basisBits n _ z; rw [basisBits_symm_apply]
  by_cases hz : z ∈ r.image
  · obtain ⟨q, rfl⟩ := (QRegister.mem_image r z).mp hz; rw [r.basisBits_replaceIndex_apply, h_in q]
  · rw [r.basisBits_replaceIndex_of_not_mem _ _ z (fun ⟨q, hq⟩ ↦ hz ((QRegister.mem_image r z).mpr
      ⟨q, hq⟩)),
      basisBits_symm_apply, h_out z hz]
lemma diagOn_rCoreBlock48_of_comm_high_wire {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires
    mPayload) n)
    (rPGTwist : QRegister 48 n) (hCP : rCore.DisjointWires rPGTwist) (U : Unitary (2 ^
      (fullSysCoreWires mPayload)))
    (hComm : ∀ q : Wire (fullSysCoreWires mPayload), 3948 ≤ q.val → U.1 * slotBitProj q 0 =
      slotBitProj q 0 * U.1)
    {S_ext : Finset (Wire n)} (hDisj : Disjoint rCore.image S_ext) : DiagOn ((rHigh rCore).image ∪
      S_ext) ((rCore.concat
    rPGTwist hCP).embedUnitary ((rCoreBlock48 mPayload).embedUnitary U)).1 := by
  rw [← QRegister.embedUnitary_compose, compose_rCoreBlock48_eq rCore rPGTwist hCP]
  have hHigh : DiagOn (rHigh rCore).image (rCore.embedUnitary U).1 := by
    apply DiagOn.of_mulVec_basisKet
    intro ξ i hne u huH
    rw [QRegister.embedUnitary_val, vepEmbedMatrix_mulVec_basisKet, Finset.sum_apply] at hne
    obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hi : i = (basisBitsEquiv n).symm (vepWriteReg ξ rCore (basisBits _ l)) := by
      by_contra hne_i
      apply hl
      rw [basisKet_eq_single, Pi.smul_apply, Pi.single_eq_of_ne hne_i, smul_zero]
    have hMatNe : U.1 l ((basisBitsEquiv _).symm (fun k ↦ ξ (rCore k))) ≠ 0 := by
      intro h0
      apply hl
      rw [h0, zero_smul, Pi.zero_apply]
    rcases (QRegister.mem_image (rHigh rCore) u).mp huH with ⟨idx, rfl⟩
    have hfcw := fullSysCoreWires_eq_3954_add mPayload
    have hidx := idx.isLt
    let q : Wire (fullSysCoreWires mPayload) := ⟨3948 + idx.val, by omega⟩
    have hu_eq : rHigh rCore idx = rCore q := by
      unfold rHigh
      rw [slice_apply_eq]
    rw [hu_eq, hi, basisBits_basisBitsEquiv_symm_eq, vepWriteReg_mem]
    have hBit := entry_eq_of_comm_slotBitProj q (hComm q (by dsimp [q]; omega)) hMatNe
    rwa [basisBits_basisBitsEquiv_symm_eq] at hBit
  have hExt : DiagOn S_ext (rCore.embedUnitary U).1 := diagOn_embedMatrix_outside rCore U.1 hDisj
  intro i j hne w hw
  rcases Finset.mem_union.mp hw with hw1 | hw2
  · exact hHigh i j hne w hw1
  · exact hExt i j hne w hw2
lemma CondStageSpec.peelWork {Var : Type} [Fintype Var] [DecidableEq Var] {mPayload n : ℕ} (k : ℕ)
    (hk : k + 1 ≤ 45) (b₁
    b₂ bOut : Bool) (v : Var) (c₁ c₂ : Wire n) (rCore : QRegister (fullSysCoreWires mPayload) n)
      (rPGTwist : QRegister
    48 n) (rWork : QRegister mWorkTwist n) (hCP : rCore.DisjointWires rPGTwist) (hCW :
      rCore.DisjointWires rWork) (hPW :
    rPGTwist.DisjointWires rWork) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ rWork ⟨k, by have := mw256_b2; omega⟩)
    (h₂a : c₂ ≠ rWork ⟨k, by have := mw256_b2; omega⟩)
    (hc1Tot : c₁ ∉ (rWork.slice k (45 - k) (by have := mw256_b2; omega)).image)
    (hc2Tot : c₂ ∉ (rWork.slice k (45 - k) (by have := mw256_b2; omega)).image)
    (hc1S : c₁ ∈ (rHigh rCore).image ∪ (rWork.slice 0 k (by have := mw256_b2; omega)).image)
    (hc2S : c₂ ∈ (rHigh rCore).image ∪ (rWork.slice 0 k (by have := mw256_b2; omega)).image)
    {H_outer : BitAssignment n → Prop}
    (hH_anc : ∀ ξ₁ ξ₂ : BitAssignment n,
      (∀ w, w ≠ rWork ⟨k, by have := mw256_b2; omega⟩ → ξ₁ w = ξ₂ w) → H_outer ξ₁ → H_outer ξ₂)
    {H_inner : BitAssignment n → Prop}
    (hH_imp : ∀ η : BitAssignment n,
      H_outer η ∧ η (rWork ⟨k, by have := mw256_b2; omega⟩) = genBoolBit b₁ b₂ bOut (η c₁) (η c₂) →
      H_inner η)
    {U : Unitary (2 ^ (fullSysCoreWires mPayload + 48))} {dInner : DynamicCircuit Var n}
    (hsInner : CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice (k + 1) (45 - (k + 1)) (by have := mw256_b2; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 (k + 1) (by have := mw256_b2; omega)).image)
      H_inner U dInner) :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice k (45 - k) (by have := mw256_b2; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 k (by have := mw256_b2; omega)).image)
      H_outer U (JunctionApexCSA288.dGenBoolWrap b₁ b₂ bOut v c₁ c₂
        (rWork ⟨k, by have := mw256_b2; omega⟩) h₁₂ h₁a h₂a dInner) := by
  have hMW : mWorkTwist = 256 := rfl
  let anc : Wire n := rWork ⟨k, by omega⟩
  exact CondStageSpec.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ anc h₁₂ h₁a h₂a _ _
    (slice_sub_slice rWork _ _ (by omega) (by omega))
    (reg_mem_slice rWork _ ⟨k, by omega⟩ (by dsimp; omega) (by dsimp; omega))
    hc1Tot hc2Tot
    (reg_not_mem_slice rWork _ ⟨k, by omega⟩ (by dsimp; omega))
    (by
      rw [qreg_image_concat]
      intro hm_in
      have hancWork : anc ∈ rWork.image := (QRegister.mem_image rWork _).mpr ⟨⟨k, by omega⟩, rfl⟩
      rcases Finset.mem_union.mp hm_in with hC | hP
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC hancWork
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW) hP hancWork)
    hc1S hc2S
    (by
      intro w hw
      rcases Finset.mem_union.mp hw with hSo | hWt
      · exact Finset.mem_union_left _
          (Finset.union_subset_union_right (slice_sub_slice rWork _ _ (by omega) (by omega)) hSo)
      · rcases (QRegister.mem_image _ w).mp hWt with ⟨j, rfl⟩
        rw [slice_apply_eq]
        have hj := j.isLt
        by_cases hj0 : j.val = 0
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (reg_mem_slice rWork _ ⟨k + j.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)))
        · exact Finset.mem_union_right _
            (reg_mem_slice rWork _ ⟨k + j.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)))
    hH_anc (hsInner.weaken_H hH_imp)
def HCoin0Flag {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWorkTwist n) (ξ : BitAssignment n) : Prop :=
  ξ (rWork 1) = if coin0Active (fun q ↦ ξ (rCore q)) then 1 else 0
lemma dXor32_spec {mPayload : ℕ} (isInv : Bool) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rCore : QRegister
    (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (rWork : QRegister mWorkTwist n)
      (hCP :
    rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork) {H : BitAssignment n →
      Prop} : CondStageSpec
    (rCore.concat rPGTwist hCP) (rWork.slice 2 43 (by decide))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by decide)).image) H
      (if isInv then ((rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload))⁻¹
       else (rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload))
      (dXor32All654 (Var := Var) rCore) := by
  let rAct := rCore.concat rPGTwist hCP
  let rW43 := rWork.slice 2 43 (by decide)
  let rS2 := rWork.slice 0 2 (by decide)
  let U := (rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload)
  have hPair : RealizesCleanPair rAct rW43 U
      (dXor32All654 (Var := Var) rCore) (dXor32All654 (Var := Var) rCore) := by
    have hp := (dXor32All654_realizesPair (Var := Var) (rAct.compose (rCoreBlock48 mPayload))
      rW43).widenActive
    rwa [compose_rCoreBlock48_eq rCore rPGTwist hCP] at hp
  have hsFwd : CondStageSpec rAct rW43 ((rHigh rCore).image ∪ rS2.image) H U
      (dXor32All654 (Var := Var) rCore) :=
    ⟨⟨rAct.embedUnitary U, CleanUnitaryWp.of_realizesClean hPair.fwd, by
        rw [Finset.union_assoc]
        exact diagOn_rCoreBlock48_of_comm_high_wire rCore rPGTwist hCP (uXor32Core mPayload)
          (fun q hq ↦ uXor32Core_comm_high_wire q (by omega) 0)
          (Finset.disjoint_union_right.mpr
            ⟨(QRegExt.disjointWires_to_finset ((QRegExt.disjointWires_mono_right hCW)
              (QRegister.image_compose_subset rWork (QRegister.block 0 2 (by
              decide))))),
             (QRegExt.disjointWires_to_finset ((QRegExt.disjointWires_mono_right hCW)
               (QRegister.image_compose_subset rWork (QRegister.block 2 43 (by
               decide)))))⟩),
      fun _ _ _ ↦ rfl⟩⟩
  cases isInv
  · exact hsFwd
  · exact hsFwd.congr_unitary (by
      dsimp only [U]
      simp only [↓reduceIte, ← QRegister.embedUnitary_inv, uXor32Core_inv])
def slot4Sgn {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  if γ (wSlot2 (QRegExt.idReg _)) = 0 ∧ γ (wSlot1 (QRegExt.idReg _)) = 0 ∧
    γ (wSlot0 (QRegExt.idReg _)) = 1 then
    (if isInv then (-1 : ℤ) else 1) * (((γ (rCosetB1 hm (QRegExt.idReg _) w)).val : ℤ) -
      ((γ (rCosetB0 hm (QRegExt.idReg _) w)).val : ℤ))
  else 0
def slot4LowShift {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  slot4Sgn isInv hm w γ * (regVal ((rElecSlotAxis (QRegExt.idReg _) 0 w).slice 0 4 (by omega)) γ :
    ℤ)
def slot4TopExp {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  (2 ^ 41 : ℤ) * slot4Sgn isInv hm w γ * (16 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 4)).val :
    ℤ) +
    32 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5)).val : ℤ))
noncomputable def uSlot4AxisCat {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  uApexShift45 (fullSysCoreWires mPayload) 4 (by omega) (slot4LowShift isInv hm w) *
    (rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (slot4TopExp isInv hm w))
lemma uSlot4AxisCat_inv_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    (uSlot4AxisCat false hm w)⁻¹ = uSlot4AxisCat true hm w := by
  unfold uSlot4AxisCat
  rw [_root_.mul_inv_rev, uApexShift45_inv, ← QRegister.embedUnitary_inv,
    DyadicQft64.dyadicDiagUnitary_inv,
    show (fun γ ↦ -slot4LowShift false hm w γ) = slot4LowShift true hm w from
      funext fun γ ↦ by unfold slot4LowShift slot4Sgn; split_ifs <;> (try contradiction) <;> ring,
    show (fun γ ↦ -slot4TopExp false hm w γ) = slot4TopExp true hm w from
      funext fun γ ↦ by unfold slot4TopExp slot4Sgn; split_ifs <;> (try contradiction) <;> ring]
  exact uApexShift45_comm_coreDiag (fullSysCoreWires mPayload) 4 (by omega) 48
    (slot4TopExp true hm w) (slot4LowShift true hm w)
def HSlot4Flag {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWorkTwist n) (ξ : BitAssignment n) : Prop :=
  ξ (rWork 0) = if ξ (wSlot2 rCore) = 0 ∧ ξ (wSlot1 rCore) = 0 ∧ ξ (wSlot0 rCore) = 1 then 1 else 0
lemma HSlot4Flag_congr_S {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWorkTwist n) {S : Finset (Wire n)} (hHigh : (rHigh rCore).image ⊆ S)
    (hw0 : rWork 0 ∈ S) : ∀ ξ₁ ξ₂ : BitAssignment n, (∀ w ∈ S, ξ₁ w = ξ₂ w) →
    (HSlot4Flag rCore rWork ξ₁ ↔ HSlot4Flag rCore rWork ξ₂) := fun ξ₁ ξ₂ hEq ↦ by
  unfold HSlot4Flag
  rw [hEq (rWork 0) hw0, hEq (wSlot2 rCore) (hHigh (wSlot2_mem_rHigh rCore)),
    hEq (wSlot1 rCore) (hHigh (wSlot1_mem_rHigh rCore)), hEq (wSlot0 rCore) (hHigh (wSlot0_mem_rHigh
      rCore))]
lemma cSlot4TopPre_evolve {n : ℕ} (wNeg m4 m5 : Wire n) (hNeg5 : wNeg ≠ m5)
    (ξ : BitAssignment n) :
    (Circuit.S m5 ;;ᶜ cliffordCZ wNeg m5 hNeg5 ;;ᶜ
      (Circuit.S wNeg).inverse ;;ᶜ cApexXorT wNeg m4).eval.1.mulVec (basisKet ξ) =
      (DyadicQft64.dyadicTurn 3
        ((1 - 2 * ((ξ wNeg).val : ℤ)) * (((ξ m4).val : ℤ) + 2 * ((ξ m5).val : ℤ)) -
          ((ξ wNeg).val : ℤ))) • basisKet ξ := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, (PhasePerm.gateS m5).evolve,
    id_eq,
      Matrix.mulVec_smul, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        (phasePerm_cliffordCZ wNeg m5
      hNeg5).evolve, id_eq, Matrix.mulVec_smul, smul_smul, Circuit.eval_seq, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec,
      (PhasePerm.gateSDag wNeg).evolve, id_eq, Matrix.mulVec_smul, smul_smul, cApexXorT_evolve_any
        wNeg m4, smul_smul]
  refine congrArg (· • basisKet ξ) ?_
  rw [show (32 * ((ξ m5).val : ℤ)) = (2 ^ 4 : ℤ) * (2 * ((ξ m5).val : ℤ)) by ring,
    dyadicTurn_scale_pow 4 3,
    show (64 : ℤ) * (((ξ wNeg).val : ℤ) * ((ξ m5).val : ℤ)) =
      (2 ^ 4 : ℤ) * (4 * ((ξ wNeg).val : ℤ) * ((ξ m5).val : ℤ)) by ring,
    dyadicTurn_scale_pow 4 3,
    show (-32 * ((ξ wNeg).val : ℤ)) = (2 ^ 4 : ℤ) * (-2 * ((ξ wNeg).val : ℤ)) by ring,
    dyadicTurn_scale_pow 4 3,
    DyadicQft64.dyadicTurn_add, DyadicQft64.dyadicTurn_add, DyadicQft64.dyadicTurn_add,
    zmod2_add_val_int (ξ m4) (ξ wNeg),
    show (((2 * ((ξ m5).val : ℤ) + 4 * ((ξ wNeg).val : ℤ) * ((ξ m5).val : ℤ)) +
        -2 * ((ξ wNeg).val : ℤ)) +
      (((ξ m4).val : ℤ) + ((ξ wNeg).val : ℤ) - 2 * ((ξ m4).val : ℤ) * ((ξ wNeg).val : ℤ))) =
      ((1 - 2 * ((ξ wNeg).val : ℤ)) * (((ξ m4).val : ℤ) + 2 * ((ξ m5).val : ℤ)) -
        ((ξ wNeg).val : ℤ)) + (((ξ wNeg).val : ℤ) * ((ξ m5).val : ℤ)) * (2 ^ 3 : ℤ) by ring,
    dyadicTurn_eq_turnPow2, dyadicTurn_eq_turnPow2,
    turnPow2_add_period 3 _ (((ξ wNeg).val : ℤ) * ((ξ m5).val : ℤ))]
lemma slot4_sgn_act_eq {isInv : Bool} {b0 b1 wCoin wAct : ZMod 2} {flag : Prop}
    [Decidable flag] (hCoin : wCoin = if flag then 1 else 0) (hAct : wAct = wCoin * (b1 + b0)) :
    (1 - 2 * ((if isInv then b1 else b0).val : ℤ)) * (wAct.val : ℤ) =
      if flag then (if isInv then (-1 : ℤ) else 1) * ((b1.val : ℤ) - (b0.val : ℤ)) else 0 := by
  subst hAct hCoin; by_cases hf : flag
  · simp only [hf, ↓reduceIte, one_mul]; revert isInv b0 b1; decide
  · simp only [hf, ↓reduceIte, zero_mul, show ((0 : ZMod 2).val : ℤ) = 0 from rfl, mul_zero]
noncomputable def dSlot4Axis {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type} {n : ℕ}
    (v : Var) (w : Fin
    3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (rWork :
      QRegister mWorkTwist n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork) (hPW :
      rPGTwist.DisjointWires rWork) :
    DynamicCircuit Var n :=
  let wCoin := rWork 0
  let wb0 := rCosetB0 hm rCore w
  let wb1 := rCosetB1 hm rCore w
  let wNeg := if isInv then wb1 else wb0
  let rU6 := rElecSlotAxis rCore 0 w
  let rT4 := rPGTwist.slice 41 4 (by omega)
  let rW43 := rWork.slice 2 43 (by decide)
  let wAct := rW43 0
  let rM6 := rW43.slice 1 6 (by omega)
  let rM4 := rM6.slice 0 4 (by omega)
  let rC4 := rW43.slice 7 4 (by omega)
  have hb0Core : wb0 ∈ rCore.image := rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w,
    rfl⟩)
  have hb1Core : wb1 ∈ rCore.image := rCosetB1_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w,
    rfl⟩)
  have hNegCore : wNeg ∈ rCore.image := by
    dsimp [wNeg]
    cases isInv
    · exact hb0Core
    · exact hb1Core
  have h_b0_b1 : wb0 ≠ wb1 := by
    have := w.isLt
    have hfcw := fullSysCoreWires_eq_3954_add mPayload
    dsimp only [wb0, wb1]
    unfold rCosetB0 rCosetB1
    simp only [slice_apply_eq]
    exact core_wire_ne rCore (by dsimp; omega)
  dXorAndWrap v wCoin wb0 wb1 wAct h_b0_b1
    (fun h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core ((QRegister.mem_image
      rWork _).mpr ⟨0,
      h⟩))
    (fun h ↦ reg_not_mem_slice rWork (by decide) 0 (by decide) ((QRegister.mem_image rW43 _).mpr ⟨0,
      h.symm⟩))
    (fun h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      (QRegister.image_compose_subset rWork _
      ((QRegister.mem_image rW43 _).mpr ⟨0, h.symm⟩)))
    (dMaskRegWrap 6 v wAct rU6 rM6
      (fun i h ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rElecSlotAxis_sub_rCore rCore
        0 w
        ((QRegister.mem_image rU6 _).mpr ⟨i, rfl⟩)) (QRegister.image_compose_subset rWork _
          ((QRegister.mem_image rW43 _).mpr ⟨0, h⟩)))
      (fun i h ↦ reg_not_mem_slice rW43 (by omega) 0 (by decide) ((QRegister.mem_image rM6 _).mpr
        ⟨i, h.symm⟩))
      ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW)
        (rElecSlotAxis_sub_rCore rCore 0 w))) (Finset.Subset.trans
        (QRegister.image_compose_subset rW43 _) (QRegister.image_compose_subset rWork _)))
      (.seq
        (.circuit (Circuit.S (rM6 5) ;;ᶜ cliffordCZ wNeg (rM6 5)
          (fun h ↦
            Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
            (QRegister.image_compose_subset
            rWork _ (QRegister.image_compose_subset rW43 _ ((QRegister.mem_image rM6 _).mpr ⟨5,
              h.symm⟩)))) ;;ᶜ
          (Circuit.S wNeg).inverse ;;ᶜ cApexXorT wNeg (rM6 4)))
        (dApexTAdderCtrlSign v wNeg rM4 rT4 rC4
          (fun i h ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCP) hNegCore
            (QRegister.image_compose_subset rPGTwist _ ((QRegister.mem_image rT4 _).mpr ⟨i,
              h.symm⟩)))
          (disj_symm ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW)
            (QRegister.image_compose_subset rPGTwist _)))
            (Finset.Subset.trans (QRegister.image_compose_subset rM6 _)
              (Finset.Subset.trans (QRegister.image_compose_subset rW43 _)
                (QRegister.image_compose_subset rWork _)))))
          ((QRegExt.disjointWires_mono_left (slice_disjoint_of_le rW43 1 6 7 4 (by omega) (by omega)
            (by omega)))
            (QRegister.image_compose_subset rM6 _))
          ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW)
            (QRegister.image_compose_subset rPGTwist _)))
            (Finset.Subset.trans (QRegister.image_compose_subset rW43 _)
              (QRegister.image_compose_subset rWork _))))))
@[simp] lemma count_dSlot4Axis_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    {n : ℕ} (v : Var) (w
    : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (rWork :
      QRegister
    mWorkTwist n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Axis isInv hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW).count .TOFF = 0 := by
  unfold dSlot4Axis
  dsimp only
  rw [count_dXorAndWrap_toff, count_dMaskRegWrap_toff]
  refine dyn_seq_toff_zero ?_ (count_dApexTAdderCtrlSign_toff ..)
  simp only [DynamicCircuit.count, Circuit.count_seq, count_inverse_toff, count_cliffordCZ_toff,
    count_cApexXorT_toff]
  rfl
@[simp] lemma count_dSlot4Axis_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    {n : ℕ} (v : Var) (w :
    Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (rWork :
      QRegister mWorkTwist
    n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Axis isInv hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW).count .T = 46 := by
  let wNeg := if isInv then rCosetB1 hm rCore w else rCosetB0 hm rCore w
  let rW43 := rWork.slice 2 43 (by decide)
  let rM6 := rW43.slice 1 6 (by omega)
  let rC4 := rW43.slice 7 4 (by omega)
  have hNegCore : wNeg ∈ rCore.image := by
    dsimp [wNeg]
    cases isInv
    · exact rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
    · exact rCosetB1_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hNeg4 : wNeg ≠ rM6 4 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
    (QRegister.image_compose_subset rWork _
      (QRegister.image_compose_subset rW43 _ ((QRegister.mem_image rM6 _).mpr ⟨4, h.symm⟩)))
  have hwNegC : wNeg ∉ rC4.image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
    (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW43 _ hm_in))
  unfold dSlot4Axis
  dsimp only
  rw [count_dXorAndWrap_t, count_dMaskRegWrap_t, count_dyn_seq, count_dApexTAdderCtrlSign_t _ _ _ _
    _ _ hwNegC]
  have hPreT : ∀ h5, (Circuit.S (rM6 5) ;;ᶜ cliffordCZ wNeg (rM6 5) h5 ;;ᶜ
      (Circuit.S wNeg).inverse ;;ᶜ cApexXorT wNeg (rM6 4)).count .T = 1 := fun h5 ↦ by
    simp only [Circuit.count_seq, count_cliffordCZ_t, count_cApexXorT_t hNeg4]
    rfl
  change 4 + (4 * 6 + (Circuit.count .T _ + 17)) = 46
  rw [hPreT]
lemma dSlot4Axis_spec {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n
    : ℕ} (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist :
      QRegister 48 n) (rWork :
    QRegister mWorkTwist n) (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
      (hPW :
    rPGTwist.DisjointWires rWork) : CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice 2 43 (by have := mw256_b2; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by have := mw256_b2; omega)).image)
      (HSlot4Flag rCore rWork) (uSlot4AxisCat isInv hm w)
      (dSlot4Axis isInv hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW) := by
  let rAct := rCore.concat rPGTwist hCP
  let rS2 := rWork.slice 0 2 (by decide)
  let rW43 := rWork.slice 2 43 (by decide)
  let S_base := (rHigh rCore).image ∪ rS2.image
  let wCoin := rWork 0
  let wb0 := rCosetB0 hm rCore w
  let wb1 := rCosetB1 hm rCore w
  let wNeg := if isInv then wb1 else wb0
  let rU6 := rElecSlotAxis rCore 0 w
  let rT4 := rPGTwist.slice 41 4 (by omega)
  let wAct := rW43 0
  let rM6 := rW43.slice 1 6 (by omega)
  let rM4 := rM6.slice 0 4 (by omega)
  let rC4 := rW43.slice 7 4 (by omega)
  let rSub36 := rW43.slice 7 36 (by omega)
  let rSub42 := rW43.slice 1 42 (by omega)
  have hb0Core : wb0 ∈ rCore.image := rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w,
    rfl⟩)
  have hb1Core : wb1 ∈ rCore.image := rCosetB1_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w,
    rfl⟩)
  have hb0High : wb0 ∈ (rHigh rCore).image := rCosetB0_sub_rHigh hm rCore ((QRegister.mem_image _
    _).mpr ⟨w, rfl⟩)
  have hb1High : wb1 ∈ (rHigh rCore).image := rCosetB1_sub_rHigh hm rCore ((QRegister.mem_image _
    _).mpr ⟨w, rfl⟩)
  have hNegCore : wNeg ∈ rCore.image := by dsimp [wNeg]; exact Bool.casesOn isInv hb0Core hb1Core
  have h_b0_b1 : wb0 ≠ wb1 := by
    have := w.isLt; have hfcw := fullSysCoreWires_eq_3954_add mPayload
    dsimp only [wb0, wb1]; unfold rCosetB0 rCosetB1; simp only [slice_apply_eq]
    exact core_wire_ne rCore (by dsimp; omega)
  have h_c_act : wCoin ≠ wAct := fun h ↦
    reg_not_mem_slice rWork (by decide) 0 (by decide) ((QRegister.mem_image rW43 _).mpr ⟨0, h.symm⟩)
  have hNeg5 : wNeg ≠ rM6 5 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
    (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW43 _
      ((QRegister.mem_image rM6 _).mpr ⟨5, h.symm⟩)))
  have hwNegT : ∀ i : Fin 4, wNeg ≠ rT4 i := fun i h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCP) hNegCore
      (QRegister.image_compose_subset rPGTwist _
      ((QRegister.mem_image rT4 _).mpr ⟨i, h.symm⟩))
  have hM4T : rM4.DisjointWires rT4 :=
    disj_symm ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW)
    (QRegister.image_compose_subset
    rPGTwist _)))
    (Finset.Subset.trans (QRegister.image_compose_subset rM6 _) (Finset.Subset.trans
      (QRegister.image_compose_subset rW43 _) (QRegister.image_compose_subset rWork _))))
  have hM4C : rM4.DisjointWires rC4 :=
    (QRegExt.disjointWires_mono_left (slice_disjoint_of_le rW43 1 6 7 4 (by omega) (by omega) (by
    omega))) (QRegister.image_compose_subset rM6 _)
  have hTC : rT4.DisjointWires rC4 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW)
    (QRegister.image_compose_subset rPGTwist
    _)))
    (Finset.Subset.trans (QRegister.image_compose_subset rW43 _) (QRegister.image_compose_subset
      rWork _))
  have hT36 : rT4.DisjointWires rSub36 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW)
    (QRegister.image_compose_subset rPGTwist
    _)))
    (Finset.Subset.trans (QRegister.image_compose_subset rW43 _) (QRegister.image_compose_subset
      rWork _))
  let S_mid := (S_base ∪ rU6.image) ∪ ({wAct} : Finset (Wire n)); let S_in := S_mid ∪ rM6.image
  let H_act : BitAssignment n → Prop := fun η ↦ HSlot4Flag rCore rWork η ∧ η wAct = η wCoin *
    (η wb1 + η wb0)
  let H_in : BitAssignment n → Prop := fun η ↦ H_act η ∧ ∀ i : Fin 6, η (rM6 i) = η wAct * η (rU6 i)
  let cPre := Circuit.S (rM6 5) ;;ᶜ cliffordCZ wNeg (rM6 5) hNeg5 ;;ᶜ (Circuit.S wNeg).inverse ;;ᶜ
    cApexXorT wNeg (rM6 4)
  obtain ⟨uAdd, hwAdd, hDiagAdd, hKetAdd⟩ := dApexTAdderCtrlSign_spec v wNeg rM4 rT4 rC4
    (fun hm_in ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW43 _
        (QRegister.image_compose_subset rM6 _ hm_in))))
    hwNegT (fun hm_in ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW43 _ hm_in))) hM4T
        hM4C hTC
  have hC4_sub_36 : rC4.image ⊆ rSub36.image := slice_sub_slice rW43 (by omega) (by omega) (by
    omega) (by omega)
  have hDiagPre : DiagOn (S_in ∪ rSub36.image) cPre.eval.1 := diagOn_of_diag_ket _ _
    (cSlot4TopPre_evolve wNeg (rM6 4) (rM6 5) hNeg5)
  have hSubCW : S_in ∪ rSub36.image ⊆ rCore.image ∪ rWork.image :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.union_subset
      (Finset.union_subset (Finset.Subset.trans (rHigh_sub_rCore rCore) Finset.subset_union_left)
        (Finset.Subset.trans (QRegister.image_compose_subset rWork (QRegister.block 0 2 (by
          decide))) Finset.subset_union_right))
      (Finset.Subset.trans (rElecSlotAxis_sub_rCore rCore 0 w) Finset.subset_union_left))
      (Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ (QRegister.image_compose_subset
        rWork (QRegister.block 2 43 (by decide)) ((QRegister.mem_image rW43 _).mpr ⟨0, rfl⟩)))))
      (Finset.Subset.trans (QRegister.image_compose_subset rW43 (QRegister.block 1 6 (by omega)))
        (Finset.Subset.trans (QRegister.image_compose_subset rWork (QRegister.block 2 43 (by
          decide))) Finset.subset_union_right)))
      (Finset.Subset.trans (QRegister.image_compose_subset rW43 (QRegister.block 7 36 (by omega)))
        (Finset.Subset.trans (QRegister.image_compose_subset rWork (QRegister.block 2 43 (by
          decide))) Finset.subset_union_right))
  have hSubAdd : S_in ∪ rSub36.image ⊆ Finset.univ \ rT4.image := fun u hu ↦
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr
      ⟨(QRegExt.disjointWires_to_finset ((QRegExt.disjointWires_mono_right hCP)
        (QRegister.image_compose_subset rPGTwist _))),
       (QRegExt.disjointWires_to_finset (disj_symm ((QRegExt.disjointWires_mono_left hPW)
         (QRegister.image_compose_subset rPGTwist _))))⟩) (hSubCW
         hu)⟩
  have hs18 : CondStageSpec rAct rSub36 S_in H_in (uSlot4AxisCat isInv hm w)
      (.seq (.circuit cPre) (dApexTAdderCtrlSign v wNeg rM4 rT4 rC4 hwNegT hM4T hM4C hTC)) := by
    refine ⟨⟨uAdd * cPre.eval,
      (CleanUnitaryWp.circuit rSub36 cPre).seq_of_diag (hwAdd.mono_workspace hC4_sub_36)
        (DiagOn.anti Finset.subset_union_right hDiagPre),
      (DiagOn.anti hSubAdd hDiagAdd).mul hDiagPre, fun ξ hz36 ⟨⟨hHFlag, hActEq⟩, hMask⟩ ↦ ?_⟩⟩
    change (uAdd.1 * cPre.eval.1).mulVec (basisKet ξ) = _
    rw [← Matrix.mulVec_mulVec, cSlot4TopPre_evolve, Matrix.mulVec_smul,
      hKetAdd ξ (zero_on_sub hC4_sub_36 hz36), smul_smul]
    unfold uSlot4AxisCat
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ← QRegister.embedUnitary_compose, compose_rCoreBlock48_eq rCore rPGTwist hCP,
      embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul,
      embed_uApexShift45_mulVec_basisKet (by omega) rCore rPGTwist hCP, smul_smul]
    let γ : BitAssignment (fullSysCoreWires mPayload) := fun q ↦ ξ (rCore q)
    have hSgnAct : (1 - 2 * ((ξ wNeg).val : ℤ)) * ((ξ wAct).val : ℤ) = slot4Sgn isInv hm w γ := by
      have hNeg_eq : ξ wNeg = if isInv then γ (rCosetB1 hm (QRegExt.idReg _) w)
          else γ (rCosetB0 hm (QRegExt.idReg _) w) := by
        cases isInv
        · rfl
        · rfl
      rw [hNeg_eq]
      unfold slot4Sgn
      unfold HSlot4Flag at hHFlag
      exact slot4_sgn_act_eq hHFlag hActEq
    have hMask4 : ∀ i : Fin 4, ξ (rM4 i) = ξ wAct * ξ ((rU6.slice 0 4 (by omega)) i) := fun i ↦ by
      dsimp only [rM4]
      rw [slice_apply_eq, slice_apply_eq]
      exact hMask ⟨0 + i.val, by have := i.isLt; omega⟩
    have hLowEq : (1 - 2 * ((ξ wNeg).val : ℤ)) * (regVal rM4 ξ : ℤ) = slot4LowShift isInv hm w γ :=
      by
      rw [regVal_masked_eq wAct (rU6.slice 0 4 (by omega)) rM4 ξ hMask4, ← mul_assoc, hSgnAct]
      rfl
    have hTopEq : DyadicQft64.dyadicTurn 3 ((1 - 2 * ((ξ wNeg).val : ℤ)) * (((ξ (rM6 4)).val : ℤ) +
          2 * ((ξ (rM6 5)).val : ℤ)) - ((ξ wNeg).val : ℤ)) * DyadicQft64.dyadicTurn 3 ((ξ
            wNeg).val : ℤ) =
        DyadicQft64.dyadicTurn 48 (slot4TopExp isInv hm w γ) := by
      rw [DyadicQft64.dyadicTurn_add,
        show ((1 - 2 * ((ξ wNeg).val : ℤ)) * (((ξ (rM6 4)).val : ℤ) + 2 * ((ξ (rM6 5)).val : ℤ)) -
          ((ξ wNeg).val : ℤ)) + ((ξ wNeg).val : ℤ) =
          (1 - 2 * ((ξ wNeg).val : ℤ)) * (((ξ (rM6 4)).val : ℤ) + 2 * ((ξ (rM6 5)).val : ℤ))
            by ring,
        hMask 4, hMask 5, zmod2_mul_val_int, zmod2_mul_val_int]
      unfold slot4TopExp
      rw [show (2 ^ 41 : ℤ) * slot4Sgn isInv hm w γ *
            (16 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 4)).val : ℤ) +
             32 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5)).val : ℤ)) =
          (2 ^ 45 : ℤ) * (slot4Sgn isInv hm w γ *
            (((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 4)).val : ℤ) +
             2 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5)).val : ℤ))) by ring,
        dyadicTurn_scale_pow 45 3, ← hSgnAct]
      congr 1
      change (1 - 2 * ((ξ wNeg).val : ℤ)) * (((ξ wAct).val : ℤ) * ((γ (rElecSlotAxis
        (QRegExt.idReg _) 0 w 4)).val :
          ℤ) + 2 * (((ξ wAct).val : ℤ) * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5)).val : ℤ))) =
            _
      ring
    dsimp only [rT4] at hLowEq ⊢
    rw [hLowEq, ← mul_assoc, hTopEq]
  have hM6_36 : rM6.DisjointWires rSub36 := slice_disjoint_of_le rW43 1 6 7 36 (by omega) (by omega)
    (by omega)
  have hAct_M6 : rAct.DisjointWires rM6 := QRegExt.disjointWires_concat_left
    ((QRegExt.disjointWires_mono_right hCW) (Finset.Subset.trans (QRegister.image_compose_subset
      rW43 _)
      (QRegister.image_compose_subset rWork _)))
    ((QRegExt.disjointWires_mono_right hPW) (Finset.Subset.trans (QRegister.image_compose_subset
      rW43 _)
      (QRegister.image_compose_subset rWork _)))
  have hsMask0 := CondStageSpec.dMaskRegWrap 6 v wAct rU6 rM6
    (fun i h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rElecSlotAxis_sub_rCore rCore 0
      w
      ((QRegister.mem_image rU6 _).mpr ⟨i, rfl⟩))
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW43 _).mpr ⟨0, h⟩)))
    (fun i h ↦ reg_not_mem_slice rW43 (by omega) 0 (by decide) ((QRegister.mem_image rM6 _).mpr ⟨i,
      h.symm⟩))
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW)
      (rElecSlotAxis_sub_rCore rCore 0 w)))
      (Finset.Subset.trans (QRegister.image_compose_subset rW43 _) (QRegister.image_compose_subset
        rWork _)))
    rSub36 hM6_36 (reg_not_mem_slice rW43 (by omega) 0 (by decide))
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW)
      (rElecSlotAxis_sub_rCore rCore 0 w)))
      (Finset.Subset.trans (QRegister.image_compose_subset rW43 _) (QRegister.image_compose_subset
        rWork _)))
    hAct_M6 (Finset.mem_union_right _ (Finset.mem_singleton_self wAct))
    (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
    (fun ξ₁ ξ₂ hEq ⟨hF, hA⟩ ↦ by
      have hNotM6_Core : ∀ u ∈ rCore.image, u ∉ rM6.image := fun u hu hm_in ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu
          (QRegister.image_compose_subset rWork _
          (QRegister.image_compose_subset rW43 _ hm_in))
      have hCoinNotM6 : wCoin ∉ rM6.image := fun hm_in ↦
        reg_not_mem_slice rWork (by decide) 0 (by decide) (QRegister.image_compose_subset rW43 _
          hm_in)
      refine ⟨(HSlot4Flag_congr_S rCore rWork Finset.subset_union_left (Finset.mem_union_right _
        (Finset.mem_singleton_self wCoin)) ξ₁ ξ₂ fun u hu ↦
        hEq u (by rcases Finset.mem_union.mp hu with hH | hC0
                  · exact hNotM6_Core u (rHigh_sub_rCore rCore hH)
                  · exact Finset.mem_singleton.mp hC0 ▸ hCoinNotM6)).mp hF, ?_⟩
      rw [← hEq wAct (reg_not_mem_slice rW43 (by omega) 0 (by decide)), ← hEq wCoin hCoinNotM6,
        ← hEq wb1 (hNotM6_Core _ hb1Core), ← hEq wb0 (hNotM6_Core _ hb0Core)]
      exact hA) hs18
  have hConcat42 : (rM6.concat rSub36 hM6_36).image = rSub42.image := slice_concat_image_eq rW43 (by
    omega) (by omega) (by omega) hM6_36
  have hsMask : CondStageSpec rAct rSub42 S_mid H_act (uSlot4AxisCat isInv hm w) _ :=
    hsMask0.widen_workspace (rTot := rSub42) (by rw [hConcat42]) (by rw [hConcat42])
  refine (CondStageSpec.dXorAndWrap v wCoin wb0 wb1 wAct h_b0_b1
    (fun h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core ((QRegister.mem_image
      rWork _).mpr ⟨0,
      h⟩))
    (fun h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb0Core ((QRegister.mem_image
      rWork _).mpr ⟨0,
      h⟩)) h_c_act
    (fun h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      (QRegister.image_compose_subset rWork _
      ((QRegister.mem_image rW43 _).mpr ⟨0, h.symm⟩)))
    (fun h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb0Core
      (QRegister.image_compose_subset rWork _
      ((QRegister.mem_image rW43 _).mpr ⟨0, h.symm⟩)))
    rSub42 rW43 (QRegister.image_compose_subset rW43 _) ((QRegister.mem_image rW43 _).mpr ⟨0, rfl⟩)
    (reg_not_mem_slice rW43 (by omega) 0 (by decide)) (reg_not_mem_slice rWork (by decide) 0 (by
      decide))
    (fun hm_in ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb0Core
      (QRegister.image_compose_subset rWork
      _ hm_in))
    (fun hm_in ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      (QRegister.image_compose_subset rWork
      _ hm_in))
    (by rw [qreg_image_concat]; intro hm_in
        have hwW : wAct ∈ rWork.image := QRegister.image_compose_subset rWork _
          ((QRegister.mem_image rW43 _).mpr ⟨0, rfl⟩)
        rcases Finset.mem_union.mp hm_in with hC | hP
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC hwW
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW) hP hwW)
    (Finset.mem_union_left _ (Finset.mem_union_right _ (reg_mem_slice rWork (by decide) 0 (by
      decide) (by decide))))
    (Finset.mem_union_left _ (Finset.mem_union_left _ hb0High)) (Finset.mem_union_left _
      (Finset.mem_union_left _ hb1High))
    (fun u hu ↦ by
      rcases Finset.mem_union.mp hu with hS | hW43
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hS)
      · rcases (QRegister.mem_image rW43 u).mp hW43 with ⟨j, rfl⟩
        have hj := j.isLt
        by_cases hj0 : j.val = 0
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr
            (congrArg rW43 (Fin.ext hj0))))
        · exact Finset.mem_union_right _ (reg_mem_slice rW43 (by omega) j (by omega) (by omega)))
    (fun ξ₁ ξ₂ hEq hF ↦ by
      have hCoreNe : ∀ u ∈ rCore.image, u ≠ wAct := fun u hu h ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu
          (QRegister.image_compose_subset rWork _
          ((QRegister.mem_image rW43 _).mpr ⟨0, h.symm⟩))
      unfold HSlot4Flag at hF ⊢
      rw [← hEq wCoin h_c_act, ← hEq (wSlot2 rCore) (hCoreNe _ (rHigh_sub_rCore rCore
        (wSlot2_mem_rHigh rCore))),
        ← hEq (wSlot1 rCore) (hCoreNe _ (rHigh_sub_rCore rCore (wSlot1_mem_rHigh rCore))),
        ← hEq (wSlot0 rCore) (hCoreNe _ (rHigh_sub_rCore rCore (wSlot0_mem_rHigh rCore)))]
      exact hF) hsMask).widen_workspace (S_tot := S_base) Finset.Subset.rfl
        (Finset.union_subset_union_left Finset.subset_union_left)
lemma dSlot4Axis_biSpec {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type} [Fintype
    Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist :
      QRegister 48 n) (rWork
    : QRegister mWorkTwist n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP) (rWork.slice 2 43 (by have := mw256_b2; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by have := mw256_b2; omega)).image)
      (HSlot4Flag rCore rWork) (if isInv then (uSlot4AxisCat false hm w)⁻¹ else uSlot4AxisCat false
        hm w)
      (dSlot4Axis isInv hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW) := by
  cases isInv
  · exact dSlot4Axis_spec false hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW
  · exact (dSlot4Axis_spec true hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW).congr_unitary
      (uSlot4AxisCat_inv_eq hm w).symm
noncomputable def uSlot4ApexCat {mPayload : ℕ} (hm : 22 ≤ mPayload) : Unitary (2 ^
    (fullSysCoreWires mPayload + 48)) :=
  uSlot4AxisCat false hm 2 * (uSlot4AxisCat false hm 1 * uSlot4AxisCat false hm 0)
def HPos01AndCoin0 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWorkTwist n) (ξ : BitAssignment n) : Prop :=
  (ξ (rWork 0) = if (ξ (wSlot2 rCore) = 0 ∧ ξ (wSlot1 rCore) = 0) then 1 else 0) ∧
    HCoin0Flag rCore rWork ξ
lemma zmod2_pos01_xor_coin0_eq_slot4 {s2 s1 s0 w0 w1 : ZMod 2}
    (hw0 : w0 = if (s2 = 0 ∧ s1 = 0) then 1 else 0)
    (hw1 : w1 = if decide (s2 = 0 ∧ s1 = 0 ∧ s0 = 0) then 1 else 0) :
    w0 + w1 = if (s2 = 0 ∧ s1 = 0 ∧ s0 = 1) then 1 else 0 := by
  subst hw0 hw1
  rcases zmod2_eq_zero_or_one s2 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one s1 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one s0 with rfl | rfl <;>
    decide
noncomputable def dSlot4Conj {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type} {n : ℕ}
    (v : Var) (rCore :
    QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (rWork : QRegister
      mWorkTwist n) (hCP :
    rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires
      rWork) :
    DynamicCircuit Var n :=
  dPureConj (Circuit.CNOT (rWork 1) (rWork 0) fun h ↦ by cases rWork.wires.injective h)
    (dBiSeq isInv
      (dBiSeq isInv
        (dSlot4Axis isInv hm (Var := Var) v 0 rCore rPGTwist rWork hCP hCW hPW)
        (dSlot4Axis isInv hm (Var := Var) v 1 rCore rPGTwist rWork hCP hCW hPW))
      (dSlot4Axis isInv hm (Var := Var) v 2 rCore rPGTwist rWork hCP hCW hPW))
@[simp] lemma count_dSlot4Conj_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (rWork :
      QRegister mWorkTwist n) (hCP
    : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Conj isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW).count .TOFF = 0 := by
  unfold dSlot4Conj
  rw [count_dPureConj_toff _ (by simp [Circuit.CNOT])]
  exact count_dBiSeq_toff isInv (count_dBiSeq_toff isInv (count_dSlot4Axis_toff ..)
    (count_dSlot4Axis_toff ..)) (count_dSlot4Axis_toff ..)
@[simp] lemma count_dSlot4Conj_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n) (rWork :
      QRegister mWorkTwist n) (hCP
    : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Conj isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW).count .T = 138 := by
  unfold dSlot4Conj
  rw [count_dPureConj_t _ (by simp [Circuit.CNOT])]
  simp only [count_dBiSeq_t, count_dSlot4Axis_t]
lemma dSlot4Conj_spec {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n
    : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
      (rWork : QRegister
    mWorkTwist n) (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork) (hPW :
      rPGTwist.DisjointWires
    rWork) : CondStageSpec (rCore.concat rPGTwist hCP) (rWork.slice 2 43 (by decide)) ((rHigh
      rCore).image ∪
    (rWork.slice 0 2 (by decide)).image) (HPos01AndCoin0 rCore rWork)
      (if isInv then (uSlot4ApexCat hm)⁻¹ else uSlot4ApexCat hm)
      (dSlot4Conj isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW) := by
  have hActW := QRegExt.disjointWires_concat_left (h₁₂ := hCP)
    ((QRegExt.disjointWires_mono_right hCW) (QRegister.image_compose_subset rWork (QRegister.block 2
      43 (by decide))))
    ((QRegExt.disjointWires_mono_right hPW) (QRegister.image_compose_subset rWork (QRegister.block 2
      43 (by decide))))
  have hH_s4 := HSlot4Flag_congr_S rCore rWork Finset.subset_union_left
    (Finset.mem_union_right _ (reg_mem_slice_b2 rWork 0 2 (by decide) 0 (by decide) (by decide)))
  refine CondStageSpec.dPureConjCNOT (rWork 1) (rWork 0) (fun h ↦ by cases rWork.wires.injective h)
    (reg_not_mem_slice_b2 rWork 2 43 (by decide) 1 (by decide))
    (reg_not_mem_slice_b2 rWork 2 43 (by decide) 0 (by decide))
    (by
      rw [qreg_image_concat]
      intro hm_in
      have hwW : rWork 0 ∈ rWork.image := (QRegister.mem_image rWork _).mpr ⟨0, rfl⟩
      rcases Finset.mem_union.mp hm_in with hC | hP
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC hwW
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW) hP hwW)
    (Finset.mem_union_right _ (reg_mem_slice_b2 rWork 0 2 (by decide) 1 (by decide) (by decide)))
    (Finset.mem_union_right _ (reg_mem_slice_b2 rWork 0 2 (by decide) 0 (by decide) (by decide)))
    (fun ξ ⟨hPos, hC0⟩ ↦ by
      have hCoreNe0 : ∀ u ∈ rCore.image, u ≠ rWork 0 := fun u hu h ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu ((QRegister.mem_image rWork
          _).mpr ⟨0, h.symm⟩)
      unfold HSlot4Flag
      rw [Function.update_self, Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore
        (wSlot2_mem_rHigh rCore))),
          Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot1_mem_rHigh rCore))),
            Function.update_of_ne
          (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot0_mem_rHigh rCore)))]
      unfold HCoin0Flag coin0Active at hC0
      rw [show decide (ξ (rCore (wSlot2 (QRegExt.idReg _))) = 0 ∧
            ξ (rCore (wSlot1 (QRegExt.idReg _))) = 0 ∧
            ξ (rCore (wSlot0 (QRegExt.idReg _))) = 0) =
          decide (ξ (wSlot2 rCore) = 0 ∧ ξ (wSlot1 rCore) = 0 ∧ ξ (wSlot0 rCore) = 0) by
            unfold wSlot2 wSlot1 wSlot0
            simp [QRegExt.idReg]] at hC0
      exact zmod2_pos01_xor_coin0_eq_slot4 hPos hC0)
    ((CondStageSpec.dBiSeq hActW hH_s4 isInv
      (CondStageSpec.dBiSeq hActW hH_s4 isInv
        (dSlot4Axis_biSpec isInv hm (Var := Var) v 0 rCore rPGTwist rWork hCP hCW hPW)
        (dSlot4Axis_biSpec isInv hm (Var := Var) v 1 rCore rPGTwist rWork hCP hCW hPW))
      (dSlot4Axis_biSpec isInv hm (Var := Var) v 2 rCore rPGTwist rWork hCP hCW hPW)).congr_unitary
      (U₂ := if isInv then (uSlot4ApexCat hm)⁻¹ else uSlot4ApexCat hm) rfl)
theorem uSlot4ApexCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload) (U_cat_48 : Unitary (2 ^
    48)) (hcol0 :
    U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
      NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
    (uSlot4ApexCat hm) (uSlot4KickCore hm) := by
  have hAx (w : Fin 3) : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (uSlot4AxisCat false hm w) (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload)
      48 (fun γ ↦ slot4TopExp false hm w γ + (2 ^ 41 : ℤ) * slot4LowShift false hm w γ)) := by
    have hProd := (NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (slot4TopExp false hm w))).mul
      (uApexShift45_intertwinesLocal (fullSysCoreWires mPayload) 4 (by omega)
        (slot4LowShift false hm w) U_cat_48 hcol0)
    suffices hEff :
        DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
            (fun γ ↦ (2 ^ (45 - 4) : ℤ) * slot4LowShift false hm w γ) *
          DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (slot4TopExp false hm w) =
        DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
          (fun γ ↦ slot4TopExp false hm w γ + (2 ^ 41 : ℤ) * slot4LowShift false hm w γ) by
      rwa [hEff] at hProd
    rw [dyadicDiagUnitary_mul]
  have hAll := (hAx 0).mul ((hAx 1).mul (hAx 2))
  rw [show uSlot4AxisCat false hm 2 * uSlot4AxisCat false hm 1 * uSlot4AxisCat false hm 0 =
    uSlot4ApexCat hm by unfold uSlot4ApexCat; rw [mul_assoc]] at hAll
  suffices hEffAll :
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
          (fun γ ↦ slot4TopExp false hm 2 γ + (2 ^ 41 : ℤ) * slot4LowShift false hm 2 γ) *
        DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
          (fun γ ↦ slot4TopExp false hm 1 γ + (2 ^ 41 : ℤ) * slot4LowShift false hm 1 γ)) *
        DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
          (fun γ ↦ slot4TopExp false hm 0 γ + (2 ^ 41 : ℤ) * slot4LowShift false hm 0 γ) =
      uSlot4KickCore hm by
    rwa [hEffAll] at hAll
  unfold uSlot4KickCore
  rw [dyadicDiagUnitary_mul, dyadicDiagUnitary_mul]
  apply dyadicDiagUnitary_congr
  intro γ
  have hAxisSum : ∀ w : Fin 3, slot4TopExp false hm w γ + (2 ^ 41 : ℤ) * slot4LowShift false hm w
    γ =
      (2 ^ 41 : ℤ) * (slot4Sgn false hm w γ * (regVal (rElecSlotAxis (QRegExt.idReg _) 0 w) γ :
        ℤ)) := fun w ↦ by
    rw [show (regVal (rElecSlotAxis (QRegExt.idReg _) 0 w) γ : ℤ) =
        (regVal ((rElecSlotAxis (QRegExt.idReg _) 0 w).slice 0 4 (by omega)) γ : ℤ) +
          16 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 4)).val : ℤ) +
          32 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5)).val : ℤ) by
      unfold regVal bitsVal; rw [Fin.sum_univ_six, Fin.sum_univ_four]
      simp only [slice_apply_eq]; dsimp; ring]
    unfold slot4TopExp slot4LowShift
    ring
  rw [hAxisSum 0, hAxisSum 1, hAxisSum 2]
  unfold slot4TotalPhaseExp slot4Sgn
  rw [Fin.sum_univ_three]
  split_ifs <;> (try contradiction) <;> ring
lemma zmod2_peel0_eq_pos01 (s2 s1 : ZMod 2) :
    genBoolBit true true false s2 s1 = if s2 = 0 ∧ s1 = 0 then 1 else 0 := by revert s2 s1; decide
lemma zmod2_peel1_eq_coin0 {s2 s1 s0 w0 : ZMod 2} (hw0 : w0 = if s2 = 0 ∧ s1 = 0 then 1 else 0) :
    genBoolBit false true false w0 s0 = if decide (s2 = 0 ∧ s1 = 0 ∧ s0 = 0) then 1 else 0 := by
  subst hw0; revert s2 s1 s0; decide
end ConfigJunctionApexCSA288
end JunctionApexCSA288
end
end ModJunctionApexCSA288

end QuantumComputation.Specs.StoppingPowerSolution
