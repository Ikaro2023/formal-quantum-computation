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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.OctaSelectSwapQrom
@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
section ModSingleAnchorFermionicPauliCap
@[expose] public section
namespace SingleAnchorFermionicPauliCap
set_option maxRecDepth 4096
open Operator Matrix SpecsAux
open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner (basisBits_permElectron
  div_18_lt_numElectrons fermionicProjector_eq_groupAvgProj isGridState_permElectron
  mem_spinGroupAux_iff permElectron permElectron_comp_apply permElectron_inv_apply permElectronWire
  permElectronWireFun spinGroupAux spinGroupAux_mul)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
section PolymorphicAlgebra
variable {d : ℕ}
theorem matrix_eq_of_mulVec_eq_sp {A B : Operator d}
    (h : ∀ s x, A.mulVec s x = B.mulVec s x) : A = B := by
  ext x y; simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h (Pi.single y 1) x
theorem permutationUnitary_mul_mulVec_apply_sp (A : Operator d) (e : Equiv.Perm (Fin d))
    (s : Fin d → ℂ) (x : Fin d) :
    (((permutationUnitary e).1 * A) *ᵥ s) x = (A *ᵥ s) (e.symm x) := by
  simp only [Matrix.mulVec, dotProduct, permutationUnitary_mul_apply]
theorem eq_zero_of_eq_neg_self_sp {M : Operator d} (h : M = -M) : M = 0 := by
  ext x y; have hxy : M x y = -(M x y) := congrFun (congrFun h x) y
  have h2 : (2 : ℂ) * M x y = 0 := by linear_combination hxy
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
theorem conj_idempotent_of_left_idempotent {P N : Operator d} (hP_herm : P.IsHermitian)
    (hN_herm : N.IsHermitian) (hleft : P * (N * N) = P * N) : N * N * P = N * P := by
  have hconj := congrArg Matrix.conjTranspose hleft
  simpa only [conjTranspose_mul, hP_herm.eq, hN_herm.eq, Matrix.mul_assoc] using hconj
theorem cubic_mul_proj_zero_of_comm_idem_right {N P A B : Operator d} (hsum : A + B = N)
    (hAB : A * B = B * A) (hA : A * A * P = A * P) (hB : B * B * P = B * P) : N * (N - 1) *
    (N - (2 : ℂ) • 1) * P = 0 := by
  have hAA : A * (A * P) = A * P := by rw [← Matrix.mul_assoc, hA]
  have hBB : B * (B * P) = B * P := by rw [← Matrix.mul_assoc, hB]
  have hBA (X : Operator d) : B * (A * X) = A * (B * X) := by
    rw [← Matrix.mul_assoc, ← hAB, Matrix.mul_assoc]
  have hAAB : A * (A * (B * P)) = A * (B * P) := by
    rw [← hBA P, ← hBA (A * P), hAA, hBA P]
  rw [← hsum, two_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_assoc, hBA, hAA, hBB, hAAB]
  abel
theorem orthogSum_cubic_mul_proj_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E M : ι → Operator d} {P : Operator d}
    (hE_orth : ∀ a b, E a * E b = if a = b then E a else 0)
    (hEM_comm : ∀ a b, E a * M b = M b * E a)
    (hcub : ∀ a, M a * (M a - 1) * (M a - (2 : ℂ) • 1) * P = 0) :
    let S := ∑ a, E a * M a
    S * (S - 1) * (S - (2 : ℂ) • 1) * P = 0 := by
  intro S
  have hmul (F : ι → Operator d) : S * (∑ b, E b * F b) = ∑ a, E a * (M a * F a) := by
    simp_rw [S, Finset.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hterm (b : ι) : (E a * M a) * (E b * F b) =
        if a = b then E a * (M a * F b) else 0 := by
      rw [hEM_comm a a, Matrix.mul_assoc, ← Matrix.mul_assoc (E a) (E b),
        ← Matrix.mul_assoc, hE_orth a b]
      by_cases hab : a = b
      · rw [ite_eq_left hab, ite_eq_left hab, ← hEM_comm a a, Matrix.mul_assoc]
      · rw [ite_eq_right hab, ite_eq_right hab, Matrix.mul_zero, Matrix.zero_mul]
    simp_rw [hterm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hS2 : S * S = ∑ a, E a * (M a * M a) := hmul M
  have hS3 : S * S * S = ∑ a, E a * (M a * M a * M a) := by
    rw [Matrix.mul_assoc, hS2, hmul]
    simp only [Matrix.mul_assoc]
  have expand_cubic (X : Operator d) : X * (X - 1) * (X - (2 : ℂ) • 1) =
      X * X * X - (3 : ℂ) • (X * X) + (2 : ℂ) • X := by
    rw [show (2 : ℂ) • (1 : Operator d) = 1 + 1 from two_smul ℂ 1,
      show (3 : ℂ) • (X * X) = X * X + X * X + X * X by
        rw [show (3 : ℂ) = 2 + 1 by norm_num, add_smul, two_smul, one_smul, add_assoc],
      two_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [expand_cubic S, hS3, hS2, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  calc (E a * (M a * M a * M a) - (3 : ℂ) • (E a * (M a * M a)) + (2 : ℂ) • (E a * M a)) * P
      = E a * ((M a * (M a - 1) * (M a - (2 : ℂ) • 1)) * P) := by
          rw [expand_cubic (M a)]
          simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hcub a, Matrix.mul_zero]
theorem projector_sandwich_comm_and_norm_zero {G P A B : Operator d} (hG_herm : G.IsHermitian)
    (hP_herm : P.IsHermitian) (hA_herm : A.IsHermitian) (hB_herm : B.IsHermitian)
    (hGP : G * P = P) (hGBG_comm : (G * B * G) * P = P * (G * B * G)) (heq : A * P = B * P) :
    (G * A * G) * P = P * (G * A * G) ∧ ‖P * (G * A * G - G * B * G) * P‖ ≤ (0 : ℝ) := by
  have hAG_eq : (G * A * G) * P = (G * B * G) * P := by
    have h1 (X : Operator d) : (G * X * G) * P = G * (X * P) := by
      rw [Matrix.mul_assoc (G * X) G P, Matrix.mul_assoc G X (G * P), hGP]
    rw [h1 A, heq, ← h1 B]
  have hHerm {X : Operator d} (hX : X.IsHermitian) : (G * X * G).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.mul_assoc, conjTranspose_mul, conjTranspose_mul,
      hG_herm.eq, hX.eq, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [hAG_eq, hGBG_comm, ← hP_herm.eq, ← (hHerm hB_herm).eq, ← conjTranspose_mul,
      ← hAG_eq, conjTranspose_mul, hP_herm.eq, (hHerm hA_herm).eq]
  · rw [Matrix.mul_assoc, Matrix.sub_mul, hAG_eq, sub_self, Matrix.mul_zero, norm_zero]
theorem sum_sq_left_idem_of_pair_zero {ι : Type*} (S : Finset ι)
    (P : Operator d) (O : ι → Operator d) (hself : ∀ i ∈ S, O i * O i = O i)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → P * (O i * O j) = 0) : P *
    ((∑ i ∈ S, O i) * (∑ j ∈ S, O j)) = P * (∑ i ∈ S, O i) := by
  classical
  rw [Finset.sum_mul, Matrix.mul_sum, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Matrix.mul_sum, Matrix.mul_sum, Finset.sum_eq_single i]
  · rw [hself i hi]
  · exact fun j hj hne ↦ hpair i hi j hj hne.symm
  · exact fun hnot ↦ (hnot hi).elim
theorem sandwich_mul_idem_comm {G M : Operator d} (hG : G * G = G) :
    (G * M * G) * G = G * (G * M * G) := by
  rw [Matrix.mul_assoc (G * M), hG, ← Matrix.mul_assoc G (G * M),
    ← Matrix.mul_assoc G G, hG, Matrix.mul_assoc]
theorem sandwich_comm_of_comm {G M U : Operator d} (hGU : G * U = U * G) (hMU : M * U = U * M)
    : (G * M * G) * U = U * (G * M * G) := by
  calc (G * M * G) * U = G * (M * U) * G := by
        rw [Matrix.mul_assoc (G * M) G U, hGU]; simp only [Matrix.mul_assoc]
    _ = U * (G * M * G) := by
        rw [hMU, ← Matrix.mul_assoc G U M, hGU]; simp only [Matrix.mul_assoc]
end PolymorphicAlgebra
def rEl_sp (i : Fin numElectrons) : QRegister 18 systemQubits :=
  QRegister.block (18 * i.val) 18 (by
    have hi : i.val < 218 := i.isLt
    change 18 * i.val + 18 ≤ 3948
    omega)
theorem rEl_disjoint_of_ne_sp {i j : Fin numElectrons} (hne : i ≠ j) :
    (rEl_sp i).DisjointWires (rEl_sp j) := by
  rw [QRegister.disjoint_iff]
  intro a b hab
  have hv := congrArg Fin.val hab
  have hne' := Fin.val_ne_of_ne hne
  have := a.isLt; have := b.isLt
  change 18 * i.val + a.val = 18 * j.val + b.val at hv
  omega
theorem peWire_rEl_sp (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons) (b : Fin 18) :
    permElectronWire g (rEl_sp i b) = rEl_sp (g i) b := by
  apply Fin.ext
  have hi : i.val < 218 := i.isLt; have hb : b.val < 18 := b.isLt
  have hlt : (rEl_sp i b).val < 3924 := by change 18 * i.val + b.val < 3924; omega
  change (permElectronWireFun g (rEl_sp i b)).val = 18 * (g i).val + b.val
  unfold permElectronWireFun
  simp only [hlt, ↓reduceDIte]
  rw [show (⟨(rEl_sp i b).val / 18, div_18_lt_numElectrons hlt⟩ : Fin numElectrons) = i from
    Fin.ext (by change (18 * i.val + b.val) / 18 = i.val; omega)]
  exact congrArg (18 * (g i).val + ·) (by change (18 * i.val + b.val) % 18 = b.val; omega)
theorem mem_range_rEl_peWire_iff_sp (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons)
    (q : Wire systemQubits) :
    permElectronWire g q ∈ Set.range (rEl_sp (g i)).wires ↔ q ∈ Set.range (rEl_sp i).wires :=
  ⟨fun ⟨b, hb⟩ ↦ ⟨b, (permElectronWire g).injective (by rw [← hb]; exact peWire_rEl_sp g i b)⟩,
   fun ⟨b, hb⟩ ↦ ⟨b, by rw [← hb]; exact (peWire_rEl_sp g i b).symm⟩⟩
theorem basisBits_pe_apply_sp (g : Equiv.Perm (Fin numElectrons)) (x : Fin (2 ^ systemQubits))
    (q : Wire systemQubits) : basisBits systemQubits (permElectron g x) q = basisBits
    systemQubits x (permElectronWire g q) := basisBits_permElectron (permElectronWire g) x q
theorem extIdx_rEl_pe_sp (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons)
    (x : Fin (2 ^ systemQubits)) :
    (rEl_sp i).extractIndex (permElectron g x) = (rEl_sp (g i)).extractIndex x := by
  apply (basisBitsEquiv 18).injective
  funext b
  change basisBits 18 ((rEl_sp i).extractIndex (permElectron g x)) b =
    basisBits 18 ((rEl_sp (g i)).extractIndex x) b
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    ← peWire_rEl_sp, basisBits_pe_apply_sp]
theorem ao_rEl_pe_iff_sp (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons)
    (x y : Fin (2 ^ systemQubits)) : (rEl_sp i).AgreeOutside (permElectron g x)
    (permElectron g y) ↔ (rEl_sp (g i)).AgreeOutside x y := by
  refine ⟨fun h q hq ↦ ?_, fun h q hq ↦ ?_⟩
  · have hq' : (permElectronWire g).symm q ∉ Set.range (rEl_sp i).wires := by
      rw [← mem_range_rEl_peWire_iff_sp g i, Equiv.apply_symm_apply]; exact hq
    have hb := h ((permElectronWire g).symm q) hq'
    rwa [basisBits_pe_apply_sp, basisBits_pe_apply_sp, Equiv.apply_symm_apply] at hb
  · rw [basisBits_pe_apply_sp, basisBits_pe_apply_sp]
    exact h (permElectronWire g q) (mt (mem_range_rEl_peWire_iff_sp g i q).mp hq)
theorem emb_rEl_pe_sp (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons)
    (A : Operator (2 ^ 18)) (x y : Fin (2 ^ systemQubits)) : ((rEl_sp i).embedMatrix A)
    (permElectron g x) (permElectron g y) = ((rEl_sp (g i)).embedMatrix A) x y := by
  classical
  rw [QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside,
    extIdx_rEl_pe_sp, extIdx_rEl_pe_sp, if_congr (ao_rEl_pe_iff_sp g i x y) rfl rfl]
theorem emb_rEl_mul_pe_sp (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons)
    (A : Operator (2 ^ 18)) :
    (rEl_sp i).embedMatrix A * (permutationUnitary (permElectron g)).1 =
      (permutationUnitary (permElectron g)).1 * (rEl_sp (g i)).embedMatrix A := by
  ext x y
  rw [mul_permutationUnitary_apply, permutationUnitary_mul_apply,
    ← emb_rEl_pe_sp g i A ((permElectron g).symm x) y, Equiv.apply_symm_apply]
def rk1_sp (χ : Fin (2 ^ 18) → ℂ) : Operator (2 ^ 18) := Matrix.of fun u v ↦ χ u * star (χ v)
noncomputable def op_sp (χ : Fin (2 ^ 18) → ℂ) (i : Fin numElectrons) : Operator
    (2 ^ systemQubits) := (rEl_sp i).embedMatrix (rk1_sp χ)
theorem rk1_isHermitian_sp (χ : Fin (2 ^ 18) → ℂ) : (rk1_sp χ).IsHermitian := by
  ext u v; simp [rk1_sp, Matrix.conjTranspose_apply, mul_comm]
theorem rk1_mul_self_sp {χ : Fin (2 ^ 18) → ℂ} (hnorm : ∑ u : Fin (2 ^ 18), star (χ u) * χ u = 1) :
    rk1_sp χ * rk1_sp χ = rk1_sp χ := by
  ext u v; simp only [Matrix.mul_apply, rk1_sp, Matrix.of_apply]
  calc ∑ z, χ u * star (χ z) * (χ z * star (χ v))
    _ = χ u * (∑ z, star (χ z) * χ z) * star (χ v) := by
        rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun z _ ↦ by ring
    _ = χ u * star (χ v) := by rw [hnorm, mul_one]
theorem op_isHermitian_sp (χ : Fin (2 ^ 18) → ℂ) (i : Fin numElectrons) :
    (op_sp χ i).IsHermitian := by
  rw [Matrix.IsHermitian, op_sp, ← QRegister.embedMatrix_conjTranspose, (rk1_isHermitian_sp χ).eq]
theorem op_mul_self_sp {χ : Fin (2 ^ 18) → ℂ} (hnorm : ∑ u : Fin (2 ^ 18), star (χ u) * χ u = 1)
    (i : Fin numElectrons) : op_sp χ i * op_sp χ i = op_sp χ i := by
  rw [op_sp, ← QRegister.embedMatrix_mul, rk1_mul_self_sp hnorm]
theorem op_comm_of_ne_sp (χ : Fin (2 ^ 18) → ℂ) {i j : Fin numElectrons} (hne : i ≠ j) :
    op_sp χ i * op_sp χ j = op_sp χ j * op_sp χ i :=
  QRegister.embedMatrix_comm_of_disjoint (rEl_sp i) (rEl_sp j) (rEl_disjoint_of_ne_sp hne) _ _
theorem peWire_swap_of_not_mem_sp {i j : Fin numElectrons} {q : Wire systemQubits}
    (hqi : q ∉ Set.range (rEl_sp i).wires) (hqj : q ∉ Set.range (rEl_sp j).wires) :
    permElectronWire (Equiv.swap i j) q = q := by
  apply Fin.ext
  change (permElectronWireFun (Equiv.swap i j) q).val = q.val
  unfold permElectronWireFun
  by_cases hq : q.val < 3924
  · simp only [hq, ↓reduceDIte]
    let k : Fin numElectrons := ⟨q.val / 18, div_18_lt_numElectrons hq⟩
    let r : Fin 18 := ⟨q.val % 18, Nat.mod_lt _ (by decide)⟩
    have hq_eq : (rEl_sp k).wires r = q :=
      Fin.ext (by change 18 * (q.val / 18) + q.val % 18 = q.val; omega)
    rw [Equiv.swap_apply_of_ne_of_ne (fun h : k = i ↦ hqi ⟨r, h ▸ hq_eq⟩)
      (fun h : k = j ↦ hqj ⟨r, h ▸ hq_eq⟩)]
    change 18 * (q.val / 18) + q.val % 18 = q.val
    omega
  · simp [hq]
theorem repIdx_rEl_swap_sp {i j : Fin numElectrons} (x : Fin (2 ^ systemQubits))
    (u v : Fin (2 ^ 18)) :
    (rEl_sp j).replaceIndex ((rEl_sp i).replaceIndex (permElectron (Equiv.swap i j) x) u) v =
      (rEl_sp j).replaceIndex ((rEl_sp i).replaceIndex x u) v := by
  apply (basisBitsEquiv systemQubits).injective
  funext q
  change basisBits systemQubits _ q = basisBits systemQubits _ q
  by_cases hqj : q ∈ Set.range (rEl_sp j).wires
  · obtain ⟨b, rfl⟩ := hqj
    rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqj,
      QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqj]
    by_cases hqi : q ∈ Set.range (rEl_sp i).wires
    · obtain ⟨b, rfl⟩ := hqi
      rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqi,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqi,
        basisBits_pe_apply_sp, peWire_swap_of_not_mem_sp hqi hqj]
theorem pe_swap_mul_op_pair_sp (χ : Fin (2 ^ 18) → ℂ) {i j : Fin numElectrons} (hne : i ≠ j) :
    (permutationUnitary (permElectron (Equiv.swap i j))).1 * (op_sp χ i * op_sp χ j) =
      op_sp χ i * op_sp χ j := by
  apply matrix_eq_of_mulVec_eq_sp
  intro state x
  rw [permutationUnitary_mul_mulVec_apply_sp, ← permElectron_inv_apply, Equiv.swap_inv]
  simp_rw [← Matrix.mulVec_mulVec, op_sp, QRegister.embedMatrix_mulVec_apply]
  have hdisj := rEl_disjoint_of_ne_sp hne.symm
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  let x' := permElectron (Equiv.swap i j) x
  change rk1_sp χ ((rEl_sp i).extractIndex x') u *
      ∑ v, rk1_sp χ ((rEl_sp j).extractIndex ((rEl_sp i).replaceIndex x' u)) v *
        state ((rEl_sp j).replaceIndex ((rEl_sp i).replaceIndex x' u) v) =
    rk1_sp χ ((rEl_sp i).extractIndex x) u *
      ∑ v, rk1_sp χ ((rEl_sp j).extractIndex ((rEl_sp i).replaceIndex x u)) v *
        state ((rEl_sp j).replaceIndex ((rEl_sp i).replaceIndex x u) v)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [QRegister.extractIndex_replaceIndex_of_disjoint _ _ hdisj,
    QRegister.extractIndex_replaceIndex_of_disjoint _ _ hdisj, extIdx_rEl_pe_sp,
    extIdx_rEl_pe_sp, Equiv.swap_apply_left, Equiv.swap_apply_right, repIdx_rEl_swap_sp]
  simp only [rk1_sp, Matrix.of_apply]
  ring
theorem spinGroupAux_swap_mem {η : ℕ} {spinUp : Finset (Fin η)} {i j : Fin η}
    (hspin : i ∈ spinUp ↔ j ∈ spinUp) : Equiv.swap i j ∈ spinGroupAux spinUp := by
  rw [mem_spinGroupAux_iff]
  intro k
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left]
    exact hspin.symm
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right]
      exact hspin
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
theorem groupAvgProj_mul_swap_eq_neg {η d : ℕ} (spinUp : Finset (Fin η))
    (Pred : Fin d → Prop) (π : Equiv.Perm (Fin η) → Equiv.Perm (Fin d))
    (hcomp : ∀ g₁ g₂ x, π g₁ (π g₂ x) = π (g₂ * g₁) x)
    {i j : Fin η} (hne : i ≠ j) (hspin : i ∈ spinUp ↔ j ∈ spinUp) :
    groupAvgProj (spinGroupAux spinUp) (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ)) Pred π *
        (permutationUnitary (π (Equiv.swap i j))).1 =
      -groupAvgProj (spinGroupAux spinUp) (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ)) Pred π := by
  let τ := Equiv.swap i j
  have hτ : τ ∈ spinGroupAux spinUp := spinGroupAux_swap_mem hspin
  rw [groupAvgProj, Matrix.smul_mul, Finset.sum_mul, ← smul_neg, ← Finset.sum_neg_distrib]
  refine congrArg (((spinGroupAux spinUp).card : ℂ)⁻¹ • ·) ?_
  refine Finset.sum_bij (fun g _ ↦ τ * g) (fun g hg ↦ spinGroupAux_mul hτ hg)
    (fun _ _ _ _ h ↦ mul_left_cancel h)
    (fun k hk ↦ ⟨τ * k, spinGroupAux_mul hτ hk,
      by rw [← mul_assoc, Equiv.swap_mul_self, one_mul]⟩) fun g _ ↦ ?_
  rw [Matrix.smul_mul, Matrix.mul_assoc, permutationUnitary_mul_of_comp (hcomp g τ), map_mul,
    Equiv.Perm.sign_swap hne]
  simp [neg_smul]
theorem fermionicProjector_mul_op_pair_eq_zero_sp (χ : Fin (2 ^ 18) → ℂ)
    {spinUp : Finset (Fin numElectrons)} {i j : Fin numElectrons} (hne : i ≠ j)
    (hspin : i ∈ spinUp ↔ j ∈ spinUp) :
    fermionicProjector spinUp * (op_sp χ i * op_sp χ j) = 0 := by
  refine eq_zero_of_eq_neg_self_sp ?_
  have hswap : fermionicProjector spinUp *
      (permutationUnitary (permElectron (Equiv.swap i j))).1 = -fermionicProjector spinUp := by
    rw [fermionicProjector_eq_groupAvgProj spinUp]
    exact groupAvgProj_mul_swap_eq_neg spinUp IsGridState permElectron
      permElectron_comp_apply hne hspin
  calc fermionicProjector spinUp * (op_sp χ i * op_sp χ j)
    _ = fermionicProjector spinUp *
          ((permutationUnitary (permElectron (Equiv.swap i j))).1 * (op_sp χ i * op_sp χ j)) := by
        rw [pe_swap_mul_op_pair_sp χ hne]
    _ = -(fermionicProjector spinUp * (op_sp χ i * op_sp χ j)) := by
        rw [← Matrix.mul_assoc, hswap, Matrix.neg_mul]
noncomputable def nSub_sp (χ : Fin (2 ^ 18) → ℂ) (S : Finset (Fin numElectrons)) :
    Operator (2 ^ systemQubits) := ∑ i ∈ S, op_sp χ i
noncomputable def nTot_sp (χ : Fin (2 ^ 18) → ℂ) : Operator (2 ^ systemQubits) :=
  nSub_sp χ Finset.univ
theorem sum_perm_finset_eq {η : ℕ} {M : Type*} [AddCommMonoid M] (S : Finset (Fin η))
    (g : Equiv.Perm (Fin η)) (hS : ∀ i, g i ∈ S ↔ i ∈ S) (f : Fin η → M) : (∑ i ∈ S, f (g i))
    = ∑ i ∈ S, f i :=
  Finset.sum_bij (fun i _ ↦ g i) (fun i hi ↦ (hS i).mpr hi)
    (fun _ _ _ _ h ↦ g.injective h)
    (fun j hj ↦ ⟨g.symm j, (hS (g.symm j)).mp (by rwa [Equiv.apply_symm_apply]),
      Equiv.apply_symm_apply g j⟩)
    (fun _ _ ↦ rfl)
theorem nSub_isHermitian_any (χ : Fin (2 ^ 18) → ℂ) (S : Finset (Fin numElectrons)) :
    (nSub_sp χ S).IsHermitian := by
  rw [Matrix.IsHermitian, nSub_sp, conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (op_isHermitian_sp χ i).eq
theorem nSub_mul_self_mul_fermionicProjector {χ : Fin (2 ^ 18) → ℂ}
    (hnorm : ∑ u : Fin (2 ^ 18), star (χ u) * χ u = 1) (spinUp S : Finset (Fin numElectrons))
    (hS_same : ∀ i ∈ S, ∀ j ∈ S, i ∈ spinUp ↔ j ∈ spinUp) : nSub_sp χ S * nSub_sp χ S *
    fermionicProjector spinUp = nSub_sp χ S * fermionicProjector spinUp :=
    conj_idempotent_of_left_idempotent (fermionicProjector_isHermitian spinUp)
    (nSub_isHermitian_any χ S) (sum_sq_left_idem_of_pair_zero S (fermionicProjector spinUp)
    (op_sp χ) (fun i _ ↦ op_mul_self_sp hnorm i) (fun i hi j hj hne ↦
    fermionicProjector_mul_op_pair_eq_zero_sp χ hne (hS_same i hi j hj)))
theorem nSub_cubic_mul_fermionicProjector_zero {χ : Fin (2 ^ 18) → ℂ}
    (hnorm : ∑ u : Fin (2 ^ 18), star (χ u) * χ u = 1) (spinUp S : Finset (Fin numElectrons))
    : nSub_sp χ S * (nSub_sp χ S - 1) * (nSub_sp χ S - (2 : ℂ) • 1) * fermionicProjector
    spinUp = 0 := by
  let S_up := S.filter (· ∈ spinUp)
  let S_dn := S.filter (· ∉ spinUp)
  have hAB : nSub_sp χ S_up * nSub_sp χ S_dn = nSub_sp χ S_dn * nSub_sp χ S_up := by
    simp_rw [nSub_sp, Finset.sum_mul, Matrix.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun i hi ↦
      op_comm_of_ne_sp χ fun h ↦ (Finset.mem_filter.mp hj).2 (h ▸ (Finset.mem_filter.mp hi).2)
  exact cubic_mul_proj_zero_of_comm_idem_right
    (Finset.sum_filter_add_sum_filter_not S (· ∈ spinUp) (op_sp χ)) hAB
    (nSub_mul_self_mul_fermionicProjector hnorm spinUp S_up fun _ hi _ hj ↦
      ⟨fun _ ↦ (Finset.mem_filter.mp hj).2, fun _ ↦ (Finset.mem_filter.mp hi).2⟩)
    (nSub_mul_self_mul_fermionicProjector hnorm spinUp S_dn fun _ hi _ hj ↦
      ⟨fun h ↦ ((Finset.mem_filter.mp hi).2 h).elim,
       fun h ↦ ((Finset.mem_filter.mp hj).2 h).elim⟩)
noncomputable def singleAnchorPairOp {ι : Type*} [Fintype ι]
    (χ₀ : ι → Fin (2 ^ 18) → ℂ) (χ₁ : ι → Fin (2 ^ 18) → ℂ) (f : ι → ι)
    (i : Fin numElectrons) : Operator (2 ^ systemQubits) :=
  ∑ y₀ : ι, op_sp (χ₀ y₀) i * nSub_sp (χ₁ (f y₀)) (Finset.univ.erase i)
theorem op_sp_mul_op_sp_of_orthog {χ α : Fin (2 ^ 18) → ℂ}
    (h : ∑ u : Fin (2 ^ 18), star (χ u) * α u = 0) (i : Fin numElectrons) :
    op_sp χ i * op_sp α i = 0 := by
  have hrk : rk1_sp χ * rk1_sp α = 0 := by
    ext u v
    simp only [Matrix.mul_apply, rk1_sp, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ z, χ u * star (χ z) * (α z * star (α v))
      _ = χ u * (∑ z, star (χ z) * α z) * star (α v) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = 0 := by rw [h, mul_zero, zero_mul]
  rw [op_sp, op_sp, ← QRegister.embedMatrix_mul, hrk, QRegister.embedMatrix_zero]
theorem op_sp_comm_nSub_erase (χ₀ χ₁ : Fin (2 ^ 18) → ℂ) (i : Fin numElectrons) : op_sp χ₀ i *
    nSub_sp χ₁ (Finset.univ.erase i) = nSub_sp χ₁ (Finset.univ.erase i) * op_sp χ₀ i := by
  simp only [nSub_sp, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k hk ↦ QRegister.embedMatrix_comm_of_disjoint (rEl_sp i)
    (rEl_sp k) (rEl_disjoint_of_ne_sp (Finset.mem_erase.mp hk).1.symm) _ _
theorem singleAnchorPairOp_isHermitian {ι : Type*} [Fintype ι] (χ₀ χ₁ : ι → Fin (2 ^ 18) → ℂ)
    (f : ι → ι) (i : Fin numElectrons) : (singleAnchorPairOp χ₀ χ₁ f i).IsHermitian := by
  rw [Matrix.IsHermitian, singleAnchorPairOp, conjTranspose_sum]
  refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
  rw [conjTranspose_mul, (nSub_isHermitian_any (χ₁ (f y₀)) _).eq,
    (op_isHermitian_sp (χ₀ y₀) i).eq, ← op_sp_comm_nSub_erase]
theorem singleAnchorPairOp_cubic_mul_fermionicProjector_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] {χ₀ χ₁ : ι → Fin (2 ^ 18) → ℂ} (f : ι → ι) (i : Fin numElectrons)
    (spinUp : Finset (Fin numElectrons)) (horth₀ : ∀ a b, ∑ u : Fin (2 ^ 18), star (χ₀ a u) *
    χ₀ b u = if a = b then 1 else 0)
    (hnorm₁ : ∀ b, ∑ u : Fin (2 ^ 18), star (χ₁ b u) * χ₁ b u = 1) : singleAnchorPairOp χ₀ χ₁
    f i * (singleAnchorPairOp χ₀ χ₁ f i - 1) * (singleAnchorPairOp χ₀ χ₁ f i - (2 : ℂ) • 1) *
    fermionicProjector spinUp = 0 :=
  orthogSum_cubic_mul_proj_zero
    (E := fun a ↦ op_sp (χ₀ a) i)
    (M := fun a ↦ nSub_sp (χ₁ (f a)) (Finset.univ.erase i))
    (fun a b ↦ by
      by_cases hab : a = b
      · subst hab
        rw [ite_eq_left rfl]
        exact op_mul_self_sp (by simpa using horth₀ a a) i
      · rw [ite_eq_right hab]
        exact op_sp_mul_op_sp_of_orthog (by simpa [hab] using horth₀ a b) i)
    (fun a b ↦ op_sp_comm_nSub_erase (χ₀ a) (χ₁ (f b)) i)
    (fun a ↦ nSub_cubic_mul_fermionicProjector_zero (hnorm₁ (f a)) spinUp (Finset.univ.erase i))
theorem gridProjector_eq_predProjector : gridProjector = predProjector IsGridState := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : IsGridState x <;> simp [gridProjector, predProjector, hx]
  · simp [gridProjector, predProjector, hxy]
theorem gridProjector_comm_permutationUnitary (g : Equiv.Perm (Fin numElectrons)) :
    gridProjector * (permutationUnitary (permElectron g)).1 =
      (permutationUnitary (permElectron g)).1 * gridProjector := by
  refine commutes_permutationUnitary_of_entry (permElectron g) gridProjector fun x y ↦ ?_
  classical
  by_cases hxy : x = y
  · subst hxy
    simp [gridProjector, isGridState_permElectron]
  · simp [gridProjector, hxy, (permElectron g).injective.ne hxy]
theorem agreesOnFermionicSector_gridSandwich_of_mul_eq {spinUp : Finset (Fin numElectrons)}
    {M₁ M₂ : Operator (2 ^ systemQubits)} (hA_herm : M₁.IsHermitian)
    (hB_herm : M₂.IsHermitian) (hperm : ∀ g ∈ spinGroupAux spinUp, M₂ * (permutationUnitary
    (permElectron g)).1 = (permutationUnitary (permElectron g)).1 * M₂) (heq : M₁ *
    fermionicProjector spinUp = M₂ * fermionicProjector spinUp) : AgreesOnFermionicSector
    spinUp (gridProjector * M₁ * gridProjector) (gridProjector * M₂ * gridProjector) 0 := by
  have hGBG_comm : (gridProjector * M₂ * gridProjector) * fermionicProjector spinUp =
      fermionicProjector spinUp * (gridProjector * M₂ * gridProjector) := by
    rw [fermionicProjector_eq_groupAvgProj spinUp]
    exact commutes_groupAvgProj (spinGroupAux spinUp) _ IsGridState permElectron
      (gridProjector * M₂ * gridProjector)
      (gridProjector_eq_predProjector ▸ sandwich_mul_idem_comm gridProjector_mul_self)
      fun g hg ↦ sandwich_comm_of_comm (gridProjector_comm_permutationUnitary g) (hperm g hg)
  exact @projector_sandwich_comm_and_norm_zero _ gridProjector (fermionicProjector spinUp) M₁
    M₂ gridProjector_isHermitian (fermionicProjector_isHermitian spinUp) hA_herm hB_herm
    (gridProjector_mul_fermionicProjector spinUp) hGBG_comm heq
theorem singleAnchorPairOp_mul_perm {ι : Type*} [Fintype ι]
    (χ₀ χ₁ : ι → Fin (2 ^ 18) → ℂ) (f : ι → ι)
    (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons) :
    singleAnchorPairOp χ₀ χ₁ f i * (permutationUnitary (permElectron g)).1 =
      (permutationUnitary (permElectron g)).1 * singleAnchorPairOp χ₀ χ₁ f (g i) := by
  let U_g := (permutationUnitary (permElectron g)).1
  simp only [singleAnchorPairOp, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
  have rotAux : nSub_sp (χ₁ (f y₀)) (Finset.univ.erase i) * U_g =
      U_g * nSub_sp (χ₁ (f y₀)) (Finset.univ.erase (g i)) := by
    simp only [nSub_sp, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_bij (fun k _ ↦ g k)
      (fun k hk ↦ Finset.mem_erase.mpr
        ⟨fun h ↦ (Finset.mem_erase.mp hk).1 (g.injective h), Finset.mem_univ _⟩)
      (fun _ _ _ _ h ↦ g.injective h)
      (fun j hj ↦ ⟨g.symm j, Finset.mem_erase.mpr
        ⟨fun h ↦ (Finset.mem_erase.mp hj).1 (by rw [← h, Equiv.apply_symm_apply]),
         Finset.mem_univ _⟩, Equiv.apply_symm_apply g j⟩)
      fun k _ ↦ emb_rEl_mul_pe_sp g k _
  rw [Matrix.mul_assoc, rotAux, ← Matrix.mul_assoc, op_sp, emb_rEl_mul_pe_sp g i _,
    Matrix.mul_assoc]
  rfl
theorem sum_singleAnchorPairOp_comm_perm {ι : Type*} [Fintype ι]
    (χ₀ χ₁ : ι → Fin (2 ^ 18) → ℂ) (f : ι → ι) (g : Equiv.Perm (Fin numElectrons)) :
    (∑ i : Fin numElectrons, singleAnchorPairOp χ₀ χ₁ f i) *
    (permutationUnitary (permElectron g)).1 = (permutationUnitary (permElectron g)).1 *
    (∑ i : Fin numElectrons, singleAnchorPairOp χ₀ χ₁ f i) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Eq.trans (Finset.sum_congr rfl fun i _ ↦ singleAnchorPairOp_mul_perm χ₀ χ₁ f g i)
    (sum_perm_finset_eq Finset.univ g (fun _ ↦ by simp)
      fun i ↦ (permutationUnitary (permElectron g)).1 * singleAnchorPairOp χ₀ χ₁ f i)
end SingleAnchorFermionicPauliCap
end
end ModSingleAnchorFermionicPauliCap
section ModSlots01AndGridGuardBridge
@[expose] public section
namespace Slots01AndGridGuardBridge
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
noncomputable def ctrlInvolutionMatrix {k N : ℕ} (q : Wire N) (r : QRegister k N)
    (R : Operator (2 ^ k)) : Operator (2 ^ N) := (QRegister.singleton q).basisOutcomeProjector
    0 + (QRegister.singleton q).basisOutcomeProjector 1 * r.embedMatrix R
def elecAxisWord6 (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin 3) : Fin 64 :=
  let sm := signMagnitude x (.electron i) w
  ⟨32 * (sm.1 % 2) + sm.2 % 32, by omega⟩
private theorem lemHex2a4 (x : Fin (2 ^ systemQubits)) (a : Particle)
    (w : Fin 3) : (signMagnitude x a w).1 < 2 := by
  simp only [signMagnitude]
  omega
theorem elecAxisWord6_ne_32_of_isGridState {x : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (i : Fin numElectrons) (w : Fin 3) : (elecAxisWord6 x i w).val ≠ 32 := by
  intro h32
  apply hx (.electron i) w
  apply Prod.ext <;>
    (simp only [elecAxisWord6, signMagnitude,
      show componentBits (.electron i) - 1 = 5 by rfl, show 2 ^ 5 = 32 by rfl] at h32 ⊢; omega)
def signedMagToTwos6 (w : Fin 64) : Fin 64 :=
  if _ : w.val ≤ 32 then w else ⟨96 - w.val, by have := w.isLt; omega⟩
theorem signedMagToTwos6_involutive (w : Fin 64) :
    signedMagToTwos6 (signedMagToTwos6 w) = w := by
  have hw := w.isLt
  by_cases h : w.val ≤ 32
  · simp [signedMagToTwos6, h]
  · ext
    simp [signedMagToTwos6, h, show ¬ (96 - w.val ≤ 32) by omega]
    omega
def signedMagToTwos6Perm : Equiv.Perm (Fin 64) where
  toFun := signedMagToTwos6
  invFun := signedMagToTwos6
  left_inv := signedMagToTwos6_involutive
  right_inv := signedMagToTwos6_involutive
@[simp] theorem signedMagToTwos6Perm_apply (w : Fin 64) :
    signedMagToTwos6Perm w = signedMagToTwos6 w := rfl
def twosComp6Int (u : Fin 64) : ℤ := if u.val < 32 then (u.val : ℤ) else (u.val : ℤ) - 64
def signedMagToOffset6 (w : Fin 64) : Fin 64 :=
  ⟨((signedMagToTwos6Perm w).val + 32) % 64, by omega⟩
theorem signedMagToOffset6_eq_xor32 :
    ∀ w : Fin 64, (signedMagToOffset6 w).val = (signedMagToTwos6Perm w).val ^^^ 32 := by
  decide
theorem signedMagToOffset6_elecAxisWord6_eq_momentum {x : Fin (2 ^ systemQubits)}
    (hx : IsGridState x) (i : Fin numElectrons) (w : Fin 3) :
    ((signedMagToOffset6 (elecAxisWord6 x i w)).val : ℤ) - 32 =
      momentum x (.electron i) w := by
  have hne := elecAxisWord6_ne_32_of_isGridState hx i w
  have hs := lemHex2a4 x (.electron i) w
  have hm : (signMagnitude x (.electron i) w).2 < 32 := by
    simp only [signMagnitude, componentBits, electronBits]
    omega
  by_cases h0 : (signMagnitude x (.electron i) w).1 = 0
  · simp only [elecAxisWord6, signedMagToOffset6, signedMagToTwos6Perm_apply,
      signedMagToTwos6, momentum, h0, Nat.zero_mod, mul_zero, zero_add, Nat.mod_eq_of_lt hm]
    rw [dite_eq_left (by omega)]
    dsimp only
    omega
  · have h1 : (signMagnitude x (.electron i) w).1 = 1 := by omega
    have hgt : ¬ (32 + (signMagnitude x (.electron i) w).2 ≤ 32) := by
      simp only [elecAxisWord6, h1, Nat.one_mod, mul_one, Nat.mod_eq_of_lt hm] at hne
      omega
    simp only [elecAxisWord6, signedMagToOffset6, signedMagToTwos6Perm_apply,
      signedMagToTwos6, momentum, h1, Nat.one_mod, mul_one, Nat.mod_eq_of_lt hm]
    rw [dite_eq_right hgt]
    dsimp only
    omega
def projAxisWord8 (x : Fin (2 ^ systemQubits)) (w : Fin 3) : Fin 256 :=
  let sm := signMagnitude x .projectile w
  ⟨128 * (sm.1 % 2) + sm.2 % 128, by omega⟩
def esmSignedInt256 (w : Fin 256) : ℤ :=
  if w.val < 128 then (w.val : ℤ) else -((w.val - 128 : ℕ) : ℤ)
def signedMagToTwos8 (w : Fin 256) : Fin 256 :=
  if _ : w.val ≤ 128 then w else ⟨384 - w.val, by have := w.isLt; omega⟩
theorem signedMagToTwos8_involutive (w : Fin 256) :
    signedMagToTwos8 (signedMagToTwos8 w) = w := by
  have hw := w.isLt
  by_cases h : w.val ≤ 128
  · simp [signedMagToTwos8, h]
  · ext
    simp [signedMagToTwos8, h, show ¬ (384 - w.val ≤ 128) by omega]
    omega
def signedMagToTwos8Perm : Equiv.Perm (Fin 256) where
  toFun := signedMagToTwos8
  invFun := signedMagToTwos8
  left_inv := signedMagToTwos8_involutive
  right_inv := signedMagToTwos8_involutive
@[simp] theorem signedMagToTwos8Perm_apply (w : Fin 256) :
    signedMagToTwos8Perm w = signedMagToTwos8 w := rfl
def twosComp8Int (u : Fin 256) : ℤ := if u.val < 128 then (u.val : ℤ) else (u.val : ℤ) - 256
noncomputable def slot2Op_Uen (c : Configuration) : Operator (2 ^ systemQubits) :=
  open Classical in
  Matrix.of fun x y ↦
    if IsGridState x ∧ IsGridState y then
      ∑ i : Fin numElectrons,
        if ∀ b ≠ Particle.electron i, momentum x b = momentum y b then
          -(structureFactor c (momentum x (.electron i) - momentum y (.electron i)) *
            (coulombKernel (momentum x (.electron i) - momentum y (.electron i)) : ℂ))
        else 0
    else 0
noncomputable def slot5Op_Vep : Operator (2 ^ systemQubits) :=
  open Classical in
  Matrix.of fun x y ↦
    if IsGridState x ∧ IsGridState y then
      ∑ i : Fin numElectrons,
        if (∀ d, d ≠ Particle.electron i → d ≠ Particle.projectile →
            momentum x d = momentum y d) ∧
            momentum x (.electron i) + momentum x .projectile =
              momentum y (.electron i) + momentum y .projectile then
          -(2 : ℂ) * (coulombKernel (momentum x (.electron i) - momentum y (.electron i)) : ℂ)
        else 0
    else 0
theorem commute_fermionicProjector_of_grid_and_perm (A : Operator (2 ^ systemQubits))
    (hoff : ∀ x y, ¬ (IsGridState x ∧ IsGridState y) → A x y = 0) (hperm : ∀ (g : Equiv.Perm
    (Fin numElectrons)) x y, A (permElectron g x) (permElectron g y) = A x y)
    (spinUp : Finset (Fin numElectrons)) : A * fermionicProjector spinUp = fermionicProjector
    spinUp * A := by
  rw [fermionicProjector_eq_groupAvgProj spinUp]
  exact commutes_groupAvgProj (spinGroupAux spinUp) (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ))
    IsGridState permElectron A (commutes_predProjector_of_off_zero IsGridState A hoff) (fun g
    _ ↦ commutes_permutationUnitary_of_entry (permElectron g) A (hperm g))
end Slots01AndGridGuardBridge
end
end ModSlots01AndGridGuardBridge
section ModAnchorTwistSelect
@[expose] public section
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
namespace AnchorTwistSelect
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.FullScaleBESector
open SpecsAux.DyadicSubgridToeplitz128
open SingleAnchorFermionicPauliCap
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem swapWireZero_conj_singleAnchorPairOp {ι : Type*} [Fintype ι]
    (χ₀ χ₁ : ι → Fin (2 ^ 18) → ℂ) (f : ι → ι) (i : Fin numElectrons) :
    (Operator.permutationUnitary
    (SpecsAux.BridgeFermionicComm.SpecInner.permElectron (Equiv.swap i
    0))).1ᴴ * singleAnchorPairOp χ₀ χ₁ f 0 * (Operator.permutationUnitary
    (SpecsAux.BridgeFermionicComm.SpecInner.permElectron (Equiv.swap i
    0))).1 = singleAnchorPairOp χ₀ χ₁ f i := by
  let g := Equiv.swap i (0 : Fin numElectrons)
  let U := Operator.permutationUnitary
    (SpecsAux.BridgeFermionicComm.SpecInner.permElectron g)
  have hU : U.1ᴴ * U.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.2
  rw [Matrix.mul_assoc, singleAnchorPairOp_mul_perm χ₀ χ₁ f g 0, Equiv.swap_apply_right,
    ← Matrix.mul_assoc, hU, Matrix.one_mul]
end AnchorTwistSelect
end
end ModAnchorTwistSelect
section ModSixSlotEndpointJunctionBridge
@[expose] public section
namespace SixSlotEndpointJunctionBridge
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SingleRBEGridGuardWalk
open Slots01AndGridGuardBridge
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (elecNucOp elecProjOp
  sixChannelRaw)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable def gridValidBool (x : Fin (2 ^ systemQubits)) : Bool :=
  open Classical in decide (IsGridState x)
@[simp] theorem gridValidBool_eq_true_iff (x : Fin (2 ^ systemQubits)) :
    gridValidBool x = true ↔ IsGridState x := by
  classical
  simp [gridValidBool]
theorem diagProj_gridValidBool_eq_specsGridProjector :
    diagProj systemQubits gridValidBool = SpecsAux.gridProjector := by
  classical
  ext x y
  simp [diagProj, SpecsAux.gridProjector, gridValidBool]
theorem sixChannelGridProjector_eq_specsGridProjector :
    SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector =
      SpecsAux.gridProjector := by
  classical
  ext x y
  simp [SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector,
    SpecsAux.gridProjector]
theorem projAxisWord8_ne_128_of_isGridState {x : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (w : Fin 3) : (projAxisWord8 x w).val ≠ 128 := by
  intro h128
  apply hx .projectile w
  apply Prod.ext <;>
    (simp only [projAxisWord8, signMagnitude,
      show componentBits .projectile - 1 = 7 by rfl,
      show 2 ^ 7 = 128 by rfl] at h128 ⊢; omega)
theorem isGridState_iff_axisWords_ne_minInt (x : Fin (2 ^ systemQubits)) : IsGridState x ↔ (∀
    (i : Fin numElectrons) (w : Fin 3),(elecAxisWord6 x i w).val ≠ 32) ∧
    (∀ w : Fin 3, (projAxisWord8 x w).val ≠ 128) := by
  constructor
  · intro hx
    exact ⟨elecAxisWord6_ne_32_of_isGridState hx, projAxisWord8_ne_128_of_isGridState hx⟩
  · rintro ⟨he, hp⟩ a w
    cases a with
    | electron i =>
      intro hsm
      exact he i w (by simp [elecAxisWord6, hsm])
    | projectile =>
      intro hsm
      exact hp w (by simp [projAxisWord8, hsm])
theorem slot2Op_Uen_eq_sixChannelRaw (c : Configuration) :
    slot2Op_Uen c = sixChannelRaw c 2 := by
  classical
  ext x y
  simp only [slot2Op_Uen, sixChannelRaw, Fin.isValue, Matrix.cons_val,
    elecNucOp, Matrix.sum_apply, Matrix.of_apply]
  by_cases hx : IsGridState x
  · by_cases hy : IsGridState y
    · simp only [hx, hy, and_self, true_and, ↓reduceIte]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hc : ∀ b ≠ Particle.electron i, momentum x b = momentum y b <;>
        simp [hc, charge]
    · simp [hy]
  · simp [hx]
theorem slot5Op_Vep_eq_sixChannelRaw (c : Configuration) :
    slot5Op_Vep = sixChannelRaw c 5 := by
  classical
  ext x y
  simp only [slot5Op_Vep, sixChannelRaw, Fin.isValue, Matrix.cons_val,
    elecProjOp, Matrix.sum_apply, Matrix.of_apply]
  by_cases hx : IsGridState x
  · by_cases hy : IsGridState y
    · simp only [hx, hy, and_self, true_and, ↓reduceIte]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      split_ifs
      · push_cast; ring
      · exact Complex.ofReal_zero
    · simp [hy]
  · simp [hx]
theorem norm_fermionicProjector_le_one (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp‖ ≤ 1 :=
  SpecsAux.SpecMirror.SixChannelHamiltonianSplit.norm_projector_le_one
    (fermionicProjector spinUp)
    (SpecsAux.fermionicProjector_isHermitian spinUp)
    (fermionicProjector_idem spinUp)
noncomputable def endpointHeff (E : Fin 6 → ℝ)
    (H_branch : Fin 6 → Operator (2 ^ systemQubits)) : Operator (2 ^ systemQubits) :=
  (∑ k : Fin 6, H_branch k) +
    ((∑ k : Fin 6, E k : ℝ) : ℂ) • (1 : Operator (2 ^ systemQubits))
@[simp] theorem endpointHeff_sub_shift_eq_sum (E : Fin 6 → ℝ)
    (H_branch : Fin 6 → Operator (2 ^ systemQubits)) : endpointHeff E H_branch -
    ((∑ k : Fin 6, E k : ℝ) : ℂ) • (1 : Operator (2 ^ systemQubits)) = ∑ k : Fin 6, H_branch k
    := add_sub_cancel_right _ _
theorem isQubitizedBE_ghostZeroedBE {m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : 0 < α)
    (B_raw : Operator (2 ^ systemQubits))
    (U_raw : Unitary (2 ^ (systemQubits + m)))
    (hU_sa : U_raw.1ᴴ = U_raw.1)
    (hRawTop :
      let sys0 : QRegister systemQubits (systemQubits + m) := .block 0 systemQubits (by omega)
      let anc0 : QRegister m (systemQubits + m) := .block systemQubits m le_rfl
      anc0.basisOutcomeProjector 0 * U_raw.1 * anc0.basisOutcomeProjector 0 =
        (α : ℂ)⁻¹ •
          (anc0.basisOutcomeProjector 0 * sys0.embedMatrix B_raw * anc0.basisOutcomeProjector 0)) :
    FullScaleBESector.IsQubitizedBlockEncodingUnitary α
      (SpecsAux.gridProjector * B_raw *
        SpecsAux.gridProjector)
      (ghostZeroedBE systemQubits m hm gridValidBool U_raw) := by
  refine ⟨hα, ghostZeroedBE_conjTranspose hm gridValidBool hU_sa, ?_⟩
  let sys0 : QRegister systemQubits (systemQubits + m) := .block 0 systemQubits (by omega)
  let anc0 : QRegister m (systemQubits + m) := .block systemQubits m le_rfl
  have hBE_scaled : anc0.basisOutcomeProjector 0 * U_raw.1 * anc0.basisOutcomeProjector 0 =
      anc0.basisOutcomeProjector 0 * sys0.embedMatrix ((α : ℂ)⁻¹ • B_raw) *
      anc0.basisOutcomeProjector 0 := by
    rw [sys0.embedMatrix_smul, Matrix.mul_smul, Matrix.smul_mul]
    exact hRawTop
  have htop := ghostZeroedBE_topBlock_eq_proj_conj systemQubits m hm gridValidBool
    U_raw ((α : ℂ)⁻¹ • B_raw) hBE_scaled
  rw [diagProj_gridValidBool_eq_specsGridProjector, Matrix.mul_smul, Matrix.smul_mul,
    (sysReg systemQubits m).embedMatrix_smul, Matrix.mul_smul, Matrix.smul_mul] at htop
  exact htop
theorem commute_fermionicProjector_of_inGridPerm (B : Operator (2 ^ systemQubits)) (hperm : ∀
    (g : Equiv.Perm (Fin numElectrons)) (x y : Fin (2 ^ systemQubits)), IsGridState x →
    IsGridState y → B (permElectron g x) (permElectron g y) = B x y)
    (spinUp : Finset (Fin numElectrons)) : (SpecsAux.gridProjector * B *
    SpecsAux.gridProjector) * fermionicProjector spinUp =
    fermionicProjector spinUp * (SpecsAux.gridProjector * B *
    SpecsAux.gridProjector) := by
  let G := SpecsAux.gridProjector
  have hentry : ∀ x y : Fin (2 ^ systemQubits),
      (G * B * G) x y = open Classical in if IsGridState x ∧ IsGridState y then B x y else 0 := by
    intro x y
    classical
    simp only [G, SpecsAux.gridProjector, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    by_cases hx : IsGridState x <;> by_cases hy : IsGridState y <;> simp [hx, hy]
  apply commute_fermionicProjector_of_grid_and_perm
  · intro x y hxy
    classical
    rw [hentry]
    simp [hxy]
  · intro g x y
    classical
    rw [hentry, hentry]
    simp only [isGridState_permElectron]
    by_cases hxy : IsGridState x ∧ IsGridState y
    · simp [hxy, hperm g x y hxy.1 hxy.2]
    · simp [hxy]
end SixSlotEndpointJunctionBridge
end
end ModSixSlotEndpointJunctionBridge
section ModSlot2Slot4QuantizedChannelBridge
@[expose] public section
namespace Slot2Slot4QuantizedChannelBridge
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.DyadicSubgridToeplitz128 (NyqGrid3D64 NyqParity3D
  subGridUnitary64)
open SingleAnchorFermionicPauliCap
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem norm_le_one_of_conjTranspose_mul_self {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix α α ℂ) (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  have hsq : ‖U‖ * ‖U‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self U, hU]
    exact
      SpecsAux.SpecMirror.SixChannelHamiltonianSplit.norm_projector_le_one
      1 Matrix.isHermitian_one (Matrix.mul_one 1)
  nlinarith [norm_nonneg U]
theorem norm_diagonal_of_real_le {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hf : ∀ a, |f a| ≤ M) :
    ‖Matrix.diagonal (fun a ↦ (f a : ℂ))‖ ≤ M := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hM0).mpr fun a ↦ by simpa [Real.norm_eq_abs] using hf a
theorem norm_conj_diag_left {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix α α ℂ) (hU : Uᴴ * U = 1)
    (f : α → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hf : ∀ a, |f a| ≤ M) :
    ‖Uᴴ * Matrix.diagonal (fun a ↦ (f a : ℂ)) * U‖ ≤ M := by
  have h1 : ‖U‖ ≤ 1 := norm_le_one_of_conjTranspose_mul_self U hU
  have h2 : ‖Uᴴ‖ ≤ 1 := (Matrix.l2_opNorm_conjTranspose U).le.trans h1
  have hd : ‖Matrix.diagonal (fun a ↦ (f a : ℂ))‖ ≤ M := norm_diagonal_of_real_le f hM0 hf
  have hL : ‖Uᴴ * Matrix.diagonal (fun a ↦ (f a : ℂ))‖ ≤ M :=
    (norm_mul_le _ _).trans ((mul_le_mul h2 hd (norm_nonneg _) zero_le_one).trans (one_mul M).le)
  exact (norm_mul_le _ _).trans (by simpa using mul_le_mul hL h1 (norm_nonneg _) hM0)
theorem norm_conj_diagonal_of_real_le {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix α α ℂ) (hU_left : Uᴴ * U = 1) (_hU_right : U * Uᴴ = 1)
    (f : α → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hf : ∀ a, |f a| ≤ M) :
    ‖Uᴴ * Matrix.diagonal (fun a ↦ (f a : ℂ)) * U‖ ≤ M :=
  norm_conj_diag_left U hU_left f hM0 hf
theorem embedMatrix_sum {k n : ℕ} {α : Type*} (r : QRegister k n) (s : Finset α)
    (g : α → Operator (2 ^ k)) :
    r.embedMatrix (∑ a ∈ s, g a) = ∑ a ∈ s, r.embedMatrix (g a) :=
  r.embedMatrix_sum s g
theorem diag_sum_eq {α β : Type*} [DecidableEq α] (s : Finset β) (f : β → α → ℂ) :
    (∑ b ∈ s, Matrix.diagonal (f b)) = Matrix.diagonal (fun x ↦ ∑ b ∈ s, f b x) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, hxy]
theorem conj_sum_eq {d : ℕ} {α : Type*} (U : Operator d) (s : Finset α) (F : α → Operator d) :
    (∑ a ∈ s, Uᴴ * F a * U) = Uᴴ * (∑ a ∈ s, F a) * U := by
  rw [← Finset.sum_mul, ← Matrix.mul_sum]
theorem orthoBasis_embed_props {nSys : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : QRegister 18 nSys) (e : Fin (2 ^ 18) ≃ ι) (χ : ι → Fin (2 ^ 18) → ℂ)
    (hcomp : ∀ u v : Fin (2 ^ 18), ∑ a : ι, χ a u * star (χ a v) = if u = v then 1 else 0) :
    let U : Operator (2 ^ nSys) := r.embedMatrix (Matrix.of fun k u ↦ star (χ (e k) u))
    Uᴴ * U = 1 ∧
      ∀ a : ι, r.embedMatrix (rk1_sp (χ a)) =
        Uᴴ * r.embedMatrix (Matrix.diagonal fun k ↦ if e k = a then (1 : ℂ) else 0) * U := by
  intro U
  let V : Operator (2 ^ 18) := Matrix.of fun k u ↦ star (χ (e k) u)
  have hV_left : Vᴴ * V = 1 := by
    ext u v
    simp only [Matrix.mul_apply, Matrix.one_apply, V, Matrix.of_apply,
      Matrix.conjTranspose_apply, star_star]
    rw [Equiv.sum_comp e (fun a ↦ χ a u * star (χ a v)), hcomp u v]
  refine ⟨by
      rw [← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, hV_left, r.embedMatrix_one],
    fun a ↦ ?_⟩
  have hloc : rk1_sp (χ a) =
      Vᴴ * Matrix.diagonal (fun k ↦ if e k = a then (1 : ℂ) else 0) * V := by
    ext u v
    rw [Matrix.mul_apply]
    have hrow (k : Fin (2 ^ 18)) :
        (Vᴴ * Matrix.diagonal (fun k' ↦ if e k' = a then (1 : ℂ) else 0)) u k * V k v =
          if k = e.symm a then χ a u * star (χ a v) else 0 := by
      rw [Matrix.mul_apply]
      simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, V, Matrix.conjTranspose_apply, Matrix.of_apply, star_star]
      by_cases hk : e k = a
      · simp [show k = e.symm a by rw [← hk, Equiv.symm_apply_apply]]
      · simp [hk, show k ≠ e.symm a from fun h ↦ hk (by rw [h, Equiv.apply_symm_apply])]
    simp_rw [hrow]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, rk1_sp, Matrix.of_apply]
  rw [hloc, r.embedMatrix_mul, r.embedMatrix_mul, r.embedMatrix_conjTranspose]
theorem norm_sum_op_sp_le_of_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin (2 ^ 18) ≃ ι) (χ : ι → Fin (2 ^ 18) → ℂ)
    (_horth : ∀ a b, ∑ u : Fin (2 ^ 18), star (χ a u) * χ b u = if a = b then 1 else 0)
    (hcomp : ∀ u v : Fin (2 ^ 18), ∑ a : ι, χ a u * star (χ a v) = if u = v then 1 else 0)
    (i : Fin numElectrons) (f : ι → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hf : ∀ a, |f a| ≤ M) :
    ‖∑ a : ι, (f a : ℂ) • op_sp (χ a) i‖ ≤ M := by
  let r := rEl_sp i
  obtain ⟨hU_left, hrk⟩ := orthoBasis_embed_props r e χ hcomp
  let U : Operator (2 ^ systemQubits) := r.embedMatrix (Matrix.of fun k u ↦ star (χ (e k) u))
  have hterm (a : ι) : (f a : ℂ) • op_sp (χ a) i =
      Uᴴ * Matrix.diagonal
        (fun x ↦ if e (r.extractIndex x) = a then (f a : ℂ) else 0) * U := by
    rw [op_sp, hrk a, r.embedMatrix_diagonal, ← Matrix.smul_mul, ← Matrix.mul_smul]
    refine congrArg (fun D ↦ Uᴴ * D * U) ?_
    ext x y
    by_cases hxy : x = y <;> simp [hxy]
  simp_rw [hterm, conj_sum_eq, diag_sum_eq]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  exact norm_conj_diag_left U hU_left _ hM0 (fun _ ↦ hf _)
theorem norm_sum_pair_op_sp_le_of_orthonormal {ι : Type*} [Fintype ι]
    (e : Fin (2 ^ 18) ≃ ι) (χ₀ χ₁ : ι → Fin (2 ^ 18) → ℂ)
    (hcomp₀ : ∀ u v : Fin (2 ^ 18), ∑ a : ι, χ₀ a u * star (χ₀ a v) = if u = v then 1 else 0)
    (hcomp₁ : ∀ u v : Fin (2 ^ 18), ∑ a : ι, χ₁ a u * star (χ₁ a v) = if u = v then 1 else 0)
    {i j : Fin numElectrons} (hne : i ≠ j)
    (f : ι × ι → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hf : ∀ p, |f p| ≤ M) :
    ‖∑ a : ι, ∑ b : ι, (f (a, b) : ℂ) • (op_sp (χ₀ a) i * op_sp (χ₁ b) j)‖ ≤ M := by
  classical
  let r₀ := rEl_sp i
  let r₁ := rEl_sp j
  have hcomm_U := r₀.embedMatrix_comm_of_disjoint r₁ (rEl_disjoint_of_ne_sp hne)
  obtain ⟨hU₀_l, hrk₀⟩ := orthoBasis_embed_props r₀ e χ₀ hcomp₀
  obtain ⟨hU₁_l, hrk₁⟩ := orthoBasis_embed_props r₁ e χ₁ hcomp₁
  let V₀ : Operator (2 ^ 18) := Matrix.of fun k u ↦ star (χ₀ (e k) u)
  let V₁ : Operator (2 ^ 18) := Matrix.of fun k u ↦ star (χ₁ (e k) u)
  let U₀ : Operator (2 ^ systemQubits) := r₀.embedMatrix V₀
  let U₁ : Operator (2 ^ systemQubits) := r₁.embedMatrix V₁
  let U : Operator (2 ^ systemQubits) := U₀ * U₁
  have hU_l : Uᴴ * U = 1 := by
    calc (U₀ * U₁)ᴴ * (U₀ * U₁) = U₁ᴴ * (U₀ᴴ * U₀) * U₁ := by
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU₀_l, Matrix.mul_one, hU₁_l]
  have hterm (a b : ι) :
      (f (a, b) : ℂ) • (op_sp (χ₀ a) i * op_sp (χ₁ b) j) =
        Uᴴ * Matrix.diagonal (fun x ↦
          if e (r₀.extractIndex x) = a ∧ e (r₁.extractIndex x) = b then
            (f (a, b) : ℂ) else 0) * U := by
    let dA : Operator (2 ^ 18) := Matrix.diagonal fun k ↦ if e k = a then (1 : ℂ) else 0
    let dB : Operator (2 ^ 18) := Matrix.diagonal fun k ↦ if e k = b then (1 : ℂ) else 0
    have hmid : (U₀ᴴ * r₀.embedMatrix dA * U₀) * (U₁ᴴ * r₁.embedMatrix dB * U₁) =
        Uᴴ * (r₀.embedMatrix dA * r₁.embedMatrix dB) * U := by
      dsimp only [U, U₀, U₁]
      rw [conjTranspose_mul, ← r₀.embedMatrix_conjTranspose, ← r₁.embedMatrix_conjTranspose]
      calc (r₀.embedMatrix V₀ᴴ * r₀.embedMatrix dA * r₀.embedMatrix V₀) *
              (r₁.embedMatrix V₁ᴴ * r₁.embedMatrix dB * r₁.embedMatrix V₁)
          = (r₀.embedMatrix V₀ᴴ * r₁.embedMatrix V₁ᴴ) * r₀.embedMatrix dA *
              (r₀.embedMatrix V₀ * r₁.embedMatrix dB) * r₁.embedMatrix V₁ := by
                simp only [Matrix.mul_assoc]
                rw [← Matrix.mul_assoc (r₀.embedMatrix V₀) (r₁.embedMatrix V₁ᴴ),
                  hcomm_U V₀ V₁ᴴ]
                simp only [← Matrix.mul_assoc]
                rw [Matrix.mul_assoc (r₀.embedMatrix V₀ᴴ) (r₀.embedMatrix dA),
                  hcomm_U dA V₁ᴴ]
                simp only [Matrix.mul_assoc]
        _ = (r₁.embedMatrix V₁ᴴ * r₀.embedMatrix V₀ᴴ) *
              (r₀.embedMatrix dA * r₁.embedMatrix dB) *
              (r₀.embedMatrix V₀ * r₁.embedMatrix V₁) := by
                rw [hcomm_U V₀ᴴ V₁ᴴ, hcomm_U V₀ dB]
                simp only [Matrix.mul_assoc]
    rw [op_sp, op_sp, hrk₀ a, hrk₁ b, hmid, r₀.embedMatrix_diagonal, r₁.embedMatrix_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.smul_mul, ← Matrix.mul_smul]
    refine congrArg (fun D ↦ Uᴴ * D * U) ?_
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases ha : e (r₀.extractIndex x) = a <;>
        by_cases hb : e (r₁.extractIndex x) = b <;> simp [ha, hb]
    · simp [hxy]
  simp_rw [hterm, conj_sum_eq, diag_sum_eq]
  have hdiag (x : Fin (2 ^ systemQubits)) :
      (∑ a : ι, ∑ b : ι,
        if e (r₀.extractIndex x) = a ∧ e (r₁.extractIndex x) = b then (f (a, b) : ℂ) else 0) =
        (f (e (r₀.extractIndex x), e (r₁.extractIndex x)) : ℂ) := by
    have h1 (a : ι) : (∑ b : ι, if e (r₀.extractIndex x) = a ∧ e (r₁.extractIndex x) = b then
        (f (a, b) : ℂ) else 0) = if e (r₀.extractIndex x) = a then
        (f (a, e (r₁.extractIndex x)) : ℂ) else 0 := by
      by_cases ha : e (r₀.extractIndex x) = a <;> simp [ha]
    simp_rw [h1]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp_rw [hdiag]
  exact norm_conj_diag_left U hU_l _ hM0 (fun _ ↦ hf _)
theorem diag_pred_sandwich_apply {d : ℕ} (P : Fin d → Prop) [DecidablePred P] (M : Operator d)
    (x y : Fin d) : (Matrix.diagonal (fun z ↦ if P z then (1 : ℂ) else 0) * M *
    Matrix.diagonal (fun z ↦ if P z then (1 : ℂ) else 0)) x y =
    if P x ∧ P y then M x y else 0 := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]
theorem sum_erase_const_elec {V : Type*} [AddCommGroup V] [Module ℂ V]
    (oneV : V) (i : Fin numElectrons) :
    (∑ _j ∈ Finset.univ.erase i, oneV) = (((numElectrons : ℝ) - 1 : ℝ) : ℂ) • oneV := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  refine congrArg (fun z : ℂ ↦ z • oneV) ?_
  norm_num [numElectrons]
def signedMagToOffset6Equiv : Equiv.Perm (Fin 64) where
  toFun := Slots01AndGridGuardBridge.signedMagToOffset6
  invFun := fun u ↦ Slots01AndGridGuardBridge.signedMagToTwos6Perm
    ⟨(u.val + 32) % 64, by omega⟩
  left_inv := by decide
  right_inv := by decide
@[simp] theorem signedMagToOffset6Equiv_apply (w : Fin 64) : signedMagToOffset6Equiv w =
    Slots01AndGridGuardBridge.signedMagToOffset6 w := rfl
def u18AxisSplitEquiv : Fin (2 ^ 18) ≃ NyqGrid3D64 where
  toFun u := fun w ↦ ⟨(u.val / 2 ^ (6 * w.val)) % 64, by omega⟩
  invFun g := ⟨(g 0).val + 64 * (g 1).val + 4096 * (g 2).val, by
    have := (g 0).isLt
    have := (g 1).isLt
    have := (g 2).isLt
    omega⟩
  left_inv u := by
    have := u.isLt
    ext
    change ((u.val / 1) % 64 + 64 * ((u.val / 64) % 64) + 4096 * ((u.val / 4096) % 64)) = u.val
    omega
  right_inv g := by
    have := (g 0).isLt
    have := (g 1).isLt
    have := (g 2).isLt
    funext w
    ext
    fin_cases w <;> (dsimp; omega)
def elecOffsetGridEquiv18 : Fin (2 ^ 18) ≃ NyqGrid3D64 :=
  u18AxisSplitEquiv.trans (Equiv.arrowCongr (Equiv.refl (Fin 3)) signedMagToOffset6Equiv)
@[simp] theorem elecOffsetGridEquiv18_apply (u : Fin (2 ^ 18)) (w : Fin 3) :
    elecOffsetGridEquiv18 u w =
      Slots01AndGridGuardBridge.signedMagToOffset6
        (u18AxisSplitEquiv u w) := rfl
theorem u18AxisSplitEquiv_extractIndex_rEl_sp (x : Fin (2 ^ systemQubits))
    (i : Fin numElectrons) (w : Fin 3) : u18AxisSplitEquiv ((rEl_sp i).extractIndex x) w =
    Slots01AndGridGuardBridge.elecAxisWord6 x i w := by
  have hext_val : ((rEl_sp i).extractIndex x).val = (x.val / 2 ^ (18 * i.val)) % 2 ^ 18 := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 18
    · have hb := QRegister.basisBits_extractIndex (rEl_sp i) x ⟨k, hk⟩
      rw [basisBits_eq_testBit, basisBits_eq_testBit] at hb
      have hwire : ((rEl_sp i) ⟨k, hk⟩).val = 18 * i.val + k := rfl
      rw [hwire] at hb
      have htb : ((rEl_sp i).extractIndex x).val.testBit k =
          x.val.testBit (18 * i.val + k) := by
        cases h1 : ((rEl_sp i).extractIndex x).val.testBit k <;>
          cases h2 : x.val.testBit (18 * i.val + k) <;> simp [h1, h2] at hb ⊢
      rw [htb,
        SixChannelHamiltonianSplit.testBit_div_two_pow_mod_two_pow
          x.val (18 * i.val) 18 k hk]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ((rEl_sp i).extractIndex x).isLt
          (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by decide))
          (Nat.pow_le_pow_right (by decide) (by omega)))]
  ext
  change (((rEl_sp i).extractIndex x).val / 2 ^ (6 * w.val)) % 64 =
    (Slots01AndGridGuardBridge.elecAxisWord6 x i w).val
  rw [hext_val]
  dsimp [Slots01AndGridGuardBridge.elecAxisWord6, signMagnitude,
    bitOffset, componentBits, electronBits]
  rw [show 6 * (3 * i.val + w.val) = 18 * i.val + 6 * w.val by ring,
    Nat.pow_add, ← Nat.div_div_eq_div_mul]
  fin_cases w <;> (dsimp; omega)
open SpecsAux.DyadicSubgridToeplitz128 (shiftedFin64ToInt shiftedMom3D) in
theorem shiftedMom3D_elecOffsetGridEquiv18_extractIndex {x : Fin (2 ^ systemQubits)}
    (hx : IsGridState x) (i : Fin numElectrons) : shiftedMom3D
    (elecOffsetGridEquiv18 ((rEl_sp i).extractIndex x)) = momentum x (.electron i) := by
  funext w
  dsimp [shiftedMom3D, shiftedFin64ToInt]
  rw [elecOffsetGridEquiv18_apply, u18AxisSplitEquiv_extractIndex_rEl_sp]
  exact
    Slots01AndGridGuardBridge.signedMagToOffset6_elecAxisWord6_eq_momentum
    hx i w
theorem bitOffset_lt_sys (a : Particle) (w : Fin 3) {k : ℕ} (hk : k < componentBits a) :
    bitOffset a w + k < systemQubits := by
  cases a with
  | electron j =>
    have := j.isLt
    have := w.isLt
    dsimp [bitOffset, componentBits, electronBits, systemQubits] at hk ⊢
    omega
  | projectile =>
    have := w.isLt
    dsimp [bitOffset, componentBits, electronBits, projectileBits, numElectrons,
      systemQubits] at hk ⊢
    omega
theorem mem_rEl_bitOffset_iff (i : Fin numElectrons) (a : Particle) (w : Fin 3)
    {k : ℕ} (hk : k < componentBits a) :
    (⟨bitOffset a w + k, bitOffset_lt_sys a w hk⟩ : Wire systemQubits) ∈
        Set.range (rEl_sp i).wires ↔ a = .electron i := by
  have hmem : (⟨bitOffset a w + k, bitOffset_lt_sys a w hk⟩ : Wire systemQubits) ∈
      Set.range (rEl_sp i).wires ↔
      18 * i.val ≤ bitOffset a w + k ∧ bitOffset a w + k < 18 * i.val + 18 :=
    ⟨fun ⟨b, hb⟩ ↦ by
      have := b.isLt
      have hv := congrArg Fin.val hb
      change 18 * i.val + b.val = bitOffset a w + k at hv
      omega,
     fun h ↦ ⟨⟨bitOffset a w + k - 18 * i.val, by omega⟩,
      Fin.ext (by change 18 * i.val + (bitOffset a w + k - 18 * i.val) = bitOffset a w + k; omega)⟩⟩
  rw [hmem]
  cases a with
  | electron j =>
    have := j.isLt
    have := i.isLt
    have := w.isLt
    dsimp [bitOffset, componentBits, electronBits] at hk ⊢
    exact ⟨fun _ ↦ congrArg Particle.electron (Fin.ext (by omega)),
      fun h ↦ by have := congrArg Fin.val (Particle.electron.inj h); omega⟩
  | projectile =>
    have hi : i.val < 218 := i.isLt
    have := w.isLt
    dsimp [bitOffset, componentBits, electronBits, projectileBits, numElectrons] at hk ⊢
    exact ⟨fun _ ↦ by omega, fun h ↦ nomatch h⟩
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
    (signMagnitude_fst_eq_testBit componentBits_pos testBit_div_two_pow_mod_two_pow) in
theorem mom_eq_of_basisBits_eq {x y : Fin (2 ^ systemQubits)} {b : Particle}
    (hbb : ∀ (w : Fin 3) {k : ℕ} (hk : k < componentBits b),
      basisBits systemQubits x ⟨bitOffset b w + k, bitOffset_lt_sys b w hk⟩ =
        basisBits systemQubits y ⟨bitOffset b w + k, bitOffset_lt_sys b w hk⟩) :
    momentum x b = momentum y b := by
  funext w
  have hbits (k : ℕ) (hk : k < componentBits b) :
      x.val.testBit (bitOffset b w + k) = y.val.testBit (bitOffset b w + k) := by
    have h := hbb w hk
    rw [basisBits_eq_testBit, basisBits_eq_testBit] at h
    cases h1 : x.val.testBit (bitOffset b w + k) <;>
      cases h2 : y.val.testBit (bitOffset b w + k) <;> simp [h1, h2] at h ⊢
  have hsm : signMagnitude x b w = signMagnitude y b w := by
    apply Prod.ext
    · rw [SixChannelHamiltonianSplit.signMagnitude_fst_eq_testBit,
        SixChannelHamiltonianSplit.signMagnitude_fst_eq_testBit,
        hbits (componentBits b - 1) (by
          have := SixChannelHamiltonianSplit.componentBits_pos b
          omega)]
    · apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < componentBits b - 1
      · simpa only [signMagnitude,
          SixChannelHamiltonianSplit.testBit_div_two_pow_mod_two_pow _ _ _ _ hk] using
          hbits k (by omega)
      · dsimp only [signMagnitude]
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_le_pow_right (by decide) (by omega)))]
  simp [momentum, hsm]
theorem agreeOutside_rEl_sp_iff_momentum {x y : Fin (2 ^ systemQubits)}
    (hx : IsGridState x) (hy : IsGridState y) (i : Fin numElectrons) :
    (rEl_sp i).AgreeOutside x y ↔ ∀ b ≠ Particle.electron i, momentum x b = momentum y b := by
  refine ⟨fun hao b hb ↦ mom_eq_of_basisBits_eq fun w _ hk ↦
    hao _ (mt (mem_rEl_bitOffset_iff i b w hk).mp hb), fun hmom q hq ↦ ?_⟩
  obtain ⟨a, w, k, hk, hqval⟩ :=
    SixChannelHamiltonianSplit.exists_particle_field_of_lt
      q.val q.isLt
  have hq_eq : q = ⟨bitOffset a w + k, bitOffset_lt_sys a w hk⟩ := Fin.ext hqval
  have hne : a ≠ .electron i :=
    fun ha ↦ hq (hq_eq ▸ (mem_rEl_bitOffset_iff i a w hk).mpr ha)
  rw [basisBits_eq_testBit, basisBits_eq_testBit, hqval,
    SixChannelHamiltonianSplit.testBit_eq_of_signMagnitude_eq
      x y a w
      (SixChannelHamiltonianSplit.signMagnitude_eq_of_momentum_eq_of_isGridState
        hx hy a w (congrFun (hmom a hne) w)) k hk]
def AgreeOutsidePair (i j : Fin numElectrons) (x y : Fin (2 ^ systemQubits)) : Prop := ∀ q :
    Wire systemQubits, q ∉ Set.range (rEl_sp i).wires → q ∉ Set.range (rEl_sp j).wires →
    basisBits systemQubits x q = basisBits systemQubits y q
open Classical in
theorem embedMatrix_rEl_mul_apply_of_ne {i j : Fin numElectrons} (hne : i ≠ j)
    (A B : Operator (2 ^ 18)) (x y : Fin (2 ^ systemQubits)) :
    ((rEl_sp i).embedMatrix A * (rEl_sp j).embedMatrix B) x y = if AgreeOutsidePair i j x y
    then A ((rEl_sp i).extractIndex x) ((rEl_sp i).extractIndex y) * B
    ((rEl_sp j).extractIndex x) ((rEl_sp j).extractIndex y) else 0 := by
  have hdisj := rEl_disjoint_of_ne_sp hne
  have hnot_both (q : Wire systemQubits) :
      q ∈ Set.range (rEl_sp i).wires → q ∈ Set.range (rEl_sp j).wires → False := by
    rintro ⟨b₁, rfl⟩ ⟨b₂, hb₂⟩
    exact (QRegister.disjoint_iff.mp hdisj) b₁ b₂ hb₂.symm
  rw [Matrix.mul_apply]
  by_cases hp : AgreeOutsidePair i j x y
  · simp only [hp, ↓reduceIte]
    let z₀ : Fin (2 ^ systemQubits) := (rEl_sp i).replaceIndex x ((rEl_sp i).extractIndex y)
    have hao_i : (rEl_sp i).AgreeOutside x z₀ := fun q hq ↦
      (QRegister.basisBits_replaceIndex_of_not_mem (rEl_sp i) x _ q hq).symm
    have hao_j : (rEl_sp j).AgreeOutside z₀ y := fun q hqj ↦ by
      by_cases hqi : q ∈ Set.range (rEl_sp i).wires
      · obtain ⟨b, rfl⟩ := hqi
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
      · rw [QRegister.basisBits_replaceIndex_of_not_mem (rEl_sp i) x _ q hqi]
        exact hp q hqi hqj
    rw [Finset.sum_eq_single z₀]
    · simp only [QRegister.embedMatrix_apply_of_agreeOutside, hao_i, hao_j, ↓reduceIte]
      dsimp only [z₀]
      rw [QRegister.extractIndex_replaceIndex,
        QRegister.extractIndex_replaceIndex_of_disjoint (rEl_sp j) (rEl_sp i) hdisj.symm]
      ring
    · intro z _ hzne
      rw [QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside]
      by_cases h1 : (rEl_sp i).AgreeOutside x z
      · by_cases h2 : (rEl_sp j).AgreeOutside z y
        · refine (hzne ((basisBitsEquiv systemQubits).injective (funext fun q ↦ ?_))).elim
          change basisBits systemQubits z q = basisBits systemQubits z₀ q
          by_cases hqi : q ∈ Set.range (rEl_sp i).wires
          · obtain ⟨b, rfl⟩ := hqi
            rw [h2 _ (hnot_both _ ⟨b, rfl⟩), QRegister.basisBits_replaceIndex_apply,
              QRegister.basisBits_extractIndex]
          · rw [← h1 q hqi, QRegister.basisBits_replaceIndex_of_not_mem (rEl_sp i) x _ q hqi]
        · simp [h1, h2]
      · simp [h1]
    · exact fun hnot ↦ (hnot (Finset.mem_univ z₀)).elim
  · simp only [hp, ↓reduceIte]
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    rw [QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside]
    by_cases h1 : (rEl_sp i).AgreeOutside x z
    · by_cases h2 : (rEl_sp j).AgreeOutside z y
      · exact (hp fun q hqi hqj ↦ (h1 q hqi).trans (h2 q hqj)).elim
      · simp [h1, h2]
    · simp [h1]
theorem agreeOutsidePair_iff_momentum {x y : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (hy : IsGridState y) (i j : Fin numElectrons) : AgreeOutsidePair i j x y ↔ ∀ d, d ≠
    Particle.electron i → d ≠ Particle.electron j → momentum x d = momentum y d := by
  refine ⟨fun hao d hdi hdj ↦ mom_eq_of_basisBits_eq fun w _ hk ↦
    hao _ (mt (mem_rEl_bitOffset_iff i d w hk).mp hdi)
      (mt (mem_rEl_bitOffset_iff j d w hk).mp hdj), fun hmom q hqi hqj ↦ ?_⟩
  obtain ⟨a, w, k, hk, hqval⟩ :=
    SixChannelHamiltonianSplit.exists_particle_field_of_lt
      q.val q.isLt
  have hq_eq : q = ⟨bitOffset a w + k, bitOffset_lt_sys a w hk⟩ := Fin.ext hqval
  have h1 : a ≠ .electron i :=
    fun ha ↦ hqi (hq_eq ▸ (mem_rEl_bitOffset_iff i a w hk).mpr ha)
  have h2 : a ≠ .electron j :=
    fun ha ↦ hqj (hq_eq ▸ (mem_rEl_bitOffset_iff j a w hk).mpr ha)
  rw [basisBits_eq_testBit, basisBits_eq_testBit, hqval,
    SixChannelHamiltonianSplit.testBit_eq_of_signMagnitude_eq
      x y a w
      (SixChannelHamiltonianSplit.signMagnitude_eq_of_momentum_eq_of_isGridState
        hx hy a w (congrFun (hmom a h1 h2) w)) k hk]
noncomputable def veeSubGridKet (b : NyqParity3D) (y : NyqGrid3D64) (u : Fin (2 ^ 18)) : ℂ :=
  star (subGridUnitary64 b y (elecOffsetGridEquiv18 u))
open SpecsAux.DyadicSubgridToeplitz128 (shiftedMom3D oneElectronPhase) in
noncomputable def uenSubGridKet (c : Configuration) (l : Fin 216)
    (b : NyqParity3D) (y : NyqGrid3D64) (u : Fin (2 ^ 18)) : ℂ :=
  oneElectronPhase (c.nuclei l) (shiftedMom3D (elecOffsetGridEquiv18 u)) * veeSubGridKet b y u
open SpecsAux.DyadicSubgridToeplitz128 (subGridUnitary64_mul_conjTranspose) in
theorem veeSubGridKet_orthonormal (b : NyqParity3D) (y₁ y₂ : NyqGrid3D64) : (∑ u : Fin (2 ^
    18), star (veeSubGridKet b y₁ u) * veeSubGridKet b y₂ u) = if y₁ = y₂ then 1 else 0 := by
  have h1 (u : Fin (2 ^ 18)) : star (veeSubGridKet b y₁ u) * veeSubGridKet b y₂ u =
      subGridUnitary64 b y₁ (elecOffsetGridEquiv18 u) *
        (subGridUnitary64 b)ᴴ (elecOffsetGridEquiv18 u) y₂ := by simp [veeSubGridKet]
  simp_rw [h1]
  rw [Equiv.sum_comp elecOffsetGridEquiv18
    (fun p ↦ subGridUnitary64 b y₁ p * (subGridUnitary64 b)ᴴ p y₂)]
  simpa only [Matrix.mul_apply, Matrix.one_apply] using
    congrFun (congrFun (subGridUnitary64_mul_conjTranspose b) y₁) y₂
theorem veeSubGridKet_norm_sq (b : NyqParity3D) (y : NyqGrid3D64) :
    (∑ u : Fin (2 ^ 18), star (veeSubGridKet b y u) * veeSubGridKet b y u) = 1 := by
  simpa using veeSubGridKet_orthonormal b y y
open SpecsAux.DyadicSubgridToeplitz128 (conjTranspose_mul_subGridUnitary64) in
theorem veeSubGridKet_complete (b : NyqParity3D) (u v : Fin (2 ^ 18)) : (∑ y : NyqGrid3D64,
    veeSubGridKet b y u * star (veeSubGridKet b y v)) = if u = v then 1 else 0 := by
  have h1 (y : NyqGrid3D64) : veeSubGridKet b y u * star (veeSubGridKet b y v) =
      (subGridUnitary64 b)ᴴ (elecOffsetGridEquiv18 u) y *
        subGridUnitary64 b y (elecOffsetGridEquiv18 v) := by simp [veeSubGridKet]
  simp_rw [h1]
  have hmul := congrFun (congrFun (conjTranspose_mul_subGridUnitary64 b)
    (elecOffsetGridEquiv18 u)) (elecOffsetGridEquiv18 v)
  rw [Matrix.mul_apply, Matrix.one_apply] at hmul
  exact hmul.trans (if_congr elecOffsetGridEquiv18.injective.eq_iff rfl rfl)
open SpecsAux.DyadicSubgridToeplitz128 (shiftedMom3D oneElectronPhase
  oneElectronPhase_mul_star) in
theorem uenSubGridKet_orthonormal (c : Configuration) (l : Fin 216) (b : NyqParity3D)
    (y₁ y₂ : NyqGrid3D64) : (∑ u : Fin (2 ^ 18), star (uenSubGridKet c l b y₁ u) *
    uenSubGridKet c l b y₂ u) = if y₁ = y₂ then 1 else 0 := by
  have h1 (u : Fin (2 ^ 18)) : star (uenSubGridKet c l b y₁ u) * uenSubGridKet c l b y₂ u =
      star (veeSubGridKet b y₁ u) * veeSubGridKet b y₂ u := by
    have hp := oneElectronPhase_mul_star (c.nuclei l)
      (shiftedMom3D (elecOffsetGridEquiv18 u)) (shiftedMom3D (elecOffsetGridEquiv18 u))
    rw [sub_self, show oneElectronPhase (c.nuclei l) 0 = 1 by
      simp [oneElectronPhase, waveVector, dotProduct]] at hp
    dsimp only [uenSubGridKet]
    rw [star_mul]
    linear_combination (star (veeSubGridKet b y₁ u) * veeSubGridKet b y₂ u) * hp
  simp_rw [h1]
  exact veeSubGridKet_orthonormal b y₁ y₂
open SpecsAux.DyadicSubgridToeplitz128 (shiftedMom3D oneElectronPhase
  oneElectronPhase_mul_star) in
theorem uenSubGridKet_complete (c : Configuration) (l : Fin 216) (b : NyqParity3D)
    (u v : Fin (2 ^ 18)) : (∑ y : NyqGrid3D64, uenSubGridKet c l b y u * star (uenSubGridKet c
    l b y v)) = if u = v then 1 else 0 := by
  have h1 (y : NyqGrid3D64) : uenSubGridKet c l b y u * star (uenSubGridKet c l b y v) =
      oneElectronPhase (c.nuclei l)
          (shiftedMom3D (elecOffsetGridEquiv18 u) - shiftedMom3D (elecOffsetGridEquiv18 v)) *
        (veeSubGridKet b y u * star (veeSubGridKet b y v)) := by
    dsimp only [uenSubGridKet]
    rw [star_mul, ← oneElectronPhase_mul_star]
    ring
  simp_rw [h1, ← Finset.mul_sum, veeSubGridKet_complete]
  by_cases huv : u = v <;> simp [huv, oneElectronPhase, waveVector, dotProduct]
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 omega128 nyquist128Char3D
  dualWeight128Fine coulombDual128Real) in
theorem coulombDual128Real_eq_w128Dual (d : NyqFine3D128) :
    coulombDual128Real d = Dyadic128CoulombMath.w128Dual d := by
  have hbox : SpecsAux.DyadicSubgridToeplitz128.openBox3D62 =
      Dyadic128CoulombMath.momentumTransferBox62 := by
    ext ν
    rw [SpecsAux.DyadicSubgridToeplitz128.mem_openBox3D62_iff,
      Dyadic128CoulombMath.mem_momentumTransferBox62]
  unfold coulombDual128Real dualWeight128Fine
    Dyadic128CoulombMath.w128Dual
  rw [hbox, Complex.re_sum]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  have hchar : star (nyquist128Char3D ν d) =
      Complex.exp (-(2 * π * (∑ w : Fin 3, (ν w : ℝ) * (d w).val) / 128 : ℝ) * Complex.I) := by
    rw [SpecsAux.DyadicSubgridToeplitz128.star_nyquist128Char3D]
    unfold nyquist128Char3D omega128
    rw [← Complex.exp_sum]
    refine congrArg Complex.exp ?_
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [Pi.neg_apply]
    push_cast
    ring
  rw [hchar, Complex.re_ofReal_mul]
  exact congrArg _ (by simpa [Real.cos_neg] using
    Complex.exp_ofReal_mul_I_re (-(2 * π * (∑ w : Fin 3, (ν w : ℝ) * (d w).val) / 128 : ℝ)))
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 coulombDual128Real) in
theorem coulombDual128Real_eq_orbit (d : NyqFine3D128) : coulombDual128Real d =
    Dyadic128CoulombMath.w128Orbit
    (Dyadic128CoulombMath.tetRank65
    (Dyadic128CoulombMath.canonTriple128 d)) :=
    (coulombDual128Real_eq_w128Dual d).trans
    (Dyadic128CoulombMath.w128Dual_eq_orbit d)
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 nyq128Equiv3D) in
noncomputable def uenSubGridRaw (c : Configuration) (K128 : NyqFine3D128 → ℝ) : Operator
    (2 ^ systemQubits) := (-((1 / 8 : ℝ) : ℂ)) • ∑ l : Fin 216, ∑ b : NyqParity3D, ∑ y :
    NyqGrid3D64, (K128 (nyq128Equiv3D (y, b)) : ℂ) • nTot_sp (uenSubGridKet c l b y)
noncomputable def uenMidpointShift (kCut kMin : NyqParity3D → ℝ) : ℝ :=
  -((numElectrons : ℝ) * 216 / 8) * ∑ b : NyqParity3D, (kCut b + kMin b) / 2
open SpecsAux.DyadicSubgridToeplitz128 (uEnManyBody) in
theorem uEnManyBody_eq_sixChannelRaw (c : Configuration) :
    uEnManyBody c =
      SpecsAux.SpecMirror.SixChannelHamiltonianSplit.sixChannelRaw c 2 := by
  classical
  ext x y
  dsimp only [uEnManyBody, Matrix.of_apply,
    SpecsAux.SpecMirror.SixChannelHamiltonianSplit.sixChannelRaw,
    Matrix.cons_val,
      SpecsAux.SpecMirror.SixChannelHamiltonianSplit.elecNucOp]
  rw [Matrix.sum_apply]
  simp only [Matrix.of_apply]
  by_cases hxy : IsGridState x ∧ IsGridState y
  · rcases hxy with ⟨hx, hy⟩
    simp only [hx, hy, true_and, and_self, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs
    · simp only [charge]
      push_cast
      ring
    · rfl
  · simp only [hxy, ↓reduceIte]
    exact (Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hxy ⟨h.1, h.2.1⟩).symm
theorem pull_sum4 {α β γ δ : Type*} (sA : Finset α) (sB : Finset β) (sC : Finset γ)
    (sI : Finset δ) (c : ℂ) (w : β → γ → ℂ) (g : α → β → γ → δ → ℂ) :
    c * (∑ a ∈ sA, ∑ b ∈ sB, ∑ y ∈ sC, w b y * ∑ i ∈ sI, g a b y i) =
      ∑ i ∈ sI, ∑ a ∈ sA, ∑ b ∈ sB, ∑ y ∈ sC, c * (w b y * g a b y i) := by
  simp_rw [Finset.mul_sum]
  have h1 (a : α) (b : β) :
      (∑ y ∈ sC, ∑ i ∈ sI, c * (w b y * g a b y i)) =
        ∑ i ∈ sI, ∑ y ∈ sC, c * (w b y * g a b y i) := Finset.sum_comm
  have h2 (a : α) :
      (∑ b ∈ sB, ∑ i ∈ sI, ∑ y ∈ sC, c * (w b y * g a b y i)) =
        ∑ i ∈ sI, ∑ b ∈ sB, ∑ y ∈ sC, c * (w b y * g a b y i) := Finset.sum_comm
  simp_rw [h1, h2]
  exact Finset.sum_comm
open SpecsAux.DyadicSubgridToeplitz128 (nyq128Equiv3D
  inMomGrid3D_electron_of_state subGridElem64_3D dualWeight128 subGridAvgToeplitz128_eq_openBox
  coulombDual128Real ofReal_coulombDual128Real oneElectronPhase oneElectronPhase_mul_star
  uEnManyBody) in
theorem gridSandwich_uenSubGridRaw_coulomb_eq (c : Configuration) : SpecsAux.gridProjector *
    uenSubGridRaw c coulombDual128Real * SpecsAux.gridProjector = uEnManyBody c := by
  classical
  ext x y
  rw [show SpecsAux.gridProjector = Matrix.diagonal (fun z ↦ if IsGridState z then (1 : ℂ) else 0)
    from rfl, diag_pred_sandwich_apply]
  by_cases hgrid : IsGridState x ∧ IsGridState y
  · rcases hgrid with ⟨hx, hy⟩
    dsimp only [uEnManyBody, Matrix.of_apply]
    rw [ite_eq_left ⟨hx, hy⟩, ite_eq_left ⟨hx, hy⟩]
    simp only [uenSubGridRaw, nTot_sp, nSub_sp, op_sp, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul]
    rw [pull_sum4]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hao_iff := agreeOutside_rEl_sp_iff_momentum hx hy i
    by_cases hmom : ∀ b ≠ Particle.electron i, momentum x b = momentum y b
    · rw [ite_eq_left hmom]
      have hao : (rEl_sp i).AgreeOutside x y := hao_iff.mpr hmom
      let px := momentum x (.electron i)
      let py := momentum y (.electron i)
      have hpx := shiftedMom3D_elecOffsetGridEquiv18_extractIndex hx i
      have hpy := shiftedMom3D_elecOffsetGridEquiv18_extractIndex hy i
      have hket (l : Fin 216) (b : NyqParity3D) (y₀ : NyqGrid3D64) :
          (-((1 / 8 : ℝ) : ℂ)) * ((coulombDual128Real (nyq128Equiv3D (y₀, b)) : ℂ) *
            ((rEl_sp i).embedMatrix (rk1_sp (uenSubGridKet c l b y₀))) x y) =
          (-oneElectronPhase (c.nuclei l) (px - py)) * ((1 / 8 : ℂ) *
            (star (subGridElem64_3D b y₀ px) *
              dualWeight128 (fun ν ↦ (coulombKernel ν : ℂ)) b y₀ *
              subGridElem64_3D b y₀ py)) := by
        rw [QRegister.embedMatrix_apply_of_agreeOutside, ite_eq_left hao,
          ofReal_coulombDual128Real]
        unfold rk1_sp uenSubGridKet veeSubGridKet subGridUnitary64 dualWeight128
        simp only [Matrix.of_apply, star_mul, star_star, hpx, hpy]
        rw [← oneElectronPhase_mul_star]
        push_cast
        ring
      have havg : (1 / 8 : ℂ) * (∑ b : NyqParity3D, ∑ y₀ : NyqGrid3D64, star (subGridElem64_3D
          b y₀ px) * dualWeight128 (fun ν ↦ (coulombKernel ν : ℂ)) b y₀ * subGridElem64_3D b
          y₀ py) = (coulombKernel (px - py) : ℂ) := subGridAvgToeplitz128_eq_openBox
          (fun ν ↦ (coulombKernel ν : ℂ)) (inMomGrid3D_electron_of_state x i)
          (inMomGrid3D_electron_of_state y i)
      simp_rw [hket, ← Finset.mul_sum]
      rw [← Finset.sum_mul, havg, Finset.sum_neg_distrib, neg_mul]
      rfl
    · rw [ite_eq_right hmom]
      refine Finset.sum_eq_zero fun l _ ↦ Finset.sum_eq_zero fun b _ ↦
        Finset.sum_eq_zero fun y₀ _ ↦ ?_
      rw [QRegister.embedMatrix_apply_of_agreeOutside, ite_eq_right (mt hao_iff.mp hmom)]
      ring
  · dsimp only [uEnManyBody, Matrix.of_apply]
    rw [ite_eq_right hgrid, ite_eq_right hgrid]
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 nyq128Equiv3D) in
theorem norm_uenSubGridRaw_sub_le (c : Configuration) (K₁ K₂ : NyqFine3D128 → ℝ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hK : ∀ d, |K₁ d - K₂ d| ≤ δ) :
    ‖uenSubGridRaw c K₁ - uenSubGridRaw c K₂‖ ≤ 47088 * δ := by
  have hdiff : uenSubGridRaw c K₁ - uenSubGridRaw c K₂ = (-((1 / 8 : ℝ) : ℂ)) • ∑ l : Fin 216,
      ∑ b : NyqParity3D, ∑ i : Fin numElectrons, ∑ y : NyqGrid3D64,
      ((K₁ (nyq128Equiv3D (y, b)) - K₂ (nyq128Equiv3D (y, b)) : ℝ) : ℂ) • op_sp
      (uenSubGridKet c l b y) i := by
    unfold uenSubGridRaw nTot_sp nSub_sp
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun l _ ↦ ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_smul, ← Complex.ofReal_sub, Finset.smul_sum]
    exact Finset.sum_comm
  rw [hdiff, norm_smul, show ‖(-((1 / 8 : ℝ) : ℂ))‖ = (1 / 8 : ℝ) by norm_num]
  have hsum : ‖∑ l : Fin 216, ∑ b : NyqParity3D, ∑ i : Fin numElectrons, ∑ y : NyqGrid3D64,
      ((K₁ (nyq128Equiv3D (y, b)) - K₂ (nyq128Equiv3D (y, b)) : ℝ) : ℂ) • op_sp
      (uenSubGridKet c l b y) i‖ ≤ ∑ _l : Fin 216, ∑ _b : NyqParity3D, ∑ _i : Fin numElectrons,
      δ :=
    (norm_sum_le _ _).trans <| Finset.sum_le_sum fun l _ ↦
      (norm_sum_le _ _).trans <| Finset.sum_le_sum fun b _ ↦
        (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ ↦
          norm_sum_op_sp_le_of_orthonormal elecOffsetGridEquiv18 (uenSubGridKet c l b)
            (uenSubGridKet_orthonormal c l b) (uenSubGridKet_complete c l b) i
            (fun y ↦ K₁ (nyq128Equiv3D (y, b)) - K₂ (nyq128Equiv3D (y, b))) hδ0
            (fun y ↦ hK (nyq128Equiv3D (y, b)))
  have hcard : Fintype.card NyqParity3D = 8 := by decide
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hcard, numElectrons,
    nsmul_eq_mul, Nat.cast_ofNat] at hsum
  linarith
open SpecsAux.DyadicSubgridToeplitz128 (nyq128Equiv3D nyq128Equiv3D_val
  anchorParity1D anchorParity3D) in
theorem anchorParity3D_nyq128Equiv3D (b₀ dp : NyqParity3D) (dy : NyqGrid3D64) :
    anchorParity3D b₀ (nyq128Equiv3D (dy, dp)) = anchorParity3D b₀ (nyq128Equiv3D (0, dp)) := by
  funext w
  ext
  dsimp only [anchorParity3D, anchorParity1D]
  rw [nyq128Equiv3D_val, nyq128Equiv3D_val, show ((0 : NyqGrid3D64) w).val = 0 from rfl]
  omega
open SpecsAux.DyadicSubgridToeplitz128 (nyq128Equiv3D nyq128Equiv3D_val
  anchorSubTarget1D_fst_eq_borrow anchorSubTarget3D) in
theorem anchorSubTarget3D_fst_val (b₀ dp : NyqParity3D) (y₀ dy : NyqGrid3D64) (w : Fin 3) :
    ((anchorSubTarget3D y₀ b₀ (nyq128Equiv3D (dy, dp))).1 w).val =
      ((y₀ w).val + 64 - (dy w).val - (1 - (b₀ w).val) * (dp w).val) % 64 := by
  have hfst := congrArg Fin.val
    (anchorSubTarget1D_fst_eq_borrow (y₀ w) (b₀ w) (nyq128Equiv3D (dy, dp) w))
  dsimp only [anchorSubTarget3D] at hfst ⊢
  rw [nyq128Equiv3D_val] at hfst
  rw [hfst]
  have := (dy w).isLt
  have := (y₀ w).isLt
  rcases b₀ w with ⟨bv, hb0⟩
  rcases dp w with ⟨pv, hdp⟩
  dsimp only
  interval_cases bv <;> interval_cases pv <;> omega
open SpecsAux.DyadicSubgridToeplitz128 (nyq128Equiv3D anchorSubTarget3D) in
def anchorSubTargetEquiv (b₀ dp : NyqParity3D) (y₀ : NyqGrid3D64) :
    NyqGrid3D64 ≃ NyqGrid3D64 where
  toFun dy := (anchorSubTarget3D y₀ b₀ (nyq128Equiv3D (dy, dp))).1
  invFun y₁ := fun w ↦
    ⟨((y₀ w).val + 64 - (y₁ w).val - (1 - (b₀ w).val) * (dp w).val) % 64, by omega⟩
  left_inv dy := by
    funext w
    ext
    dsimp only
    rw [anchorSubTarget3D_fst_val]
    have := (dy w).isLt
    have := (y₀ w).isLt
    rcases b₀ w with ⟨bv, hb0⟩
    rcases dp w with ⟨pv, hdp⟩
    dsimp only
    interval_cases bv <;> interval_cases pv <;> omega
  right_inv y₁ := by
    funext w
    ext
    rw [anchorSubTarget3D_fst_val]
    dsimp only
    have := (y₁ w).isLt
    have := (y₀ w).isLt
    rcases b₀ w with ⟨bv, hb0⟩
    rcases dp w with ⟨pv, hdp⟩
    dsimp only
    interval_cases bv <;> interval_cases pv <;> omega
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 anchorParity3D
  anchorSubTarget3D) in
noncomputable def veeSingleAnchorRaw (K128 : NyqFine3D128 → ℝ) : Operator (2 ^ systemQubits)
    := ((1 / 128 : ℝ) : ℂ) • ∑ b₀ : NyqParity3D, ∑ d : NyqFine3D128, (K128 d : ℂ) • ∑ i : Fin
    numElectrons, singleAnchorPairOp (veeSubGridKet b₀) (veeSubGridKet (anchorParity3D b₀ d))
    (fun y₀ ↦ (anchorSubTarget3D y₀ b₀ d).1) i
noncomputable def veeMidpointShift (kCut kMin : NyqParity3D → ℝ) : ℝ :=
  (((numElectrons : ℝ) * ((numElectrons : ℝ) - 1)) / 16) *
    ∑ b : NyqParity3D, (kCut b + kMin b) / 2
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 kHead128) in
noncomputable def veeCenteredShift (K128 : NyqFine3D128 → ℝ) (kCut kMin : NyqParity3D → ℝ)
    (H_fine : Finset NyqFine3D128) : ℝ :=
  ((numElectrons : ℝ) / 16) * (∑ d ∈ H_fine, kHead128 K128 kCut d) + veeMidpointShift kCut kMin
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128) in
theorem veeSingleAnchorRaw_comm_perm (K128 : NyqFine3D128 → ℝ)
    (g : Equiv.Perm (Fin numElectrons)) :
    veeSingleAnchorRaw K128 * (permutationUnitary (permElectron g)).1 =
      (permutationUnitary (permElectron g)).1 * veeSingleAnchorRaw K128 := by
  unfold veeSingleAnchorRaw
  rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Matrix.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun b₀ _ ↦ ?_)
  rw [Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, sum_singleAnchorPairOp_comm_perm]
theorem singleAnchorPairOp_apply_ite {χ₀ χ₁ : NyqGrid3D64 → Fin (2 ^ 18) → ℂ}
    (f : NyqGrid3D64 → NyqGrid3D64) (i : Fin numElectrons) (x y : Fin (2 ^ systemQubits)) :
    singleAnchorPairOp χ₀ χ₁ f i x y = ∑ y₀ : NyqGrid3D64, ∑ j : Fin numElectrons,
      if i ≠ j then (op_sp (χ₀ y₀) i * op_sp (χ₁ (f y₀)) j) x y else 0 := by
  classical
  unfold singleAnchorPairOp nSub_sp
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
  rw [Matrix.mul_sum, Matrix.sum_apply, ← Finset.sum_filter]
  refine Finset.sum_congr (by ext j; simp [ne_comm]) fun _ _ ↦ rfl
open SpecsAux.DyadicSubgridToeplitz128 (vEeManyBody) in
theorem vEeManyBody_eq_sixChannelRaw (c : Configuration) :
    vEeManyBody =
      SpecsAux.SpecMirror.SixChannelHamiltonianSplit.sixChannelRaw c 4 := by
  classical
  ext x y
  dsimp only [vEeManyBody, Matrix.of_apply,
    SpecsAux.SpecMirror.SixChannelHamiltonianSplit.sixChannelRaw,
    Matrix.cons_val,
      SpecsAux.SpecMirror.SixChannelHamiltonianSplit.elecElecOp]
  rw [Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, Matrix.of_apply]
  by_cases hxy : IsGridState x ∧ IsGridState y
  · rcases hxy with ⟨hx, hy⟩
    simp only [hx, hy, true_and, and_self, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · push_cast
      ring
    · rfl
  · simp only [hxy, ↓reduceIte]
    exact (Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦
      ite_eq_right fun h ↦ hxy ⟨h.1, h.2.1⟩).symm
theorem pull_sum_vee {α β γ δ : Type*} (sB : Finset α) (sD : Finset β) (sI : Finset γ)
    (sY : Finset δ) (c : ℂ) (w : β → ℂ) (g : α → β → γ → δ → γ → ℂ) :
    c * (∑ b₀ ∈ sB, ∑ d ∈ sD, w d * ∑ i ∈ sI, ∑ y₀ ∈ sY, ∑ j ∈ sI, g b₀ d i y₀ j) =
      ∑ i ∈ sI, ∑ j ∈ sI, ∑ b₀ ∈ sB, ∑ d ∈ sD, w d * ∑ y₀ ∈ sY, c * g b₀ d i y₀ j := by
  simp_rw [Finset.mul_sum]
  have h_yj (b₀ : α) (d : β) (i : γ) :
      (∑ y₀ ∈ sY, ∑ j ∈ sI, c * (w d * g b₀ d i y₀ j)) =
        ∑ j ∈ sI, ∑ y₀ ∈ sY, w d * (c * g b₀ d i y₀ j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  simp_rw [h_yj]
  have h_d (b₀ : α) :
      (∑ d ∈ sD, ∑ i ∈ sI, ∑ j ∈ sI, ∑ y₀ ∈ sY, w d * (c * g b₀ d i y₀ j)) =
        ∑ i ∈ sI, ∑ j ∈ sI, ∑ d ∈ sD, ∑ y₀ ∈ sY, w d * (c * g b₀ d i y₀ j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  simp_rw [h_d]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 anchorParity3D
  anchorSubTarget3D inMomGrid3D_electron_of_state subGridElem64_3D dualWeight128Fine
  coulombDual128Real ofReal_coulombDual128Real singleAnchorPairSubElem128
  singleAnchorPairSubElem128_dualWeight128_eq vEeManyBody) in
theorem gridSandwich_veeSingleAnchorRaw_coulomb_eq : SpecsAux.gridProjector *
    veeSingleAnchorRaw coulombDual128Real * SpecsAux.gridProjector = vEeManyBody := by
  classical
  ext x y
  rw [show SpecsAux.gridProjector = Matrix.diagonal (fun z ↦ if IsGridState z then (1 : ℂ) else 0)
    from rfl, diag_pred_sandwich_apply]
  by_cases hgrid : IsGridState x ∧ IsGridState y
  · rcases hgrid with ⟨hx, hy⟩
    dsimp only [vEeManyBody, Matrix.of_apply]
    rw [ite_eq_left ⟨hx, hy⟩, ite_eq_left ⟨hx, hy⟩]
    simp only [veeSingleAnchorRaw, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      singleAnchorPairOp_apply_ite]
    rw [pull_sum_vee]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hij : i ≠ j
    · have hao_iff := agreeOutsidePair_iff_momentum hx hy i j
      by_cases hspec : ∀ d, d ≠ Particle.electron i → d ≠ Particle.electron j →
          momentum x d = momentum y d
      · have hao : AgreeOutsidePair i j x y := hao_iff.mpr hspec
        let pᵢ := momentum x (.electron i)
        let qᵢ := momentum y (.electron i)
        let pⱼ := momentum x (.electron j)
        let qⱼ := momentum y (.electron j)
        have hpᵢ := shiftedMom3D_elecOffsetGridEquiv18_extractIndex hx i
        have hqᵢ := shiftedMom3D_elecOffsetGridEquiv18_extractIndex hy i
        have hpⱼ := shiftedMom3D_elecOffsetGridEquiv18_extractIndex hx j
        have hqⱼ := shiftedMom3D_elecOffsetGridEquiv18_extractIndex hy j
        have hentry (b₀ : NyqParity3D) (d : NyqFine3D128) (y₀ : NyqGrid3D64) :
            ((1 / 128 : ℝ) : ℂ) * (if i ≠ j then (op_sp (veeSubGridKet b₀ y₀) i *
              op_sp (veeSubGridKet (anchorParity3D b₀ d)
                ((anchorSubTarget3D y₀ b₀ d).1)) j) x y else 0) =
            ((1 / 128 : ℝ) : ℂ) * ((star (subGridElem64_3D b₀ y₀ pᵢ) * subGridElem64_3D b₀ y₀ qᵢ) *
              (star (subGridElem64_3D (anchorSubTarget3D y₀ b₀ d).2
                  (anchorSubTarget3D y₀ b₀ d).1 pⱼ) *
                subGridElem64_3D (anchorSubTarget3D y₀ b₀ d).2
                  (anchorSubTarget3D y₀ b₀ d).1 qⱼ)) := by
          rw [ite_eq_left hij, op_sp, op_sp, embedMatrix_rEl_mul_apply_of_ne hij, ite_eq_left hao]
          simp only [rk1_sp, Matrix.of_apply, veeSubGridKet, subGridUnitary64, star_star,
            hpᵢ, hqᵢ, hpⱼ, hqⱼ]
          rfl
        simp_rw [hentry, ← Finset.mul_sum]
        have hpull : (∑ b₀ : NyqParity3D, ∑ d : NyqFine3D128, (coulombDual128Real d : ℂ) *
            (((1 / 128 : ℝ) : ℂ) * ∑ y₀ : NyqGrid3D64, (star (subGridElem64_3D b₀ y₀ pᵢ) *
              subGridElem64_3D b₀ y₀ qᵢ) *
              (star (subGridElem64_3D (anchorSubTarget3D y₀ b₀ d).2
                (anchorSubTarget3D y₀ b₀ d).1 pⱼ) *
                subGridElem64_3D (anchorSubTarget3D y₀ b₀ d).2
                  (anchorSubTarget3D y₀ b₀ d).1 qⱼ))) =
            (1 / 2 : ℂ) * singleAnchorPairSubElem128
              (dualWeight128Fine (fun ν ↦ (coulombKernel ν : ℂ))) pᵢ qᵢ pⱼ qⱼ := by
          unfold singleAnchorPairSubElem128
          rw [← mul_assoc, show (1 / 2 : ℂ) * (1 / 64 : ℂ) = ((1 / 128 : ℝ) : ℂ) by norm_num,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun b₀ _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          rw [ofReal_coulombDual128Real]
          ring
        rw [hpull, singleAnchorPairSubElem128_dualWeight128_eq (fun ν ↦ (coulombKernel ν : ℂ))
          (inMomGrid3D_electron_of_state x i) (inMomGrid3D_electron_of_state y i)
          (inMomGrid3D_electron_of_state x j) (inMomGrid3D_electron_of_state y j)]
        by_cases hcons : pᵢ + pⱼ = qᵢ + qⱼ
        · rw [ite_eq_left hcons, ite_eq_left ⟨hij, hspec, hcons⟩]
          ring
        · rw [ite_eq_right hcons, ite_eq_right fun h ↦ hcons h.2.2, mul_zero]
      · rw [ite_eq_right fun h ↦ hspec h.2.1]
        refine Finset.sum_eq_zero fun b₀ _ ↦ Finset.sum_eq_zero fun d _ ↦
          mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y₀ _ ↦ ?_)
        rw [ite_eq_left hij, op_sp, op_sp, embedMatrix_rEl_mul_apply_of_ne hij,
          ite_eq_right (mt hao_iff.mp hspec), mul_zero]
    · rw [ite_eq_right fun h ↦ hij h.1]
      exact Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
        mul_eq_zero_of_right _ (Finset.sum_eq_zero fun _ _ ↦ by rw [ite_eq_right hij, mul_zero])
  · dsimp only [vEeManyBody, Matrix.of_apply]
    rw [ite_eq_right hgrid, ite_eq_right hgrid]
open SpecsAux.DyadicSubgridToeplitz128 (nyq128Equiv3D anchorParity3D
  anchorSubTarget3D) in
theorem sum_dy_singleAnchorPairOp_eq_const (b₀ dp : NyqParity3D) (i : Fin numElectrons) : (∑
    dy : NyqGrid3D64, singleAnchorPairOp (veeSubGridKet b₀) (veeSubGridKet (anchorParity3D b₀
    (nyq128Equiv3D (dy, dp)))) (fun y₀ ↦ (anchorSubTarget3D y₀ b₀ (nyq128Equiv3D (dy, dp))).1)
    i) = (((numElectrons : ℝ) - 1 : ℝ) : ℂ) • (1 : Operator (2 ^ systemQubits)) := by
  let b₁ : NyqParity3D := anchorParity3D b₀ (nyq128Equiv3D (0, dp))
  have hop_id (b : NyqParity3D) (k : Fin numElectrons) :
      (∑ y : NyqGrid3D64, op_sp (veeSubGridKet b y) k) = 1 := by
    rw [show (∑ y : NyqGrid3D64, op_sp (veeSubGridKet b y) k) =
        (rEl_sp k).embedMatrix (∑ y : NyqGrid3D64, rk1_sp (veeSubGridKet b y)) from
        ((rEl_sp k).embedMatrix_sum Finset.univ _).symm,
      show (∑ y : NyqGrid3D64, rk1_sp (veeSubGridKet b y)) = 1 by
        ext u v
        rw [Matrix.sum_apply, Matrix.one_apply]
        exact veeSubGridKet_complete b u v,
      (rEl_sp k).embedMatrix_one]
  unfold singleAnchorPairOp nSub_sp
  have hpar (dy y₀ : NyqGrid3D64) : (∑ j ∈ Finset.univ.erase i, op_sp
      (veeSubGridKet (anchorParity3D b₀ (nyq128Equiv3D (dy, dp)))
        ((anchorSubTarget3D y₀ b₀ (nyq128Equiv3D (dy, dp))).1)) j) =
      ∑ j ∈ Finset.univ.erase i,
        op_sp (veeSubGridKet b₁ (anchorSubTargetEquiv b₀ dp y₀ dy)) j :=
    Finset.sum_congr rfl fun j _ ↦ congrArg (op_sp · j)
      (congrArg₂ veeSubGridKet (anchorParity3D_nyq128Equiv3D b₀ dp dy) rfl)
  simp_rw [hpar]
  rw [Finset.sum_comm]
  have hinner (y₀ : NyqGrid3D64) : (∑ dy : NyqGrid3D64, op_sp (veeSubGridKet b₀ y₀) i *
      ∑ j ∈ Finset.univ.erase i, op_sp (veeSubGridKet b₁ (anchorSubTargetEquiv b₀ dp y₀ dy)) j) =
      (((numElectrons : ℝ) - 1 : ℝ) : ℂ) • op_sp (veeSubGridKet b₀ y₀) i := by
    rw [← Matrix.mul_sum, Equiv.sum_comp (anchorSubTargetEquiv b₀ dp y₀)
      (fun y₁ ↦ ∑ j ∈ Finset.univ.erase i, op_sp (veeSubGridKet b₁ y₁) j), Finset.sum_comm]
    simp_rw [hop_id b₁]
    rw [sum_erase_const_elec (1 : Operator (2 ^ systemQubits)) i, Matrix.mul_smul, Matrix.mul_one]
  simp_rw [hinner, ← Finset.smul_sum, hop_id b₀ i]
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 nyq128Equiv3D
  anchorParity3D anchorSubTarget3D) in
theorem norm_veeSingleAnchorRaw_sub_le (K₁ K₂ : NyqFine3D128 → ℝ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hK : ∀ d, |K₁ d - K₂ d| ≤ δ) :
    ‖veeSingleAnchorRaw K₁ - veeSingleAnchorRaw K₂‖ ≤ 23653 * δ := by
  let dK (dy : NyqGrid3D64) (dp : NyqParity3D) : ℝ :=
    K₁ (nyq128Equiv3D (dy, dp)) - K₂ (nyq128Equiv3D (dy, dp))
  let term (b₀ dp : NyqParity3D) (i j : Fin numElectrons) (y₀ dy : NyqGrid3D64) :
      Operator (2 ^ systemQubits) :=
    (dK dy dp : ℂ) • (op_sp (veeSubGridKet b₀ y₀) i *
      op_sp (veeSubGridKet (anchorParity3D b₀ (nyq128Equiv3D (dy, dp)))
        ((anchorSubTarget3D y₀ b₀ (nyq128Equiv3D (dy, dp))).1)) j)
  have hpair (b₀ dp : NyqParity3D) {i j : Fin numElectrons} (hne : i ≠ j) :
      ‖∑ y₀ : NyqGrid3D64, ∑ dy : NyqGrid3D64, term b₀ dp i j y₀ dy‖ ≤ δ := by
    let b₁ : NyqParity3D := anchorParity3D b₀ (nyq128Equiv3D (0, dp))
    have hre (y₀ : NyqGrid3D64) : (∑ dy : NyqGrid3D64, term b₀ dp i j y₀ dy) =
        ∑ y₁ : NyqGrid3D64, (dK ((anchorSubTargetEquiv b₀ dp y₀).symm y₁) dp : ℂ) •
          (op_sp (veeSubGridKet b₀ y₀) i * op_sp (veeSubGridKet b₁ y₁) j) := by
      have h1 (dy : NyqGrid3D64) : term b₀ dp i j y₀ dy =
          (dK dy dp : ℂ) • (op_sp (veeSubGridKet b₀ y₀) i *
            op_sp (veeSubGridKet b₁ (anchorSubTargetEquiv b₀ dp y₀ dy)) j) :=
        congrArg ((dK dy dp : ℂ) • (op_sp (veeSubGridKet b₀ y₀) i * ·))
          (congrArg (op_sp · j) (congrArg₂ veeSubGridKet
            (anchorParity3D_nyq128Equiv3D b₀ dp dy) rfl))
      simp_rw [h1]
      exact (Equiv.sum_comp (anchorSubTargetEquiv b₀ dp y₀).symm fun dy ↦
        (dK dy dp : ℂ) • (op_sp (veeSubGridKet b₀ y₀) i *
          op_sp (veeSubGridKet b₁ (anchorSubTargetEquiv b₀ dp y₀ dy)) j)).symm.trans
        (Finset.sum_congr rfl fun _ _ ↦ by rw [Equiv.apply_symm_apply])
    simp_rw [hre]
    exact norm_sum_pair_op_sp_le_of_orthonormal elecOffsetGridEquiv18 (veeSubGridKet b₀)
      (veeSubGridKet b₁) (veeSubGridKet_complete b₀) (veeSubGridKet_complete b₁) hne
      (fun p ↦ dK ((anchorSubTargetEquiv b₀ dp p.1).symm p.2) dp) hδ0 (fun _ ↦ hK _)
  have hdiff : veeSingleAnchorRaw K₁ - veeSingleAnchorRaw K₂ = ((1 / 128 : ℝ) : ℂ) •
      ∑ b₀ : NyqParity3D, ∑ dp : NyqParity3D, ∑ i : Fin numElectrons,
      ∑ j ∈ Finset.univ.erase i, ∑ y₀ : NyqGrid3D64, ∑ dy : NyqGrid3D64,
        term b₀ dp i j y₀ dy := by
    unfold veeSingleAnchorRaw singleAnchorPairOp nSub_sp
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun b₀ _ ↦ ?_)
    rw [← Finset.sum_sub_distrib, ← Equiv.sum_comp nyq128Equiv3D, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun dp _ ↦ ?_
    simp_rw [← sub_smul, ← Complex.ofReal_sub, Finset.smul_sum,
      Matrix.mul_sum, Finset.smul_sum]
    change (∑ dy : NyqGrid3D64, ∑ i : Fin numElectrons, ∑ y₀ : NyqGrid3D64,
        ∑ j ∈ Finset.univ.erase i, term b₀ dp i j y₀ dy) = _
    have hsw (dy : NyqGrid3D64) (i : Fin numElectrons) :
        (∑ y₀ : NyqGrid3D64, ∑ j ∈ Finset.univ.erase i, term b₀ dp i j y₀ dy) =
          ∑ j ∈ Finset.univ.erase i, ∑ y₀ : NyqGrid3D64, term b₀ dp i j y₀ dy :=
      Finset.sum_comm
    simp_rw [hsw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  rw [hdiff, norm_smul, show ‖((1 / 128 : ℝ) : ℂ)‖ = (1 / 128 : ℝ) by norm_num]
  have hsum : ‖∑ b₀ : NyqParity3D, ∑ dp : NyqParity3D, ∑ i : Fin numElectrons,
      ∑ j ∈ Finset.univ.erase i, ∑ y₀ : NyqGrid3D64, ∑ dy : NyqGrid3D64,
        term b₀ dp i j y₀ dy‖ ≤ (8 * 8 * 218 * 217 : ℝ) * δ := by
    refine ((norm_sum_le _ _).trans <| Finset.sum_le_sum fun b₀ _ ↦
      (norm_sum_le _ _).trans <| Finset.sum_le_sum fun dp _ ↦
        (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ ↦
          (norm_sum_le _ _).trans <| Finset.sum_le_sum fun _ hj ↦
            hpair b₀ dp (Finset.mem_erase.mp hj).1.symm).trans ?_
    have hcard : Fintype.card NyqParity3D = 8 := by decide
    simp [Finset.card_erase_of_mem, hcard, numElectrons, nsmul_eq_mul, mul_assoc]
  linarith
end Slot2Slot4QuantizedChannelBridge
end
end ModSlot2Slot4QuantizedChannelBridge
section ModSlot2SingleElecTwistBound
@[expose] public section
namespace Slot2SingleElecTwistBound
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SingleAnchorFermionicPauliCap
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem norm_unitary_conj_sub_le_gen {D : ℕ} (U₁ U₂ : Unitary D) (A : Operator D) :
    ‖U₁.1 * A * U₁.1ᴴ - U₂.1 * A * U₂.1ᴴ‖ ≤ 2 * ‖A‖ * ‖U₁.1 - U₂.1‖ := by
  have htel : U₁.1 * A * U₁.1ᴴ - U₂.1 * A * U₂.1ᴴ =
      (U₁.1 - U₂.1) * A * U₁.1ᴴ + U₂.1 * A * (U₁.1 - U₂.1)ᴴ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, conjTranspose_sub, Matrix.mul_assoc]
    abel
  have hU1 : ‖U₁.1ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact l2_opNorm_unitary_le_one U₁
  have hU2 : ‖U₂.1‖ ≤ 1 := l2_opNorm_unitary_le_one U₂
  have hdh : ‖(U₁.1 - U₂.1)ᴴ‖ = ‖U₁.1 - U₂.1‖ := Matrix.l2_opNorm_conjTranspose _
  rw [htel]
  have hL : ‖(U₁.1 - U₂.1) * A * U₁.1ᴴ‖ ≤ ‖U₁.1 - U₂.1‖ * ‖A‖ :=
    (norm_mul_le _ _).trans <| (mul_le_of_le_one_right (norm_nonneg _) hU1).trans (norm_mul_le _ _)
  have hR : ‖U₂.1 * A * (U₁.1 - U₂.1)ᴴ‖ ≤ ‖A‖ * ‖U₁.1 - U₂.1‖ := by
    rw [← hdh]
    exact (norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_right
      ((norm_mul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_right hU2 (norm_nonneg A)))
      (norm_nonneg _)
  linarith [norm_add_le ((U₁.1 - U₂.1) * A * U₁.1ᴴ) (U₂.1 * A * (U₁.1 - U₂.1)ᴴ)]
theorem list_prod_conj_comm_eq {D : ℕ} :
    ∀ (L : List (Unitary D)) (M : Operator D),
      (∀ u ∈ L, u.1 * M = M * u.1) → L.prod.1 * M * L.prod.1ᴴ = M
  | [], M, _ => by simp
  | u :: t, M, hcomm => by
      rw [List.prod_cons, Submonoid.coe_mul, Matrix.conjTranspose_mul]
      have ht := list_prod_conj_comm_eq t M (fun v hv ↦ hcomm v (List.mem_cons_of_mem _ hv))
      have huU : u.1 * u.1ᴴ = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp u.2
      calc u.1 * t.prod.1 * M * (t.prod.1ᴴ * u.1ᴴ)
          = u.1 * (t.prod.1 * M * t.prod.1ᴴ) * u.1ᴴ := by simp only [Matrix.mul_assoc]
        _ = M * (u.1 * u.1ᴴ) := by rw [ht, hcomm u List.mem_cons_self, Matrix.mul_assoc]
        _ = M := by rw [huU, Matrix.mul_one]
theorem list_ofFn_prod_conj_eq_single {D : ℕ} :
    ∀ {m : ℕ} (f : Fin m → Unitary D) (i : Fin m) (M : Operator D),
      (∀ j : Fin m, j ≠ i → (f j).1 * M = M * (f j).1) →
      (∀ j : Fin m, j ≠ i → (f j).1 * (f i).1 = (f i).1 * (f j).1) →
      (∀ j : Fin m, j ≠ i → (f j).1 * (f i).1ᴴ = (f i).1ᴴ * (f j).1) →
      (List.ofFn f).prod.1 * M * (List.ofFn f).prod.1ᴴ = (f i).1 * M * (f i).1ᴴ
  | 0, _, i, _ => Fin.elim0 i
  | m + 1, f, i, M => by
      let tail := (List.ofFn fun k : Fin m ↦ f k.succ).prod
      refine Fin.cases (fun hM _ _ ↦ ?_) (fun k hM hU hUs ↦ ?_) i
      · rw [List.ofFn_succ, List.prod_cons, Submonoid.coe_mul, Matrix.conjTranspose_mul]
        have htail : tail.1 * M * tail.1ᴴ = M := list_prod_conj_comm_eq _ M fun u hu ↦ by
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hu
          exact hM k.succ (Fin.succ_ne_zero k)
        calc (f 0).1 * tail.1 * M * (tail.1ᴴ * (f 0).1ᴴ)
            = (f 0).1 * (tail.1 * M * tail.1ᴴ) * (f 0).1ᴴ := by simp only [Matrix.mul_assoc]
          _ = (f 0).1 * M * (f 0).1ᴴ := by rw [htail]
      · rw [List.ofFn_succ, List.prod_cons, Submonoid.coe_mul, Matrix.conjTranspose_mul]
        have ih : tail.1 * M * tail.1ᴴ = (f k.succ).1 * M * (f k.succ).1ᴴ :=
          list_ofFn_prod_conj_eq_single (fun r : Fin m ↦ f r.succ) k M
            (fun r hr ↦ hM r.succ (mt Fin.succ_inj.mp hr))
            (fun r hr ↦ hU r.succ (mt Fin.succ_inj.mp hr))
            (fun r hr ↦ hUs r.succ (mt Fin.succ_inj.mp hr))
        have h0_ne : (0 : Fin (m + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
        have h0unit : (f 0).1 * (f 0).1ᴴ = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (f 0).2
        calc (f 0).1 * tail.1 * M * (tail.1ᴴ * (f 0).1ᴴ)
            = (f 0).1 * (tail.1 * M * tail.1ᴴ) * (f 0).1ᴴ := by simp only [Matrix.mul_assoc]
          _ = (f k.succ).1 * M * (f k.succ).1ᴴ * ((f 0).1 * (f 0).1ᴴ) := by
                rw [ih]
                simp only [← Matrix.mul_assoc]
                rw [hU 0 h0_ne, Matrix.mul_assoc ((f k.succ).1) ((f 0).1) M, hM 0 h0_ne,
                  ← Matrix.mul_assoc, Matrix.mul_assoc ((f k.succ).1 * M) ((f 0).1),
                  hUs 0 h0_ne]
                simp only [Matrix.mul_assoc]
          _ = (f k.succ).1 * M * (f k.succ).1ᴴ := by rw [h0unit, Matrix.mul_one]
theorem rEl_prod_conj_embed_eq_single
    (u : Fin numElectrons → Unitary (2 ^ 18))
    (e : Fin numElectrons) (A : Operator (2 ^ 18)) :
    let D := (List.ofFn fun j : Fin numElectrons ↦ (rEl_sp j).embedUnitary (u j)).prod
    D.1 * (rEl_sp e).embedMatrix A * D.1ᴴ =
      ((rEl_sp e).embedUnitary (u e)).1 * (rEl_sp e).embedMatrix A *
        ((rEl_sp e).embedUnitary (u e)).1ᴴ := by
  refine list_ofFn_prod_conj_eq_single
    (fun j : Fin numElectrons ↦ (rEl_sp j).embedUnitary (u j)) e ((rEl_sp e).embedMatrix A)
    (fun j hje ↦ (rEl_sp j).embedMatrix_comm_of_disjoint (rEl_sp e)
      (rEl_disjoint_of_ne_sp hje) (u j).1 A)
    (fun j hje ↦ (rEl_sp j).embedMatrix_comm_of_disjoint (rEl_sp e)
      (rEl_disjoint_of_ne_sp hje) (u j).1 (u e).1) fun j hje ↦ ?_
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
    ← QRegister.embedMatrix_conjTranspose]
  exact (rEl_sp j).embedMatrix_comm_of_disjoint (rEl_sp e)
    (rEl_disjoint_of_ne_sp hje) (u j).1 (u e).1ᴴ
end Slot2SingleElecTwistBound
end
end ModSlot2SingleElecTwistBound

section ModSlot3Slot5QuantizedChannelBridge
@[expose] public section
namespace Slot3Slot5QuantizedChannelBridge
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open scoped Matrix BigOperators Matrix.Norms.L2Operator
set_option maxRecDepth 4096 in
theorem norm_mul_fermionicProjector_le (spinUp : Finset (Fin numElectrons))
    (M : Operator (2 ^ systemQubits)) : ‖M * fermionicProjector spinUp‖ ≤ ‖M‖ ∧
    ‖fermionicProjector spinUp * M * fermionicProjector spinUp‖ ≤ ‖M‖ :=
  (ModWrapCoarse8PureMomentum.norm_fermionicProjector_sandwich_le
    spinUp M).symm
end Slot3Slot5QuantizedChannelBridge
end
end ModSlot3Slot5QuantizedChannelBridge
section ModStreamingBchComparator
@[expose] public section
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MeasureBranchHadamardSem
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace StreamingBchComparator
section CleanBridges
theorem gket_eq_ket {n : ℕ} (β : BitAssignment n) : DynCircuitExt.gket β = ket β := rfl
theorem restrictZeroWires_wireList_eq_conj_projZeroAll
    {Var : Type} {n : ℕ} :
    ∀ (k : ℕ) (scr : Fin k → Wire n) (Θ : CQAssertionCompat Var (2 ^ n)) (σ : Store Var),
      ((DynCircuitExt.restrictZeroWires (DynCircuitExt.wireList k scr) Θ σ).1) =
        ((Θ σ).1).conj (projZeroAll k scr)
  | 0, _, Θ, σ => by
      simp [DynCircuitExt.wireList, DynCircuitExt.restrictZeroWires, projZeroAll]
  | k + 1, scr, Θ, σ => by
      simp only [DynCircuitExt.wireList, DynCircuitExt.restrictZeroWires,
        CQAssertion.restrictToZeroAncilla_coe]
      rw [restrictZeroWires_wireList_eq_conj_projZeroAll k (fun i => scr i.succ) Θ σ, conj_conj]
      rfl
def PreservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (d : DynamicCircuit Var n) : Prop :=
  ∀ (M : Observable (Fin (2 ^ n))), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ =>
    M) = fun _ => M'
theorem PreservesStoreConst.circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (c : Circuit n) : PreservesStoreConst (Var := Var) (.circuit c) :=
  InPlaceFullAddSlice.PreservesStoreConst.circuit c
theorem PreservesStoreConst.identity {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} :
    PreservesStoreConst (Var := Var) (n := n) .identity := fun M => ⟨M, rfl⟩
theorem PreservesStoreConst.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {d₁ d₂ : DynamicCircuit Var n} (h₁ : PreservesStoreConst d₁) (h₂ : PreservesStoreConst d₂)
    : PreservesStoreConst (.seq d₁ d₂) :=
  InPlaceFullAddSlice.PreservesStoreConst.seq h₁ h₂
theorem PreservesStoreConst.andUncompute {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) :
    PreservesStoreConst (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) :=
  InPlaceFullAddSlice.PreservesStoreConst.andUncompute
    v c₁ c₂ anc h₁₂
theorem PreservesStoreConst.withAndChain {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) :
    ∀ (k : ℕ) (acc : Wire n) (ctrls : Fin k → Wire n) (scratches : Fin k → Wire n)
      (hacc_c : ∀ i, acc ≠ ctrls i) (hacc_s : ∀ i, acc ≠ scratches i)
      (hc_s : ∀ i j, ctrls i ≠ scratches j) (hs_inj : Function.Injective scratches)
      (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → Circuit n),
      PreservesStoreConst (DynCircuitExt.withAndChain v k acc ctrls scratches
        hacc_c hacc_s hc_s hs_inj (fun w hw => .circuit (leaf w hw)))
  | 0, acc, _, _, _, _, _, _, leaf => PreservesStoreConst.circuit (leaf acc (Or.inl rfl))
  | k + 1, acc, ctrls, scratches, hacc_c, _, hc_s, hs_inj, _ =>
      PreservesStoreConst.seq
        (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq
          (PreservesStoreConst.withAndChain v k (scratches 0)
            (fun i => ctrls i.succ) (fun i => scratches i.succ)
            (fun i => (hc_s i.succ 0).symm)
            (fun i h => Fin.succ_ne_zero i (hs_inj h).symm)
            (fun i j => hc_s i.succ j.succ)
            (hs_inj.comp (Fin.succ_injective _)) _)
          (PreservesStoreConst.andUncompute v acc (ctrls 0) (scratches 0) (hacc_c 0)))
section UnsealMeasureAndBranch
unseal MeasureBranchHadamardSem.measureAndBranchSeq
theorem PreservesStoreConst.measureAndBranchSeq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) :
    ∀ (m : ℕ) (qs : Fin m → QRegister 1 n) (fixup : (Fin m → Bool) → DynamicCircuit Var n),
      (∀ g, PreservesStoreConst (fixup g)) →
      PreservesStoreConst (MeasureBranchHadamardSem.measureAndBranchSeq v m qs fixup)
  | 0, _, fixup, hfix => hfix Fin.elim0
  | m + 1, qs, fixup, hfix => by
      have : NeZero (2 ^ n) := ⟨by positivity⟩
      intro M
      let σ₀ : Store Var := fun _ => 0
      obtain ⟨MF, hMF⟩ := PreservesStoreConst.measureAndBranchSeq v m (fun i => qs i.succ)
        (fun rest => fixup (Fin.cons false rest)) (fun rest => hfix (Fin.cons false rest)) M
      obtain ⟨MT, hMT⟩ := PreservesStoreConst.measureAndBranchSeq v m (fun i => qs i.succ)
        (fun rest => fixup (Fin.cons true rest)) (fun rest => hfix (Fin.cons true rest)) M
      refine ⟨wp (MeasureBranchHadamardSem.measureAndBranchSeq v (m + 1) qs fixup).compile
        (fun _ => M) σ₀, ?_⟩
      funext σ
      simp only [MeasureBranchHadamardSem.measureAndBranchSeq, DynamicCircuit.compile_seq,
        DynamicCircuit.compile_measure, DynamicCircuit.compile_qIf, QProg.measureRegister, wp_qSeq,
        wp_qIf, wp_qMeasure_apply, CQAssertionCompat.subst_apply, hMT, hMF]
      congr 1; funext o
      simp [Store.subst]
end UnsealMeasureAndBranch
end CleanBridges
section StreamingOracle
def slotAllWires {n k : ℕ} (firstCtrl lastCtrl : Wire n) (midCtrls : Fin k → Wire n) : Fin
    (k + 2) → Wire n := Fin.cons firstCtrl (Fin.cons lastCtrl midCtrls)
theorem fin_cons_ne {α : Type*} {k : ℕ} {x y : α} {ys : Fin k → α} (hxy : x ≠ y)
    (hys : ∀ j, x ≠ ys j) (idx : Fin (k + 1)) : x ≠ @Fin.cons k (fun _ => α) y ys idx :=
  Fin.cases hxy hys idx
theorem fin_cons_ne_left {α : Type*} {k m : ℕ} {y : α} {ys : Fin k → α} {zs : Fin m → α}
    (hyz : ∀ r, y ≠ zs r) (hysz : ∀ j r, ys j ≠ zs r) (idx : Fin (k + 1)) (r : Fin m) :
    @Fin.cons k (fun _ => α) y ys idx ≠ zs r :=
  Fin.cases (hyz r) (fun j => hysz j r) idx
def slotHitBit {n k : ℕ} (firstCtrl lastCtrl : Wire n) (midCtrls : Fin k → Wire n)
    (pat : Fin (k + 2) → Bool) (β : BitAssignment n) : ZMod 2 :=
  let ws := slotAllWires firstCtrl lastCtrl midCtrls
  ∏ idx : Fin (k + 2), if pat idx then β (ws idx) else β (ws idx) + 1
end StreamingOracle
end StreamingBchComparator
end
end ModStreamingBchComparator
section ModBchCubeDecoder
@[expose] public section
open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MeasureBranchHadamardSem
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace BchCubeDecoder
section AlgebraicSoundness
theorem eq_of_add_eq_zero_of_char2 {R : Type*} [AddCommGroup R] (hchar : ∀ a : R, a + a = 0)
    {x y : R} (hxy : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [hchar, add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [hxy, zero_add]
def zeroParityThreshExp (negate t s1Zero rZero : Bool) : Bool :=
  xor negate (xor ((!t) && s1Zero) (t && rZero))
end AlgebraicSoundness
section CleanWorkspaceSemantics
variable {Var : Type} {n : ℕ}
noncomputable def diagonalSignUnitary {d : ℕ} (phase : Fin (2 ^ d) → Bool) : Unitary (2 ^ d) :=
  ⟨Matrix.diagonal (fun g => if phase g then (-1 : ℂ) else 1), by
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro g
    cases phase g <;> simp [Unitary.mem_iff]⟩
noncomputable def diagonalSignUnitaryN (phase : BitAssignment n → Bool) : Unitary (2 ^ n) :=
  diagonalSignUnitary (fun g => phase (basisBits n g))
theorem ket_diagonalSignUnitaryN (phase : BitAssignment n → Bool) (β : BitAssignment n) :
    (diagonalSignUnitaryN phase).1.mulVec (ket β) =
      (if phase β then (-1 : ℂ) else 1) • ket β := by
  have hsingle : ket β = (Pi.single ((basisBitsEquiv n).symm β) 1 : Fin (2 ^ n) → ℂ) := by
    simp [ket, basisState]
  have hbits : basisBits n ((basisBitsEquiv n).symm β) = β :=
    (basisBitsEquiv n).apply_symm_apply β
  rw [hsingle, diagonalSignUnitaryN, diagonalSignUnitary]
  change (Matrix.diagonal _).mulVec (Pi.single _ 1) = _
  rw [Matrix.diagonal_mulVec_single, mul_one, hbits]
  cases phase β <;> ext g <;> simp [Pi.single_apply]
end CleanWorkspaceSemantics
section ConcreteGF256
@[implicit_reducible] def GF256 : Type := Fin 8 → ZMod 2
@[ext] theorem GF256.ext {u v : GF256} (h : ∀ i : Fin 8, u i = v i) : u = v := funext h
instance instDecidableEqGF256 : DecidableEq GF256 := Fintype.decidablePiFintype
instance instAddCommGroupGF256 : AddCommGroup GF256 :=
  Pi.addCommGroup (I := Fin 8) (f := fun _ => ZMod 2)
theorem gf256_char2 (a : GF256) : a + a = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (a i)
private theorem lemHex2bd (P : ℕ → Prop)
    (h : ∀ (q r : Fin 16), P (16 * q.val + r.val)) (m : ℕ) (hm : m < 256) : P m := by
  simpa only [show 16 * (m / 16) + m % 16 = m by omega] using
    h ⟨m / 16, by omega⟩ ⟨m % 16, by omega⟩
def gf256ToNat (v : GF256) : ℕ :=
  (if v 0 = 1 then 1 else 0) + 2 * (if v 1 = 1 then 1 else 0) +
    4 * (if v 2 = 1 then 1 else 0) + 8 * (if v 3 = 1 then 1 else 0) +
    16 * (if v 4 = 1 then 1 else 0) + 32 * (if v 5 = 1 then 1 else 0) +
    64 * (if v 6 = 1 then 1 else 0) + 128 * (if v 7 = 1 then 1 else 0)
def gf256OfNat (m : ℕ) : GF256 := fun j => if (m / (2 ^ j.val)) % 2 = 1 then 1 else 0
private theorem lemHex2c1 (m : ℕ) (hm : m < 256) : gf256ToNat (gf256OfNat m) = m :=
  lemHex2bd (fun n => gf256ToNat (gf256OfNat n) = n) (by decide) m hm
def proj38CodeByte (i : ℕ) : ℕ :=
  match i / 16 with
  | 0 =>
    match i % 16 with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7
    | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 12 | 12 => 13 | 13 => 14 | 14 => 15 | _ => 16
  | 1 =>
    match i % 16 with
    | 0 => 17 | 1 => 18 | 2 => 19 | 3 => 20 | 4 => 21 | 5 => 22 | 6 => 24 | 7 => 25
    | 8 => 26 | 9 => 27 | 10 => 28 | 11 => 29 | 12 => 30 | 13 => 33 | 14 => 34 | _ => 35
  | 2 =>
    match i % 16 with
    | 0 => 36 | 1 => 37 | 2 => 38 | 3 => 40 | 4 => 41 | 5 => 42 | 6 => 43 | 7 => 44
    | 8 => 45 | 9 => 46 | 10 => 47 | 11 => 48 | 12 => 49 | 13 => 50 | 14 => 52 | _ => 53
  | 3 =>
    match i % 16 with
    | 0 => 55 | 1 => 56 | 2 => 58 | 3 => 60 | 4 => 61 | 5 => 62 | 6 => 63 | 7 => 64
    | 8 => 65 | 9 => 67 | 10 => 69 | 11 => 71 | 12 => 72 | 13 => 73 | 14 => 74 | _ => 75
  | 4 =>
    match i % 16 with
    | 0 => 76 | 1 => 77 | 2 => 78 | 3 => 79 | 4 => 80 | 5 => 81 | 6 => 82 | 7 => 83
    | 8 => 84 | 9 => 85 | 10 => 86 | 11 => 88 | 12 => 89 | 13 => 90 | 14 => 91 | _ => 92
  | 5 =>
    match i % 16 with
    | 0 => 93 | 1 => 94 | 2 => 95 | 3 => 97 | 4 => 98 | 5 => 100 | 6 => 101 | 7 => 102
    | 8 => 103 | 9 => 104 | 10 => 107 | 11 => 110 | 12 => 111 | 13 => 112 | 14 => 113 | _ => 114
  | 6 =>
    match i % 16 with
    | 0 => 115 | 1 => 116 | 2 => 117 | 3 => 118 | 4 => 119 | 5 => 121 | 6 => 122 | 7 => 123
    | 8 => 124 | 9 => 125 | 10 => 126 | 11 => 127 | 12 => 128 | 13 => 129 | 14 => 130 | _ => 131
  | 7 =>
    match i % 16 with
    | 0 => 133 | 1 => 135 | 2 => 137 | 3 => 139 | 4 => 140 | 5 => 141 | 6 => 143 | 7 => 144
    | 8 => 145 | 9 => 146 | 10 => 147 | 11 => 148 | 12 => 149 | 13 => 150 | 14 => 151 | _ => 152
  | 8 =>
    match i % 16 with
    | 0 => 153 | 1 => 155 | 2 => 156 | 3 => 157 | 4 => 159 | 5 => 160 | 6 => 161 | 7 => 162
    | 8 => 163 | 9 => 165 | 10 => 166 | 11 => 168 | 12 => 169 | 13 => 170 | 14 => 172 | _ => 173
  | 9 =>
    match i % 16 with
    | 0 => 175 | 1 => 176 | 2 => 177 | 3 => 178 | 4 => 179 | 5 => 180 | 6 => 181 | 7 => 184
    | 8 => 185 | 9 => 186 | 10 => 187 | 11 => 188 | 12 => 189 | 13 => 190 | 14 => 191 | _ => 192
  | 10 =>
    match i % 16 with
    | 0 => 193 | 1 => 194 | 2 => 195 | 3 => 196 | 4 => 197 | 5 => 198 | 6 => 199 | 7 => 200
    | 8 => 201 | 9 => 202 | 10 => 203 | 11 => 204 | 12 => 205 | 13 => 206 | 14 => 208 | _ => 209
  | 11 =>
    match i % 16 with
    | 0 => 211 | 1 => 212 | 2 => 213 | 3 => 214 | 4 => 215 | 5 => 216 | 6 => 217 | 7 => 218
    | 8 => 219 | 9 => 220 | 10 => 221 | 11 => 222 | 12 => 223 | 13 => 224 | 14 => 225 | _ => 226
  | 12 =>
    match i % 16 with
    | 0 => 227 | 1 => 228 | 2 => 229 | 3 => 230 | 4 => 231 | 5 => 232 | 6 => 233 | 7 => 234
    | 8 => 235 | 9 => 236 | 10 => 237 | 11 => 238 | 12 => 239 | 13 => 240 | 14 => 241 | _ => 242
  | 13 =>
    match i % 16 with
    | 0 => 243 | 1 => 244 | 2 => 245 | 3 => 246 | 4 => 247 | 5 => 249 | 6 => 251 | 7 => 252
    | 8 => 253 | 9 => 254 | _ => 0
  | _ => 0
def proj38Code218 (i : Fin 218) : GF256 := gf256OfNat (proj38CodeByte i.val)
private theorem proj38CodeByte_lt :
    ∀ {a b : ℕ}, a < b → b < 218 → proj38CodeByte a < proj38CodeByte b
  | a, b + 1, hab, hb => by
      have hstep : proj38CodeByte b < proj38CodeByte (b + 1) :=
        lemHex2bd (fun n => n < 217 → proj38CodeByte n < proj38CodeByte (n + 1))
          (by decide) b (by omega) (by omega)
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hlt
      · exact hstep
      · exact (proj38CodeByte_lt hlt (by omega)).trans hstep
theorem proj38Code218_injective : Function.Injective proj38Code218 := by
  intro i j hij
  have hlt256 (m : ℕ) (hm : m < 218) : proj38CodeByte m < 256 :=
    lemHex2bd (fun n => n < 218 → proj38CodeByte n < 256) (by decide) m (by omega) hm
  have hval := congrArg gf256ToNat hij
  rw [proj38Code218, proj38Code218, lemHex2c1 _ (hlt256 _ i.isLt),
    lemHex2c1 _ (hlt256 _ j.isLt)] at hval
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact absurd hval (ne_of_lt (proj38CodeByte_lt h j.isLt))
  · exact Fin.ext h
  · exact absurd hval.symm (ne_of_lt (proj38CodeByte_lt h i.isLt))
def proj38ZeroBit (S : Finset (Fin 218)) : Bool := decide ((∑ e ∈ S, proj38Code218 e) = 0)
def proj38OddXorZeroBit (S : Finset (Fin 218)) : Bool :=
  xor (decide (S.card % 2 = 1)) (proj38ZeroBit S)
private theorem lemHex2f0 {S : Finset (Fin 218)} (h2 : S.card = 2) : proj38ZeroBit S = false := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
  rw [proj38ZeroBit, Finset.sum_pair hab]
  exact decide_eq_false fun h => hab (proj38Code218_injective
    (eq_of_add_eq_zero_of_char2 gf256_char2 h))
theorem proj38_zeroParity_slot4_pauliCap_eq (S : Finset (Fin 218)) (hcard : S.card ≤ 2) :
    (1 / 2 : ℂ) * ((if zeroParityThreshExp false false (proj38ZeroBit S) (proj38OddXorZeroBit
    S) then (-1 : ℂ) else 1) + (if zeroParityThreshExp false true (proj38ZeroBit S)
    (proj38OddXorZeroBit S) then (-1 : ℂ) else 1)) = ((min S.card 2 : ℕ) : ℂ) - (1 : ℂ) := by
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2) with h0 | h1 | h2
  · obtain rfl := Finset.card_eq_zero.mp h0
    have hz : proj38ZeroBit ∅ = true := by simp [proj38ZeroBit]
    have hr : proj38OddXorZeroBit ∅ = true := by simp [proj38OddXorZeroBit, hz]
    rw [hz, hr]
    norm_num [zeroParityThreshExp]
  · unfold proj38OddXorZeroBit
    rw [h1]
    simp only [Nat.one_mod, decide_true]
    cases proj38ZeroBit S <;> norm_num [zeroParityThreshExp]
  · rw [proj38OddXorZeroBit, h2, lemHex2f0 h2]
    norm_num [zeroParityThreshExp]
theorem proj38_zeroParity_negated_lcu_eq_min_card (S : Finset (Fin 218)) (hcard : S.card ≤ 2)
    : (1 / 2 : ℂ) * ((-1 : ℂ) ^ (zeroParityThreshExp true false (proj38ZeroBit S)
    (proj38OddXorZeroBit S)).toNat + (-1 : ℂ) ^ (zeroParityThreshExp true true (proj38ZeroBit
    S) (proj38OddXorZeroBit S)).toNat) = (1 : ℂ) - ((min S.card 2 : ℕ) : ℂ) := by
  have hneg (t z r : Bool) : (-1 : ℂ) ^ (zeroParityThreshExp true t z r).toNat =
      -(if zeroParityThreshExp false t z r then (-1 : ℂ) else 1) := by
    cases t <;> cases z <;> cases r <;> norm_num [zeroParityThreshExp]
  rw [hneg, hneg]
  linear_combination -proj38_zeroParity_slot4_pauliCap_eq S hcard
end ConcreteGF256
end BchCubeDecoder
end
end ModBchCubeDecoder
section ModSubmatrixOpNorm
@[expose] public section
namespace SpecsAux
open Operator Matrix SpecsAux.SpecMirror
namespace SubmatrixOpNorm
open scoped Matrix.Norms.L2Operator
theorem l2_opNorm_le_of_submatrix {d₁ d₂ : ℕ} (f : Fin d₁ ↪ Fin d₂)
    (M₁ : Matrix (Fin d₁) (Fin d₁) ℂ) (M₂ : Matrix (Fin d₂) (Fin d₂) ℂ)
    (hsub : ∀ x y : Fin d₁, M₁ x y = M₂ (f x) (f y)) : ‖M₁‖ ≤ ‖M₂‖ := by
  let T₁ := Matrix.toEuclideanCLM (n := Fin d₁) (𝕜 := ℂ) M₁
  let T₂ := Matrix.toEuclideanCLM (n := Fin d₂) (𝕜 := ℂ) M₂
  rw [← Matrix.l2_opNorm_toEuclideanCLM M₁]
  refine T₁.opNorm_le_bound (norm_nonneg M₂) fun v ↦ ?_
  let f0 : Fin d₂ → ℂ := 0
  let w : EuclideanSpace ℂ (Fin d₂) := WithLp.toLp 2 (Function.extend f (WithLp.ofLp v) f0)
  have hw_f (y : Fin d₁) : w.ofLp (f y) = v.ofLp y := f.injective.extend_apply v.ofLp f0 y
  have hw_out {g : Fin d₂} (hg : g ∉ Finset.univ.map f) : w.ofLp g = 0 :=
    Function.extend_apply' v.ofLp f0 g (by simpa using hg)
  have hw_sq : ‖w‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f))
        fun g _ hg ↦ by simp [hw_out hg], Finset.sum_map]
    exact Finset.sum_congr rfl fun y _ ↦ by rw [hw_f y]
  have hmulVec (x : Fin d₁) : (T₁ v).ofLp x = (T₂ w).ofLp (f x) := by
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f))
      fun g _ hg ↦ by simp [hw_out hg], Finset.sum_map]
    exact Finset.sum_congr rfl fun y _ ↦ by rw [hsub x y, hw_f y]
  have h_le_sq : ‖T₁ v‖ ^ 2 ≤ ‖T₂ w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hmap : ∑ x : Fin d₁, ‖(T₁ v).ofLp x‖ ^ 2 =
        ∑ g ∈ Finset.univ.map f, ‖(T₂ w).ofLp g‖ ^ 2 := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hmulVec x]
    rw [hmap]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ sq_nonneg _
  have h_le : ‖T₁ v‖ ≤ ‖T₂ w‖ := by nlinarith [norm_nonneg (T₁ v), norm_nonneg (T₂ w)]
  have hw_norm : ‖w‖ = ‖v‖ := by nlinarith [norm_nonneg w, norm_nonneg v]
  calc ‖T₁ v‖
    _ ≤ ‖T₂ w‖ := h_le
    _ ≤ ‖M₂‖ * ‖w‖ := Matrix.l2_opNorm_toEuclideanCLM M₂ ▸ T₂.le_opNorm w
    _ = ‖M₂‖ * ‖v‖ := by rw [hw_norm]
theorem l2_opNorm_projector_le_one {d : Type*} [Fintype d] [DecidableEq d] (P : Matrix d d ℂ)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P) : ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ = ‖P‖ * ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self P, hP_herm.eq, hP_idem]
  nlinarith [norm_nonneg P]
theorem l2_opNorm_basisOutcomeProjector_le_one {n m : ℕ} (r : QRegister m n) (o : Fin (2 ^ m))
    : ‖r.basisOutcomeProjector o‖ ≤ 1 := l2_opNorm_projector_le_one
    (r.basisOutcomeProjector o) (r.basisOutcomeProjector_conjTranspose o)
    (r.basisOutcomeProjector_mul_self o)
theorem l2_opNorm_embedMatrix_le {n k : ℕ} (r : QRegister k n)
    (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) : ‖r.embedMatrix M‖ ≤ ‖M‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin (2 ^ n)) (𝕜 := ℂ) (r.embedMatrix M)
  let TM := Matrix.toEuclideanCLM (n := Fin (2 ^ k)) (𝕜 := ℂ) M
  rw [← Matrix.l2_opNorm_toEuclideanCLM (r.embedMatrix M)]
  refine T.opNorm_le_bound (norm_nonneg M) fun x ↦
    (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  have hsplit (u : EuclideanSpace ℂ (Fin (2 ^ n))) : ‖u‖ ^ 2 =
      ∑ env : r.Environment → ZMod 2, ∑ j : Fin (2 ^ k),
        ‖u.ofLp (r.basisSplitEquiv.symm (j, env))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq,
      ← r.basisSplitEquiv.symm.sum_comp (fun i ↦ ‖u.ofLp i‖ ^ 2),
      Fintype.sum_prod_type_right]
  rw [mul_pow, hsplit (T x), hsplit x, Finset.mul_sum]
  refine Finset.sum_le_sum fun env _ ↦ ?_
  let x_env : EuclideanSpace ℂ (Fin (2 ^ k)) :=
    WithLp.toLp 2 (fun j ↦ x.ofLp (r.basisSplitEquiv.symm (j, env)))
  have hmul (j : Fin (2 ^ k)) :
      (T x).ofLp (r.basisSplitEquiv.symm (j, env)) = (TM x_env).ofLp j := by
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM, r.embedMatrix_mulVec_apply,
      ← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    rfl
  simp_rw [hmul, ← EuclideanSpace.norm_sq_eq (TM x_env)]
  rw [show (∑ j : Fin (2 ^ k), ‖x.ofLp (r.basisSplitEquiv.symm (j, env))‖ ^ 2) = ‖x_env‖ ^ 2
      from (EuclideanSpace.norm_sq_eq x_env).symm, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (Matrix.l2_opNorm_toEuclideanCLM M ▸ TM.le_opNorm x_env) 2
noncomputable def idxSplitZero {k n : ℕ} (r : QRegister k n) : Fin (2 ^ k) ↪ Fin (2 ^ n) where
  toFun j := r.basisSplitEquiv.symm (j, 0)
  inj' := fun _ _ h ↦ (Prod.mk.inj (r.basisSplitEquiv.symm.injective h)).1
theorem basisBits_idxSplitZero_of_not_mem {k n : ℕ} (r : QRegister k n) (j : Fin (2 ^ k))
    (w : Wire n) (hw : w ∉ Set.range r.wires) : basisBits n (idxSplitZero r j) w = 0 :=
  congrFun (congrArg Prod.snd (r.basisSplitEquiv.apply_symm_apply (j, 0))) ⟨w, hw⟩
theorem embedMatrix_idxSplitZero {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (x y : Fin (2 ^ k)) :
    (r.embedMatrix A) (idxSplitZero r x) (idxSplitZero r y) = A x y := by
  change (r.embedMatrix A) (r.basisSplitEquiv.symm (x, 0)) (r.basisSplitEquiv.symm (y, 0)) = A x y
  simp [QRegister.embedMatrix_apply, ← QRegister.basisSplitEquiv_apply_fst]
end SubmatrixOpNorm
end SpecsAux
end
end ModSubmatrixOpNorm

section ModBridgeDuhamel
@[expose] public section
namespace SpecsAux
open Operator Matrix SpecsAux.SpecMirror
open scoped Matrix
namespace BridgeDuhamel
open FullScaleBESector SubmatrixOpNorm
theorem exp_neg_I_smul_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    (t : ℝ) (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) ∈ Matrix.unitaryGroup n ℂ := by
  set X : Matrix n n ℂ := (-Complex.I * (t : ℂ)) • H
  have hX : Xᴴ = -X := by
    rw [conjTranspose_smul, hH.eq, show star (-Complex.I * (t : ℂ)) =
        -(-Complex.I * (t : ℂ)) by simp [Complex.conj_ofReal],
      neg_smul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
    hX, ← Matrix.exp_add_of_commute (-X) X (Commute.neg_left (Commute.refl X)),
    neg_add_cancel, NormedSpace.exp_zero]
open scoped Matrix.Norms.L2Operator in
theorem norm_of_mem_unitaryGroup_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty n with _ | _
  · simp [Subsingleton.elim U 0]
  · exact (CStarRing.norm_coe_unitary ⟨U, hU⟩).le
open scoped Matrix.Norms.L2Operator in
theorem norm_exp_neg_I_smul_le_one {n : Type*} [Fintype n] [DecidableEq n] (t : ℝ)
    (H : Matrix n n ℂ) (hH : H.IsHermitian) : ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤
    1 := norm_of_mem_unitaryGroup_le_one (exp_neg_I_smul_mem_unitaryGroup t H hH)
open scoped Matrix.Norms.L2Operator in
theorem norm_projector_le_one {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P) : ‖P‖ ≤ 1 := l2_opNorm_projector_le_one P
    hP_herm hP_idem
open scoped Matrix.Norms.L2Operator in
theorem norm_basisOutcomeProjector_le_one {n m : ℕ} (r : QRegister m n) (o : Fin (2 ^ m)) :
    ‖r.basisOutcomeProjector o‖ ≤ 1 := l2_opNorm_basisOutcomeProjector_le_one r o
open scoped Matrix.Norms.L2Operator in
theorem norm_embedMatrix_le {n k : ℕ} (r : QRegister k n)
    (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) : ‖r.embedMatrix M‖ ≤ ‖M‖ :=
    l2_opNorm_embedMatrix_le r M
open scoped Matrix.Norms.L2Operator in
@[implicit_reducible]
noncomputable def instL2OpNormedAlgebraReal {n : Type*} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le
open scoped Matrix.Norms.L2Operator in
theorem real_smul_neg_I_smul {n : Type*} (s : ℝ) (H : Matrix n n ℂ) :
    s • ((-Complex.I) • H) = (-Complex.I * (s : ℂ)) • H := by
  ext i j
  simp [Complex.real_smul]
  ring
open scoped Matrix.Norms.L2Operator in
theorem norm_exp_sub_exp_le_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (t : ℝ) (ht : 0 ≤ t) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • A) - NormedSpace.exp
    ((-Complex.I * (t : ℂ)) • B)‖ ≤ t * ‖A - B‖ := by
  let : NormedAlgebra ℝ (Matrix n n ℂ) := instL2OpNormedAlgebraReal
  let X : Matrix n n ℂ := (-Complex.I) • A
  let Y : Matrix n n ℂ := (-Complex.I) • B
  let f : ℝ → Matrix n n ℂ := fun s ↦ NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • Y)
  let f' : ℝ → Matrix n n ℂ := fun s ↦
    NormedSpace.exp (s • X) * (X - Y) * NormedSpace.exp ((t - s) • Y)
  have hderiv (s : ℝ) : HasDerivAt f (f' s) s := by
    have hd1 := hasDerivAt_exp_smul_const X s
    have hd2_raw : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp ((t - u) • Y))
        ((-1 : ℝ) • (Y * NormedSpace.exp ((t - s) • Y))) s :=
      HasDerivAt.scomp s (hasDerivAt_exp_smul_const' Y (t - s))
        ((hasDerivAt_id' s).const_sub t)
    have hd2 : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp ((t - u) • Y))
        (-(Y * NormedSpace.exp ((t - s) • Y))) s := by
      simpa only [neg_one_smul] using hd2_raw
    refine (hd1.fun_mul hd2).congr_deriv ?_
    change _ = NormedSpace.exp (s • X) * (X - Y) * NormedSpace.exp ((t - s) • Y)
    noncomm_ring
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t, ‖f' s‖ ≤ ‖A - B‖ := fun s _ ↦ by
    have hX : ‖NormedSpace.exp (s • X)‖ ≤ 1 :=
      real_smul_neg_I_smul s A ▸ norm_exp_neg_I_smul_le_one s A hA
    have hY : ‖NormedSpace.exp ((t - s) • Y)‖ ≤ 1 :=
      real_smul_neg_I_smul (t - s) B ▸ norm_exp_neg_I_smul_le_one (t - s) B hB
    have hXY : ‖X - Y‖ = ‖A - B‖ := by
      rw [show X - Y = (-Complex.I) • (A - B) from (smul_sub _ _ _).symm,
        norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact (norm_mul_le _ _).trans <| (mul_le_of_le_one_right (norm_nonneg _) hY).trans <|
      (norm_mul_le _ _).trans (by
        rw [hXY]
        linarith [mul_le_mul_of_nonneg_right hX (norm_nonneg (A - B))])
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := t) (f := f)
    (f' := f') (C := ‖A - B‖) (fun s _ ↦ (hderiv s).hasDerivWithinAt) hbound t
    (Set.right_mem_Icc.mpr ht)
  dsimp only [f, X, Y] at hmvt
  simpa only [sub_self, zero_smul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul,
    sub_zero, real_smul_neg_I_smul, mul_comm ‖A - B‖ t] using hmvt
set_option backward.isDefEq.respectTransparency false in
theorem semiconjBy_exp {n : Type*} [Fintype n] [DecidableEq n] {P A B : Matrix n n ℂ}
    (h : SemiconjBy P A B) : SemiconjBy P (NormedSpace.exp A) (NormedSpace.exp B) :=
  open scoped Matrix.Norms.Operator in h.exp_right
theorem exp_commute_of_commute {n : Type*} [Fintype n] [DecidableEq n] (A P : Matrix n n ℂ)
    (hcomm : A * P = P * A) : NormedSpace.exp A * P = P * NormedSpace.exp A :=
  (semiconjBy_exp (P := P) (A := A) (B := A) hcomm.symm).eq.symm
theorem exp_mul_projector_eq_exp_projected {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℂ) (t : ℝ) (hP_idem : P * P = P) (hcomm : A * P = P * A) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • A) * P =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • (P * A * P)) * P := by
  have hsemi : SemiconjBy P ((-Complex.I * (t : ℂ)) • A)
      ((-Complex.I * (t : ℂ)) • (P * A * P)) := by
    change P * ((-Complex.I * (t : ℂ)) • A) = ((-Complex.I * (t : ℂ)) • (P * A * P)) * P
    rw [Matrix.mul_smul, Matrix.smul_mul]
    refine congrArg _ ?_
    calc P * A = (P * P) * A := by rw [hP_idem]
      _ = P * (A * P) := by rw [Matrix.mul_assoc, hcomm]
      _ = (P * A * P) * P := by simp only [Matrix.mul_assoc, hP_idem]
  rw [exp_commute_of_commute _ _ (by rw [Matrix.smul_mul, hcomm, Matrix.mul_smul]),
    (semiconjBy_exp hsemi).eq]
open scoped Matrix.Norms.L2Operator in
theorem norm_exp_sub_exp_mul_projector_le {k : ℕ} (Heff H P : Operator (2 ^ k)) (t ε_BE : ℝ)
    (ht : 0 ≤ t) (hHeff : Heff.IsHermitian) (hH : H.IsHermitian) (hP_herm : P.IsHermitian)
    (hP_idem : P * P = P) (hCommHeff : Heff * P = P * Heff) (hCommH : H * P = P * H)
    (hDiff : ‖P * (Heff - H) * P‖ ≤ ε_BE) : ‖(NormedSpace.exp ((-Complex.I * (t : ℂ)) • Heff)
    - NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)) * P‖ ≤ t * ε_BE := by
  have hHP {M : Operator (2 ^ k)} (hM : M.IsHermitian) : (P * M * P).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul, hP_herm.eq, hM.eq,
      Matrix.mul_assoc]
  rw [Matrix.sub_mul, exp_mul_projector_eq_exp_projected Heff P t hP_idem hCommHeff,
    exp_mul_projector_eq_exp_projected H P t hP_idem hCommH, ← Matrix.sub_mul]
  exact (norm_mul_le _ _).trans <|
    (mul_le_of_le_one_right (norm_nonneg _)
      (norm_projector_le_one P hP_herm hP_idem)).trans <|
      (norm_exp_sub_exp_le_of_isHermitian _ _ t ht (hHP hHeff) (hHP hH)).trans <| by
        rw [show P * Heff * P - P * H * P = P * (Heff - H) * P by noncomm_ring]
        exact mul_le_mul_of_nonneg_left hDiff ht
theorem exp_smul_one_eq {n : Type*} [Fintype n] [DecidableEq n] (z : ℂ) :
    NormedSpace.exp (z • (1 : Matrix n n ℂ)) = Complex.exp z • (1 : Matrix n n ℂ) := by
  have hdiag (w : ℂ) : w • (1 : Matrix n n ℂ) = Matrix.diagonal (fun _ : n ↦ w) := by
    ext i j; by_cases h : i = j <;> simp [h, Matrix.diagonal]
  rw [hdiag, hdiag, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]
theorem exp_neg_I_smul_sub_scalar_one {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (E₀ t : ℝ) : NormedSpace.exp
    ((-Complex.I * (t : ℂ)) • (H - (E₀ : ℂ) • (1 : Matrix n n ℂ))) = Complex.exp
    ((E₀ * t : ℝ) * Complex.I) • NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) := by
  have h_eq : (-Complex.I * (t : ℂ)) • (H - (E₀ : ℂ) • (1 : Matrix n n ℂ)) =
      (((E₀ * t : ℝ) : ℂ) * Complex.I) • (1 : Matrix n n ℂ) +
        ((-Complex.I * (t : ℂ)) • H) := by
    push_cast
    rw [smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul, add_comm]
    exact congrArg (· + _) (congrArg (· • _) (by ring))
  rw [h_eq, Matrix.exp_add_of_commute _ _ ((Commute.one_left _).smul_left _),
    exp_smul_one_eq, Matrix.smul_mul, Matrix.one_mul]
theorem ApproximatesTimeEvolution.of_scalar_shift {k m : ℕ} (H : Operator (2 ^ k))
    (E₀ t ε : ℝ) (P : Operator (2 ^ k)) (W : Unitary (2 ^ (k + m))) (h :
    ApproximatesTimeEvolution (H - (E₀ : ℂ) • (1 : Operator (2 ^ k))) t ε P W) :
    ApproximatesTimeEvolution H t ε P W := by
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ + E₀ * t, ?_⟩
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  have htarget : Complex.exp (φ * Complex.I) • sys.embedMatrix (NormedSpace.exp ((-Complex.I *
      (t : ℂ)) • (H - (E₀ : ℂ) • (1 : Operator (2 ^ k))))) = Complex.exp
      ((φ + E₀ * t : ℝ) * Complex.I) • sys.embedMatrix
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)) := by
    rw [exp_neg_I_smul_sub_scalar_one, sys.embedMatrix_smul, smul_smul, ← Complex.exp_add]
    exact congrArg (· • _) (congrArg Complex.exp (by push_cast; ring))
  let anc : QRegister m (k + m) := .block k m le_rfl
  change open scoped Matrix.Norms.L2Operator in
    ‖(W.1 - Complex.exp ((φ + E₀ * t : ℝ) * Complex.I) •
      sys.embedMatrix (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))) *
        (sys.embedMatrix P * anc.basisOutcomeProjector 0)‖ ≤ ε
  rw [← htarget]
  exact hφ
theorem embedMatrix_sub {k n : ℕ} (r : QRegister k n)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) : r.embedMatrix (A - B) = r.embedMatrix A -
    r.embedMatrix B := by
  rw [sub_eq_add_neg, r.embedMatrix_add, ← neg_one_smul ℂ B,
    r.embedMatrix_smul, neg_one_smul, ← sub_eq_add_neg]
private theorem lemHex31b (k m : ℕ) (x : Fin (2 ^ k)) : (QRegister.block k m le_rfl).extractIndex
    (idxSplitZero (QRegister.block 0 k (by omega) : QRegister k (k + m)) x) = 0 := by
  rw [QRegExt.extractIndex_eq_zero_iff]
  intro i
  refine basisBits_idxSplitZero_of_not_mem _ x _ fun ⟨j, hj⟩ ↦ ?_
  have hv := congrArg Fin.val hj
  simp only [QRegister.block_apply_val] at hv
  omega
open scoped Matrix.Norms.L2Operator in
theorem norm_le_of_isQubitizedBlockEncodingUnitary {k m : ℕ} {α : ℝ} {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m))}
    (hBE : FullScaleBESector.IsQubitizedBlockEncodingUnitary α A U_BE) : ‖A‖ ≤ α := by
  rcases hBE with ⟨hα, _, hblock⟩
  let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
  let anc : QRegister m (k + m) := QRegister.block k m le_rfl
  let P₀ := anc.basisOutcomeProjector 0
  have hA_le : ‖A‖ ≤ ‖P₀ * sys.embedMatrix A * P₀‖ := by
    refine l2_opNorm_le_of_submatrix (idxSplitZero sys) A (P₀ * sys.embedMatrix A * P₀)
      fun x y ↦ ?_
    rw [show P₀ = Matrix.diagonal (fun g ↦ if anc.extractIndex g = 0 then (1 : ℂ) else 0)
        from anc.basisOutcomeProjector_eq_diagonal 0,
      Matrix.mul_diagonal, Matrix.diagonal_mul,
      ite_eq_left (lemHex31b k m x), ite_eq_left (lemHex31b k m y), one_mul, mul_one,
        embedMatrix_idxSplitZero]
  have hsand : P₀ * sys.embedMatrix A * P₀ = (α : ℂ) • (P₀ * U_BE.1 * P₀) := by
    have hα_ne : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
    rw [hblock, smul_smul, mul_inv_cancel₀ hα_ne, one_smul]
  have hP₀ : ‖P₀‖ ≤ 1 := l2_opNorm_basisOutcomeProjector_le_one anc 0
  have hPU : ‖P₀ * U_BE.1 * P₀‖ ≤ 1 :=
    (norm_mul_le _ _).trans <| (mul_le_of_le_one_right (norm_nonneg _) hP₀).trans <|
      (norm_mul_le _ _).trans <|
        (mul_le_of_le_one_right (norm_nonneg _)
          (norm_of_mem_unitaryGroup_le_one U_BE.2)).trans hP₀
  refine hA_le.trans ?_
  rw [hsand, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  exact mul_le_of_le_one_right (le_of_lt hα) hPU
open scoped Matrix.Norms.L2Operator in
theorem ApproximatesTimeEvolution.of_perturbation_direct {k m : ℕ}
    (Heff H P : Operator (2 ^ k)) (t ε ε_BE : ℝ) (W : Unitary (2 ^ (k + m))) (ht : 0 ≤ t)
    (hHeff : Heff.IsHermitian) (hH : H.IsHermitian) (hP_herm : P.IsHermitian)
    (hP_idem : P * P = P) (hCommHeff : Heff * P = P * Heff) (hCommH : H * P = P * H)
    (hDiff : ‖P * (Heff - H) * P‖ ≤ ε_BE)
    (hEvol : ApproximatesTimeEvolution Heff t (ε - t * ε_BE) P W) : ApproximatesTimeEvolution
    H t ε P W := by
  rcases hEvol with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let input := sys.embedMatrix P * anc.basisOutcomeProjector 0
  let U_Heff := NormedSpace.exp ((-Complex.I * (t : ℂ)) • Heff)
  let U_H := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
  have h_split : (W.1 - Complex.exp (φ * Complex.I) • sys.embedMatrix U_H) * input =
      (W.1 - Complex.exp (φ * Complex.I) • sys.embedMatrix U_Heff) * input + Complex.exp
        (φ * Complex.I) •
          (sys.embedMatrix ((U_Heff - U_H) * P) * anc.basisOutcomeProjector 0) := by
    dsimp only [input]
    rw [sys.embedMatrix_mul, embedMatrix_sub,
      Matrix.mul_assoc (sys.embedMatrix U_Heff - sys.embedMatrix U_H),
      Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul, smul_sub,
      smul_mul_assoc, smul_mul_assoc, sub_add_sub_cancel]
  have h_rem : ‖Complex.exp (φ * Complex.I) • (sys.embedMatrix ((U_Heff - U_H) * P) *
      anc.basisOutcomeProjector 0)‖ ≤ t * ε_BE := by
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I φ, one_mul]
    exact (norm_mul_le _ _).trans <|
      (mul_le_of_le_one_right (norm_nonneg _)
        (norm_basisOutcomeProjector_le_one anc 0)).trans <|
        (norm_embedMatrix_le sys _).trans
          (norm_exp_sub_exp_mul_projector_le Heff H P t ε_BE ht
            hHeff hH hP_herm hP_idem hCommHeff hCommH hDiff)
  change ‖(W.1 - Complex.exp (φ * Complex.I) • sys.embedMatrix U_H) * input‖ ≤ ε
  rw [h_split]
  linarith [norm_add_le ((W.1 - Complex.exp (φ * Complex.I) • sys.embedMatrix U_Heff) * input)
    (Complex.exp (φ * Complex.I) •
      (sys.embedMatrix ((U_Heff - U_H) * P) * anc.basisOutcomeProjector 0)), hφ, h_rem]
end BridgeDuhamel
end SpecsAux
end
end ModBridgeDuhamel

section ModPhaseGradCatalystCore
@[expose] public section
namespace SpecsAux
open Operator SpecsAux.SpecMirror
namespace PhaseGradCatalystCore
open Matrix QProg HermitianMat Circuit
open scoped Matrix ComplexOrder MatrixOrder QHLExpectation
noncomputable instance instHPowComplexRealCompat : HPow ℂ ℝ ℂ := ⟨fun z r ↦ z ^ (r : ℂ)⟩
noncomputable def phaseGradientState (b : ℕ) : Fin (2 ^ b) → ℂ :=
  fun m ↦ ((2 : ℝ) ^ (-(b : ℝ) / 2) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * (m.val : ℂ)) / 2 ^ b)
section PhaseGradPrep97
variable {n : ℕ}
def hadamardAll {b : ℕ} (rCoin : QRegister b n) : Circuit n :=
  Circuit.sequence (List.ofFn fun i : Fin b ↦ Circuit.H (rCoin i))
@[simp] theorem hadamardAll_count_T {b : ℕ} (rCoin : QRegister b n) :
    (hadamardAll rCoin).count PrimitiveGate.T = 0 := by
  simp [hadamardAll, List.sum_ofFn]
@[simp] theorem hadamardAll_count_TOFF {b : ℕ} (rCoin : QRegister b n) :
    (hadamardAll rCoin).count PrimitiveGate.TOFF = 0 := by
  simp [hadamardAll, List.sum_ofFn]
end PhaseGradPrep97
section CatalystSandwichAlgebra
theorem norm_mul_le_of_left_le_one {A : Type*} [NormedRing A] {U X : A} (hU : ‖U‖ ≤ 1) :
    ‖U * X‖ ≤ ‖X‖ :=
  (norm_mul_le U X).trans
    ((mul_le_mul_of_nonneg_right hU (norm_nonneg X)).trans (one_mul ‖X‖).le)
theorem norm_mul_le_of_right_le_one {A : Type*} [NormedRing A] {X U : A} (hU : ‖U‖ ≤ 1) :
    ‖X * U‖ ≤ ‖X‖ :=
  (norm_mul_le X U).trans (mul_le_of_le_one_right (norm_nonneg X) hU)
theorem norm_pow_mul_le_of_le_one {A : Type*} [NormedRing A] {W : A} (hW : ‖W‖ ≤ 1) :
    ∀ (R : ℕ) (X : A), ‖W ^ R * X‖ ≤ ‖X‖
  | 0, _ => by simp
  | r + 1, X => by
      rw [pow_succ', mul_assoc]
      exact (norm_mul_le_of_left_le_one hW).trans (norm_pow_mul_le_of_le_one hW r X)
theorem catalyst_pow_commute_of_step {A : Type*} [Monoid A] (U_cat W_seg W_sys_anc P_Cat0 : A)
    (hCat_step : W_seg * U_cat * P_Cat0 = U_cat * W_sys_anc * P_Cat0)
    (hComm_Cat : W_sys_anc * P_Cat0 = P_Cat0 * W_sys_anc) :
    ∀ R : ℕ, W_seg ^ R * U_cat * P_Cat0 = U_cat * W_sys_anc ^ R * P_Cat0
  | 0 => by simp
  | r + 1 => by
      have ih :=
        catalyst_pow_commute_of_step U_cat W_seg W_sys_anc P_Cat0 hCat_step hComm_Cat r
      calc W_seg ^ (r + 1) * U_cat * P_Cat0
          = W_seg ^ r * (W_seg * U_cat * P_Cat0) := by rw [pow_succ]; simp only [mul_assoc]
        _ = (W_seg ^ r * U_cat * P_Cat0) * W_sys_anc := by
            rw [hCat_step, mul_assoc U_cat W_sys_anc P_Cat0, hComm_Cat]
            simp only [mul_assoc]
        _ = U_cat * W_sys_anc ^ (r + 1) * P_Cat0 := by
            rw [ih, mul_assoc (U_cat * W_sys_anc ^ r) P_Cat0 W_sys_anc, ← hComm_Cat, pow_succ]
            simp only [mul_assoc]
theorem catalyst_sandwich_sub_target_eq {A : Type*} [Ring A]
    (V_inv V_prep U_cat W_R W_sys_R T P_anc P_in : A) (hV_inv : V_inv * V_prep = 1)
    (hPanc_Pin : P_anc * P_in = P_in) (hPanc_T : P_anc * (T * P_in) = T * P_in)
    (hPow_Pin : W_R * U_cat * P_in = U_cat * W_sys_R * P_in) : (V_inv * W_R * V_prep - T) *
    P_in = V_inv * (W_R * (((V_prep - U_cat) * P_anc) * P_in)) + V_inv *
    (U_cat * ((W_sys_R - T) * P_in)) + V_inv * (((U_cat - V_prep) * P_anc) * (T * P_in)) := by
  have ht1 : V_inv * (W_R * (((V_prep - U_cat) * P_anc) * P_in)) =
      V_inv * W_R * V_prep * P_in - V_inv * (U_cat * W_sys_R * P_in) := by
    rw [mul_assoc (V_prep - U_cat) P_anc P_in, hPanc_Pin, sub_mul, mul_sub, mul_sub]
    simp only [mul_assoc, ← hPow_Pin]
  have ht3 : V_inv * (((U_cat - V_prep) * P_anc) * (T * P_in)) =
      V_inv * U_cat * (T * P_in) - T * P_in := by
    rw [mul_assoc (U_cat - V_prep) P_anc (T * P_in), hPanc_T, sub_mul, mul_sub,
      ← mul_assoc V_inv V_prep, hV_inv, one_mul, ← mul_assoc]
  rw [sub_mul, ht1, ht3]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel
theorem norm_catalyst_sandwich_sub_le {A : Type*} [NormedRing A]
    (V_inv V_prep U_cat W_seg W_sys_anc T P_Cat0 P_anc P_in : A) (R : ℕ)
    (hV_inv : V_inv * V_prep = 1) (hV_inv_norm : ‖V_inv‖ ≤ 1) (hW_norm : ‖W_seg‖ ≤ 1)
    (hU_norm : ‖U_cat‖ ≤ 1) (hPin_norm : ‖P_in‖ ≤ 1) (hTPin_norm : ‖T * P_in‖ ≤ 1)
    (hPCat_Pin : P_Cat0 * P_in = P_in) (hPanc_Pin : P_anc * P_in = P_in)
    (hPanc_T : P_anc * (T * P_in) = T * P_in)
    (hCat_step : W_seg * U_cat * P_Cat0 = U_cat * W_sys_anc * P_Cat0)
    (hComm_Cat : W_sys_anc * P_Cat0 = P_Cat0 * W_sys_anc) : ‖(V_inv * W_seg ^ R * V_prep - T)
    * P_in‖ ≤ ‖(W_sys_anc ^ R - T) * P_in‖ + 2 * ‖(V_prep - U_cat) * P_anc‖ := by
  have hPow_Pin : W_seg ^ R * U_cat * P_in = U_cat * W_sys_anc ^ R * P_in := by
    rw [← hPCat_Pin, ← mul_assoc (W_seg ^ R * U_cat),
      catalyst_pow_commute_of_step U_cat W_seg W_sys_anc P_Cat0 hCat_step hComm_Cat R,
      mul_assoc (U_cat * W_sys_anc ^ R), hPCat_Pin]
  rw [catalyst_sandwich_sub_target_eq V_inv V_prep U_cat (W_seg ^ R) (W_sys_anc ^ R)
    T P_anc P_in hV_inv hPanc_Pin hPanc_T hPow_Pin]
  have h1 : ‖V_inv * (W_seg ^ R * (((V_prep - U_cat) * P_anc) * P_in))‖ ≤
      ‖(V_prep - U_cat) * P_anc‖ :=
    (norm_mul_le_of_left_le_one hV_inv_norm).trans <|
      (norm_pow_mul_le_of_le_one hW_norm R _).trans (norm_mul_le_of_right_le_one hPin_norm)
  have h2 : ‖V_inv * (U_cat * ((W_sys_anc ^ R - T) * P_in))‖ ≤ ‖(W_sys_anc ^ R - T) * P_in‖ :=
    (norm_mul_le_of_left_le_one hV_inv_norm).trans (norm_mul_le_of_left_le_one hU_norm)
  have h3 : ‖V_inv * (((U_cat - V_prep) * P_anc) * (T * P_in))‖ ≤
      ‖(V_prep - U_cat) * P_anc‖ := by
    refine (norm_mul_le_of_left_le_one hV_inv_norm).trans
      ((norm_mul_le_of_right_le_one hTPin_norm).trans ?_)
    rw [← neg_sub V_prep U_cat, neg_mul, norm_neg]
  exact (norm_add_le _ _).trans <|
    (add_le_add (norm_add_le _ _) le_rfl).trans (by linarith)
open scoped Matrix.Norms.L2Operator in
theorem norm_of_mem_unitaryGroup_le_one {d : Type*} [Fintype d] [DecidableEq d]
    {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) : ‖U‖ ≤ 1 :=
  BridgeDuhamel.norm_of_mem_unitaryGroup_le_one hU
open scoped Matrix.Norms.L2Operator in
theorem norm_projector_le_one {d : Type*} [Fintype d] [DecidableEq d] (P : Matrix d d ℂ)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P) : ‖P‖ ≤ 1 :=
    SubmatrixOpNorm.l2_opNorm_projector_le_one P hP_herm hP_idem
open scoped Matrix.Norms.L2Operator in
theorem norm_basisOutcomeProjector_le_one {n m : ℕ} (r : QRegister m n) (o : Fin (2 ^ m)) :
    ‖r.basisOutcomeProjector o‖ ≤ 1 :=
  SubmatrixOpNorm.l2_opNorm_basisOutcomeProjector_le_one r o
noncomputable def unitarySandwichPow {n : ℕ} (U_inv W U : Unitary (2 ^ n)) (R : ℕ) :
    Unitary (2 ^ n) := U_inv * W ^ R * U
open scoped Matrix.Norms.L2Operator in
theorem approximatesTimeEvolution_of_catalyst_sandwich {k m : ℕ}
    (H P : Operator (2 ^ k)) (t ε_evol δ_prep : ℝ) (R : ℕ)
    (V_inv V_prep U_cat W_seg W_sys_anc : Unitary (2 ^ (k + m)))
    (P_Cat0 : Operator (2 ^ (k + m)))
    (hV_inv : V_inv.1 * V_prep.1 = 1)
    (hH : H.IsHermitian)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P)
    (hPCat_Pin :
      let sys : QRegister k (k + m) := .block 0 k (by omega)
      let anc : QRegister m (k + m) := .block k m le_rfl
      P_Cat0 * (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
        sys.embedMatrix P * anc.basisOutcomeProjector 0)
    (hCat_step : W_seg.1 * U_cat.1 * P_Cat0 = U_cat.1 * W_sys_anc.1 * P_Cat0)
    (hComm_Cat : W_sys_anc.1 * P_Cat0 = P_Cat0 * W_sys_anc.1)
    (hPrep :
      let anc : QRegister m (k + m) := .block k m le_rfl
      ‖(V_prep.1 - U_cat.1) * anc.basisOutcomeProjector 0‖ ≤ δ_prep)
    (hEvol : ApproximatesTimeEvolution H t ε_evol P (W_sys_anc ^ R)) :
    ApproximatesTimeEvolution H t (ε_evol + 2 * δ_prep) P
      (unitarySandwichPow V_inv W_seg V_prep R) := by
  rcases hEvol with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let P_anc := anc.basisOutcomeProjector 0
  let P_in := sys.embedMatrix P * P_anc
  let U_exp : Operator (2 ^ k) := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
  let T : Operator (2 ^ (k + m)) := Complex.exp (φ * Complex.I) • sys.embedMatrix U_exp
  have hComm (X : Operator (2 ^ k)) : P_anc * sys.embedMatrix X = sys.embedMatrix X * P_anc :=
    (sys.embedMatrix_comm_of_disjoint anc
      (QRegister.block_disjoint_of_le 0 k k m (by omega) le_rfl (by omega)) X (compProj 0)).symm
  have hPanc_Pin : P_anc * P_in = P_in := by
    rw [← Matrix.mul_assoc, hComm P, Matrix.mul_assoc, anc.basisOutcomeProjector_mul_self 0]
  have hPanc_T : P_anc * (T * P_in) = T * P_in := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hComm U_exp,
      Matrix.mul_assoc, hPanc_Pin]
  have hPin_norm : ‖P_in‖ ≤ 1 :=
    (norm_mul_le_of_right_le_one (norm_basisOutcomeProjector_le_one anc 0)).trans
      ((BridgeDuhamel.norm_embedMatrix_le sys P).trans (norm_projector_le_one P hP_herm hP_idem))
  have hT_norm : ‖T‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_of_mem_unitaryGroup_le_one
      (sys.embedUnitary ⟨U_exp, BridgeDuhamel.exp_neg_I_smul_mem_unitaryGroup t H hH⟩).2
  change ‖((unitarySandwichPow V_inv W_seg V_prep R).1 - T) * P_in‖ ≤ ε_evol + 2 * δ_prep
  rw [unitarySandwichPow, Submonoid.coe_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  have hMain := norm_catalyst_sandwich_sub_le V_inv.1 V_prep.1 U_cat.1 W_seg.1 W_sys_anc.1 T
    P_Cat0 P_anc P_in R hV_inv (norm_of_mem_unitaryGroup_le_one V_inv.2)
    (norm_of_mem_unitaryGroup_le_one W_seg.2) (norm_of_mem_unitaryGroup_le_one U_cat.2)
    hPin_norm ((norm_mul_le_of_left_le_one hT_norm).trans hPin_norm)
    hPCat_Pin hPanc_Pin hPanc_T hCat_step hComm_Cat
  linarith [hMain, SubmonoidClass.coe_pow W_sys_anc R ▸ hφ, hPrep]
end CatalystSandwichAlgebra
section ParametricPrepLifting
variable {n m_anc : ℕ}
theorem basisOutcomeProjector_zero_compose_mul {m ℓ : ℕ} (rAnc : QRegister m n)
    (inner : QRegister ℓ m) : (rAnc.compose inner).basisOutcomeProjector 0 *
    rAnc.basisOutcomeProjector 0 = rAnc.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  by_cases hg : rAnc.extractIndex g = 0
  · have hsub : (rAnc.compose inner).extractIndex g = 0 := by
      rw [QRegExt.extractIndex_eq_zero_iff] at hg ⊢
      exact fun j ↦ hg (inner j)
    simp [hsub, hg]
  · simp [hg]
end ParametricPrepLifting
section CatalystIntertwine
def IntertwinesCat {N : ℕ} (U_cat P_Cat0 M_cat M_eff : Operator N) : Prop := M_cat *
    U_cat * P_Cat0 = U_cat * M_eff * P_Cat0 ∧ M_eff * U_cat = U_cat * M_eff ∧ M_eff * P_Cat0 =
    P_Cat0 * M_eff
theorem IntertwinesCat.one {N : ℕ} (U_cat P_Cat0 : Operator N) :
    IntertwinesCat U_cat P_Cat0 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp
theorem IntertwinesCat.refl_of_comm {N : ℕ} {U_cat P_Cat0 M : Operator N}
    (hU : M * U_cat = U_cat * M) (hP : M * P_Cat0 = P_Cat0 * M) :
    IntertwinesCat U_cat P_Cat0 M M :=
  ⟨by rw [hU], hU, hP⟩
theorem IntertwinesCat.mul {N : ℕ} {U_cat P_Cat0 A_cat A_eff B_cat B_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff)
    (hB : IntertwinesCat U_cat P_Cat0 B_cat B_eff) :
    IntertwinesCat U_cat P_Cat0 (A_cat * B_cat) (A_eff * B_eff) := by
  refine ⟨?_, ?_, ?_⟩
  · calc (A_cat * B_cat) * U_cat * P_Cat0
      _ = A_cat * (U_cat * B_eff * P_Cat0) := by simp only [Matrix.mul_assoc, hB.1]
      _ = (A_cat * U_cat * P_Cat0) * B_eff := by
          rw [Matrix.mul_assoc U_cat B_eff P_Cat0, hB.2.2]
          simp only [Matrix.mul_assoc]
      _ = U_cat * (A_eff * B_eff) * P_Cat0 := by
          rw [hA.1, Matrix.mul_assoc (U_cat * A_eff) P_Cat0 B_eff, ← hB.2.2]
          simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hB.2.1, ← Matrix.mul_assoc, hA.2.1, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hB.2.2, ← Matrix.mul_assoc, hA.2.2, Matrix.mul_assoc]
theorem IntertwinesCat.add {N : ℕ} {U_cat P_Cat0 A_cat A_eff B_cat B_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff)
    (hB : IntertwinesCat U_cat P_Cat0 B_cat B_eff) :
    IntertwinesCat U_cat P_Cat0 (A_cat + B_cat) (A_eff + B_eff) :=
  ⟨by simp only [Matrix.add_mul, Matrix.mul_add, hA.1, hB.1],
    by rw [Matrix.add_mul, Matrix.mul_add, hA.2.1, hB.2.1],
    by rw [Matrix.add_mul, Matrix.mul_add, hA.2.2, hB.2.2]⟩
theorem IntertwinesCat.neg {N : ℕ} {U_cat P_Cat0 A_cat A_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff) :
    IntertwinesCat U_cat P_Cat0 (-A_cat) (-A_eff) :=
  ⟨by simp only [Matrix.neg_mul, Matrix.mul_neg, hA.1],
    by simp only [Matrix.neg_mul, Matrix.mul_neg, hA.2.1],
    by simp only [Matrix.neg_mul, Matrix.mul_neg, hA.2.2]⟩
theorem IntertwinesCat.sub {N : ℕ} {U_cat P_Cat0 A_cat A_eff B_cat B_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff)
    (hB : IntertwinesCat U_cat P_Cat0 B_cat B_eff) :
    IntertwinesCat U_cat P_Cat0 (A_cat - B_cat) (A_eff - B_eff) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg
theorem IntertwinesCat.pow {N : ℕ} {U_cat P_Cat0 A_cat A_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff) :
    ∀ d : ℕ, IntertwinesCat U_cat P_Cat0 (A_cat ^ d) (A_eff ^ d)
  | 0 => by simpa using IntertwinesCat.one U_cat P_Cat0
  | d + 1 => by simpa only [pow_succ] using (hA.pow d).mul hA
theorem IntertwinesCat.sum {N : ℕ} {ι : Type*} (s : Finset ι)
    {U_cat P_Cat0 : Operator N} (F_cat F_eff : ι → Operator N)
    (hF : ∀ x ∈ s, IntertwinesCat U_cat P_Cat0 (F_cat x) (F_eff x)) :
    IntertwinesCat U_cat P_Cat0 (∑ x ∈ s, F_cat x) (∑ x ∈ s, F_eff x) := by
  classical
  induction s using Finset.induction_on with
  | empty => refine ⟨?_, ?_, ?_⟩ <;> simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun x hx ↦ hF x (Finset.mem_insert_of_mem hx))
theorem IntertwinesCat.unitary_star {N : ℕ} {U_cat P_Cat0 : Operator N}
    (hP_sa : star P_Cat0 = P_Cat0) (B_cat B_eff : Unitary N)
    (h : IntertwinesCat U_cat P_Cat0 B_cat.1 B_eff.1) : IntertwinesCat U_cat P_Cat0
    (star B_cat.1) (star B_eff.1) := by
  have hP_comm : star B_eff.1 * P_Cat0 = P_Cat0 * star B_eff.1 := by
    simpa only [star_mul, hP_sa] using (congrArg star h.2.2).symm
  have hU_comm : star B_eff.1 * U_cat = U_cat * star B_eff.1 := by
    calc star B_eff.1 * U_cat
      _ = star B_eff.1 * (U_cat * B_eff.1) * star B_eff.1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, B_eff.2.2, Matrix.mul_one]
      _ = U_cat * star B_eff.1 := by
          rw [← h.2.1, ← Matrix.mul_assoc, B_eff.2.1, Matrix.one_mul]
  refine ⟨?_, hU_comm, hP_comm⟩
  calc star B_cat.1 * U_cat * P_Cat0
    _ = star B_cat.1 * (U_cat * B_eff.1 * P_Cat0) * star B_eff.1 := by
        rw [← Matrix.mul_one (star B_cat.1 * U_cat), ← B_eff.2.2]
        simp only [Matrix.mul_assoc]
        rw [← hP_comm]
    _ = U_cat * star B_eff.1 * P_Cat0 := by
        rw [← h.1]
        simp only [← Matrix.mul_assoc, B_cat.2.1, Matrix.one_mul]
        rw [Matrix.mul_assoc, ← hP_comm, ← Matrix.mul_assoc]
theorem IntertwinesCat.embedMatrix {m n : ℕ} (r : QRegister m n)
    {U_cat P_Cat0 M_cat M_eff : Operator (2 ^ m)}
    (h : IntertwinesCat U_cat P_Cat0 M_cat M_eff) : IntertwinesCat (r.embedMatrix U_cat)
    (r.embedMatrix P_Cat0) (r.embedMatrix M_cat) (r.embedMatrix M_eff) :=
  ⟨by simpa only [r.embedMatrix_mul] using congrArg r.embedMatrix h.1,
    by simpa only [r.embedMatrix_mul] using congrArg r.embedMatrix h.2.1,
    by simpa only [r.embedMatrix_mul] using congrArg r.embedMatrix h.2.2⟩
theorem intertwinesCat_of_disjoint {N k_cat m_sub : ℕ} (rSub : QRegister m_sub N)
    (rCat : QRegister k_cat N) (hdisj : rSub.DisjointWires rCat)
    (U_cat_0 : Unitary (2 ^ k_cat)) (M : Operator (2 ^ m_sub)) : IntertwinesCat
    (rCat.embedUnitary U_cat_0).1 (rCat.basisOutcomeProjector 0) (rSub.embedMatrix M)
    (rSub.embedMatrix M) := IntertwinesCat.refl_of_comm
    (rSub.embedMatrix_comm_of_disjoint rCat hdisj M U_cat_0.1)
    (rSub.embedMatrix_comm_of_disjoint rCat hdisj M (compProj 0))
end CatalystIntertwine
end PhaseGradCatalystCore
end SpecsAux
end
end ModPhaseGradCatalystCore

section ModAdaptiveCleanScheduleEndpoint
@[expose] public section
namespace AdaptiveCleanScheduleEndpointAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k)
    (i : Fin m) : (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
end AdaptiveCleanScheduleEndpointAlt
namespace SpecsAux
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux.SpecMirror
  BridgeDuhamel
open BridgeFermionicComm BridgeFermionicComm.SpecInner FullScaleBESector
open PhaseGradCatalystCore
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem approximatesTimeEvolution_embed_clean_work {k mAct mWork : ℕ}
    (H : Operator (2 ^ k)) (t ε : ℝ) (P : Operator (2 ^ k))
    (W_act : Unitary (2 ^ (k + mAct)))
    (h : ApproximatesTimeEvolution H t ε P W_act) :
    let rAct : QRegister (k + mAct) (k + (mAct + mWork)) := QRegister.block 0 (k + mAct) (by omega)
    ApproximatesTimeEvolution H t ε P (rAct.embedUnitary W_act) := by
  intro rAct
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  let sys_act : QRegister k (k + mAct) := .block 0 k (by omega)
  let anc_act : QRegister mAct (k + mAct) := .block k mAct le_rfl
  let sys_tot : QRegister k (k + (mAct + mWork)) := .block 0 k (by omega)
  let anc_tot : QRegister (mAct + mWork) (k + (mAct + mWork)) := .block k (mAct + mWork) le_rfl
  let scr_tot : QRegister mWork (k + (mAct + mWork)) := .block (k + mAct) mWork (by omega)
  have h_sys_comp : rAct.compose sys_act = sys_tot :=
    AdaptiveCleanScheduleEndpointAlt.qreg_ext fun i ↦ by
      ext; simp [rAct, sys_act, sys_tot]
  have hdisj_anc : (rAct.compose anc_act).DisjointWires scr_tot := by
    rw [QRegister.disjoint_iff]
    intro i j heq
    have hv := congrArg Fin.val heq
    simp [rAct, anc_act, scr_tot] at hv
    omega
  have h_anc_concat : (rAct.compose anc_act).concat scr_tot hdisj_anc = anc_tot :=
    AdaptiveCleanScheduleEndpointAlt.qreg_ext fun idx ↦
      Fin.addCases (m := mAct) (n := mWork)
        (motive := fun idx ↦
          ((rAct.compose anc_act).concat scr_tot hdisj_anc) idx = anc_tot idx)
        (fun i ↦ by
          ext
          simp [QRegister.concat_apply_left, rAct, anc_act, anc_tot])
        (fun j ↦ by
          ext
          simp [QRegister.concat_apply_right, scr_tot, anc_tot]
          omega) idx
  have h_anc_proj : anc_tot.basisOutcomeProjector 0 =
      rAct.embedMatrix (anc_act.basisOutcomeProjector 0) * scr_tot.basisOutcomeProjector 0 := by
    rw [← h_anc_concat, QRegExt.basisOutcomeProjector_concat_zero]
    exact congrArg (· * _) (QRegister.embedMatrix_compose rAct anc_act (compProj 0))
  have h_sys_emb (A : Operator (2 ^ k)) :
      sys_tot.embedMatrix A = rAct.embedMatrix (sys_act.embedMatrix A) := by
    rw [← h_sys_comp, QRegister.embedMatrix_compose]
  let U_exp := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
  let D_act := (W_act.1 - Complex.exp (φ * Complex.I) • sys_act.embedMatrix U_exp) *
      (sys_act.embedMatrix P * anc_act.basisOutcomeProjector 0)
  change ‖((rAct.embedUnitary W_act).1 - Complex.exp (φ * Complex.I) • sys_tot.embedMatrix
    U_exp) * (sys_tot.embedMatrix P * anc_tot.basisOutcomeProjector 0)‖ ≤ ε
  have h_eq : ((rAct.embedUnitary W_act).1 - Complex.exp (φ * Complex.I) • sys_tot.embedMatrix
      U_exp) * (sys_tot.embedMatrix P * anc_tot.basisOutcomeProjector 0) = rAct.embedMatrix
      D_act * scr_tot.basisOutcomeProjector 0 := by
    rw [QRegister.embedUnitary_val, h_sys_emb U_exp, h_sys_emb P, h_anc_proj,
      ← rAct.embedMatrix_smul, ← embedMatrix_sub, ← Matrix.mul_assoc,
      ← rAct.embedMatrix_mul, ← Matrix.mul_assoc, ← rAct.embedMatrix_mul]
    simp only [D_act, Matrix.mul_assoc]
  rw [h_eq]
  exact (norm_mul_le_of_right_le_one (BridgeDuhamel.norm_basisOutcomeProjector_le_one scr_tot
    0)).trans
    ((norm_embedMatrix_le rAct D_act).trans hφ)
theorem realizesUnitary_of_anc_eq {Var : Type} [DecidableEq Var]
    {kSys mAnc n : ℕ} [NeZero (2 ^ (kSys + mAnc))] {rSys : QRegister kSys n}
    {outcomes : Finset (Fin (2 ^ kSys))} {rAnc₁ rAnc₂ : QRegister mAnc n}
    (hEq : rAnc₁ = rAnc₂) {hDisj₁ : rSys.DisjointWires rAnc₁}
    {hDisj₂ : rSys.DisjointWires rAnc₂} {W : Unitary (2 ^ (kSys + mAnc))}
    {p : QProg Var (2 ^ n)} (h : RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys
    outcomes rAnc₁ hDisj₁ W p) : RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys
    outcomes rAnc₂ hDisj₂ W p :=
  hEq ▸ h
theorem cleanScheduleActWorkDisj {kSys mAct mWork n : ℕ} {rSys : QRegister kSys n}
    {rAnc : QRegister (mAct + mWork) n} (hdisj : rSys.DisjointWires rAnc) : (rSys.concat
    (rAnc.compose (QRegister.block 0 mAct (by omega))) (hdisj.compose_right _)).DisjointWires
    (rAnc.compose (QRegister.block mAct mWork (by omega))) := by
  let rActAnc : QRegister mAct n := rAnc.compose (QRegister.block 0 mAct (by omega))
  let rWork : QRegister mWork n := rAnc.compose (QRegister.block mAct mWork (by omega))
  let rAct : QRegister (kSys + mAct) n := rSys.concat rActAnc (hdisj.compose_right _)
  rw [QRegister.disjoint_iff]
  intro idx w heq
  refine Fin.addCases (m := kSys) (n := mAct)
    (motive := fun idx ↦ rAct idx = rWork w → False)
    (fun i hi ↦ by
      simp only [rAct, QRegister.concat_apply_left, rWork, QRegister.compose_apply]
        at hi
      exact hdisj.ne i _ hi)
    (fun i hi ↦ by
      simp only [rAct, QRegister.concat_apply_right, rActAnc, rWork, QRegister.compose_apply]
        at hi
      have hv := congrArg Fin.val (rAnc.wires.injective hi)
      simp at hv
      omega)
    idx heq
open Classical in
noncomputable def cleanScheduleProgramGen {Cfg Var : Type} {kSys mAct mWork n : ℕ}
    (R : Fin 10 → ℕ) (mkInit : (rAct : QRegister (kSys + mAct) n) → (rWork : QRegister mWork
    n) → rAct.DisjointWires rWork → DynamicCircuit Var n) (mkSeg : Cfg → Fin 10 → (rAct :
    QRegister (kSys + mAct) n) → (rWork : QRegister mWork n) → rAct.DisjointWires rWork →
    DynamicCircuit Var n) (mkUninit : (rAct : QRegister (kSys + mAct) n) → (rWork : QRegister
    mWork n) → rAct.DisjointWires rWork → DynamicCircuit Var n) (c : Cfg) (j : Fin 10)
    (rSys : QRegister kSys n) (rAnc : QRegister (mAct + mWork) n) : DynamicCircuit Var n :=
  if hdisj : rSys.DisjointWires rAnc then
    let rActAnc : QRegister mAct n := rAnc.compose (QRegister.block 0 mAct (by omega))
    let rWork : QRegister mWork n := rAnc.compose (QRegister.block mAct mWork (by omega))
    let rAct : QRegister (kSys + mAct) n := rSys.concat rActAnc (hdisj.compose_right _)
    let hDisjActWork : rAct.DisjointWires rWork := cleanScheduleActWorkDisj hdisj
    runScheduleCircuitAdaptive R
      (mkInit rAct rWork hDisjActWork)
      (fun j' ↦ mkSeg c j' rAct rWork hDisjActWork)
      (mkUninit rAct rWork hDisjActWork)
      j
  else
    .identity
end SpecsAux
end
end ModAdaptiveCleanScheduleEndpoint

section ModFullSysWalkStepEndpoint
@[expose] public section
set_option maxRecDepth 8192
namespace FullSysWalkStepEndpoint
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux
open BridgeDuhamel BridgeFermionicComm FullScaleBESector PhaseGradCatalystCore
open scoped Matrix BigOperators Matrix.Norms.L2Operator
section SystemBasisConjugation
theorem fullSys_zero_add_le (a b : ℕ) : 0 + a ≤ a + b :=
  (Nat.zero_add a).le.trans (Nat.le_add_right a b)
theorem exp_neg_I_smul_unitary_conj {d : ℕ} (U : Unitary d) (H : Operator d) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • (U.1 * H * U.1ᴴ)) =
      U.1 * NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) * U.1ᴴ := by
  let u : (Operator d)ˣ := ⟨U.1, U.1ᴴ, (Unitary.mem_iff.mp U.2).2, (Unitary.mem_iff.mp U.2).1⟩
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  simpa [u] using Matrix.exp_units_conj u ((-Complex.I * (t : ℂ)) • H)
theorem approximatesTimeEvolution_conj_sysUnitary {kSys mAnc : ℕ}
    (U_sys : Unitary (2 ^ kSys)) (H P : Operator (2 ^ kSys)) (t ε : ℝ)
    (W_mid : Unitary (2 ^ (kSys + mAnc)))
    (hMid : ApproximatesTimeEvolution
      (U_sys.1 * H * U_sys.1ᴴ) t ε (U_sys.1 * P * U_sys.1ᴴ) W_mid) :
    let sys : QRegister kSys (kSys + mAnc) := .block 0 kSys (fullSys_zero_add_le kSys mAnc)
    let U_full : Unitary (2 ^ (kSys + mAnc)) := sys.embedUnitary U_sys
    ApproximatesTimeEvolution H t ε P (U_full⁻¹ * W_mid * U_full) := by
  intro sys U_full
  rcases hMid with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  let anc : QRegister mAnc (kSys + mAnc) := .block kSys mAnc le_rfl
  let H' : Operator (2 ^ kSys) := U_sys.1 * H * U_sys.1ᴴ
  let P' : Operator (2 ^ kSys) := U_sys.1 * P * U_sys.1ᴴ
  let E : Operator (2 ^ kSys) := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
  let E' : Operator (2 ^ kSys) := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H')
  have hstar_sys : U_sys.1ᴴ * U_sys.1 = 1 := (Unitary.mem_iff.mp U_sys.2).1
  have hdisj : sys.DisjointWires anc := QRegister.block_disjoint_of_le 0 kSys kSys mAnc
    (fullSys_zero_add_le kSys mAnc) le_rfl (Nat.zero_add kSys).le
  have hU_inv_val : (U_full⁻¹).1 = sys.embedMatrix U_sys.1ᴴ := by
    change star (sys.embedUnitary U_sys).1 = sys.embedMatrix U_sys.1ᴴ
    rw [Matrix.star_eq_conjTranspose, QRegister.embedUnitary_val, ← sys.embedMatrix_conjTranspose]
  have hTarget : sys.embedMatrix E = (U_full⁻¹).1 * sys.embedMatrix E' * U_full.1 := by
    rw [hU_inv_val, QRegister.embedUnitary_val, show E' = U_sys.1 * E * U_sys.1ᴴ from
      exp_neg_I_smul_unitary_conj U_sys H t, ← sys.embedMatrix_mul, ← sys.embedMatrix_mul]
    exact congrArg sys.embedMatrix (by
      simp only [← Matrix.mul_assoc]
      rw [hstar_sys, Matrix.one_mul, Matrix.mul_assoc, hstar_sys, Matrix.mul_one])
  have hCommAnc : sys.embedMatrix U_sys.1 * anc.basisOutcomeProjector 0 =
      anc.basisOutcomeProjector 0 * sys.embedMatrix U_sys.1 :=
    sys.embedMatrix_comm_of_disjoint anc hdisj U_sys.1 (compProj 0)
  have hInput : U_full.1 * (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
      (sys.embedMatrix P' * anc.basisOutcomeProjector 0) * U_full.1 := by
    have hP_conj : U_sys.1 * P = P' * U_sys.1 := by
      dsimp only [P']; rw [Matrix.mul_assoc, hstar_sys, Matrix.mul_one]
    rw [QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← sys.embedMatrix_mul, hP_conj,
      sys.embedMatrix_mul, Matrix.mul_assoc, hCommAnc, ← Matrix.mul_assoc]
  let D' : Operator (2 ^ (kSys + mAnc)) :=
    (W_mid.1 - Complex.exp ((φ : ℂ) * Complex.I) • sys.embedMatrix E') *
      (sys.embedMatrix P' * anc.basisOutcomeProjector 0)
  have hDiff : ((U_full⁻¹ * W_mid * U_full).1 - Complex.exp ((φ : ℂ) * Complex.I) •
      sys.embedMatrix E) * (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
      (U_full⁻¹).1 * D' * U_full.1 := by
    have hSub : (U_full⁻¹ * W_mid * U_full).1 - Complex.exp ((φ : ℂ) * Complex.I) •
        sys.embedMatrix E = (U_full⁻¹).1 *
        (W_mid.1 - Complex.exp ((φ : ℂ) * Complex.I) • sys.embedMatrix E') * U_full.1 := by
      rw [Submonoid.coe_mul, Submonoid.coe_mul, hTarget,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hSub, Matrix.mul_assoc ((U_full⁻¹).1 *
      (W_mid.1 - Complex.exp ((φ : ℂ) * Complex.I) • sys.embedMatrix E')), hInput]
    simp only [D', Matrix.mul_assoc]
  change ‖((U_full⁻¹ * W_mid * U_full).1 - Complex.exp ((φ : ℂ) * Complex.I) • sys.embedMatrix
    E) * (sys.embedMatrix P * anc.basisOutcomeProjector 0)‖ ≤ ε
  rw [hDiff]
  exact (norm_mul_le_of_right_le_one (l2_opNorm_unitary_le_one U_full)).trans
    ((norm_mul_le_of_left_le_one (l2_opNorm_unitary_le_one U_full⁻¹)).trans hφ)
theorem unitarySandwichPow_conj_outer {k : ℕ} (U_full V_inv W_seg V_prep : Unitary (2 ^ k))
    (R : ℕ) : unitarySandwichPow (U_full⁻¹ * V_inv) W_seg (V_prep * U_full) R = U_full⁻¹ *
    unitarySandwichPow V_inv W_seg V_prep R * U_full := by
  simp only [unitarySandwichPow, mul_assoc]
noncomputable def cleanBasisScheduleProgramGen {Cfg Var : Type} {kSys mAct mWork n : ℕ}
    (R : Fin 10 → ℕ) (mkBasisFwd : (rAct : QRegister (kSys + mAct) n) → (rWork : QRegister
    mWork n) → rAct.DisjointWires rWork → DynamicCircuit Var n) (mkInit : (rAct : QRegister
    (kSys + mAct) n) → (rWork : QRegister mWork n) → rAct.DisjointWires rWork → DynamicCircuit
    Var n) (mkSeg : Cfg → Fin 10 → (rAct : QRegister (kSys + mAct) n) → (rWork : QRegister
    mWork n) → rAct.DisjointWires rWork → DynamicCircuit Var n) (mkUninit : (rAct : QRegister
    (kSys + mAct) n) → (rWork : QRegister mWork n) → rAct.DisjointWires rWork → DynamicCircuit
    Var n) (mkBasisInv : (rAct : QRegister (kSys + mAct) n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n) (c : Cfg) (j : Fin 10)
    (rSys : QRegister kSys n) (rAnc : QRegister (mAct + mWork) n) : DynamicCircuit Var n :=
    cleanScheduleProgramGen R (fun rAct rWork hD ↦ .seq (mkBasisFwd rAct rWork hD) (mkInit
    rAct rWork hD)) mkSeg (fun rAct rWork hD ↦ .seq (mkUninit rAct rWork hD) (mkBasisInv rAct
    rWork hD)) c j rSys rAnc
noncomputable abbrev cleanBasisScheduleProgram {Var : Type} {n mAct mWork : ℕ} :=
  @cleanBasisScheduleProgramGen
    SpecsAux.SpecMirror.Configuration Var SpecsAux.SpecMirror.systemQubits mAct mWork n
theorem cleanBasisSchedule_perHorizon_const_cost {Var : Type}
    {n mAct mWork cBasis_T cInit_T costCap : ℕ} (R wSeg_T : Fin 10 → ℕ) {mkBasisFwd mkInit
    mkUninit mkBasisInv : (rAct : QRegister (SpecsAux.SpecMirror.systemQubits + mAct) n) → (rWork :
    QRegister mWork n) → rAct.DisjointWires rWork → DynamicCircuit Var n} {mkSeg :
    SpecsAux.SpecMirror.Configuration → Fin 10 →
      (rAct : QRegister (SpecsAux.SpecMirror.systemQubits +
    mAct) n) → (rWork : QRegister mWork n) → rAct.DisjointWires rWork → DynamicCircuit Var n}
    (hBasisFwd_toff : ∀ rAct rWork hD, (mkBasisFwd rAct rWork hD).count PrimitiveGate.TOFF =
    0) (hInit_toff : ∀ rAct rWork hD, (mkInit rAct rWork hD).count PrimitiveGate.TOFF = 0)
    (hSeg_toff : ∀ c j rAct rWork hD, (mkSeg c j rAct rWork hD).count PrimitiveGate.TOFF = 0)
    (hUninit_toff : ∀ rAct rWork hD, (mkUninit rAct rWork hD).count PrimitiveGate.TOFF = 0)
    (hBasisInv_toff : ∀ rAct rWork hD, (mkBasisInv rAct rWork hD).count PrimitiveGate.TOFF =
    0) (hBasis_T : ∀ rAct rWork hD, (mkBasisFwd rAct rWork hD).count PrimitiveGate.T +
    (mkBasisInv rAct rWork hD).count PrimitiveGate.T ≤ cBasis_T) (hInit_T : ∀ rAct rWork hD,
    (mkInit rAct rWork hD).count PrimitiveGate.T + (mkUninit rAct rWork hD).count
    PrimitiveGate.T ≤ cInit_T) (hSeg_T : ∀ c j rAct rWork hD, (mkSeg c j rAct rWork hD).count
    PrimitiveGate.T ≤ wSeg_T j) (hCap : (SpecsAux.SpecMirror.systemQubits + (mAct + mWork)) * (50 *
    (10 * (cBasis_T + cInit_T) + ∑ j : Fin 10, R j * wSeg_T j)) ≤ costCap)
    (c : SpecsAux.SpecMirror.Configuration) (rSys : QRegister SpecsAux.SpecMirror.systemQubits n)
    (rAnc : QRegister (mAct + mWork) n) : (∀ j : Fin 10, (cleanBasisScheduleProgram R
    mkBasisFwd mkInit mkSeg mkUninit mkBasisInv c j rSys rAnc).count PrimitiveGate.TOFF = 0) ∧
    (SpecsAux.SpecMirror.systemQubits + (mAct + mWork)) * (50 * ∑ j : Fin 10,
    (cleanBasisScheduleProgram R mkBasisFwd mkInit mkSeg mkUninit mkBasisInv c j rSys
    rAnc).count PrimitiveGate.T) ≤ costCap := by
  classical
  let prog (j : Fin 10) :=
    cleanBasisScheduleProgram R mkBasisFwd mkInit mkSeg mkUninit mkBasisInv c j rSys rAnc
  by_cases hdisj : rSys.DisjointWires rAnc
  · refine ⟨fun j ↦ by
      simp [cleanBasisScheduleProgram, cleanBasisScheduleProgramGen, cleanScheduleProgramGen,
        dite_eq_left hdisj, count_runScheduleCircuitAdaptive, DynamicCircuit.count,
        hBasisFwd_toff, hInit_toff, hSeg_toff, hUninit_toff, hBasisInv_toff], ?_⟩
    have hEach (j : Fin 10) : (prog j).count PrimitiveGate.T ≤
        (cBasis_T + cInit_T) + R j * wSeg_T j := by
      simp only [prog, cleanBasisScheduleProgram, cleanBasisScheduleProgramGen,
        cleanScheduleProgramGen, dite_eq_left hdisj, count_runScheduleCircuitAdaptive,
        DynamicCircuit.count]
      have hB := hBasis_T _ _ (cleanScheduleActWorkDisj hdisj)
      have hI := hInit_T _ _ (cleanScheduleActWorkDisj hdisj)
      have hS := Nat.mul_le_mul_left (R j) (hSeg_T c j _ _ (cleanScheduleActWorkDisj hdisj))
      omega
    have hSum : (∑ j : Fin 10, (prog j).count PrimitiveGate.T) ≤
        10 * (cBasis_T + cInit_T) + ∑ j : Fin 10, R j * wSeg_T j :=
      (Finset.sum_le_sum fun j _ ↦ hEach j).trans (by simp [Finset.sum_add_distrib])
    exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 50 hSum)).trans hCap
  · refine ⟨fun j ↦ ?_, ?_⟩
    · simp [cleanBasisScheduleProgram, cleanBasisScheduleProgramGen, cleanScheduleProgramGen,
        dite_eq_right hdisj, DynamicCircuit.count]
    · simp [cleanBasisScheduleProgram, cleanBasisScheduleProgramGen, cleanScheduleProgramGen,
        dite_eq_right hdisj, DynamicCircuit.count]
end SystemBasisConjugation
end FullSysWalkStepEndpoint
end
end ModFullSysWalkStepEndpoint
section ModGhostGuardCircuitBridge
@[expose] public section
set_option maxRecDepth 2000000
namespace GhostGuardCircuitBridge
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SingleRBEGridGuardWalk
open scoped Matrix BigOperators Matrix.Norms.L2Operator
section ReflectionUnification
theorem singleRBEReflNegMatrix_eq_phaseOp_neg_one (k m : ℕ) (P : Operator (2 ^ k)) :
    singleRBEReflNegMatrix k m P = phaseOp (-1 : ℂ) (projGridAncZero k m P) :=
  (phaseOp_neg_one (projGridAncZero k m P)).symm
end ReflectionUnification
end GhostGuardCircuitBridge
end
end ModGhostGuardCircuitBridge

end QuantumComputation.Specs.StoppingPowerSolution
