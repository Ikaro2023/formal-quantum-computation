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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectMux

/-!
# Reversible Temporary-AND Compute/Uncompute Engine (`TempProg`)

Defines the `TempProg` AST of linear `CNOT`/`X` fan-ins and Gidney temporary `AND` gates (`0 TOFF`,
`4 T` per `AND`), `wrapDyn`, `cleanRealizes_mux`, and `O(1)` wire-embedding / subregister lifting.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore Operator Matrix Circuit QProg CleanDyn HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-- Flip the last bit `k_t + k_c` of `g : Fin (2 ^ (k_t + (k_c + 1)))` by `f (ctrlBits g)`. -/
def flipLastBitBy (k_t k_c : ℕ) (f : (Fin k_c → Bool) → Bool)
    (g : Fin (2 ^ (k_t + (k_c + 1)))) : Fin (2 ^ (k_t + (k_c + 1))) :=
  let rCtrlSub : QRegister k_c (k_t + (k_c + 1)) := QRegister.block k_t k_c (by omega)
  let b := f (bitsOfFin k_c (rCtrlSub.extractIndex g))
  (basisBits (k_t + (k_c + 1))).symm fun w ↦
    if w.val = k_t + k_c then
      basisBits (k_t + (k_c + 1)) g w + (if b then 1 else 0)
    else
      basisBits (k_t + (k_c + 1)) g w

theorem basisBits_flipLastBitBy (k_t k_c : ℕ) (f : (Fin k_c → Bool) → Bool)
    (g : Fin (2 ^ (k_t + (k_c + 1)))) (w : Wire (k_t + (k_c + 1))) :
    basisBits (k_t + (k_c + 1)) (flipLastBitBy k_t k_c f g) w =
      if w.val = k_t + k_c then
        basisBits (k_t + (k_c + 1)) g w +
          (if f (bitsOfFin k_c ((QRegister.block k_t k_c (by omega)).extractIndex g)) then 1 else 0)
      else
        basisBits (k_t + (k_c + 1)) g w := by
  simp [flipLastBitBy]

theorem extractCtrlSub_flipLastBitBy (k_t k_c : ℕ) (f : (Fin k_c → Bool) → Bool)
    (g : Fin (2 ^ (k_t + (k_c + 1)))) :
    (QRegister.block k_t k_c (by omega)).extractIndex (flipLastBitBy k_t k_c f g) =
      (QRegister.block k_t k_c (by omega)).extractIndex g := by
  apply (basisBits k_c).injective
  funext i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_flipLastBitBy]
  have hne : ((QRegister.block k_t k_c (by omega : k_t + k_c ≤ k_t + (k_c + 1))) i).val ≠
      k_t + k_c := by simp; omega
  exact ite_eq_right hne

theorem flipLastBitBy_comp (k_t k_c : ℕ) (f₁ f₂ : (Fin k_c → Bool) → Bool)
    (g : Fin (2 ^ (k_t + (k_c + 1)))) :
    flipLastBitBy k_t k_c f₂ (flipLastBitBy k_t k_c f₁ g) =
      flipLastBitBy k_t k_c (fun x ↦ xor (f₁ x) (f₂ x)) g := by
  apply (basisBits (k_t + (k_c + 1))).injective
  funext w
  rw [basisBits_flipLastBitBy, extractCtrlSub_flipLastBitBy, basisBits_flipLastBitBy,
    basisBits_flipLastBitBy]
  by_cases hw : w.val = k_t + k_c
  · rw [ite_eq_left hw, ite_eq_left hw, ite_eq_left hw, add_assoc]
    congr 1
    cases f₁ (bitsOfFin k_c ((QRegister.block k_t k_c (by omega)).extractIndex g)) <;>
      cases f₂ (bitsOfFin k_c ((QRegister.block k_t k_c (by omega)).extractIndex g)) <;> decide
  · simp [hw]

/-- Core local conjugation identity shared by `TempProg.linear` and `TempProg.andGate`. -/
theorem bitCompute_conj_muxOnAct_mul_proj0 (k_t k_c : ℕ)
    (f : (Fin k_c → Bool) → Bool)
    (C : Unitary (2 ^ (k_t + (k_c + 1))))
    (hC : ∀ g, C.1 *ᵥ Pi.single g 1 = Pi.single (flipLastBitBy k_t k_c f g) 1)
    (F' : (Fin (k_c + 1) → Bool) → Unitary (2 ^ k_t)) :
    let anc_loc : Wire (k_t + (k_c + 1)) := Fin.natAdd (k_t + k_c) (0 : Fin 1)
    let P₀_loc := (QRegister.singleton anc_loc).basisOutcomeProjector 0
    let rAct_sub : QRegister (k_t + k_c) (k_t + (k_c + 1)) := .block 0 (k_t + k_c) (by omega)
    C.1 * (muxOnAct k_t (k_c + 1) F').1 * C.1 * P₀_loc =
      (rAct_sub.embedUnitary (muxOnAct k_t k_c (fun x ↦ F' (Fin.snoc x (f x))))).1 * P₀_loc := by
  intro anc_loc P₀_loc rAct_sub
  ext a g
  have hlhs_vec := congrFun
    (show (C.1 * (muxOnAct k_t (k_c + 1) F').1 * C.1 * P₀_loc) *ᵥ Pi.single g 1 =
      ((rAct_sub.embedUnitary (muxOnAct k_t k_c (fun x ↦ F' (Fin.snoc x (f x))))).1 * P₀_loc) *ᵥ
        Pi.single g 1 from ?_) a
  · simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hlhs_vec
  have hmv1 : (C.1 * (muxOnAct k_t (k_c + 1) F').1 * C.1 * P₀_loc) *ᵥ Pi.single g 1 =
      (C.1 * (muxOnAct k_t (k_c + 1) F').1 * C.1) *ᵥ (P₀_loc *ᵥ Pi.single g 1) := by
    rw [Matrix.mulVec_mulVec]
  have hmv2 :
      ((rAct_sub.embedUnitary (muxOnAct k_t k_c (fun x ↦ F' (Fin.snoc x (f x))))).1 * P₀_loc) *ᵥ
        Pi.single g 1 =
      (rAct_sub.embedUnitary (muxOnAct k_t k_c (fun x ↦ F' (Fin.snoc x (f x))))).1 *ᵥ
        (P₀_loc *ᵥ Pi.single g 1) := by
    rw [Matrix.mulVec_mulVec]
  rw [hmv1, hmv2]
  have hp0_single : P₀_loc *ᵥ Pi.single g 1 =
      if (QRegister.singleton anc_loc).extractIndex g = 0 then Pi.single g 1 else 0 := by
    funext q
    rw [QRegister.basisOutcomeProjector_mulVec]
    by_cases hq : q = g
    · subst hq; split_ifs <;> simp
    · by_cases h0 : (QRegister.singleton anc_loc).extractIndex g = 0 <;>
        simp [h0, Pi.single_eq_of_ne hq]
  rw [hp0_single]
  by_cases h0 : (QRegister.singleton anc_loc).extractIndex g = 0
  · rw [ite_eq_left h0]
    have hbit0 : basisBits (k_t + (k_c + 1)) g anc_loc = 0 := by
      have h := (extractIndex_eq_zero_iff_basisBits_eq_zero
        (QRegister.singleton anc_loc) g).mp h0 0
      simpa using h
    let rT_big : QRegister k_t (k_t + (k_c + 1)) := QRegister.block 0 k_t (by omega)
    let rC_big : QRegister (k_c + 1) (k_t + (k_c + 1)) := QRegister.block k_t (k_c + 1) (by omega)
    let rC_sub : QRegister k_c (k_t + (k_c + 1)) := QRegister.block k_t k_c (by omega)
    let x := bitsOfFin k_c (rC_sub.extractIndex g)
    let g₁ := flipLastBitBy k_t k_c f g
    have hc₁_bits : bitsOfFin (k_c + 1) (rC_big.extractIndex g₁) = Fin.snoc x (f x) := by
      funext j
      induction j using Fin.lastCases with
      | last =>
          simp only [g₁, Fin.snoc_last, bitsOfFin, QRegister.basisBits_extractIndex,
            basisBits_flipLastBitBy]
          have hw : (rC_big (Fin.last k_c)).val = k_t + k_c := by simp [rC_big]
          have hweq : rC_big (Fin.last k_c) = anc_loc := by ext; simp [rC_big, anc_loc]
          rw [ite_eq_left hw, hweq, hbit0, zero_add]
          cases f x <;> decide
      | cast i =>
          simp only [g₁, Fin.snoc_castSucc, bitsOfFin, QRegister.basisBits_extractIndex,
            basisBits_flipLastBitBy]
          have hne : (rC_big i.castSucc).val ≠ k_t + k_c := by simp [rC_big]; omega
          rw [ite_eq_right hne]
          change decide (basisBits (k_t + (k_c + 1)) g (rC_big i.castSucc) = 1) =
            decide (basisBits k_c (rC_sub.extractIndex g) i = 1)
          rw [QRegister.basisBits_extractIndex]
          rfl
    simp only [← Matrix.mulVec_mulVec]
    rw [hC g]
    have hg₁_proj (q : Fin (2 ^ (k_t + (k_c + 1))))
        (hq : rC_big.extractIndex q ≠ rC_big.extractIndex g₁) :
        Pi.single (M := fun _ ↦ ℂ) g₁ 1 q = 0 := by
      rw [Pi.single_eq_of_ne]; rintro rfl; exact hq rfl
    change C.1 *ᵥ ((muxOnAct k_t (k_c + 1) F').1 *ᵥ Pi.single g₁ 1) = _
    rw [show muxOnAct k_t (k_c + 1) F' =
          muxUnitary rC_big rT_big _ (fun c ↦ F' (bitsOfFin (k_c + 1) c)) from rfl,
      muxUnitary_mulVec_of_proj rC_big rT_big _ _ (rC_big.extractIndex g₁) _ hg₁_proj,
      hc₁_bits]
    let M := (F' (Fin.snoc x (f x))).1
    have hM_expand (h : Fin (2 ^ (k_t + (k_c + 1)))) :
        (rT_big.embedMatrix M) *ᵥ Pi.single h 1 =
          ∑ t' : Fin (2 ^ k_t), M t' (rT_big.extractIndex h) •
            Pi.single (rT_big.replaceIndex h t') 1 := by
      rw [rT_big.embedMatrix_mulVec_single_factors]
      have hvec : M *ᵥ Pi.single (rT_big.extractIndex h) 1 =
          ∑ t' : Fin (2 ^ k_t), M t' (rT_big.extractIndex h) • Pi.single t' 1 := by
        funext t'
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hvec]
      funext q
      have hsum_ts (u : Fin (2 ^ k_t) → ℂ) :
          rT_big.tensorState (∑ t', u t' • Pi.single t' 1)
            (Pi.single (rT_big.basisSplitEquiv h).2 1) q =
          (∑ t', (u t' • rT_big.tensorState (Pi.single t' 1)
            (Pi.single (rT_big.basisSplitEquiv h).2 1))) q := by
        simp only [QRegister.tensorState, Finset.sum_apply, Pi.smul_apply,
          Finset.sum_mul, smul_mul_assoc]
      have hts := hsum_ts (fun t' ↦ M t' (rT_big.extractIndex h))
      simpa only [rT_big.tensorState_single_replaceIndex] using hts
    rw [hM_expand g₁, Matrix.mulVec_sum]
    have ht_eq : rT_big.extractIndex g₁ = rT_big.extractIndex g := by
      apply (basisBits k_t).injective; funext i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        basisBits_flipLastBitBy]
      have hne : (rT_big i).val ≠ k_t + k_c := by simp [rT_big]; omega
      exact ite_eq_right hne
    have hflip_rep (t' : Fin (2 ^ k_t)) :
        flipLastBitBy k_t k_c f (rT_big.replaceIndex g₁ t') = rT_big.replaceIndex g t' := by
      have hctrl_rep : rC_sub.extractIndex (rT_big.replaceIndex g₁ t') = rC_sub.extractIndex g := by
        have h1 : rC_sub.extractIndex (rT_big.replaceIndex g₁ t') = rC_sub.extractIndex g₁ := by
          apply (basisBits k_c).injective; funext i
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
            rT_big.basisBits_replaceIndex_of_not_mem]
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; simp [rT_big, rC_sub] at hv; omega
        rw [h1, extractCtrlSub_flipLastBitBy]
      apply (basisBits (k_t + (k_c + 1))).injective; funext w
      rw [basisBits_flipLastBitBy, hctrl_rep]
      by_cases hw : w.val = k_t + k_c
      · rw [ite_eq_left hw]
        have hnot : w ∉ Set.range rT_big.wires := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; simp [rT_big] at hv; omega
        rw [rT_big.basisBits_replaceIndex_of_not_mem _ _ w hnot,
          rT_big.basisBits_replaceIndex_of_not_mem _ _ w hnot,
          basisBits_flipLastBitBy, ite_eq_left hw, add_assoc]
        have h2 : (if f x then (1 : ZMod 2) else 0) + (if f x then 1 else 0) = 0 := by
          cases f x <;> decide
        change _ + ((if f x then (1 : ZMod 2) else 0) + (if f x then 1 else 0)) = _
        rw [h2, add_zero]
      · rw [ite_eq_right hw]
        by_cases hmem : w ∈ Set.range rT_big.wires
        · obtain ⟨j, rfl⟩ := hmem
          rw [rT_big.basisBits_replaceIndex_apply, rT_big.basisBits_replaceIndex_apply]
        · rw [rT_big.basisBits_replaceIndex_of_not_mem _ _ w hmem,
            rT_big.basisBits_replaceIndex_of_not_mem _ _ w hmem,
            basisBits_flipLastBitBy, ite_eq_right hw]
    have hrhs_eq :
        (rAct_sub.embedUnitary (muxOnAct k_t k_c (fun x ↦ F' (Fin.snoc x (f x))))).1 *ᵥ
          Pi.single g 1 =
        (rT_big.embedMatrix M) *ᵥ Pi.single g 1 := by
      have hcompT : rAct_sub.compose (QRegister.block 0 k_t (by omega)) = rT_big := by
        ext i; simp [rAct_sub, rT_big]
      have hcompC : rAct_sub.compose (QRegister.block k_t k_c (by omega)) = rC_sub := by
        ext j; simp [rAct_sub, rC_sub]
      have hm : rAct_sub.embedUnitary (muxOnAct k_t k_c (fun x ↦ F' (Fin.snoc x (f x)))) =
          muxUnitary rC_sub rT_big
            (by rw [QRegister.disjoint_iff]; intro i j heq; have hv := congrArg Fin.val heq
                simp [rC_sub, rT_big] at hv; omega)
            (fun c ↦ F' (Fin.snoc (bitsOfFin k_c c) (f (bitsOfFin k_c c)))) := by
        apply Subtype.ext
        change rAct_sub.embedMatrix (muxOnAct k_t k_c _).1 = _
        dsimp only [muxOnAct, muxUnitary]
        rw [rAct_sub.embedMatrix_sum]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [QRegister.embedMatrix_mul]
        have hP : rAct_sub.embedMatrix
              ((QRegister.block k_t k_c (by omega)).basisOutcomeProjector c) =
            rC_sub.basisOutcomeProjector c := by
          unfold QRegister.basisOutcomeProjector; rw [← QRegister.embedMatrix_compose, hcompC]
        have hE : rAct_sub.embedMatrix ((QRegister.block 0 k_t (by omega)).embedMatrix
              (F' (Fin.snoc (bitsOfFin k_c c) (f (bitsOfFin k_c c)))).1) =
            rT_big.embedMatrix (F' (Fin.snoc (bitsOfFin k_c c) (f (bitsOfFin k_c c)))).1 := by
          rw [← QRegister.embedMatrix_compose, hcompT]
        rw [hP, hE]
      rw [hm, muxUnitary_mulVec_of_proj rC_sub rT_big _ _ (rC_sub.extractIndex g) _
        (fun q hq ↦ by rw [Pi.single_eq_of_ne]; rintro rfl; exact hq rfl)]
    rw [hrhs_eq, hM_expand g, ht_eq]
    refine Finset.sum_congr rfl fun t' _ ↦ ?_
    rw [Matrix.mulVec_smul, hC, hflip_rep]
  · rw [ite_eq_right h0]
    simp

/-! #### Gate-Action Lemmas for `X`, `CNOT`, `TOFF` on `flipLastBitBy` -/

private theorem embedPerm_mulVec_single {n m : ℕ} (r : QRegister m n)
    (π : Equiv.Perm (Fin (2 ^ m))) (g : Fin (2 ^ n)) :
    (r.embedUnitary (Operator.permutationUnitary π)).1 *ᵥ Pi.single g 1 =
      Pi.single (r.replaceIndex g (π (r.extractIndex g))) 1 := by
  change (r.embedMatrix (Operator.permutationUnitary π).1) *ᵥ Pi.single g 1 = _
  rw [r.embedMatrix_mulVec_single_factors, Operator.permutationUnitary_mulVec_single,
    r.tensorState_single_replaceIndex]

theorem xLast_mulVec_single (k_t k_c : ℕ) (g : Fin (2 ^ (k_t + (k_c + 1)))) :
    (Circuit.X (Fin.natAdd (k_t + k_c) (0 : Fin 1))).eval.1 *ᵥ Pi.single g 1 =
      Pi.single (flipLastBitBy k_t k_c (fun _ ↦ true) g) 1 := by
  let anc_loc : Wire (k_t + (k_c + 1)) := Fin.natAdd (k_t + k_c) (0 : Fin 1)
  have hX : Qubit.X = Operator.permutationUnitary (Equiv.swap (0 : Fin 2) 1) := by
    apply Subtype.ext; ext a b; fin_cases a <;> fin_cases b <;>
      simp [Qubit.X, Operator.permutationUnitary, Equiv.Perm.permMatrix]
  change ((QRegister.singleton anc_loc).embedUnitary Qubit.X).1 *ᵥ Pi.single g 1 = _
  rw [hX, embedPerm_mulVec_single]
  congr 1
  apply (basisBits (k_t + (k_c + 1))).injective
  funext w
  rw [basisBits_flipLastBitBy]
  by_cases hw : w.val = k_t + k_c
  · have hweq : w = anc_loc := by ext; simpa [anc_loc] using hw
    subst hweq
    change basisBits _ ((QRegister.singleton anc_loc).replaceIndex g _)
      ((QRegister.singleton anc_loc) 0) = _
    rw [(QRegister.singleton anc_loc).basisBits_replaceIndex_apply]
    have hex : ∀ x : Fin 2, basisBits 1 (Equiv.swap (0 : Fin 2) 1 x) 0 = basisBits 1 x 0 + 1 := by
      intro x; fin_cases x <;> decide
    rw [hex, QRegister.basisBits_extractIndex]
    simp [anc_loc]
  · rw [ite_eq_right hw, (QRegister.singleton anc_loc).basisBits_replaceIndex_of_not_mem]
    rintro ⟨j, rfl⟩; fin_cases j; exact hw (by simp [anc_loc])

theorem cnotCtrlLast_mulVec_single (k_t k_c : ℕ) (i : Fin k_c)
    (g : Fin (2 ^ (k_t + (k_c + 1)))) :
    let c_loc : Wire (k_t + (k_c + 1)) := ⟨k_t + i.val, by omega⟩
    let anc_loc : Wire (k_t + (k_c + 1)) := Fin.natAdd (k_t + k_c) (0 : Fin 1)
    (Circuit.CNOT c_loc anc_loc
      (by intro h; have hv := congrArg Fin.val h; simp [c_loc, anc_loc] at hv; omega)).eval.1 *ᵥ
      Pi.single g 1 =
      Pi.single (flipLastBitBy k_t k_c (fun x ↦ x i) g) 1 := by
  intro c_loc anc_loc
  have hne : c_loc ≠ anc_loc := by
    intro h; have hv := congrArg Fin.val h; simp [c_loc, anc_loc] at hv; omega
  change ((QRegister.pair c_loc anc_loc hne).embedUnitary
    (Operator.permutationUnitary (Equiv.swap (1 : Fin 4) 3))).1 *ᵥ Pi.single g 1 = _
  rw [embedPerm_mulVec_single]
  congr 1
  let rP := QRegister.pair c_loc anc_loc hne
  have hswap2 : ∀ y : Fin 4,
      (basisBits 2 (Equiv.swap (1 : Fin 4) 3 y) 0 = basisBits 2 y 0) ∧
      (basisBits 2 (Equiv.swap (1 : Fin 4) 3 y) 1 =
        basisBits 2 y 1 + (if decide (basisBits 2 y 0 = 1) then 1 else 0)) := by
    intro y; fin_cases y <;> decide
  apply (basisBits (k_t + (k_c + 1))).injective
  funext w
  rw [basisBits_flipLastBitBy]
  by_cases hw : w.val = k_t + k_c
  · have hweq : w = rP 1 := by ext; simpa [rP, anc_loc] using hw
    rw [ite_eq_left hw, hweq, rP.basisBits_replaceIndex_apply, (hswap2 _).2,
      rP.basisBits_extractIndex, rP.basisBits_extractIndex]
    have hc_eq : basisBits k_c ((QRegister.block k_t k_c (by omega)).extractIndex g) i =
        basisBits (k_t + (k_c + 1)) g (rP 0) := by
      rw [QRegister.basisBits_extractIndex]; rfl
    simp [bitsOfFin, hc_eq]
  · rw [ite_eq_right hw]
    by_cases hmem : w ∈ Set.range rP.wires
    · obtain ⟨j, rfl⟩ := hmem
      rcases j with ⟨_ | _ | j, hj⟩
      · change basisBits _ (rP.replaceIndex g _) (rP 0) = basisBits _ g (rP 0)
        rw [rP.basisBits_replaceIndex_apply, (hswap2 _).1, rP.basisBits_extractIndex]
      · exact False.elim (hw (by simp [rP, anc_loc]))
      · omega
    · exact rP.basisBits_replaceIndex_of_not_mem _ _ w hmem

theorem toffCtrlLast_mulVec_single (k_t k_c : ℕ) (i₁ i₂ : Fin k_c) (hi₁₂ : i₁ ≠ i₂)
    (g : Fin (2 ^ (k_t + (k_c + 1)))) :
    let c₁_loc : Wire (k_t + (k_c + 1)) := ⟨k_t + i₁.val, by omega⟩
    let c₂_loc : Wire (k_t + (k_c + 1)) := ⟨k_t + i₂.val, by omega⟩
    let anc_loc : Wire (k_t + (k_c + 1)) := Fin.natAdd (k_t + k_c) (0 : Fin 1)
    let h₁₂ : c₁_loc ≠ c₂_loc := by
      intro h; have hv := congrArg Fin.val h; simp [c₁_loc, c₂_loc] at hv
      exact hi₁₂ (Fin.ext (by omega))
    let h₁a : c₁_loc ≠ anc_loc := by
      intro h; have hv := congrArg Fin.val h; simp [c₁_loc, anc_loc] at hv; omega
    let h₂a : c₂_loc ≠ anc_loc := by
      intro h; have hv := congrArg Fin.val h; simp [c₂_loc, anc_loc] at hv; omega
    (Circuit.TOFF c₁_loc c₂_loc anc_loc h₁₂ h₁a h₂a).eval.1 *ᵥ Pi.single g 1 =
      Pi.single (flipLastBitBy k_t k_c (fun x ↦ x i₁ && x i₂) g) 1 := by
  intro c₁_loc c₂_loc anc_loc h₁₂ h₁a h₂a
  let rTr := QRegister.triple c₁_loc c₂_loc anc_loc h₁₂ h₁a h₂a
  change (rTr.embedUnitary (Operator.permutationUnitary (Equiv.swap (3 : Fin 8) 7))).1 *ᵥ
    Pi.single g 1 = _
  rw [embedPerm_mulVec_single]
  congr 1
  have hswap3 : ∀ y : Fin 8,
      (basisBits 3 (Equiv.swap (3 : Fin 8) 7 y) 0 = basisBits 3 y 0) ∧
      (basisBits 3 (Equiv.swap (3 : Fin 8) 7 y) 1 = basisBits 3 y 1) ∧
      (basisBits 3 (Equiv.swap (3 : Fin 8) 7 y) 2 =
        basisBits 3 y 2 +
          (if (decide (basisBits 3 y 0 = 1) && decide (basisBits 3 y 1 = 1)) then 1 else 0)) := by
    intro y; fin_cases y <;> decide
  apply (basisBits (k_t + (k_c + 1))).injective
  funext w
  rw [basisBits_flipLastBitBy]
  by_cases hw : w.val = k_t + k_c
  · have hweq : w = rTr 2 := by ext; simpa [rTr, anc_loc] using hw
    rw [ite_eq_left hw, hweq, rTr.basisBits_replaceIndex_apply, (hswap3 _).2.2,
      rTr.basisBits_extractIndex, rTr.basisBits_extractIndex, rTr.basisBits_extractIndex]
    have hc₁ : basisBits k_c ((QRegister.block k_t k_c (by omega)).extractIndex g) i₁ =
        basisBits (k_t + (k_c + 1)) g (rTr 0) := by
      rw [QRegister.basisBits_extractIndex]; rfl
    have hc₂ : basisBits k_c ((QRegister.block k_t k_c (by omega)).extractIndex g) i₂ =
        basisBits (k_t + (k_c + 1)) g (rTr 1) := by
      rw [QRegister.basisBits_extractIndex]; rfl
    simp [bitsOfFin, hc₁, hc₂]
  · rw [ite_eq_right hw]
    by_cases hmem : w ∈ Set.range rTr.wires
    · obtain ⟨j, rfl⟩ := hmem
      rcases j with ⟨_ | _ | _ | j, hj⟩
      · change basisBits _ (rTr.replaceIndex g _) (rTr 0) = basisBits _ g (rTr 0)
        rw [rTr.basisBits_replaceIndex_apply, (hswap3 _).1, rTr.basisBits_extractIndex]
      · change basisBits _ (rTr.replaceIndex g _) (rTr 1) = basisBits _ g (rTr 1)
        rw [rTr.basisBits_replaceIndex_apply, (hswap3 _).2.1, rTr.basisBits_extractIndex]
      · exact False.elim (hw (by simp [rTr, anc_loc]))
      · omega
    · exact rTr.basisBits_replaceIndex_of_not_mem _ _ w hmem

/-! #### `TempProg` AST, Semantics, `DynamicCircuit` Lowering & `CleanRealizes` Proof -/

/-- Purely read-only temporary Boolean wire program extending `k_in` control bits to `k_out`
control bits using `s` temporary scratch bits (`linear` = `0 T`, `andGate` = `4 T` via Gidney
measurement-assisted uncompute). -/
inductive TempProg : ℕ → ℕ → ℕ → Type where
  | nil {k : ℕ} : TempProg k k 0
  | linear {k k_out s : ℕ} (terms : List (Fin k)) (neg : Bool)
      (rest : TempProg (k + 1) k_out s) : TempProg k k_out (s + 1)
  | andGate {k k_out s : ℕ} (i₁ i₂ : Fin k) (hne : i₁ ≠ i₂)
      (rest : TempProg (k + 1) k_out s) : TempProg k k_out (s + 1)

/-- Number of temporary AND gates (`4 T` each) in a `TempProg`. -/
def TempProg.numAnds : {k k_out s : ℕ} → TempProg k k_out s → ℕ
  | _, _, _, .nil => 0
  | _, _, _, .linear _ _ rest => rest.numAnds
  | _, _, _, .andGate _ _ _ rest => 1 + rest.numAnds

/-- Boolean bit-vector evaluation of a `TempProg` on input `x : Fin k_in → Bool`. -/
def TempProg.evalBits : {k_in k_out s : ℕ} → TempProg k_in k_out s →
    (Fin k_in → Bool) → (Fin k_out → Bool)
  | _, _, _, .nil, x => x
  | _, _, _, .linear terms neg rest, x =>
      rest.evalBits (Fin.snoc x (terms.foldl (fun acc i ↦ xor acc (x i)) neg))
  | _, _, _, .andGate i₁ i₂ _ rest, x =>
      rest.evalBits (Fin.snoc x (x i₁ && x i₂))

/-- Local Clifford CNOT fanout circuit for `TempProg.linear`. -/
def linearXorListCircuit (k_t k_c : ℕ) : List (Fin k_c) → Circuit (k_t + (k_c + 1))
  | [] => .identity
  | i :: rest =>
      Circuit.CNOT ⟨k_t + i.val, by omega⟩ (Fin.natAdd (k_t + k_c) (0 : Fin 1))
        (by intro h; have hv := congrArg Fin.val h; simp at hv; omega) ;;ᶜ
      linearXorListCircuit k_t k_c rest

/-- Local Clifford compute circuit (`X` + `CNOT`s) for `TempProg.linear` (`0 T`, `0 TOFF`). -/
def linearComputeCircuit (k_t k_c : ℕ) (terms : List (Fin k_c)) (neg : Bool) :
    Circuit (k_t + (k_c + 1)) :=
  (if neg then Circuit.X (Fin.natAdd (k_t + k_c) (0 : Fin 1)) else .identity) ;;ᶜ
    linearXorListCircuit k_t k_c terms

theorem linearXorListCircuit_count_t (k_t k_c : ℕ) :
    ∀ terms : List (Fin k_c), (linearXorListCircuit k_t k_c terms).count .T = 0
  | [] => rfl
  | _ :: rest => by simp [linearXorListCircuit, linearXorListCircuit_count_t k_t k_c rest]

theorem linearXorListCircuit_count_toff (k_t k_c : ℕ) :
    ∀ terms : List (Fin k_c), (linearXorListCircuit k_t k_c terms).count .TOFF = 0
  | [] => rfl
  | _ :: rest => by simp [linearXorListCircuit, linearXorListCircuit_count_toff k_t k_c rest]

@[simp]
theorem linearComputeCircuit_count_t (k_t k_c : ℕ) (terms : List (Fin k_c)) (neg : Bool) :
    (linearComputeCircuit k_t k_c terms neg).count .T = 0 := by
  cases neg <;> simp [linearComputeCircuit, linearXorListCircuit_count_t]

@[simp]
theorem linearComputeCircuit_count_toff (k_t k_c : ℕ) (terms : List (Fin k_c)) (neg : Bool) :
    (linearComputeCircuit k_t k_c terms neg).count .TOFF = 0 := by
  cases neg <;> simp [linearComputeCircuit, linearXorListCircuit_count_toff]

@[simp]
theorem linearComputeCircuit_inverse_count_t (k_t k_c : ℕ) (terms : List (Fin k_c)) (neg : Bool) :
    (linearComputeCircuit k_t k_c terms neg).inverse.count .T = 0 := by
  cases neg <;> simp [linearComputeCircuit, Circuit.X, inverseGate, linearXorListCircuit_count_t]

theorem linearComputeCircuit_inverse_count_toff (k_t k_c : ℕ) (terms : List (Fin k_c))
    (neg : Bool) :
    (linearComputeCircuit k_t k_c terms neg).inverse.count .TOFF = 0 := by
  cases neg <;> simp [linearComputeCircuit, Circuit.X, inverseGate,
    linearXorListCircuit_count_toff]

theorem linearXorListCircuit_mulVec_single (k_t k_c : ℕ) (terms : List (Fin k_c))
    (init : (Fin k_c → Bool) → Bool) (g : Fin (2 ^ (k_t + (k_c + 1)))) :
    (linearXorListCircuit k_t k_c terms).eval.1 *ᵥ Pi.single (flipLastBitBy k_t k_c init g) 1 =
      Pi.single (flipLastBitBy k_t k_c
        (fun x ↦ terms.foldl (fun acc i ↦ xor acc (x i)) (init x)) g) 1 := by
  induction terms generalizing init with
  | nil =>
      simp only [linearXorListCircuit, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec, List.foldl_nil]
  | cons i rest ih =>
      simp only [linearXorListCircuit, Circuit.eval_seq, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec, List.foldl_cons]
      rw [cnotCtrlLast_mulVec_single k_t k_c i (flipLastBitBy k_t k_c init g),
        flipLastBitBy_comp, ih]

theorem linearComputeCircuit_mulVec_single (k_t k_c : ℕ) (terms : List (Fin k_c)) (neg : Bool)
    (g : Fin (2 ^ (k_t + (k_c + 1)))) :
    (linearComputeCircuit k_t k_c terms neg).eval.1 *ᵥ Pi.single g 1 =
      Pi.single (flipLastBitBy k_t k_c
        (fun x ↦ terms.foldl (fun acc i ↦ xor acc (x i)) neg) g) 1 := by
  simp only [linearComputeCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte, Circuit.eval_identity, Submonoid.coe_one,
      Matrix.one_mulVec]
    have hg : g = flipLastBitBy k_t k_c (fun _ ↦ false) g := by
      apply (basisBits (k_t + (k_c + 1))).injective; funext w
      rw [basisBits_flipLastBitBy]
      by_cases hw : w.val = k_t + k_c <;> simp [hw]
    conv_lhs => rw [hg]
    exact linearXorListCircuit_mulVec_single k_t k_c terms (fun _ ↦ false) g
  · simp only [↓reduceIte]
    rw [xLast_mulVec_single k_t k_c g]
    exact linearXorListCircuit_mulVec_single k_t k_c terms (fun _ ↦ true) g

theorem linearComputeCircuit_inverse_eval_eq (k_t k_c : ℕ) (terms : List (Fin k_c)) (neg : Bool) :
    (linearComputeCircuit k_t k_c terms neg).inverse.eval =
      (linearComputeCircuit k_t k_c terms neg).eval := by
  rw [Circuit.eval_inverse]
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext; ext a g
  have h := congrFun (show ((linearComputeCircuit k_t k_c terms neg).eval *
      (linearComputeCircuit k_t k_c terms neg).eval).1 *ᵥ Pi.single g 1 = Pi.single g 1 from ?_) a
  · rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    by_cases hag : a = g <;> exact h.trans (by simp [hag])
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [linearComputeCircuit_mulVec_single, linearComputeCircuit_mulVec_single, flipLastBitBy_comp]
  congr 1
  apply (basisBits (k_t + (k_c + 1))).injective; funext w
  rw [basisBits_flipLastBitBy]
  by_cases hw : w.val = k_t + k_c
  · rw [ite_eq_left hw]
    simp
  · exact ite_eq_right hw

/-- Wrap a `DynamicCircuit` `midFn` inside the reversible compute/uncompute sandwiches of a
`TempProg` (`0` `TOFF`s, `4 * p.numAnds` `T` gates). -/
def TempProg.wrapDyn {Var : Type} {N : ℕ} (v : Var) (k_t : ℕ) :
    {k_in k_out s : ℕ} → TempProg k_in k_out s →
      QRegister (k_t + k_in) N → QRegister s N →
      (QRegister (k_t + k_out) N → DynamicCircuit Var N) →
      DynamicCircuit Var N
  | _, _, _, .nil, rAct, _, midFn => midFn rAct
  | k_c, _, _, @TempProg.linear _ _ s terms neg rest, rAct, rTemp, midFn =>
      let anc := rTemp 0
      let rTempRest := rTemp.compose (QRegister.block 1 s (by omega))
      if hActAnc : rAct.DisjointWires (QRegister.singleton anc) then
        let rAct' : QRegister (k_t + (k_c + 1)) N := rAct.concat (QRegister.singleton anc) hActAnc
        let c := linearComputeCircuit k_t k_c terms neg
        let inner := rest.wrapDyn v k_t rAct' rTempRest midFn
        .seq (.circuit (c.onRegister rAct')) (.seq inner (.circuit (c.inverse.onRegister rAct')))
      else
        .identity
  | k_c, _, _, @TempProg.andGate _ _ s i₁ i₂ hne rest, rAct, rTemp, midFn =>
      let anc := rTemp 0
      let rTempRest := rTemp.compose (QRegister.block 1 s (by omega))
      if hActAnc : rAct.DisjointWires (QRegister.singleton anc) then
        let rAct' : QRegister (k_t + (k_c + 1)) N := rAct.concat (QRegister.singleton anc) hActAnc
        let j₁ : Fin (k_t + k_c) := ⟨k_t + i₁.val, by omega⟩
        let j₂ : Fin (k_t + k_c) := ⟨k_t + i₂.val, by omega⟩
        let hj₁₂ : j₁ ≠ j₂ := by
          intro h
          exact hne (Fin.ext (by have hv := congrArg Fin.val h; dsimp [j₁, j₂] at hv; omega))
        let inner := rest.wrapDyn v k_t rAct' rTempRest midFn
        andSandwichProg v (rAct j₁) (rAct j₂) anc
          (rAct.wires.injective.ne hj₁₂)
          (show rAct j₁ ≠ anc from hActAnc.ne j₁ 0)
          (show rAct j₂ ≠ anc from hActAnc.ne j₂ 0) inner
      else
        .identity

theorem TempProg.wrapDyn_count_toff {Var : Type} {N : ℕ} (v : Var) (k_t : ℕ)
    {k_in k_out s : ℕ} (p : TempProg k_in k_out s)
    (rAct : QRegister (k_t + k_in) N) (rTemp : QRegister s N)
    (midFn : QRegister (k_t + k_out) N → DynamicCircuit Var N)
    (hmid : ∀ r, (midFn r).count .TOFF = 0) :
    (p.wrapDyn v k_t rAct rTemp midFn).count .TOFF = 0 := by
  induction p with
  | nil => exact hmid rAct
  | linear terms neg rest ih =>
      simp only [TempProg.wrapDyn]
      split_ifs with hActAnc
      · simp [DynamicCircuit.count, ih _ _ midFn hmid]
      · rfl
  | andGate i₁ i₂ hne rest ih =>
      simp only [TempProg.wrapDyn]
      split_ifs with hActAnc
      · rw [count_andSandwichProg_toff, ih _ _ midFn hmid]
      · rfl

theorem TempProg.wrapDyn_count_t {Var : Type} {N : ℕ} (v : Var) (k_t : ℕ)
    {k_in k_out s s_in : ℕ} (p : TempProg k_in k_out s)
    (rAct : QRegister (k_t + k_in) N) (rTemp : QRegister s N) (rScrIn : QRegister s_in N)
    (hActTemp : rAct.DisjointWires rTemp)
    (hActIn : rAct.DisjointWires rScrIn)
    (hTempIn : rTemp.DisjointWires rScrIn)
    (midFn : QRegister (k_t + k_out) N → DynamicCircuit Var N)
    (t_mid : ℕ) (hmid : ∀ r, r.DisjointWires rScrIn → (midFn r).count .T = t_mid) :
    (p.wrapDyn v k_t rAct rTemp midFn).count .T = 4 * p.numAnds + t_mid := by
  induction p with
  | nil =>
      simp [TempProg.wrapDyn, TempProg.numAnds, hmid rAct hActIn]
  | @linear k_c k_out s terms neg rest ih =>
      let anc := rTemp 0
      let rTempRest := rTemp.compose (QRegister.block 1 s (by omega))
      have hActAnc : rAct.DisjointWires (QRegister.singleton anc) := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases j; exact hActTemp.ne i 0
      have hAncIn : (QRegister.singleton anc).DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases i; exact hTempIn.ne 0 j
      have hAct'In : (rAct.concat (QRegister.singleton anc) hActAnc).DisjointWires rScrIn :=
        QRegister.disjointWires_concat_left hActAnc hActIn hAncIn
      have hRestIn : rTempRest.DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; exact hTempIn.ne ⟨1 + i.val, by omega⟩ j
      have hRest : (rAct.concat (QRegister.singleton anc) hActAnc).DisjointWires rTempRest := by
        refine QRegister.disjointWires_concat_left hActAnc ?_ ?_
        · rw [QRegister.disjoint_iff]; intro i j; exact hActTemp.ne i ⟨1 + j.val, by omega⟩
        · rw [QRegister.disjoint_iff]; intro i j; fin_cases i
          exact rTemp.wires.injective.ne
            (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)
      simp only [TempProg.wrapDyn, TempProg.numAnds]
      rw [dite_eq_left hActAnc]
      simp only [DynamicCircuit.count, Circuit.count_onRegister,
        linearComputeCircuit_count_t, linearComputeCircuit_inverse_count_t, zero_add, add_zero]
      exact ih _ rTempRest hRest hAct'In hRestIn midFn hmid
  | @andGate k_c k_out s i₁ i₂ hne rest ih =>
      let anc := rTemp 0
      let rTempRest := rTemp.compose (QRegister.block 1 s (by omega))
      have hActAnc : rAct.DisjointWires (QRegister.singleton anc) := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases j; exact hActTemp.ne i 0
      have hAncIn : (QRegister.singleton anc).DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases i; exact hTempIn.ne 0 j
      have hAct'In : (rAct.concat (QRegister.singleton anc) hActAnc).DisjointWires rScrIn :=
        QRegister.disjointWires_concat_left hActAnc hActIn hAncIn
      have hRestIn : rTempRest.DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; exact hTempIn.ne ⟨1 + i.val, by omega⟩ j
      have hRest : (rAct.concat (QRegister.singleton anc) hActAnc).DisjointWires rTempRest := by
        refine QRegister.disjointWires_concat_left hActAnc ?_ ?_
        · rw [QRegister.disjoint_iff]; intro i j; exact hActTemp.ne i ⟨1 + j.val, by omega⟩
        · rw [QRegister.disjoint_iff]; intro i j; fin_cases i
          exact rTemp.wires.injective.ne
            (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)
      simp only [TempProg.wrapDyn, TempProg.numAnds]
      rw [dite_eq_left hActAnc, count_andSandwichProg_t,
        ih _ rTempRest hRest hAct'In hRestIn midFn hmid]
      ring

private theorem scr_step_subset {N s s_in : ℕ}
    (rTemp : QRegister (s + 1) N) (rScrIn : QRegister s_in N)
    (hTempIn : rTemp.DisjointWires rScrIn)
    (hRestIn : (rTemp.compose (QRegister.block 1 s (by omega))).DisjointWires rScrIn)
    (hAncMid : (QRegister.singleton (rTemp 0)).DisjointWires
      ((rTemp.compose (QRegister.block 1 s (by omega))).concat rScrIn hRestIn)) :
    ((QRegister.singleton (rTemp 0)).concat
      ((rTemp.compose (QRegister.block 1 s (by omega))).concat rScrIn hRestIn) hAncMid).image ⊆
    (rTemp.concat rScrIn hTempIn).image := by
  intro w hw
  simp only [QRegister.image_concat, Finset.mem_union] at hw ⊢
  rcases hw with hw0 | (hwr | hwi)
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hw0
    fin_cases i
    exact Or.inl ((QRegister.mem_image rTemp _).mpr ⟨0, rfl⟩)
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image _ _).mp hwr
    exact Or.inl ((QRegister.mem_image rTemp _).mpr ⟨⟨1 + j.val, by omega⟩, rfl⟩)
  · exact Or.inr hwi

theorem TempProg.cleanRealizes_mux {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k_t k_in k_out s s_in : ℕ} (v : Var) (p : TempProg k_in k_out s)
    (rAct : QRegister (k_t + k_in) N) (rTemp : QRegister s N) (rScrIn : QRegister s_in N)
    (hActTemp : rAct.DisjointWires rTemp)
    (hActIn : rAct.DisjointWires rScrIn)
    (hTempIn : rTemp.DisjointWires rScrIn)
    (F : (Fin k_out → Bool) → Unitary (2 ^ k_t))
    (midFn : QRegister (k_t + k_out) N → DynamicCircuit Var N)
    (hmid : ∀ rFinal : QRegister (k_t + k_out) N,
      rFinal.DisjointWires rScrIn →
      CleanRealizes v rFinal rScrIn (muxOnAct k_t k_out F) (midFn rFinal)) :
    CleanRealizes v rAct (rTemp.concat rScrIn hTempIn)
      (muxOnAct k_t k_in (fun x ↦ F (p.evalBits x)))
      (p.wrapDyn v k_t rAct rTemp midFn) := by
  induction p with
  | nil =>
      have hsub : rScrIn.image ⊆ (rTemp.concat rScrIn hTempIn).image := by
        rw [QRegister.image_concat]; exact Finset.subset_union_right
      have hdisj : rAct.DisjointWires (rTemp.concat rScrIn hTempIn) :=
        QRegister.disjointWires_concat_right hTempIn hActTemp hActIn
      exact (hmid rAct hActIn).extend_scr hdisj hsub
  | @linear k_c k_out s terms neg rest ih =>
      let anc := rTemp 0
      let rAnc1 := QRegister.singleton anc
      let rTempRest := rTemp.compose (QRegister.block 1 s (by omega))
      have hActAnc : rAct.DisjointWires rAnc1 := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases j; exact hActTemp.ne i 0
      let rAct' : QRegister (k_t + (k_c + 1)) N := rAct.concat rAnc1 hActAnc
      have hAncRest : rAnc1.DisjointWires rTempRest := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases i
        exact rTemp.wires.injective.ne
          (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)
      have hAct'Rest : rAct'.DisjointWires rTempRest := by
        refine QRegister.disjointWires_concat_left hActAnc ?_ hAncRest
        rw [QRegister.disjoint_iff]; intro i j; exact hActTemp.ne i ⟨1 + j.val, by omega⟩
      have hAncIn : rAnc1.DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases i; exact hTempIn.ne 0 j
      have hAct'In : rAct'.DisjointWires rScrIn :=
        QRegister.disjointWires_concat_left hActAnc hActIn hAncIn
      have hRestIn : rTempRest.DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; exact hTempIn.ne ⟨1 + i.val, by omega⟩ j
      let rScrMid := rTempRest.concat rScrIn hRestIn
      have hAncMid : rAnc1.DisjointWires rScrMid :=
        QRegister.disjointWires_concat_right hRestIn hAncRest hAncIn
      have hActMid : rAct.DisjointWires rScrMid := by
        refine QRegister.disjointWires_concat_right hRestIn ?_ hActIn
        rw [QRegister.disjoint_iff]; intro i j; exact hActTemp.ne i ⟨1 + j.val, by omega⟩
      have hAct'Mid : rAct'.DisjointWires rScrMid :=
        QRegister.disjointWires_concat_left hActAnc hActMid hAncMid
      have hinner := ih rAct' rTempRest hAct'Rest hAct'In hRestIn F midFn hmid
      let c := linearComputeCircuit k_t k_c terms neg
      have hc1 : CleanRealizes v rAct' rScrMid c.eval (.circuit (c.onRegister rAct')) :=
        CleanRealizes.circuit v rAct' rScrMid hAct'Mid c
          (linearComputeCircuit_count_toff k_t k_c terms neg)
      have hc2 : CleanRealizes v rAct' rScrMid c.inverse.eval
          (.circuit (c.inverse.onRegister rAct')) :=
        CleanRealizes.circuit v rAct' rScrMid hAct'Mid c.inverse
          (linearComputeCircuit_inverse_count_toff k_t k_c terms neg)
      have hseq := hc1.seq (hinner.seq hc2)
      rw [linearComputeCircuit_inverse_eval_eq] at hseq
      have hret := cleanRealizes_retract_ancilla_local v rAct anc hActAnc rScrMid hAncMid hActMid
        _ _ _ hseq
        (bitCompute_conj_muxOnAct_mul_proj0 k_t k_c
          (fun x ↦ terms.foldl (fun acc i ↦ xor acc (x i)) neg) c.eval
          (linearComputeCircuit_mulVec_single k_t k_c terms neg)
          (fun y ↦ F (rest.evalBits y)))
      simp only [TempProg.wrapDyn, TempProg.evalBits]
      rw [dite_eq_left hActAnc]
      exact hret.extend_scr
        (QRegister.disjointWires_concat_right hTempIn hActTemp hActIn)
        (scr_step_subset rTemp rScrIn hTempIn hRestIn hAncMid)
  | @andGate k_c k_out s i₁ i₂ hne rest ih =>
      let anc := rTemp 0
      let rAnc1 := QRegister.singleton anc
      let rTempRest := rTemp.compose (QRegister.block 1 s (by omega))
      have hActAnc : rAct.DisjointWires rAnc1 := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases j; exact hActTemp.ne i 0
      let rAct' : QRegister (k_t + (k_c + 1)) N := rAct.concat rAnc1 hActAnc
      have hAncRest : rAnc1.DisjointWires rTempRest := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases i
        exact rTemp.wires.injective.ne
          (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)
      have hAct'Rest : rAct'.DisjointWires rTempRest := by
        refine QRegister.disjointWires_concat_left hActAnc ?_ hAncRest
        rw [QRegister.disjoint_iff]; intro i j; exact hActTemp.ne i ⟨1 + j.val, by omega⟩
      have hAncIn : rAnc1.DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; fin_cases i; exact hTempIn.ne 0 j
      have hAct'In : rAct'.DisjointWires rScrIn :=
        QRegister.disjointWires_concat_left hActAnc hActIn hAncIn
      have hRestIn : rTempRest.DisjointWires rScrIn := by
        rw [QRegister.disjoint_iff]; intro i j; exact hTempIn.ne ⟨1 + i.val, by omega⟩ j
      let rScrMid := rTempRest.concat rScrIn hRestIn
      have hAncMid : rAnc1.DisjointWires rScrMid :=
        QRegister.disjointWires_concat_right hRestIn hAncRest hAncIn
      have hActMid : rAct.DisjointWires rScrMid := by
        refine QRegister.disjointWires_concat_right hRestIn ?_ hActIn
        rw [QRegister.disjoint_iff]; intro i j; exact hActTemp.ne i ⟨1 + j.val, by omega⟩
      have hinner := ih rAct' rTempRest hAct'Rest hAct'In hRestIn F midFn hmid
      let j₁ : Fin (k_t + k_c) := ⟨k_t + i₁.val, by omega⟩
      let j₂ : Fin (k_t + k_c) := ⟨k_t + i₂.val, by omega⟩
      have hj₁₂ : j₁ ≠ j₂ := by
        intro h
        exact hne (Fin.ext (by have hv := congrArg Fin.val h; dsimp [j₁, j₂] at hv; omega))
      have hand := CleanRealizes.andSandwich_local v rAct j₁ j₂ hj₁₂ anc hActAnc
        rScrMid hAncMid hActMid _ _ _ hinner
        (bitCompute_conj_muxOnAct_mul_proj0 k_t k_c
          (fun x ↦ x i₁ && x i₂) _
          (toffCtrlLast_mulVec_single k_t k_c i₁ i₂ hne)
          (fun y ↦ F (rest.evalBits y)))
      simp only [TempProg.wrapDyn, TempProg.evalBits]
      rw [dite_eq_left hActAnc]
      exact hand.extend_scr
        (QRegister.disjointWires_concat_right hTempIn hActTemp hActIn)
        (scr_step_subset rTemp rScrIn hTempIn hRestIn hAncMid)

/-! ### 4. Compositional `TempProg` Lifting, Concrete `SELECT` Arithmetic & 1-Bit SelectSwap QROM -/

theorem bitsOfFin_eq_div_mod (k : ℕ) (c : Fin (2 ^ k)) (i : Fin k) :
    bitsOfFin k c i = decide ((c.val / 2 ^ i.val) % 2 = 1) := by
  dsimp only [bitsOfFin]
  rw [basisBits_eq_div_mod]
  rcases Nat.mod_two_eq_zero_or_one (c.val / 2 ^ i.val) with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
