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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectSwapQromUnload
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true
open scoped Matrix BigOperators
set_option exponentiation.threshold 256

noncomputable section
open Operator QProg DynamicCircuit Matrix Circuit Qubit QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
set_option exponentiation.threshold 8192
open PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectStructKinComp
open PhotochemistrySolution.FastQft8Semantics PhotochemistrySolution.TargetBScr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] SpecDefs.systemQubits_frozen ancWOfScr
    StructuredCB.validProgMask
attribute [local irreducible] StructuredCB.finalCleanMask zGateCirc czCircuit
    AndBracketProg.toCircuit Circuit.eval QRegister.embedMatrix
attribute [local irreducible] maskFinset
theorem embedUnitary_mulVec_ket_of_isPhaseDiag {M n : ℕ} (r : QRegister M n) (U : Unitary (2 ^ M))
    {φ : BitAssignment M → ZMod 2} (hU : IsPhaseDiag U.1 φ) (δ : BitAssignment n) :
    (r.embedUnitary U).1.mulVec (KinB.ket δ) = bitSign (φ (fun j ↦ δ (r j))) • KinB.ket δ := by
  rw [QRegister.embedUnitary_val];
  exact embedMatrix_mulVec_ket_diag r U.1 (fun γ ↦ bitSign (φ γ)) hU δ
theorem embedUnitary_comm_of_disjoint {M n k : ℕ} (r : QRegister M n) (U : Unitary (2 ^ M))
    (rC : QRegister k n) (hDisj : r.DisjointWires rC) (A : Operator (2 ^ k)) :
    (r.embedUnitary U).1 * rC.embedMatrix A = rC.embedMatrix A * (r.embedUnitary U).1 := by
  rw [QRegister.embedUnitary_val]; exact r.embedMatrix_comm_of_disjoint rC hDisj U.1 A
theorem csel_eq_and_comm_of_ket {n : ℕ} (q : Wire n) (Uc Uu : Unitary (2 ^ n))
    (f : BitAssignment n → ZMod 2) (hc : ∀ δ, Uc.1.mulVec (KinB.ket δ) =
    bitSign (δ q * f δ) • KinB.ket δ) (hu : ∀ δ, Uu.1.mulVec (KinB.ket δ) =
    bitSign (f δ) • KinB.ket δ) : Uc.1 = (1 - (QRegister.singleton q).basisOutcomeProjector 1) +
    (QRegister.singleton q).basisOutcomeProjector 1 * Uu.1 ∧ Uu.1 *
    (QRegister.singleton q).basisOutcomeProjector 1 =
    (QRegister.singleton q).basisOutcomeProjector 1 * Uu.1 := by
  have h01 : (0 : ZMod 2) ≠ 1 :=
      of_decide_eq_true rfl;
      have hP : ∀ δ, ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (KinB.ket δ) =
      if δ q = 1 then KinB.ket δ else 0 := DynCircExt.ket_projector_one q
  refine ⟨KinB.matrix_ext_ket fun δ ↦ ?_, KinB.matrix_ext_ket fun δ ↦ ?_⟩
  · rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hc, hu,
        Matrix.mulVec_smul, hP]
    rcases bit_cases (δ q) with h0 | h1 <;> [rw [h0, zero_mul, bitSign_zero, one_smul,
        ite_eq_right h01, sub_zero, smul_zero, add_zero]; rw [h1, one_mul, ite_eq_left rfl,
        sub_self, zero_add]]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, hP]
    rcases bit_cases (δ q) with h0 | h1 <;> [rw [ite_eq_right (h0 ▸ h01), Matrix.mulVec_zero,
        smul_zero]; rw [ite_eq_left h1, hu]]
end QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap

namespace QuantumComputation.Specs.PhotochemistrySolution.UnembedIdleAncillas
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open PrimitiveGate ComplexConjugate PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectSandwich PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.SelectCsa64ThreeSpec
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.DiagShiftSpecBridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem posSemidef_iff_dotProduct_mulVec_loc {d : ℕ} (M : Operator d) : M.PosSemidef ↔
    M.IsHermitian ∧ ∀ ψ : Fin d → ℂ, 0 ≤ star ψ ⬝ᵥ M.mulVec ψ := by
  have hs (x : Fin d →₀ ℂ) : (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj) =
      star ⇑x ⬝ᵥ M.mulVec ⇑x := by
    simp [Finsupp.sum_fintype, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact and_congr_right fun _ ↦
      ⟨fun h ψ ↦ hs (Finsupp.equivFunOnFinite.symm ψ) ▸ h _, fun h x ↦ (hs x).symm ▸ h ⇑x⟩
theorem wp_qAssign_mat_loc {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) : (CQAssertion.qAssign U θ σ).1.mat = U.1ᴴ *
    (θ σ).1.mat * U.1 := CQAssertion.qAssign_apply_mat U θ σ
theorem exists_unembedded_unitary {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) (W₀ : Unitary (2 ^ (sysW + ancW)))
    (hClean : (1 - (rIdleCanon sysW part).basisOutcomeProjector 0) * W₀.1 *
    (ancCanon sysW ancW).basisOutcomeProjector 0 = 0) : ∃ W' : Unitary (2 ^ (sysW + ancW')),
    ((rLiveCanon sysW part).embedUnitary W').1 * (ancCanon sysW ancW).basisOutcomeProjector 0 =
    W₀.1 * (ancCanon sysW ancW).basisOutcomeProjector 0 := by
  let D := 2 ^ (sysW + ancW');
  let ancSmall : QRegister ancW' (sysW + ancW') := QRegister.block sysW ancW' le_rfl
  let s : Set (Fin D) := { j | ancSmall.extractIndex j = 0 }
  let uBig : Fin D → Fin (2 ^ (sysW + ancW)) → ℂ := fun j ↦
      (rLiveCanon sysW part).tensorState (Pi.single j 1) (Pi.single 0 1)
  let v : Fin D → EuclideanSpace ℂ (Fin D) := fun j ↦
      WithLp.toLp 2 (sliceIdleZero part (W₀.1.mulVec (uBig j)))
  have hv_tensor (j : Fin D)
      (hj : j ∈ s) : (rLiveCanon sysW part).tensorState (v j).ofLp (Pi.single 0 1) =
      W₀.1.mulVec (uBig j) :=
    tensorState_sliceIdleZero part (sub_eq_zero.mp (by
      simpa only [uBig, zero_mulVec, ← mulVec_mulVec,
          tensorState_cleanSmall_is_ancCanon_clean part hj,
        sub_mulVec, one_mulVec] using congrArg (·.mulVec (uBig j)) hClean)).symm
  have hortho : Orthonormal ℂ (s.domRestrict v) := orthonormal_iff_ite.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ ↦ by
    simp only [Set.domRestrict_apply, Subtype.mk.injEq];
    change @inner ℂ (EuclideanSpace ℂ (Fin D)) _ (v i) (v j) = _
    rw [← inner_euclidean_tensorState_single (rLiveCanon sysW part) 0 (v i).ofLp (v j).ofLp,
        hv_tensor i hi, hv_tensor j hj,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, star_mulVec, dotProduct_mulVec,
      Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, W₀.2.1, Matrix.vecMul_one,
      star_dotProduct_tensorState_single (rLiveCanon sysW part) 0]
    by_cases hij : i = j <;> simp [hij]
  obtain ⟨B, hB⟩ := hortho.exists_orthonormalBasis_extension_of_card_eq (by simp [D])
  let Wm := Matrix.of fun r c : Fin D ↦ (B c).ofLp r
  refine ⟨⟨Wm, Matrix.mem_unitaryGroup_iff'.mpr (Matrix.ext fun r c ↦ by
    rw [Matrix.mul_apply, Matrix.one_apply, ← orthonormal_iff_ite.mp B.orthonormal r c,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, dotProduct]; simp [Wm, D])⟩,
    Matrix.ext_of_mulVec_single fun g ↦ ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, (ancCanon sysW ancW).basisOutcomeProjector_mulVec_single]
  if hg0 : (ancCanon sysW ancW).extractIndex g = 0 then
    let j : Fin D := (rLiveCanon sysW part).extractIndex g
    have hg0' := (extractIndex_eq_zero_iff_basisBits_eq_zero (ancCanon sysW ancW) g).mp hg0
    have hjs : j ∈ s := (extractIndex_eq_zero_iff_basisBits_eq_zero ancSmall j).mpr fun i ↦ by
      dsimp only [j];
      rw [(QRegExt.basisBits_extractIdx (rLiveCanon sysW part)), show ancSmall i =
          Fin.natAdd sysW i from rfl]
      exact (congrArg (basisBits _ g)
          (QRegister.concat_apply_right _ _ (sysCanon_disj_keep part) i)).trans
          (hg0' (part.keepIdx i))
    rw [ite_eq_left hg0, ← (rLiveCanon sysW part).tensorState_single_factors g,
      (env_eq_zero_iff_idle_zero part g).mpr ((extractIndex_eq_zero_iff_basisBits_eq_zero _ g).mpr
          fun l ↦ hg0' (part.idleIdx l)),
      QRegister.embedUnitary_val, Subtype.coe_mk,
          (rLiveCanon sysW part).embedMatrix_mulVec_tensorState, Matrix.mulVec_single_one,
      show Wm.col ((rLiveCanon _ part).extractIndex g) = (v j).ofLp from funext fun r ↦
          congrArg (·.ofLp r) (hB j hjs), hv_tensor j hjs]
  else simp [hg0]
theorem approx_of_unitary_pullback {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) {H : Operator (2 ^ sysW)} {t eps : ℝ}
    {W₀ : Unitary (2 ^ (sysW + ancW))} {W' : Unitary (2 ^ (sysW + ancW'))}
    (hEq : ((rLiveCanon sysW part).embedUnitary W').1 *
    (ancCanon sysW ancW).basisOutcomeProjector 0 = W₀.1 *
    (ancCanon sysW ancW).basisOutcomeProjector 0)
    (hWalk₀ : ApproximatesTimeEvolution H t eps 1 W₀) : ApproximatesTimeEvolution H t eps 1 W' := by
  obtain ⟨φ, hφ⟩ := hWalk₀; refine ⟨φ, ?_⟩;
  let sysSmall : QRegister sysW (sysW + ancW') :=
      QRegister.block 0 sysW (zero_add_le_add_right sysW ancW');
      let ancSmall : QRegister ancW' (sysW + ancW') :=
      QRegister.block sysW ancW' le_rfl; let Uexp :=
                                           NormedSpace.exp ((-Complex.I *
                                           t) • H); let E_big : Operator (2 ^ (sysW + ancW)) :=
                                                      (W₀.1 - Complex.exp (φ *
                                                      Complex.I) • (sysCanon sysW ancW).embedMatrix
                                                      Uexp) * ((sysCanon sysW ancW).embedMatrix 1 *
                                                      (ancCanon sysW ancW).basisOutcomeProjector 0);
                                                      let E_small : Operator (2 ^ (sysW + ancW')) :=
                                                      (W'.1 - Complex.exp (φ *
                                                      Complex.I) • sysSmall.embedMatrix Uexp) *
                                                      (sysSmall.embedMatrix 1 *
                                                      ancSmall.basisOutcomeProjector 0); change
                                                      ‖E_small‖ ≤ eps
  have hcomp_sys : (rLiveCanon sysW part).compose sysSmall = sysCanon sysW ancW := by
    ext i;
    have hs : sysSmall i = Fin.castAdd ancW' i :=
        Fin.ext (Nat.zero_add i.val); change ((rLiveCanon sysW part) (sysSmall i)).val =
        (sysCanon sysW ancW i).val; rw [hs]; exact congrArg Fin.val (QRegister.concat_apply_left
        (sysCanon sysW ancW) ((ancCanon sysW ancW).compose part.keepIdx)
        (sysCanon_disj_keep part) i)
  have hcomp_anc : (rLiveCanon sysW part).compose ancSmall =
      (ancCanon sysW ancW).compose part.keepIdx := by
    ext i;
    have ha : ancSmall i = Fin.natAdd sysW i :=
        Fin.ext rfl; change ((rLiveCanon sysW part) (ancSmall i)).val =
        ((ancCanon sysW ancW).compose part.keepIdx i).val; rw [ha]; exact congrArg Fin.val
        (QRegister.concat_apply_right (sysCanon sysW ancW)
        ((ancCanon sysW ancW).compose part.keepIdx) (sysCanon_disj_keep part) i)
  have htensor (x : Fin (2 ^ (sysW + ancW')) → ℂ) :
      E_big.mulVec ((rLiveCanon sysW part).tensorState x (Pi.single 0 1)) =
      (rLiveCanon sysW part).tensorState (E_small.mulVec x) (Pi.single 0 1) := by
    have hidle_fix (y : Fin (2 ^ (sysW + ancW')) → ℂ) :
        ((rIdleCanon sysW part).basisOutcomeProjector 0).mulVec ((rLiveCanon sysW part).tensorState
        y (Pi.single 0 1)) = (rLiveCanon sysW part).tensorState y (Pi.single 0 1) := by
      funext g; rw [(rIdleCanon sysW part).basisOutcomeProjector_mulVec]
      by_cases hid : (rIdleCanon sysW part).extractIndex g = 0
      · simp [hid]
      · simp [QRegister.tensorState,
            Pi.single_eq_of_ne (mt (env_eq_zero_iff_idle_zero part g).mp hid)]
    have hproj_act :
        ((ancCanon sysW ancW).basisOutcomeProjector 0).mulVec ((rLiveCanon sysW part).tensorState x
        (Pi.single 0 1)) =
        (rLiveCanon sysW part).tensorState ((ancSmall.basisOutcomeProjector 0).mulVec x)
        (Pi.single 0 1) := by
      have hp : (ancCanon sysW ancW).basisOutcomeProjector 0 =
          ((rLiveCanon sysW part).compose ancSmall).basisOutcomeProjector 0 *
          (rIdleCanon sysW part).basisOutcomeProjector 0 := by
        rw [hcomp_anc,
            ← assembleAnc_basisOutcomeProjector_zero part ((ancCanon sysW ancW).compose
            part.keepIdx) (rIdleCanon sysW part) (ancCanon_keep_disj_idle part)]
        exact congrArg (fun r ↦ r.basisOutcomeProjector 0)
            (assembleAnc_canon_eq (sysW := sysW) part).symm
      rw [hp, ← Matrix.mulVec_mulVec, hidle_fix x, compose_basisOutcomeProjector_zero,
          (rLiveCanon sysW part).embedMatrix_mulVec_tensorState]
    have hE_eq : E_big = ((rLiveCanon sysW part).embedMatrix (W'.1 - Complex.exp (φ *
        Complex.I) • sysSmall.embedMatrix Uexp)) *
        (ancCanon sysW ancW).basisOutcomeProjector 0 := by
      dsimp [E_big];
      rw [(sysCanon sysW ancW).embedMatrix_one, Matrix.one_mul, Matrix.sub_mul, ← hEq,
          QRegister.embedUnitary_val, ← hcomp_sys, (rLiveCanon sysW part).embedMatrix_compose,
          ← Matrix.sub_mul, ← (rLiveCanon sysW part).embedMatrix_smul,
          ← (QRegExt.embedMatrix_sub (rLiveCanon sysW part))]
    rw [hE_eq, ← Matrix.mulVec_mulVec, hproj_act,
        (rLiveCanon sysW part).embedMatrix_mulVec_tensorState]
    dsimp [E_small]; rw [sysSmall.embedMatrix_one, Matrix.one_mul, Matrix.mulVec_mulVec]
  rw [l2_opNorm_def];
  refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E_big) fun x ↦ ?_).trans hφ
  let rL :=
      rLiveCanon sysW part; change ‖(WithLp.toLp 2 (E_small.mulVec x.ofLp) : EuclideanSpace ℂ _)‖ ≤
      _
  rw [← norm_euclidean_tensorState_single rL 0, ← htensor x.ofLp,
      ← norm_euclidean_tensorState_single rL 0 x.ofLp]
  exact E_big.l2_opNorm_mulVec (WithLp.toLp 2 (rL.tensorState x.ofLp (Pi.single 0 1)))

theorem unembedProgram_correctness {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle)
    {H : Operator (2 ^ sysW)} {t eps : ℝ}
    (P_big : ∀ {Var : Type} {m : ℕ}, Var → QRegister sysW m → QRegister ancW m →
        DynamicCircuit Var m)
    (hBigCorr : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {m : ℕ} [NeZero (2 ^ m)]
      (v : Var) (rS : QRegister sysW m) (rA : QRegister ancW m) (hd : rS.DisjointWires rA),
      ∃ W : Unitary (2 ^ (sysW + ancW)),
        ApproximatesTimeEvolution H t eps 1 W ∧
        RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rS Finset.univ rA hd W
          (P_big v rS rA).compile)
    (hWires : ∀ {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister sysW n)
      (rAncSmall : QRegister ancW' n),
      rSys.DisjointWires rAncSmall →
      let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
      let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl
      AllWiresLtDyn n (P_big v (rAmb.compose rSys)
        (assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall))))
    {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSys : QRegister sysW n) (rAncSmall : QRegister ancW' n)
    (hdisj : rSys.DisjointWires rAncSmall) :
    ∃ W' : Unitary (2 ^ (sysW + ancW')),
      ApproximatesTimeEvolution H t eps 1 W' ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAncSmall hdisj W'
        (unembedProgram part P_big v rSys rAncSmall).compile := by
  let _ : Fintype Var := Fintype.ofFinite Var
  let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
  let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl;
  let rS := rAmb.compose rSys; let rKeep := rAmb.compose rAncSmall;
  let rA := assembleAnc part rKeep rPhantom (amb_disj_phantom rAncSmall);
  let rIC := rIdleCanon sysW part; let rLC := rLiveCanon sysW part
  have hSK : rS.DisjointWires rKeep := QRegister.disjoint_iff.mpr fun i j h ↦
    QRegister.disjoint_iff.mp hdisj i j (rAmb.wires.injective h)
  have hd : rS.DisjointWires rA := assembleAnc_disjoint_left part rS rKeep rPhantom hSK
    (amb_disj_phantom rSys) (amb_disj_phantom rAncSmall)
  obtain ⟨W₀, hWalk₀, hReal₀⟩ := hBigCorr v rS rA hd
  let P_sm := unembedProgram part P_big v rSys rAncSmall
  have honReg : (DynCircExt.onRegister rAmb P_sm) = P_big v rS rA :=
    onRegister_unembedDyn_eq (Nat.le_add_right n kIdle) (P_big v rS rA)
        (hWires v rSys rAncSmall hdisj)
  let rBig : QRegister (sysW + ancW) (n + kIdle) := rS.concat rA hd
  have hrBig_anc : rBig.compose (ancCanon sysW ancW) = rA := by
    ext j; exact congrArg Fin.val (QRegister.concat_apply_right rS rA hd j)
  have hrBig_idle : rBig.compose rIC = rPhantom :=
      (congrArg (fun r ↦ r.compose part.idleIdx) hrBig_anc).trans
    (assembleAnc_compose_idle part _ _ _)
  have hrBig_live : rBig.compose rLC = rAmb.compose (rSys.concat rAncSmall hdisj) := by
    ext q; change (rBig (rLC q)).val = (rAmb ((rSys.concat rAncSmall hdisj) q)).val
    if hq : q.val < sysW then
      rw [show q = Fin.castAdd ancW' ⟨q.val, hq⟩ from Fin.ext rfl]; dsimp only [rLC, rBig, rS]
      rw [rLiveCanon, QRegister.concat_apply_left, QRegister.concat_apply_left,
        show sysCanon _ _ ⟨q.val, hq⟩ = Fin.castAdd ancW ⟨q.val, hq⟩ from Fin.ext (Nat.zero_add _),
            QRegister.concat_apply_left]; rfl
    else
      let i : Fin ancW' := ⟨q.val - sysW, by omega⟩
      rw [show q = Fin.natAdd sysW i from Fin.ext (by dsimp [i]; omega)]; dsimp only [rLC]
      rw [rLiveCanon, QRegister.concat_apply_right, QRegister.concat_apply_right,
        show rBig ((ancCanon sysW ancW).compose part.keepIdx i) =
            rA (part.keepIdx i) from QRegister.concat_apply_right rS rA hd _]
      exact congrArg (fun r ↦ (r i).val)
          (assembleAnc_compose_keep part rKeep rPhantom (amb_disj_phantom _))
  have hAmbPhDisj : rAmb.DisjointWires rPhantom := QRegister.disjoint_iff.mpr fun i j h ↦ by
    have hv : 0 + i.val = n + j.val := congrArg Fin.val h; have := i.isLt; omega
  have huniv {k m : ℕ} (r : QRegister k m) : r.basisOutcomesProjector Finset.univ = 1 := by
    simp only [QRegister.basisOutcomesProjector, Finset.mem_univ, ↓reduceIte, Matrix.diagonal_one]
  have hDirtyComm : ∀ B : Operator (2 ^ n), rAmb.embedMatrix B * (dirtyObservable rPhantom).1.mat =
      (dirtyObservable rPhantom).1.mat * rAmb.embedMatrix B := by
    intro B;
    rw [dirtyObservable_mat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    congr 1; exact rAmb.embedMatrix_comm_of_disjoint rPhantom hAmbPhDisj B (compProj 0)
  have hC : (1 - rIC.basisOutcomeProjector 0) * W₀.1 *
      (ancCanon sysW ancW).basisOutcomeProjector 0 = 0 := by
    let C :=
        (1 - rIC.basisOutcomeProjector 0) * W₀.1 *
        (ancCanon sysW ancW).basisOutcomeProjector 0; have hstep :=
                                                        hReal₀ (dirtyObservable rPhantom) default;
                                                        rw [← honReg] at hstep;
                                                        have hrhs_le :=
                                                        wp_onRegister_le_of_comm rAmb P_sm
                                                        (dirtyObservable rPhantom) hDirtyComm
                                                        default
    have hunivS := huniv rS
    have hph_zero : (dirtyObservable rPhantom).1.mat * rA.basisOutcomeProjector 0 = 0 := by
      rw [dirtyObservable_mat,
          assembleAnc_basisOutcomeProjector_zero part rKeep rPhantom (amb_disj_phantom rAncSmall),
          Matrix.sub_mul,
          Matrix.one_mul];
          have hcommKP : rPhantom.basisOutcomeProjector 0 * rKeep.basisOutcomeProjector 0 =
          rKeep.basisOutcomeProjector 0 * rPhantom.basisOutcomeProjector 0 :=
          rPhantom.embedMatrix_comm_of_disjoint rKeep (QRegister.disjoint_comm.mp (amb_disj_phantom
          rAncSmall)) (compProj 0) (compProj 0); rw [← Matrix.mul_assoc, hcommKP, Matrix.mul_assoc,
          rPhantom.basisOutcomeProjector_mul_self, sub_self]
    let dPh : CQAssertion (Store Var) (2 ^ (n + kIdle)) := fun _ ↦ dirtyObservable rPhantom
    have hrhs_psd :
        (-(CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes
        (wp (DynCircExt.onRegister rAmb P_sm).compile
            dPh) rS Finset.univ) rA default).1.mat).PosSemidef := by
      have hm :
          CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes
          (wp (DynCircExt.onRegister rAmb P_sm).compile dPh) rS Finset.univ) rA default ≤
          CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes dPh rS Finset.univ)
          rA default := by
        apply HermitianMat.le_iff.mpr;
        simp only [HermitianMat.mat_sub, restrictAssertionToZeroAncilla_coe_loc,
            PgBase.restrictAssertionToBasisOutcomes_coe]
        exact HermitianMat.le_iff.mp (HermitianMat.conj_mono (M := rA.basisOutcomeProjector 0)
          (HermitianMat.conj_mono (M := rS.basisOutcomesProjector Finset.univ) hrhs_le))
      have ht :
          (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes dPh rS
          Finset.univ) rA default).1.mat =
          0 := by
        simp only [dPh, restrictAssertionToZeroAncilla_coe_loc,
            PgBase.restrictAssertionToBasisOutcomes_coe, HermitianMat.conj_apply_mat, hunivS,
            Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
            rA.basisOutcomeProjector_conjTranspose]; rw [Matrix.mul_assoc, hph_zero,
            Matrix.mul_zero]
      have hp := HermitianMat.le_iff.mp hm
      rw [HermitianMat.mat_sub, ht, zero_sub] at hp; exact hp
    have hlhs_eq :
        (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes (CQAssertion.qAssign
        (rBig.embedUnitary W₀) dPh) rS Finset.univ) rA default).1.mat = rBig.embedMatrix (Cᴴ * C)
        := by
      simp only [dPh, restrictAssertionToZeroAncilla_coe_loc,
          PgBase.restrictAssertionToBasisOutcomes_coe, HermitianMat.conj_apply_mat, hunivS,
          Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
          rA.basisOutcomeProjector_conjTranspose, wp_qAssign_mat_loc, QRegister.embedUnitary_val]
      have hPA : rA.basisOutcomeProjector 0 =
          rBig.embedMatrix ((ancCanon sysW ancW).basisOutcomeProjector 0) := by
        rw [← hrBig_anc, compose_basisOutcomeProjector_zero]
      have hDP : (dirtyObservable rPhantom).1.mat = rBig.embedMatrix (1 -
          rIC.basisOutcomeProjector 0)
          := by
        rw [dirtyObservable_mat, ← hrBig_idle, compose_basisOutcomeProjector_zero,
            (QRegExt.embedMatrix_sub rBig), rBig.embedMatrix_one]
      have hidem : (1 - rIC.basisOutcomeProjector 0)ᴴ * (1 - rIC.basisOutcomeProjector 0) = 1 -
          rIC.basisOutcomeProjector 0 := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
            rIC.basisOutcomeProjector_conjTranspose, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
            Matrix.mul_one, rIC.basisOutcomeProjector_mul_self, sub_self, sub_zero]
      rw [hPA, hDP, ← rBig.embedMatrix_conjTranspose]; dsimp only [C];
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          (ancCanon sysW ancW).basisOutcomeProjector_conjTranspose]
      simp only [← rBig.embedMatrix_mul, Matrix.mul_assoc]
      congr 1; congr 1; congr 1
      rw [← Matrix.mul_assoc (1 - rIC.basisOutcomeProjector 0)ᴴ, hidem]
    have hstep_psd := (posSemidef_iff_dotProduct_mulVec_loc _).mp (HermitianMat.le_iff.mp hstep);
    have hrhs_mul :=
        (posSemidef_iff_dotProduct_mulVec_loc _).mp hrhs_psd; apply Matrix.ext_of_mulVec_single;
        intro g; let ψ := rBig.tensorState (Pi.single g 1) (Pi.single 0 1)
    have hψ : star ψ ⬝ᵥ (rBig.embedMatrix (Cᴴ * C)).mulVec ψ ≤ 0 := by
      have h1 := hstep_psd.2 ψ;
      have h2 :=
          hrhs_mul.2 ψ; rw [HermitianMat.mat_sub, hlhs_eq, Matrix.sub_mulVec, dotProduct_sub,
          sub_nonneg] at h1; rw [Matrix.neg_mulVec, dotProduct_neg, le_neg,
          neg_zero] at h2; exact h1.trans h2
    let u_g := C.mulVec (Pi.single g 1)
    rw [rBig.embedMatrix_mulVec_tensorState, star_dotProduct_tensorState_single rBig 0,
      ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec] at hψ
    refine funext fun z ↦
        (Complex.normSq_eq_zero.mp (((Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦
        Complex.normSq_nonneg _).mp
      (le_antisymm ?_ (Finset.sum_nonneg fun _ _ ↦
          Complex.normSq_nonneg _))) z (Finset.mem_univ _))).trans (by simp)
    refine le_trans (le_of_eq ?_) (Complex.le_def.mp hψ).1
    rw [dotProduct, Complex.re_sum]; refine Finset.sum_congr rfl fun _ _ ↦ by
      simp only [Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.normSq_apply]; ring
  obtain ⟨W', hW'_eq⟩ := exists_unembedded_unitary part W₀ hC
  refine ⟨W', approx_of_unitary_pullback part hW'_eq hWalk₀, fun M σ ↦ ?_⟩
  have hM := hReal₀ (embedObservable rAmb M) σ
  rw [← honReg, show (fun _ : Store Var ↦ embedObservable rAmb M) = embedAssertion rAmb (fun _ ↦
      M) from rfl,
    wp_onRegister_embedAssertion rAmb P_sm (fun _ ↦ M)] at hM
  let combSmall := rSys.concat rAncSmall hdisj
  let hL_sm :=
      (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes (CQAssertion.qAssign
      (combSmall.embedUnitary W') (fun _ ↦ M)) rSys Finset.univ) rAncSmall σ).1
  let hR_sm :=
      (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes (wp P_sm.compile
      (fun _ ↦ M)) rSys Finset.univ) rAncSmall σ).1
  let L_small := hL_sm.mat;
  let R_small := hR_sm.mat; apply HermitianMat.le_iff.mpr; change (R_small - L_small).PosSemidef
  have huniv_sm := huniv rSys; have hunivS := huniv rS
  have hPA_split : rA.basisOutcomeProjector 0 =
      rAmb.embedMatrix (rAncSmall.basisOutcomeProjector 0) * rPhantom.basisOutcomeProjector 0 := by
    rw [assembleAnc_basisOutcomeProjector_zero part rKeep rPhantom (amb_disj_phantom rAncSmall),
        compose_basisOutcomeProjector_zero]
  have hW_big_eq : (rBig.embedUnitary W₀).1 * rA.basisOutcomeProjector 0 =
      rAmb.embedMatrix ((combSmall.embedUnitary W').1 * rAncSmall.basisOutcomeProjector 0) *
      rPhantom.basisOutcomeProjector 0 := by
    have hPA_canon : rA.basisOutcomeProjector 0 =
        rBig.embedMatrix ((ancCanon sysW ancW).basisOutcomeProjector 0) := by
      rw [← hrBig_anc, compose_basisOutcomeProjector_zero]
    rw [hPA_canon, QRegister.embedUnitary_val, ← rBig.embedMatrix_mul, ← hW'_eq,
        rBig.embedMatrix_mul, ← hPA_canon, ← QRegister.embedUnitary_val,
        ← rBig.embedUnitary_compose, hrBig_live, QRegister.embedUnitary_compose,
        QRegister.embedUnitary_val, hPA_split, ← Matrix.mul_assoc, ← rAmb.embedMatrix_mul]
  have hBig_LR :
      (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes (embedAssertion rAmb
      (wp P_sm.compile fun _ ↦ M)) rS Finset.univ) rA σ).1.mat -
      (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes (CQAssertion.qAssign
      (rBig.embedUnitary W₀) (embedAssertion rAmb fun _ ↦ M)) rS Finset.univ) rA σ).1.mat =
      rAmb.embedMatrix (R_small - L_small) * rPhantom.basisOutcomeProjector 0 := by
    have hcommP (X : Operator (2 ^ n)) : rPhantom.basisOutcomeProjector 0 * rAmb.embedMatrix X =
        rAmb.embedMatrix X * rPhantom.basisOutcomeProjector 0 :=
        rPhantom.embedMatrix_comm_of_disjoint rAmb (QRegister.disjoint_comm.mp hAmbPhDisj)
        (compProj 0) X
    have hpush (X : Operator (2 ^ n)) (Y : Operator (2 ^ (n + kIdle)))
        (hY : rPhantom.basisOutcomeProjector 0 * Y = Y) : rPhantom.basisOutcomeProjector 0 *
        (rAmb.embedMatrix X * Y) = rAmb.embedMatrix X * Y := by
      rw [← Matrix.mul_assoc, hcommP, Matrix.mul_assoc, hY]
    have hR :
        (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes (embedAssertion rAmb
        (wp P_sm.compile fun _ ↦ M)) rS Finset.univ) rA σ).1.mat = rAmb.embedMatrix R_small *
        rPhantom.basisOutcomeProjector 0 := by
      simp only [restrictAssertionToZeroAncilla_coe_loc,
          PgBase.restrictAssertionToBasisOutcomes_coe, HermitianMat.conj_apply_mat, hunivS,
          Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
          rA.basisOutcomeProjector_conjTranspose, embedAssertion, embedObservable_mat]
      rw [hPA_split]; dsimp only [R_small, hR_sm]
      simp only [restrictAssertionToZeroAncilla_coe_loc,
          PgBase.restrictAssertionToBasisOutcomes_coe, HermitianMat.conj_apply_mat, huniv_sm,
          Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
          rAncSmall.basisOutcomeProjector_conjTranspose, rAmb.embedMatrix_mul,
          Matrix.mul_assoc]; congr 1; exact hpush _ _ (hpush _ _
          (rPhantom.basisOutcomeProjector_mul_self 0))
    have hL :
        (CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToBasisOutcomes (CQAssertion.qAssign
        (rBig.embedUnitary W₀) (embedAssertion rAmb (fun _ ↦ M))) rS Finset.univ) rA σ).1.mat =
        rAmb.embedMatrix L_small * rPhantom.basisOutcomeProjector 0 := by
      simp only [restrictAssertionToZeroAncilla_coe_loc,
          PgBase.restrictAssertionToBasisOutcomes_coe, HermitianMat.conj_apply_mat, hunivS,
          Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
          rA.basisOutcomeProjector_conjTranspose, wp_qAssign_mat_loc, embedAssertion,
          embedObservable_mat]
      have hleft_adj : rA.basisOutcomeProjector 0 * (rBig.embedUnitary W₀).1ᴴ =
          ((rBig.embedUnitary W₀).1 * rA.basisOutcomeProjector 0)ᴴ := by
        rw [Matrix.conjTranspose_mul, rA.basisOutcomeProjector_conjTranspose]
      have hmid : rA.basisOutcomeProjector 0 * ((rBig.embedUnitary W₀).1ᴴ *
          rAmb.embedMatrix M.1.mat * (rBig.embedUnitary W₀).1) * rA.basisOutcomeProjector 0 =
          ((rBig.embedUnitary W₀).1 * rA.basisOutcomeProjector 0)ᴴ * rAmb.embedMatrix M.1.mat *
          ((rBig.embedUnitary W₀).1 * rA.basisOutcomeProjector 0) := by
        simp only [Matrix.mul_assoc];
        rw [← Matrix.mul_assoc (rA.basisOutcomeProjector 0), hleft_adj]
      rw [hmid, hW_big_eq, Matrix.conjTranspose_mul, rPhantom.basisOutcomeProjector_conjTranspose,
          ← rAmb.embedMatrix_conjTranspose]; dsimp only [L_small,
          hL_sm]; simp only [restrictAssertionToZeroAncilla_coe_loc,
          PgBase.restrictAssertionToBasisOutcomes_coe, HermitianMat.conj_apply_mat, huniv_sm,
          Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
          rAncSmall.basisOutcomeProjector_conjTranspose,
          wp_qAssign_mat_loc]; rw [Matrix.conjTranspose_mul,
          rAncSmall.basisOutcomeProjector_conjTranspose]; simp only [rAmb.embedMatrix_mul,
          Matrix.mul_assoc]; exact hpush _ _ (hpush _ _ (hpush _ _ (hpush _ _ (hpush _ _
          (rPhantom.basisOutcomeProjector_mul_self 0)))))
    rw [hR, hL, ← Matrix.sub_mul, (QRegExt.embedMatrix_sub rAmb)]
  have hposBig : (rAmb.embedMatrix (R_small - L_small) *
      rPhantom.basisOutcomeProjector 0).PosSemidef
      := by rw [← hBig_LR]; exact HermitianMat.le_iff.mp hM
  have hposBig_mul :=
      (posSemidef_iff_dotProduct_mulVec_loc _).mp hposBig; refine
      (posSemidef_iff_dotProduct_mulVec_loc _).mpr ⟨Matrix.IsHermitian.sub hR_sm.2 hL_sm.2,
      ?_⟩; intro x; let ψ := rAmb.tensorState x (Pi.single 0 1)
  have hph_ψ : (rPhantom.basisOutcomeProjector 0).mulVec ψ = ψ := funext fun g ↦ by
    rw [rPhantom.basisOutcomeProjector_mulVec]
    if hph : rPhantom.extractIndex g = 0 then simp only [hph, ↓reduceIte]
    else simp only [hph, ↓reduceIte, ψ, QRegister.tensorState, mul_zero,
      Pi.single_eq_of_ne fun hz : (rAmb.basisSplitEquiv g).2 = 0 ↦
          hph ((extractIndex_eq_zero_iff_basisBits_eq_zero _ g).mpr
        fun l ↦
            (QRegister.basisSplitEquiv_apply_snd rAmb g ⟨_, fun ⟨i, hi⟩ ↦
            hAmbPhDisj.ne i l hi⟩).symm.trans (congrFun hz _))]
  have hψ := hposBig_mul.2 ψ
  rwa [← Matrix.mulVec_mulVec, hph_ψ, rAmb.embedMatrix_mulVec_tensorState,
      star_dotProduct_tensorState_single rAmb 0] at hψ
end QuantumComputation.Specs.PhotochemistrySolution.UnembedIdleAncillas

namespace QuantumComputation.Specs.PhotochemistrySolution.UnembedDualBell531
set_option exponentiation.threshold 8192
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.UnembedIdleAncillas
/- ## 2. `< 20ms` Structural `AllWiresLtCirc` / `AllWiresLtDyn` Combinators -/

theorem assembleAnc_val_lt_of_not_idle {ancW ancW' kIdle n : ℕ}
    (part : AncillaPartition ancW ancW' kIdle)
    (rAncSmall : QRegister ancW' n)
    (j : Fin ancW)
    (hNotIdle : ∀ l : Fin kIdle, part.idleIdx l ≠ j) :
    let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
    let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl
    (assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall) j).val <
        n := by
  intro rAmb rPhantom
  refine (part.cover j).elim (fun ⟨i, hi⟩ ↦ hi ▸ ?_) fun ⟨l, hl⟩ ↦ absurd hl (hNotIdle l)
  exact (congrArg (fun r : QRegister ancW' _ ↦ (r i).val)
    (assembleAnc_compose_keep part _ _ (amb_disj_phantom rAncSmall))).trans_lt
    ((zero_add _).trans_lt (rAncSmall i).isLt)
theorem concat_val_lt_of_not_idle {sysW ancW ancW' kIdle n : ℕ}
    (part : AncillaPartition ancW ancW' kIdle)
    (rSys : QRegister sysW n) (rAncSmall : QRegister ancW' n)
    (w : Fin (sysW + ancW))
    (hNotIdle : ∀ l : Fin kIdle, sysW + (part.idleIdx l).val ≠ w.val) :
    let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
    let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl;
    let rS := rAmb.compose rSys;
    let rA := assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall)
    ∀ hd : rS.DisjointWires rA, ((rS.concat rA hd) w).val < n := by
  intro rAmb rPhantom rS rA hd
  if hw : w.val < sysW then
    rw [show w = Fin.castAdd ancW ⟨w.val, hw⟩ from Fin.ext rfl, QRegister.concat_apply_left]
    exact (zero_add _).trans_lt (rSys ⟨w.val, hw⟩).isLt
  else
    rw [show w = Fin.natAdd sysW ⟨w.val - sysW, by omega⟩ from Fin.ext (by dsimp; omega),
      QRegister.concat_apply_right]
    exact assembleAnc_val_lt_of_not_idle part rAncSmall ⟨w.val - sysW, by omega⟩ fun l hl ↦
      hNotIdle l (by have := congrArg Fin.val hl; dsimp at this; omega)
end QuantumComputation.Specs.PhotochemistrySolution.UnembedDualBell531

namespace QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen
open scoped Matrix.Norms.L2Operator
open PrimitiveGate ComplexConjugate PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectSymDyn
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectGidneyFast PhotochemistrySolution.TargetBScr
  PhotochemistrySolution.OvBidir PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectCompactRot34
open PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectLcu70Rot32
  PhotochemistrySolution.SelectCsa64GqspWalk PhotochemistrySolution.SelectCsa64ThreeSpec
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local semireducible] fwdCirc wrapDyn mkShared34DataLGenOff
theorem cpWires_norChainReflProg_fs {n m : ℕ} {P : Wire n → Prop} {rLcu : Fin (m + 2) → Wire n}
    {rCln : Fin (m + 1) → Wire n} {hIC : ∀ i j, rLcu i ≠ rCln j} {hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rCln j₁ ≠
    rCln j₂} {hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rLcu i₁ ≠ rLcu i₂} (hL : ∀ i, P (rLcu i))
    (hC : ∀ j, P (rCln j)) : ComputeProgWires P (norChainReflProg m rLcu rCln hIC hCC hIn) := by
  have hfin k : ∀ f, (∀ i, ComputeProgWires P (f i)) → ComputeProgWires P (finSeqProg k f) := by
    induction k with
      | zero => exact fun _ _ ↦ trivial
      | succ k ih => exact fun _ hf ↦ ⟨ih _ fun i ↦ hf i.castSucc, hf _⟩
  have hch k : ∀ rI rK h1 h2 h3, (∀ i, P (rI i)) → (∀ j, P (rK j)) →
      ComputeProgWires P (andChainProg k rI rK h1 h2 h3) := by
    induction k with | zero => exact fun _ _ _ _ _ _ _ ↦ trivial | succ k ih => cases k with
      | zero => exact fun _ _ _ _ _ hI hK ↦ ⟨hI 0, hI 1, hK 0⟩
      | succ k => exact fun _ _ _ _ _ hI hK ↦
            ⟨ih _ _ _ _ _ (fun i ↦ hI i.castSucc) (fun j ↦ hK j.castSucc), hK _, hI _, hK _⟩
  exact ⟨hfin _ _ hL, hch _ _ _ _ _ _ hL hC⟩
theorem allWiresLtDyn_fastReflCircLGenOff {scrW scrL m offRefl ancW' kIdle : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hm : offRefl + (m + 1) ≤ scrL)
    (part : AncillaPartition (ancWOfScr scrW) ancW' kIdle)
    (hIdleRefl : ∀ l : Fin kIdle,
      let u := (part.idleIdx l).val
      u < 34 + offRefl ∨ (34 + offRefl + (m + 1) ≤ u ∧ u < 34 + scrL) ∨
        (34 + scrL + (m + 2) ≤ u ∧ u < ancWOfScr scrW - 1))
    {Var : Type} {n : ℕ} (v : Var)
    (rSys : QRegister systemQubits_frozen n) (rAncSmall : QRegister ancW' n)
    (_hdisj : rSys.DisjointWires rAncSmall) :
    let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
    let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl;
    let rS := rAmb.compose rSys;
    let rA := assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall)
    ∀ hdisj' : rS.DisjointWires rA,
      AllWiresLtDyn n (fastReflCircLGenOff hp hm v rS rA hdisj') := by
  intro rAmb rPhantom rS rA hdisj'
  let P : Wire (totDimCompactGen scrW) → Prop := fun w ↦
      w.val < systemQubits_frozen ∨ (systemQubits_frozen + 34 + offRefl ≤ w.val ∧ w.val <
      systemQubits_frozen + 34 + offRefl + (m + 1)) ∨ (systemQubits_frozen + 34 + scrL ≤ w.val ∧
      w.val < systemQubits_frozen + 34 + scrL + (m + 2)) ∨ w.val = systemQubits_frozen + 34 + scrW +
      70
  have hP : ∀ w : Wire (totDimCompactGen scrW), P w → ((rS.concat rA hdisj') w).val < n := by
    intro w hw; refine UnembedDualBell531.concat_val_lt_of_not_idle part rSys rAncSmall w ?_ hdisj';
    intro l hl; have hu := hIdleRefl l
    dsimp only at hu; dsimp only [P] at hw; unfold ancWOfScr at hu; omega
  unfold fastReflCircLGenOff fastReflBracketLGenOff;
  refine allWiresLtDyn_of_andBracketWires v (rS.concat rA hdisj') P hP ?_
  have hQ : P (locQCompactGen scrW) := by
    simp only [P, locQCompactGen, locAncCompactGen, QRegister.block_apply_val]; omega
  have hCln (j : Fin (m + 1)) : P (reflRCleanLGenOff hp hm j) := by
    simp only [P, reflRCleanLGenOff, rScrLGen, scrSubLGen, locAncCompactGen,
        QRegister.compose_apply, QRegister.block_apply_val]; omega
  refine ⟨andBracketWires_wrap (cpWires_norChainReflProg_fs (fun i ↦ by
      simp only [P, rLcuLGen, lcuSubLGen, locAncCompactGen, QRegister.compose_apply,
          QRegister.block_apply_val]; omega) hCln)
    ⟨fun i ↦ Subsingleton.elim i 0 ▸ hCln _, fun i ↦ by
        fin_cases i
        · exact hQ
        · exact hCln _,
      fun i ↦ Subsingleton.elim i 0 ▸ hCln _⟩, fun i ↦ Subsingleton.elim i 0 ▸ hQ⟩
theorem comm_circWires_embedMatrix_fs {k n : ℕ} (rSub : QRegister k n) (M : Operator (2 ^ k))
    {c : Circuit n} : CircWires (fun w ↦ w ∉ Set.range rSub.wires) c → c.eval.1 *
    rSub.embedMatrix M = rSub.embedMatrix M * c.eval.1 := by
  induction c with
  | identity => simp [Circuit.eval_identity]
  | gate g reg => refine fun h ↦ by rw [Circuit.eval_gate, QRegister.embedUnitary_val]; exact
      reg.embedMatrix_comm_of_disjoint rSub (QRegister.disjoint_iff.mpr fun i j e ↦
                                      h i ⟨j, e.symm⟩) g.eval.1 M
  | seq _ _ ih₁ ih₂ => rintro ⟨h₁, h₂⟩; rw [Circuit.eval_seq, Submonoid.coe_mul,
      mul_assoc, ih₁ h₁, ← mul_assoc, ih₂ h₂, mul_assoc]
theorem circWires_fwdCirc_of_cpWires_fs {n : ℕ} {P : Wire n → Prop} {p : ComputeProg n} :
    ComputeProgWires P p → CircWires P (fwdCirc p) := by
  induction p with
  | id => intro _; trivial
  | x _ => intro hu i; have e : i = 0 := Subsingleton.elim i 0; subst e; exact hu
  | cnot _ _ _ => rintro ⟨hc, ht⟩ i; fin_cases i <;> assumption
  | andGate _ _ _ _ _ _ => rintro ⟨h₁, h₂, ha⟩ i; fin_cases i <;> assumption
  | seq _ _ ih₁ ih₂ => rintro ⟨h₁, h₂⟩; exact ⟨ih₁ h₁, ih₂ h₂⟩
theorem allWiresLtDyn_wrapDyn_fs {Var : Type} {n M : ℕ} (v : Var) {p : ComputeProg n}
    {mid : DynamicCircuit Var n} : ComputeProgWires (fun w ↦ w.val < M) p → AllWiresLtDyn M mid →
    AllWiresLtDyn M (wrapDyn v p mid) := by
  induction p generalizing mid with
  | id => exact fun _ hm ↦ hm
  | x _ => exact fun hu hm ↦ ⟨allWiresLtCirc_single hu, hm, allWiresLtCirc_single hu⟩
  | cnot _ _ _ => exact fun ⟨hc, ht⟩ hm ↦ ⟨allWiresLtCirc_pair hc ht, hm, allWiresLtCirc_pair hc ht⟩
  | andGate _ _ _ _ _ _ => exact (fun ⟨h₁, h₂, h₃⟩ hm ↦
    let a {g} : AllWiresLtCirc M (.gate g (QRegister.singleton _)) := allWiresLtCirc_single h₃
    (fun b c d e ↦ ⟨⟨a, a, d, e, c, a, d, e, c, a, a⟩, hm, ⟨a, fun i ↦ Subsingleton.elim i 0 ▸ h₃,
        ⟨a, ⟨b, allWiresLtCirc_pair h₁ h₂,
      b⟩⟩, trivial⟩⟩) (allWiresLtCirc_single h₂) (allWiresLtCirc_pair h₁ h₃)
          (allWiresLtCirc_pair h₂ h₃) (allWiresLtCirc_inverse a))
  | seq _ _ ih₁ ih₂ => exact fun ⟨h₁, h₂⟩ hm ↦ ih₁ h₁ (ih₂ h₂ hm)
end QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen

namespace QuantumComputation.Specs.PhotochemistrySolution.FastQft8
set_option autoImplicit false
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
-- tempAnd wrapper for 34-AND QFT8 (-120 T/step at +0 Q)
abbrev toff0 {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M) (β : BitAssignment M) :
    BitAssignment M := Function.update β (rDelta 6) (β (rDelta 6) + β (rP 0) * β (rP 7))
end QuantumComputation.Specs.PhotochemistrySolution.FastQft8
end
end
