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
public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE46687
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TwoGearQPE
/-! # Bond-Wire Deferred Two-Gear Sine-Window QPE (`TwoGearBondDefer`)
Defers the `s' = 0` `wordPairTreeCircuit` bond-wire layer of `twoGearZeroAncHi` past coarse `StageA`
in Two-Gear QPE (`TwoGearQPE`): the top `16 - mLow` layers act on `mLow .. 15`, while the
`s' = 0` layer on `mLow - 1` uses `mLow .. 15` purely as computational-basis `CNOT` controls and
commutes with `StageA`'s `qpeMuxUnitary`, keeping `nDirtyLo .. mLow - 1` in `|0⟩` throughout
`StageA` (`sUbA ≤ sRem + (mLow - nDirtyLo)`, `-1` qubit, `0` extra `T` gates, `0` extra `δWin`).
## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- M. Möttönen et al., *Phys. Rev. Lett.* **93**, 130502 (2004), DOI: 10.1103/PhysRevLett.93.130502.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee et al., *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305. -/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBondDefer
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Real TopIntegrationBridge Cat11CompactPhase2Bridge TwoGearQPEPhase5
open Solution.TwoGearBox Solution.BlockEncodingCore
open DihedralWalkQPE DihedralWalkQPE.MultiGearQPE DihedralWalkQPE.BlockReflection
open scoped Matrix Matrix.Norms.L2Operator BigOperators
local instance (priority := 1000000) instNeZeroTwoPowBondDefer (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
/-! ## Section 1: `wordPairTreeCircuit` Relocation & Top-Down `mottonenCascade` Split -/
/-- Relocating a quantum circuit twice via `Circuit.onRegister` equals `r₂.compose r₁`. -/
theorem circuit_onRegister_onRegister {a b c : ℕ} (r₂ : QRegister b c) (r₁ : QRegister a b) :
    ∀ circ : Circuit a, (circ.onRegister r₁).onRegister r₂ = circ.onRegister (r₂.compose r₁)
  | .identity | .gate _ _ => rfl
  | .seq c₁ c₂ => by dsimp only [Circuit.onRegister]; rw [circuit_onRegister_onRegister r₂ r₁ c₁,
      circuit_onRegister_onRegister r₂ r₁ c₂]
/-- Relocating `wordPairTreeCircuit` along `r` gives `wordPairTreeCircuit` on `r.compose rCtrl`. -/
theorem wordPairTreeCircuit_onRegister {m n : ℕ} (r : QRegister m n) :
    ∀ (k : ℕ) (rCtrl : QRegister k m) (tgt : Wire m)
      (hdisj : rCtrl.DisjointWires (QRegister.singleton tgt))
      (hrdisj : (r.compose rCtrl).DisjointWires (QRegister.singleton (r tgt))) (tr : WordPairTree),
      (wordPairTreeCircuit k rCtrl tgt hdisj tr).onRegister r =
        wordPairTreeCircuit k (r.compose rCtrl) (r tgt) hrdisj tr
  | _, _, _, _, _, .skip | _ + 1, _, _, _, _, .leaf _ _ _ _ | 0, _, _, _, _, .branch _ _ =>
      by simp [wordPairTreeCircuit]
  | 0, _, tgt, _, _, .leaf _ _ _ _ => by
      dsimp only [wordPairTreeCircuit]; rw [circuit_onRegister_onRegister]
      exact congrArg (Circuit.onRegister · _) (by ext i; rfl)
  | k + 1, rCtrl, tgt, hdisj, hrdisj, .branch tP tM => by
      have hSlice : r.compose (rCtrl.slice 0 k (by omega)) =
          (r.compose rCtrl).slice 0 k (by omega) := by ext i; rfl
      have hLo0 := hdisj.compose_left (QRegister.block 0 k (by omega))
      have hLo2 := hrdisj.compose_left (QRegister.block 0 k (by omega))
      have hLo1 : (r.compose (rCtrl.slice 0 k (by omega))).DisjointWires
          (QRegister.singleton (r tgt)) := hSlice.symm ▸ hLo2
      have hcnot : r.compose (QRegister.pair (rCtrl ⟨k, by omega⟩) tgt (hdisj.ne ⟨k, by omega⟩ 0)) =
          QRegister.pair ((r.compose rCtrl) ⟨k, by omega⟩) (r tgt) (hrdisj.ne ⟨k, by omega⟩ 0) := by
        ext i; fin_cases i <;> rfl
      have hCongr (rC₁ rC₂ : QRegister k n) (h₁ : rC₁.DisjointWires (QRegister.singleton (r tgt)))
          (h₂ : rC₂.DisjointWires (QRegister.singleton (r tgt))) (heq : rC₁ = rC₂) (u) :
          wordPairTreeCircuit k rC₁ (r tgt) h₁ u = wordPairTreeCircuit k rC₂ (r tgt) h₂ u :=
        heq ▸ rfl
      dsimp only [wordPairTreeCircuit, Circuit.sequence, Circuit.onRegister]
      rw [(wordPairTreeCircuit_onRegister r k (rCtrl.slice 0 k (by omega)) tgt hLo0 hLo1 tP).trans
          (hCongr _ _ hLo1 hLo2 hSlice tP), (wordPairTreeCircuit_onRegister r k
          (rCtrl.slice 0 k (by omega)) tgt hLo0 hLo1 tM).trans (hCongr _ _ hLo1 hLo2 hSlice tM),
          hcnot]
/-- Splitting `mottonenCascade (q + 1) (s + 1)` into top `s` layers + `s = 1` bond layer. -/
theorem mottonenCascade_split (q : ℕ) : ∀ (s : ℕ) (hs : s ≤ q) (trs : List WordPairTree),
    (∀ {d : ℕ} (g : PrimitiveGate d), (mottonenCascade q s hs (trs.take s)).count g +
        (mottonenCascade (q + 1) 1 (by omega) (trs.drop s)).count g =
      (mottonenCascade (q + 1) (s + 1) (by omega) trs).count g) ∧
    (mottonenCascade (q + 1) 1 (by omega) (trs.drop s)).eval *
      (QRegister.block 1 q (by omega)).embedUnitary (mottonenCascade q s hs (trs.take s)).eval =
    (mottonenCascade (q + 1) (s + 1) (by omega) trs).eval
  | 0, _, _ | _ + 1, _, [] => ⟨fun _ ↦ by simp [mottonenCascade], by simp [mottonenCascade]⟩
  | s' + 1, _, tr :: trs => by
      obtain ⟨ihCnt, ihEval⟩ := mottonenCascade_split q s' (by omega) trs
      let rHi : QRegister q (q + 1) := QRegister.block 1 q (by omega)
      have hBlk {a b c d : ℕ} (hab : a + b ≤ c) (hd : d < a) :
          (QRegister.block a b hab).DisjointWires (QRegister.singleton ⟨d, by omega⟩) := by
        rw [QRegister.disjoint_iff]; intro i j hij; have hv := congrArg Fin.val hij
        simp only [QRegister.block_apply_val, QRegister.singleton_apply] at hv; omega
      have hDisj₁ := hBlk (a := s' + 1) (b := q - (s' + 1)) (c := q) (by omega)
        (Nat.lt_succ_self s')
      have hDisj₂ := hBlk (a := s' + 2) (b := (q + 1) - (s' + 2)) (c := q + 1) (by omega)
        (Nat.lt_succ_self (s' + 1))
      have hDisjComp : (rHi.compose (QRegister.block (s' + 1) (q - (s' + 1))
          (by omega))).DisjointWires (QRegister.singleton (rHi ⟨s', by omega⟩)) := by
        rw [QRegister.disjoint_iff]; intro i j hij; have hv := congrArg Fin.val hij
        simp only [rHi, QRegister.compose_apply, QRegister.block_apply_val,
          QRegister.singleton_apply] at hv; omega
      have hTreeCongr {k₁ k₂ : ℕ} (hk : k₁ = k₂) (r₁ : QRegister k₁ (q + 1))
          (r₂ : QRegister k₂ (q + 1)) (t₁ t₂ : Wire (q + 1)) (ht : t₁ = t₂)
          (hd₁ : r₁.DisjointWires (QRegister.singleton t₁))
          (hd₂ : r₂.DisjointWires (QRegister.singleton t₂))
          (hr : ∀ (i : ℕ) (hi₁ : i < k₁) (hi₂ : i < k₂), (r₁ ⟨i, hi₁⟩).val = (r₂ ⟨i, hi₂⟩).val) :
          wordPairTreeCircuit k₁ r₁ t₁ hd₁ tr = wordPairTreeCircuit k₂ r₂ t₂ hd₂ tr := by
        subst hk; subst ht
        have hreq : r₁ = r₂ := by ext i; exact hr i.val i.isLt i.isLt
        subst hreq; rfl
      have hCircEq : (wordPairTreeCircuit (q - (s' + 1))
          (QRegister.block (s' + 1) (q - (s' + 1)) (by omega)) ⟨s', by omega⟩ hDisj₁ tr).onRegister
            rHi = wordPairTreeCircuit ((q + 1) - (s' + 2))
            (QRegister.block (s' + 2) ((q + 1) - (s' + 2)) (by omega)) ⟨s' + 1, by omega⟩ hDisj₂
              tr :=
        (wordPairTreeCircuit_onRegister rHi (q - (s' + 1))
          (QRegister.block (s' + 1) (q - (s' + 1)) (by omega)) ⟨s', by omega⟩ hDisj₁ hDisjComp
          tr).trans (hTreeCongr (by omega) _ _ _ _
          (Fin.ext (by simp only [rHi, QRegister.block_apply_val]; omega)) hDisjComp hDisj₂
          fun i _ _ ↦ by simp only [rHi, QRegister.compose_apply, QRegister.block_apply_val]; omega)
      refine ⟨fun g ↦ ?_, ?_⟩
      · have hCnt := congrArg (fun c ↦ c.count g) hCircEq; rw [Circuit.count_onRegister] at hCnt
        simp only [List.take_succ_cons, List.drop_succ_cons, mottonenCascade, Circuit.count_seq,
          Nat.add_assoc, ihCnt g, hCnt]
      · have hEv := congrArg Circuit.eval hCircEq; rw [Circuit.eval_onRegister] at hEv
        dsimp only [rHi] at hEv; simp only [List.take_succ_cons, List.drop_succ_cons,
          mottonenCascade, Circuit.eval_seq, QRegister.embedUnitary_mul, ← mul_assoc, ihEval, hEv]
/-! ## Section 2: General Commutation of `wordPairTreeCircuit` with `qpeMuxUnitary` -/
/-- Updating a bit assignment outside `r.image` leaves `r.extractIndex` unchanged. -/
theorem extractIndex_update_of_not_mem {k n : ℕ} (r : QRegister k n) (t : Wire n)
    (ht : t ∉ r.image) (β : BitAssignment n) (v : ZMod 2) :
    r.extractIndex ((basisBits n).symm (Function.update β t v)) =
      r.extractIndex ((basisBits n).symm β) := by
  apply (basisBits k).injective; funext i
  rw [r.basisBits_extractIndex, r.basisBits_extractIndex]
  have h1 := congrFun ((basisBits n).apply_symm_apply (Function.update β t v)) (r i)
  have h2 := congrFun ((basisBits n).apply_symm_apply β) (r i)
  change basisBits n _ (r i) = _ at h1 h2; rw [h1, h2]
  exact Function.update_of_ne (fun heq ↦ ht ((QRegister.mem_image r t).mpr ⟨i, heq⟩)) v β
/-- `Circuit.CNOT c t` commutes with `r.basisOutcomeProjector m` whenever `t ∉ r.image`. -/
theorem cnot_comm_basisOutcomeProjector_of_not_mem {k n : ℕ} (r : QRegister k n)
    (m : Fin (2 ^ k)) (c t : Wire n) (hct : c ≠ t) (ht : t ∉ r.image) :
    (Circuit.CNOT c t hct).eval.1 * r.basisOutcomeProjector m =
      r.basisOutcomeProjector m * (Circuit.CNOT c t hct).eval.1 := by
  have hvec (j : Fin (2 ^ n)) :
      ((Circuit.CNOT c t hct).eval.1 * r.basisOutcomeProjector m) *ᵥ Pi.single j (1 : ℂ) =
        (r.basisOutcomeProjector m * (Circuit.CNOT c t hct).eval.1) *ᵥ Pi.single j (1 : ℂ) := by
    let β : BitAssignment n := basisBits n j; rw [((basisBits n).symm_apply_apply j).symm,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (Circuit.CNOT c t hct).eval.1 *ᵥ (r.basisOutcomeProjector m *ᵥ
      OuterWeights.SineWindowPrep.ket n β)
      = r.basisOutcomeProjector m *ᵥ
        ((Circuit.CNOT c t hct).evolve (OuterWeights.SineWindowPrep.ket n β))
    rw [OuterWeights.SineWindowPrep.evolve_CNOT_ket];
      dsimp only [OuterWeights.SineWindowPrep.ket, basisState]
    rw [r.basisOutcomeProjector_mulVec_single, r.basisOutcomeProjector_mulVec_single,
      extractIndex_update_of_not_mem r t ht β (β t + β c)]
    by_cases hm : r.extractIndex ((basisBits n).symm β) = m
    · rw [ite_eq_left hm, ite_eq_left hm];
        exact OuterWeights.SineWindowPrep.evolve_CNOT_ket c t hct β
    · rw [ite_eq_right hm, ite_eq_right hm, Matrix.mulVec_zero]
  ext i j; simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hvec j) i
/-- General operator commutation for `wordPairTreeCircuit` from leaf-wire and `CNOT` commutation. -/
theorem wordPairTreeCircuit_comm_of_leaf_and_cnot {n : ℕ} (A : Operator (2 ^ n)) (t : Wire n)
    (hLeaf : ∀ M : Operator 2,
      (QRegister.singleton t).embedMatrix M * A = A * (QRegister.singleton t).embedMatrix M) :
    ∀ (k : ℕ) (rTreeCtrl : QRegister k n) (hdisj : rTreeCtrl.DisjointWires (QRegister.singleton t))
      (_hCnot : ∀ (i : Fin k) (hct : rTreeCtrl i ≠ t),
        (Circuit.CNOT (rTreeCtrl i) t hct).eval.1 * A =
          A * (Circuit.CNOT (rTreeCtrl i) t hct).eval.1) (tr : WordPairTree),
      (wordPairTreeCircuit k rTreeCtrl t hdisj tr).eval.1 * A =
        A * (wordPairTreeCircuit k rTreeCtrl t hdisj tr).eval.1
  | _, _, _, _, .skip | _ + 1, _, _, _, .leaf _ _ _ _ | 0, _, _, _, .branch _ _ =>
      by simp [wordPairTreeCircuit]
  | 0, _, _, _, .leaf _ _ _ _ => by
      dsimp only [wordPairTreeCircuit]; rw [Circuit.eval_onRegister, QRegister.embedUnitary_val]
      exact hLeaf _
  | k + 1, rTreeCtrl, hdisj, hCnot, .branch tP tM => by
      have hMul {X Y : Operator (2 ^ n)} (hX : X * A = A * X) (hY : Y * A = A * Y) :
          (X * Y) * A = A * (X * Y) := by
        rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
      have hLo := hdisj.compose_left (QRegister.block 0 k (by omega))
      have hwTop : rTreeCtrl ⟨k, by omega⟩ ≠ t := hdisj.ne ⟨k, by omega⟩ 0
      have hSub (i : Fin k) (hct : rTreeCtrl.slice 0 k (by omega) i ≠ t) :=
        hCnot ⟨0 + i.val, by omega⟩ hct
      have ihP := wordPairTreeCircuit_comm_of_leaf_and_cnot A t hLeaf k
        (rTreeCtrl.slice 0 k (by omega)) hLo hSub tP
      have ihM := wordPairTreeCircuit_comm_of_leaf_and_cnot A t hLeaf k
        (rTreeCtrl.slice 0 k (by omega)) hLo hSub tM
      have hc := hCnot ⟨k, by omega⟩ hwTop
      dsimp only [wordPairTreeCircuit, Circuit.sequence]
      simp only [Circuit.eval_seq, Circuit.eval_identity, one_mul]
      exact hMul (hMul (hMul hc ihM) hc) ihP
/-- General commutation of `wordPairTreeCircuit` with `WalkLoop.qpeMuxUnitary`. -/
theorem wordPairTreeCircuit_comm_qpeMuxUnitary {bCtrl wWalk k n : ℕ}
    (rCtrlMux : QRegister bCtrl n) (rTgtMux : QRegister wWalk n)
    (hMuxDisj : rCtrlMux.DisjointWires rTgtMux) (rTreeCtrl : QRegister k n) (t : Wire n)
    (hTreeDisj : rTreeCtrl.DisjointWires (QRegister.singleton t))
    (htCtrl : t ∉ rCtrlMux.image) (htTgt : t ∉ rTgtMux.image)
    (hCtrlDisj : rTreeCtrl.DisjointWires rTgtMux)
    (tr : WordPairTree) (F : Fin (2 ^ bCtrl) → Unitary (2 ^ wWalk)) :
    (rCtrlMux.concat rTgtMux hMuxDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) *
        (wordPairTreeCircuit k rTreeCtrl t hTreeDisj tr).eval =
      (wordPairTreeCircuit k rTreeCtrl t hTreeDisj tr).eval *
        (rCtrlMux.concat rTgtMux hMuxDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) := by
  have hSingCtrl : (QRegister.singleton t).DisjointWires rCtrlMux := QRegister.disjoint_iff.mpr
    fun i j hij ↦ by fin_cases i; exact htCtrl ((QRegister.mem_image _ t).mpr ⟨j, hij.symm⟩)
  have hSingTgt : (QRegister.singleton t).DisjointWires rTgtMux := QRegister.disjoint_iff.mpr
    fun i j hij ↦ by fin_cases i; exact htTgt ((QRegister.mem_image _ t).mpr ⟨j, hij.symm⟩)
  apply Subtype.ext; change ((rCtrlMux.concat rTgtMux hMuxDisj).embedUnitary
      (QubitisedWalk.qpeMuxUnitary F)).1 * (wordPairTreeCircuit k rTreeCtrl t hTreeDisj tr).eval.1 =
    (wordPairTreeCircuit k rTreeCtrl t hTreeDisj tr).eval.1 *
      ((rCtrlMux.concat rTgtMux hMuxDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F)).1
  rw [QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val,
    QubitisedWalk.embedMatrix_qpeMuxMatrix,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have hProj := wordPairTreeCircuit_comm_of_leaf_and_cnot (rCtrlMux.basisOutcomeProjector m) t
    (fun M ↦ QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ rCtrlMux hSingCtrl M m)
    k rTreeCtrl hTreeDisj
    (fun i hct ↦ cnot_comm_basisOutcomeProjector_of_not_mem rCtrlMux m (rTreeCtrl i) t hct htCtrl)
    tr
  have hCnotTgt (i : Fin k) (hct : rTreeCtrl i ≠ t) :
      (Circuit.CNOT (rTreeCtrl i) t hct).eval.1 * rTgtMux.embedMatrix (F m).1 =
        rTgtMux.embedMatrix (F m).1 * (Circuit.CNOT (rTreeCtrl i) t hct).eval.1 := by
    have hPair : (QRegister.pair (rTreeCtrl i) t hct).DisjointWires rTgtMux := by
      rw [QRegister.disjoint_iff]; intro a j hij; fin_cases a
      · exact hCtrlDisj.ne i j hij
      · exact htTgt ((QRegister.mem_image rTgtMux t).mpr ⟨j, hij.symm⟩)
    dsimp only [Circuit.CNOT, Circuit.eval]; rw [QRegister.embedUnitary_val]
    exact (QRegister.pair _ _ hct).embedMatrix_comm_of_disjoint rTgtMux hPair _ (F m).1
  have hTgt := wordPairTreeCircuit_comm_of_leaf_and_cnot (rTgtMux.embedMatrix (F m).1) t
    (fun M ↦ (QRegister.singleton t).embedMatrix_comm_of_disjoint rTgtMux hSingTgt M (F m).1)
    k rTreeCtrl hTreeDisj hCnotTgt tr
  rw [Matrix.mul_assoc, ← hTgt, ← Matrix.mul_assoc, ← hProj, Matrix.mul_assoc]
/-- Relocated `mottonenCascade (q + 1) 1` bond-wire layer commutes with `WalkLoop.qpeMuxUnitary`. -/
theorem mottonenCascade_one_comm_qpeMuxUnitary {bCtrl wWalk q n : ℕ}
    (rCtrlMux : QRegister bCtrl n) (rTgtMux : QRegister wWalk n)
    (hMuxDisj : rCtrlMux.DisjointWires rTgtMux) (rPlace : QRegister (q + 1) n)
    (htCtrl : rPlace ⟨0, by omega⟩ ∉ rCtrlMux.image) (htTgt : rPlace ⟨0, by omega⟩ ∉ rTgtMux.image)
    (hCtrlDisj : (rPlace.compose (QRegister.block 1 q (by omega))).DisjointWires rTgtMux)
    (trs : List WordPairTree) (F : Fin (2 ^ bCtrl) → Unitary (2 ^ wWalk)) :
    (rCtrlMux.concat rTgtMux hMuxDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) *
        rPlace.embedUnitary (mottonenCascade (q + 1) 1 (by omega) trs).eval =
      rPlace.embedUnitary (mottonenCascade (q + 1) 1 (by omega) trs).eval *
        (rCtrlMux.concat rTgtMux hMuxDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) := by
  cases trs with
  | nil => simp [mottonenCascade]
  | cons tr rest =>
      have hDisj0 : (QRegister.block 1 q (by omega) : QRegister q (q + 1)).DisjointWires
          (QRegister.singleton ⟨0, by omega⟩) := by
        rw [QRegister.disjoint_iff]; intro i j hij; have hv := congrArg Fin.val hij
        simp only [QRegister.block_apply_val, QRegister.singleton_apply] at hv; omega
      have hDisjComp : (rPlace.compose (QRegister.block 1 q (by omega))).DisjointWires
          (QRegister.singleton (rPlace ⟨0, by omega⟩)) := by
        rw [QRegister.disjoint_iff]; intro i j hij; have hv := congrArg Fin.val
          (rPlace.wires.injective hij)
        simp only [QRegister.block_apply_val] at hv; omega
      have hOn := wordPairTreeCircuit_onRegister rPlace q
        (QRegister.block 1 q (by omega)) ⟨0, by omega⟩ hDisj0 hDisjComp tr
      have hEval : rPlace.embedUnitary (mottonenCascade (q + 1) 1 (by omega) (tr :: rest)).eval =
          (wordPairTreeCircuit q (rPlace.compose (QRegister.block 1 q (by omega)))
            (rPlace ⟨0, by omega⟩) hDisjComp tr).eval := by
        dsimp only [mottonenCascade]
        rw [Circuit.eval_seq, Circuit.eval_identity, one_mul, ← Circuit.eval_onRegister]
        exact congrArg Circuit.eval hOn
      rw [hEval]; exact wordPairTreeCircuit_comm_qpeMuxUnitary rCtrlMux rTgtMux hMuxDisj
        (rPlace.compose (QRegister.block 1 q (by omega))) (rPlace ⟨0, by omega⟩) hDisjComp
        htCtrl htTgt hCtrlDisj tr F
/-! ## Section 3: `TwoGearBondDeferSpec` & Zero-Ancilla Constructor -/
/-- Disjointness of low dirty QPE wires `0 .. nDirtyLo - 1` and high QPE wires `mLow .. 15`. -/
theorem rDirtyLo_disjoint_rHiInQPE16 (mLow nDirtyLo : ℕ) (hmLow16 : mLow ≤ 16)
    (hDirty : nDirtyLo ≤ mLow) :
    (QRegister.block 0 nDirtyLo (by omega) : QRegister nDirtyLo 16).DisjointWires
      (rHiInQPE16 mLow hmLow16) := QRegister.disjoint_iff.mpr fun i _ hij ↦ by
  have hi := i.isLt; have hv := congrArg Fin.val hij
  simp only [rHiInQPE16, QRegister.block_apply_val] at hv; omega
/-- Pre-`StageA` high-gear QPE register `(0 .. nDirtyLo - 1) ++ (mLow .. 15)`. -/
abbrev rWinHiDeferInQPE (mLow nDirtyLo : ℕ) (hmLow16 : mLow ≤ 16) (hDirty : nDirtyLo ≤ mLow) :
    QRegister (nDirtyLo + (16 - mLow)) 16 :=
  (QRegister.block 0 nDirtyLo (by omega)).concat (rHiInQPE16 mLow hmLow16)
    (rDirtyLo_disjoint_rHiInQPE16 mLow nDirtyLo hmLow16 hDirty)
/-- Bond + high-gear `(16 - mLow + 1)`-wire QPE register `mLow - 1 .. 15` inside `16`-bit QPE. -/
abbrev rBondHiInQPE16 (mLow : ℕ) (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) :
    QRegister (16 - mLow + 1) 16 := QRegister.block (mLow - 1) (16 - mLow + 1) (by omega)
/-- Certified bond-wire deferred Two-Gear sine-window split refining `TwoGearWindowSpec`. -/
structure TwoGearBondDeferSpec (M mLow nDirtyLo : ℕ) where
  /-- Underlying certified Two-Gear window specification (`uIdeal`, `cWinHi`, `cWinLo`, `δWin`). -/
  base : TwoGearWindowSpec M mLow nDirtyLo
  /-- Pre-`StageA` high-gear circuit leaving `nDirtyLo .. mLow - 1` untouched. -/
  cHiPre : Circuit (nDirtyLo + (16 - mLow))
  /-- Deferred bond-wire layer on `mLow - 1 .. 15`, executed at the start of Part 2. -/
  cHiBond : Circuit (16 - mLow + 1)
  /-- `cHiPre` is Toffoli-free. -/
  count_pre_toff : cHiPre.count .TOFF = 0
  /-- `cHiBond` is Toffoli-free. -/
  count_bond_toff : cHiBond.count .TOFF = 0
  /-- Splitting `base.cWinHi` into `cHiPre` and `cHiBond` adds zero extra `T` gates. -/
  count_split_t : cHiPre.count .T + cHiBond.count .T = base.cWinHi.count .T
  /-- `cHiBond` after `cHiPre` evaluates to `base.cWinHi` on the `16`-qubit QPE register. -/
  eval_split : (rBondHiInQPE16 mLow (by have := base.hmLow2; omega)
        (by have := base.hmLow14; omega)).embedUnitary cHiBond.eval *
      (rWinHiDeferInQPE mLow nDirtyLo (by have := base.hmLow14; omega)
        (by have := base.hDirty; omega)).embedUnitary cHiPre.eval =
    (rWinHiInQPE mLow nDirtyLo (by have := base.hmLow2; omega)
      (by have := base.hmLow14; omega) base.hDirty).embedUnitary base.cWinHi.eval
  /-- `cHiBond` commutes with any `(16 - mLow)`-controlled `WalkLoop.qpeMuxUnitary` on `StageA`. -/
  comm_mux : ∀ (mOut mMid : ℕ)
      (F : Fin (2 ^ (16 - mLow)) → Unitary (2 ^ walkCatWidth 11 mOut mMid)),
    let rBond := (rQPEInAct 16 11 mOut mMid).compose
      (rBondHiInQPE16 mLow (by have := base.hmLow2; omega) (by have := base.hmLow14; omega))
    let uMux := (rCombHiInAct mOut mMid mLow (by have := base.hmLow14; omega)).embedUnitary
      (QubitisedWalk.qpeMuxUnitary F)
    uMux * rBond.embedUnitary cHiBond.eval = rBond.embedUnitary cHiBond.eval * uMux
/-- Construct a zero-ancilla `TwoGearBondDeferSpec d.M d.mLow 0` from verified `d`. -/
noncomputable def mkTwoGearBondDeferSpec_zeroAnc (d : TwoGearRegimeData)
    (hok : checkTwoGearRegime d = true)
    (hDlo : 2 ^ (16 - d.mLow - 1) ≤ (d.M + 1) / 2 ^ d.mLow - 1) :
    TwoGearBondDeferSpec d.M d.mLow 0 :=
  let base := mkTwoGearWindowSpec_zeroAnc d hok hDlo; let q := 16 - d.mLow
  let hSplit := mottonenCascade_split q q le_rfl d.hiTrees
  let cPreRaw := mottonenCascade q q le_rfl (d.hiTrees.take q)
  let cHiPre : Circuit (0 + q) := cPreRaw.onRegister (QRegister.block 0 q le_rfl)
  let cHiBond : Circuit (q + 1) := mottonenCascade (q + 1) 1 (by omega) (d.hiTrees.drop q)
  have hCnt {dg : ℕ} (g : PrimitiveGate dg) :
      cHiPre.count g + cHiBond.count g = base.cWinHi.count g := by
    dsimp only [cHiPre, cPreRaw, cHiBond, base, mkTwoGearWindowSpec_zeroAnc, twoGearZeroAncHi, q]
    rw [Circuit.count_onRegister, Circuit.count_onRegister]; exact hSplit.1 g
  have hToffSplit := hCnt .TOFF; have hToff0 := base.count_hi_toff
  { base, cHiPre, cHiBond, count_pre_toff := by omega, count_bond_toff := by omega
    count_split_t := hCnt .T
    eval_split := by
      have hm2 := base.hmLow2; have hm14 := base.hmLow14
      have hRegPre : (rWinHiDeferInQPE d.mLow 0 (by omega) (Nat.zero_le _)).compose
            (QRegister.block 0 q le_rfl) = (rBondHiInQPE16 d.mLow (by omega) (by omega)).compose
              (QRegister.block 1 q (by omega)) := by
        ext i; have hIdx : QRegister.block 0 q le_rfl i = Fin.natAdd 0 i :=
          Fin.ext (by simp)
        simp only [rWinHiDeferInQPE, rBondHiInQPE16, rHiInQPE16, QRegister.compose_apply, hIdx,
          QRegister.concat_apply_right, QRegister.block_apply_val]; omega
      have hRegFull : (rWinHiInQPE d.mLow 0 (by omega) (by omega) base.hDirty).compose
            (QRegister.block 0 (q + 1) le_rfl) = rBondHiInQPE16 d.mLow (by omega) (by omega) := by
        ext i; have hIdx : QRegister.block 0 (q + 1) le_rfl i = Fin.natAdd 0 i :=
          Fin.ext (by simp)
        simp only [rWinHiInQPE, rBondHiInQPE16, QRegister.compose_apply, hIdx, q,
          QRegister.concat_apply_right, QRegister.block_apply_val]
      dsimp only [cHiPre, cPreRaw, cHiBond, base, mkTwoGearWindowSpec_zeroAnc, twoGearZeroAncHi, q]
      rw [Circuit.eval_onRegister, Circuit.eval_onRegister, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose, hRegPre, hRegFull, QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_mul, hSplit.2]
    comm_mux := fun mOut mMid F ↦ by
      have hm2 := base.hmLow2; have hm14 := base.hmLow14
      let rQPE := rQPEInAct 16 11 mOut mMid; let rTgtMux := rWalkCatInAct 16 11 mOut mMid
      let rCtrlMux := rQPE.compose (rHiInQPE16 d.mLow (by omega))
      let rPlace := rQPE.compose (rBondHiInQPE16 d.mLow (by omega) (by omega))
      have htCtrl : rPlace ⟨0, by omega⟩ ∉ rCtrlMux.image := fun hmem ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image rCtrlMux _).mp hmem; have hv := congrArg Fin.val hj
        simp only [rCtrlMux, rPlace, rQPE, rQPEInAct, rHiInQPE16, rBondHiInQPE16,
          QRegister.compose_apply, QRegister.block_apply_val] at hv; omega
      have htTgt : rPlace ⟨0, by omega⟩ ∉ rTgtMux.image := fun hmem ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image rTgtMux _).mp hmem
        have hjlt := j.isLt; have hv := congrArg Fin.val hj
        simp only [rTgtMux, rPlace, rQPE, rWalkCatInAct, rQPEInAct, rBondHiInQPE16,
          QRegister.compose_apply, QRegister.block_apply_val] at hv; omega
      exact mottonenCascade_one_comm_qpeMuxUnitary rCtrlMux rTgtMux
        (rHiInAct_disjoint_rWalkCatInAct mOut mMid d.mLow (by omega)) rPlace htCtrl htTgt
        (QubitisedWalk.disjointWires_compose_left (QubitisedWalk.disjointWires_compose_left
          (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid))) (d.hiTrees.drop q) F }
/-! ## Section 4: Flexible `sUbA ≤ sRem + (mLow - nDirtyLo)` Relocation (`+1` Clean Wire) -/
/-- Extended clean-zero register (`rFullZeroLocB` + `nDirtyLo .. mLow - 1`) for Part 1. -/
abbrev rExtZeroDeferLocB (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hmLow14 : mLow ≤ 14) (hDirty : nDirtyLo ≤ mLow) :
    QRegister ((scrAncillas 16 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem +
      (ko + km)) + (mLow + 1 - 1 - nDirtyLo)) (combQubitsB wOuter wInner2 ko km sRem) :=
  rExtZeroLocB wOuter wInner2 ko km (mLow +
    1) nDirtyLo sRem hkOut hkMid (by omega) (by omega) hDirty
section LocalSuper
variable {Var : Type} (wOuter wInner2 ko km M mLow nDirtyLo sRem sUbA : ℕ)
  (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
end LocalSuper
section SuperTop
variable {Var : Type} {n : ℕ} (wOuter wInner2 ko km M mLow nDirtyLo sRem sUbA : ℕ)
  (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15)
  (hDirty : nDirtyLo ≤ mLow - 1) (hsUbA : sUbA ≤ sRem + (mLow - nDirtyLo))
end SuperTop
section TurnkeySuperDefs
variable {Var : Type} {n : ℕ} (wOuter wInner2 ko km M mLow nDirtyLo sRem sUbA : ℕ) (hkOut : ko ≤
  wOuter)
  (hkMid : km ≤ wInner2) (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1)
  (hsUbA : sUbA ≤ sRem + (mLow - nDirtyLo)) (v : Var) (w : TwoGearBondDeferSpec M mLow nDirtyLo)
  (pSuperA : DynamicCircuit Var (combQubitsAt (16 - mLow) wOuter wInner2 ko km 0 sUbA))
  (pRefl2B : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem))
  (rSys : QRegister systemQubits_local n) (rAnc :
    QRegister (combAncillasB wOuter wInner2 ko km sRem) n)
end TurnkeySuperDefs
section SingleStep
variable {Var : Type} (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
  (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (v : Var)
end SingleStep
section SingleDefs
variable {Var : Type} {n : ℕ} (wOuter wInner2 ko km M mLow nDirtyLo sRem : ℕ) (hkOut : ko ≤ wOuter)
  (hkMid : km ≤ wInner2) (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15) (hDirty : nDirtyLo ≤ mLow - 1)
  (v : Var)
end SingleDefs
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBondDefer
end
