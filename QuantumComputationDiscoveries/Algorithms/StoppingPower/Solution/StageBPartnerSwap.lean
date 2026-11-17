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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.StageAConjHStream

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
attribute [-instance] Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instGroupUnitaryFast_Pack (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_Pack (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _

noncomputable section SlimStageBOuterDepsC1
set_option maxSynthPendingDepth 3
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency false
section SharedScope
attribute [-instance] ModWrapCoarse8PureMomentum.modWrapNeZeroPow2
attribute [-instance] PosSlots24BranchConcrete.instNeZeroTwoPow
attribute [-instance] PosSlots24PartnerMux288.instNeZeroTwoPowPartnerMux
attribute [-instance] DyadicQft64WalkCircuit288.instNeZeroTwoPowQft288
attribute [-instance] HoistedSwapSelectBridge.instNeZeroTwoPowHoisted
attribute [-instance] PosSlots24CompactHead123.instNeZeroTwoPowHead123
attribute [-instance] PosSlots24CompactPhase288.instNeZeroTwoPowMid254
attribute [-instance] SinglePassNuclearTwist288.instNeZeroTwoPowSinglePass
attribute [-instance] MomSlots35Slot3ProjNuclear.instNeZeroTwoPowSlot3
attribute [-instance] ZeroAncillaUSP.instNeZeroTwoPowUSP
attribute [-instance] PosSlots24PartnerMuxZeroT123.instNeZeroTwoPowZeroT123
attribute [-instance] PosSlots24PartnerMuxZeroT123.instNeZeroTwoPowPartnerMuxZeroT
attribute [-instance] BiGqspSegmentSpine.instNeZeroTwoPowSpine
attribute [-instance] OraAndPrepBundle.instNeZeroTwoPowOra
attribute [-instance] CoinDispatchedBarrel288.instNeZeroTwoPowCoinBarrel
attribute [-instance] CoinDispatchedBarrel288.instNeZeroCorePlusBarrel
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPowHoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow48HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow3948HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow3951HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4031HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4034HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4066HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4067HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4109HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4112HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4121HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4144HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4145HoistedStitch
attribute [-instance] FullSysHoistedSelectStitch.instNeZeroTwoPow4199HoistedStitch
attribute [-instance] SegmentAndTopClosure.instNeZeroTwoPowClosure
attribute [-instance] PolymorphicTopClosure.instNeZeroTwoPowPolyClosure
attribute [-instance] GeneralBetaAndAlphaTopEndpoint.instNeZeroTwoPowGeneral
attribute [-instance] ProjZ512QftAndTwist288.instNeZeroTwoPowVepClosure
attribute [-instance] ProjZ512QftAndTwist288.instNeZeroTwoPowVepTop
attribute [-instance] CoherentEndpoint.instNeZeroTwoPowCoherent80
attribute [-instance] PosPostPrep80MergedVep.instNeZeroTwoPowPosPost80
attribute [-instance] PosSlots24Semantic80Physics.instNeZeroTwoPowSem80
attribute [-instance] WindowedSlot2MulKick288.instNeZeroTwoPowWin
attribute [-instance] PosHeadRev18CacheAux.instNeZeroTwoPowHeadRev18
attribute [-instance] PosHeadMod4_15476.instNeZeroTwoPowHeadMod4
local instance (priority := 1000000) instNeZeroAux0c1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority :=
  1000000) instGroupUnitaryFast_SlimStageBOuterDepsC1 (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_SlimStageBOuterDepsC1 (D : ℕ) : Semigroup (Operator.Unitary D)
  :=
  MulMemClass.toSemigroup _
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open MeasureBranchHadamardSem (ket eval_seq_mulVec ket_H ket_X ket_CNOT matrix_ext_ket)
open Operator QProg Matrix Real
open scoped Matrix BigOperators
namespace BoothOpt_02_Cached64x4TrueSwapEngine
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open OctahedralOrbit hiding ket eval_seq_mulVec ket_H ket_X ket_CNOT ket_TOFF matrix_ext_ket
  ket_projector_zero
open MeasureBranchHadamardSem (bitSign bit_cases)
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open AnchorSwap0Split133 MultiBankWStateRouter
open StageADeconstrCore (selDataInAct concat_compose_selDataInAct)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens xor18 basisBits_xor18)
open ElecHadTrueSwapLocalCompClosure (uLensLoad)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (eval_H_mul_self)
open PureCnotLensLoadAndZeroHypTrueSwap (eval_H_comm embedUnitary_uLensLoad_mulVec_single)
open FullConcrete7StepAndTrueSwapSelect
  (cHadamardPrefix uHadamardAll cHadamardAll count_cHadamardAll_toff count_cHadamardAll_t
  eval_cHadamardAll)
open ElecHadTrueSwapHCompClosure (uWriteSub eval_cHadamardAll_compose)
open ZeroHypSlot0CommAndHMidClosure
  (P_slot0 P_slot0_eq_diagonal embedUnitary_diagSignUnitary_eq_diagonal)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
/-! `CliffProg M` predicate certifying all target wires have index `≥ base`. -/
def CliffWritesAbove {M : ℕ} (base : ℕ) : CliffProg M → Prop
  | .nil => True
  | .x q => base ≤ q.val
  | .cnot _ t _ => base ≤ t.val
  | .seq c₁ c₂ => CliffWritesAbove base c₁ ∧ CliffWritesAbove base c₂
theorem CliffWritesAbove.eval_lt {M : ℕ} {base : ℕ} :
    ∀ {c : CliffProg M}, CliffWritesAbove base c →
      ∀ (γ : BitAssignment M) (idx : Wire M), idx.val < base → c.eval γ idx = γ idx
  | .nil, _, _, _, _ => rfl
  | .x _, hq, _, _, hlt => Function.update_of_ne (wire_ne_of_lt (lt_of_lt_of_le hlt hq)) _ _
  | .cnot _ _ _, ht, _, _, hlt => Function.update_of_ne (wire_ne_of_lt (lt_of_lt_of_le hlt ht)) _ _
  | .seq c₁ _, ⟨h₁, h₂⟩, γ, idx, hlt =>
      (h₂.eval_lt (c₁.eval γ) idx hlt).trans (h₁.eval_lt γ idx hlt)
/-- `6 + 2` binary radix decomposition of an `8`-bit value (`v = v % 64 + 64 * (v / 64)`). -/
theorem bitsVal_split_6_2 (b : Fin 8 → ZMod 2) : bitsVal b =
    bitsVal (fun j : Fin 6 ↦ b ⟨j.val, by omega⟩) +
    64 * bitsVal (fun j : Fin 2 ↦ b ⟨6 + j.val, by omega⟩) := by
  simp only [bitsVal, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  change (b 0).val * 1 + ((b 1).val * 2 + ((b 2).val * 4 + ((b 3).val * 8 + ((b 4).val * 16 +
    ((b 5).val * 32 + ((b 6).val * 64 + ((b 7).val * 128 + 0))))))) = ((b 0).val * 1 + ((b
    1).val * 2 + ((b 2).val * 4 + ((b 3).val * 8 + ((b 4).val * 16 + ((b 5).val * 32 + 0))))))
    + 64 * ((b 6).val * 1 + ((b 7).val * 2 + 0))
  ring
theorem cliffWritesAbove_comm_embedUnitary {M n kAct : ℕ}
    (rAct : QRegister kAct n) (V : Unitary (2 ^ kAct))
    (rComb : QRegister M n) (base : ℕ)
    (hOutNotAct : ∀ idx : Wire M, base ≤ idx.val → rComb idx ∉ Set.range rAct.wires)
    (hCombPres : ∀ (idx : Wire M) (g : Fin (2 ^ n)) (y : Fin (2 ^ kAct)),
      V.1 y (rAct.extractIndex g) ≠ 0 →
      basisBits n (rAct.replaceIndex g y) (rComb idx) = basisBits n g (rComb idx)) :
    ∀ {c : CliffProg M}, CliffWritesAbove base c →
      (c.onRegister rComb).toCircuit.eval * rAct.embedUnitary V =
        rAct.embedUnitary V * (c.onRegister rComb).toCircuit.eval
  | .nil, _ => by
      change 1 * rAct.embedUnitary V = rAct.embedUnitary V * 1
      rw [one_mul, mul_one]
  | .x q, hq =>
      comm_embedUnitary_of_update_outside rAct V (Circuit.X (rComb q)) (rComb q)
        (hOutNotAct q hq) (fun _ ↦ 1) (fun β ↦ ket_X (rComb q) β) (fun _ _ _ ↦ rfl)
  | .cnot ctrl tgt hne, ht =>
      comm_embedUnitary_of_update_outside rAct V
        (Circuit.CNOT (rComb ctrl) (rComb tgt) (rComb.wires.injective.ne hne))
        (rComb tgt) (hOutNotAct tgt ht) (fun β ↦ β (rComb ctrl))
        (fun β ↦ ket_CNOT (rComb ctrl) (rComb tgt) (rComb.wires.injective.ne hne) β)
        (fun g y hnz ↦ hCombPres ctrl g y hnz)
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => by
      have ih₁ := cliffWritesAbove_comm_embedUnitary rAct V rComb base hOutNotAct hCombPres h₁
      have ih₂ := cliffWritesAbove_comm_embedUnitary rAct V rComb base hOutNotAct hCombPres h₂
      change ((c₂.onRegister rComb).toCircuit.eval * (c₁.onRegister rComb).toCircuit.eval) *
        rAct.embedUnitary V = rAct.embedUnitary V * ((c₂.onRegister rComb).toCircuit.eval *
        (c₁.onRegister rComb).toCircuit.eval)
      rw [mul_assoc, ih₁, ← mul_assoc, ih₂, mul_assoc]
theorem neg_one_pow_sum_zmod2 :
    ∀ {k : ℕ} (a : Fin k → ZMod 2),
      ((-1 : ℂ) ^ (∑ i : Fin k, a i).val) = ∏ i : Fin k, ((-1 : ℂ) ^ (a i).val)
  | 0, _ => by simp
  | k + 1, a => by
      rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
          ← TempPhaseProg.neg_one_pow_zmod2_mul, neg_one_pow_sum_zmod2]
theorem ite_decide_eq_one_zmod2 (z : ZMod 2) :
    (if decide (z = 1) then (-1 : ℂ) else 1) = (-1 : ℂ) ^ z.val := by
  rcases bit_cases z with hz | hz <;> simp [hz]
theorem diagSignUnitary_mulVec_ket {n : ℕ} (p : Fin (2 ^ n) → Bool) (β : BitAssignment n) :
    (diagSignUnitary p).1.mulVec (ket β) =
      (if p ((basisBitsEquiv n).symm β) then (-1 : ℂ) else 1) • ket β := by
  let g := (basisBitsEquiv n).symm β
  rw [p2d_ket_eq_single β]
  ext i
  dsimp only [diagSignUnitary]
  rw [Matrix.mulVec_diagonal]
  by_cases hig : i = g <;> simp [hig, g]
theorem embedUnitary_diagSignUnitary {n kAct : ℕ}
    (rAct : QRegister kAct n) (p : Fin (2 ^ kAct) → Bool) :
    rAct.embedUnitary (diagSignUnitary p) = diagSignUnitary (fun g ↦ p (rAct.extractIndex g)) := by
  apply Subtype.ext
  exact embedUnitary_diagSignUnitary_eq_diagonal rAct p
/-- Hadamard wall on the first `k` wires of `r : QRegister K n` (`0 T`, `TOFF = 0`). -/
def cHadRegAux {n K : ℕ} (r : QRegister K n) : ∀ (k : ℕ), k ≤ K → Circuit n
  | 0, _ => .identity
  | k + 1, hk => cHadRegAux r k (by omega) ;;ᶜ Circuit.H (r ⟨k, hk⟩)
/-- Hadamard wall on all `K` wires of `r : QRegister K n` (`0 T`, `TOFF = 0`). -/
def cHadReg {n K : ℕ} (r : QRegister K n) : Circuit n := cHadRegAux r K le_rfl
private theorem cHadRegAux_eq_onRegister {n K : ℕ} (r : QRegister K n) :
    ∀ (k : ℕ) (hk : k ≤ K), cHadRegAux r k hk = (cHadamardPrefix k hk).onRegister r
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cHadRegAux, cHadamardPrefix, Circuit.onRegister, Circuit.H, Circuit.single]
      rw [cHadRegAux_eq_onRegister r k (Nat.le_of_succ_le hk)]
      exact congrArg
        (fun q ↦ (cHadamardPrefix k (Nat.le_of_succ_le hk)).onRegister r ;;ᶜ .gate .H q)
        (QRegister.ext (Function.Embedding.ext fun _ ↦ rfl))
private theorem cHadReg_eq_cHadamardAll {n K : ℕ} (r : QRegister K n) : cHadReg r =
    cHadamardAll r := cHadRegAux_eq_onRegister r K le_rfl
theorem cHadReg_count_toff {n K : ℕ} (r : QRegister K n) : (cHadReg r).count TOFF = 0 := by
  rw [cHadReg_eq_cHadamardAll]
  exact count_cHadamardAll_toff r
theorem cHadReg_count_t {n K : ℕ} (r : QRegister K n) :
    (cHadReg r).count PrimitiveGate.T = 0 := by
  rw [cHadReg_eq_cHadamardAll]
  exact count_cHadamardAll_t r
theorem p2d_RealizesConstCleanUnitary_conj_circuit {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hPH : Pᴴ = P) (c : Circuit n) (d : DynamicCircuit Var n) (U : Unitary (2 ^ n))
    (hd : p2d_RealizesConstCleanUnitary P d U) (hPresC : P * (c.eval.1 * P) = c.eval.1 * P)
    (hPresUC : P * ((U * c.eval).1 * P) = (U * c.eval).1 * P) : p2d_RealizesConstCleanUnitary
    P (.seq (.circuit c) (.seq d (.circuit c))) (c.eval * U * c.eval) := by
  have h1 := p2d_RealizesConstCleanUnitary_seq_proj hPH hPH
    (p2d_RealizesConstCleanUnitary_circuit P c) hd hPresC
  have h2 := p2d_RealizesConstCleanUnitary_seq_proj hPH hPH
    h1 (p2d_RealizesConstCleanUnitary_circuit P c) hPresUC
  exact p2d_RealizesConstCleanUnitary_congr_unitary hPH h2 (by simp [mul_assoc])
theorem embedMatrix_comm_ketPredProj {n k : ℕ} (r : QRegister k n) (M : Operator (2 ^ k))
    (S : BitAssignment n → Prop)
    (hS : ∀ β₁ β₂ : BitAssignment n, (∀ w ∉ Set.range r.wires, β₁ w = β₂ w) → (S β₁ ↔ S β₂)) :
    p2d_ketPredProj S * r.embedMatrix M = r.embedMatrix M * p2d_ketPredProj S := by
  classical
  ext i j
  dsimp only [p2d_ketPredProj]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, QRegister.embedMatrix_apply]
  by_cases henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
  · have hEq := hS (basisBits n i) (basisBits n j) ((r.basisSplit_environment_eq_iff i j).mp henv)
    by_cases hsi : S (basisBits n i)
    · rw [ite_eq_left hsi, ite_eq_left (hEq.mp hsi)]; simp [henv]
    · rw [ite_eq_right hsi, ite_eq_right (mt hEq.mpr hsi)]; simp
  · simp [henv]
theorem cHadReg_preserves_ketPredProj {n K : ℕ} (r : QRegister K n)
    (S : BitAssignment n → Prop) (hS : ∀ β₁ β₂ : BitAssignment n, (∀ w, (∀ t : Fin K, w ≠ r t)
    → β₁ w = β₂ w) → (S β₁ ↔ S β₂)) : p2d_ketPredProj S * (cHadReg r).eval.1 =
    (cHadReg r).eval.1 * p2d_ketPredProj S := by
  rw [cHadReg_eq_cHadamardAll, eval_cHadamardAll, QRegister.embedUnitary_val]
  exact embedMatrix_comm_ketPredProj r (uHadamardAll K).1 S fun β₁ β₂ h ↦
    hS β₁ β₂ fun w hw ↦ h w fun ⟨t, ht⟩ ↦ hw t ht.symm
private theorem singleHad_conj_constPhase_ket {K : ℕ} (q : Wire K) (c : ZMod 2)
    (α : BitAssignment K) : ((Circuit.H q).eval * diagSignUnitary (fun g ↦ decide (c *
    basisBits K g q = 1)) * (Circuit.H q).eval).1.mulVec (ket α) = ket
    (Function.update α q (α q + c)) := by
  let U₁ : Unitary (2 ^ K) := diagSignUnitary (fun g ↦ decide (c * basisBits K g q = 1))
  have hMid : U₁.1.mulVec ((Circuit.H q).eval.1.mulVec (ket α)) =
      (Circuit.H q).eval.1.mulVec (ket (Function.update α q (α q + c))) := by
    rw [ket_H q α, ket_H q (Function.update α q (α q + c)),
        Function.update_idem, Function.update_idem, Function.update_self,
        Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul]
    dsimp only [U₁]
    rw [diagSignUnitary_mulVec_ket, diagSignUnitary_mulVec_ket]
    have hEq0 : basisBits K ((basisBitsEquiv K).symm (Function.update α q 0)) =
        Function.update α q 0 := (basisBitsEquiv K).apply_symm_apply _
    have hEq1 : basisBits K ((basisBitsEquiv K).symm (Function.update α q 1)) =
        Function.update α q 1 := (basisBitsEquiv K).apply_symm_apply _
    simp only [hEq0, hEq1, Function.update_self, mul_zero, mul_one]
    rcases bit_cases (α q) with hq | hq <;> rcases bit_cases c with hc | hc <;>
      simp [hq, hc, bitSign]
  change ((Circuit.H q).eval * U₁ * (Circuit.H q).eval).1.mulVec (ket α) = _
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMid, Matrix.mulVec_mulVec, ← Submonoid.coe_mul,
      BoothOpt_03_CoinBarrelIdxFastTrueSwap.eval_H_mul_self q,
      OneMemClass.coe_one, Matrix.one_mulVec]
private theorem comm_H_diagSign {K : ℕ} (q : Wire K) (p : BitAssignment K → Bool)
    (hp : ∀ (α : BitAssignment K) (v : ZMod 2), p (Function.update α q v) = p α) :
    (Circuit.H q).eval * diagSignUnitary (fun g ↦ p (basisBits K g)) =
      diagSignUnitary (fun g ↦ p (basisBits K g)) * (Circuit.H q).eval := by
  apply Subtype.ext; apply matrix_ext_ket; intro α
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, ket_H q α,
      Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      diagSignUnitary_mulVec_ket, diagSignUnitary_mulVec_ket]
  have hS : basisBits K ((basisBitsEquiv K).symm α) = α := (basisBitsEquiv K).apply_symm_apply _
  have h0 : basisBits K ((basisBitsEquiv K).symm (Function.update α q 0)) =
      Function.update α q 0 := (basisBitsEquiv K).apply_symm_apply _
  have h1 : basisBits K ((basisBitsEquiv K).symm (Function.update α q 1)) =
      Function.update α q 1 := (basisBitsEquiv K).apply_symm_apply _
  rw [hS, h0, h1, hp α 0, hp α 1]
  by_cases hpa : p α <;> simp [hpa, smul_add, smul_smul, mul_comm]
private theorem cHadamardPrefix_eval_comm {K : ℕ} (M : Unitary (2 ^ K)) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (∀ i : Fin k, (Circuit.H ⟨i.val, by omega⟩).eval * M =
        M * (Circuit.H ⟨i.val, by omega⟩).eval) →
      (cHadamardPrefix k hk).eval * M = M * (cHadamardPrefix k hk).eval
  | 0, _, _ => by
      change 1 * M = M * 1
      rw [one_mul, mul_one]
  | k + 1, hk, hM => by
      have ih := cHadamardPrefix_eval_comm M k (Nat.le_of_succ_le hk)
        (fun i ↦ hM ⟨i.val, by omega⟩)
      change ((Circuit.H ⟨k, hk⟩).eval * (cHadamardPrefix k (Nat.le_of_succ_le hk)).eval) * M =
        M * ((Circuit.H ⟨k, hk⟩).eval * (cHadamardPrefix k (Nat.le_of_succ_le hk)).eval)
      rw [mul_assoc, ih, ← mul_assoc, hM ⟨k, Nat.lt_succ_self k⟩, mul_assoc]
private theorem cHadamardPrefix_conj_constPhase_ket {K : ℕ} (c : Fin K → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ K) (γ : BitAssignment K), ((cHadamardPrefix k hk).eval *
    diagSignUnitary (fun x ↦
    decide ((∑ i : Fin k, c ⟨i.val, by omega⟩ * basisBits K x ⟨i.val, by omega⟩) = 1)) *
    (cHadamardPrefix k hk).eval).1.mulVec (ket γ) =
    ket (fun j : Fin K ↦ if j.val < k then γ j + c j else γ j) := by
  intro k
  induction k with
  | zero =>
      intro hk γ
      let U_pref : Unitary (2 ^ K) := diagSignUnitary fun x ↦
        decide ((∑ i : Fin 0, c ⟨i.val, by omega⟩ * basisBits K x ⟨i.val, by omega⟩) = 1)
      have hU0 : U_pref = 1 := by
        apply Subtype.ext; apply matrix_ext_ket; intro α
        rw [diagSignUnitary_mulVec_ket, OneMemClass.coe_one, Matrix.one_mulVec]
        simp
      change ((1 : Unitary (2 ^ K)) * U_pref * 1).1.mulVec (ket γ) = _
      rw [hU0, mul_one, mul_one, OneMemClass.coe_one, Matrix.one_mulVec]
      simp
  | succ k ih =>
      intro hk γ
      let hk' := Nat.le_of_succ_le hk
      let q : Wire K := ⟨k, hk⟩
      let U_pref : Unitary (2 ^ K) := diagSignUnitary fun x ↦
        decide ((∑ i : Fin (k + 1), c ⟨i.val, by omega⟩ * basisBits K x ⟨i.val, by omega⟩) = 1)
      let p_prev : BitAssignment K → Bool := fun α ↦
        decide ((∑ i : Fin k, c ⟨i.val, by omega⟩ * α ⟨i.val, by omega⟩) = 1)
      let p_one : BitAssignment K → Bool := fun α ↦ decide (c q * α q = 1)
      let U_prev : Unitary (2 ^ K) := diagSignUnitary fun x ↦ p_prev (basisBits K x)
      let U_one : Unitary (2 ^ K) := diagSignUnitary fun x ↦ p_one (basisBits K x)
      have hU_split : U_pref = U_one * U_prev := by
        apply Subtype.ext; apply matrix_ext_ket; intro α
        rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        dsimp only [U_pref, U_prev, U_one, p_prev, p_one, q]
        rw [diagSignUnitary_mulVec_ket, diagSignUnitary_mulVec_ket,
            Matrix.mulVec_smul, diagSignUnitary_mulVec_ket, smul_smul]
        have hα : basisBits K ((basisBitsEquiv K).symm α) = α :=
          (basisBitsEquiv K).apply_symm_apply _
        simp only [hα, ite_decide_eq_one_zmod2]
        refine congrArg (· • ket α) ?_
        rw [Fin.sum_univ_castSucc]
        dsimp only [Fin.val_castSucc, Fin.val_last]
        rw [← TempPhaseProg.neg_one_pow_zmod2_mul, mul_comm]
      have hCommH_Had : (cHadamardPrefix k hk').eval * (Circuit.H q).eval =
          (Circuit.H q).eval * (cHadamardPrefix k hk').eval :=
        cHadamardPrefix_eval_comm (Circuit.H q).eval k hk'
          (fun i ↦ eval_H_comm _ _ (Fin.ne_of_val_ne (by dsimp [q]; omega)))
      have hCommH_Prev : (Circuit.H q).eval * U_prev = U_prev * (Circuit.H q).eval :=
        comm_H_diagSign q p_prev fun α v ↦
          congrArg (fun s ↦ decide (s = 1)) (Finset.sum_congr rfl fun i _ ↦ by
            rw [Function.update_of_ne (Fin.ne_of_val_ne (by dsimp [q]; omega))])
      have hCommHad_One : (cHadamardPrefix k hk').eval * U_one =
          U_one * (cHadamardPrefix k hk').eval :=
        cHadamardPrefix_eval_comm U_one k hk' fun i ↦
          comm_H_diagSign _ p_one fun α v ↦ by
            dsimp only [p_one]
            rw [Function.update_of_ne (Fin.ne_of_val_ne (by dsimp [q]; omega))]
      have hFactor :
          (cHadamardPrefix (k + 1) hk).eval * U_pref * (cHadamardPrefix (k + 1) hk).eval =
            ((Circuit.H q).eval * U_one * (Circuit.H q).eval) *
              ((cHadamardPrefix k hk').eval * U_prev * (cHadamardPrefix k hk').eval) := by
        change ((Circuit.H q).eval * (cHadamardPrefix k hk').eval) * U_pref *
            ((Circuit.H q).eval * (cHadamardPrefix k hk').eval) = _
        rw [hU_split]
        calc
          ((Circuit.H q).eval * (cHadamardPrefix k hk').eval) * (U_one * U_prev) *
              ((Circuit.H q).eval * (cHadamardPrefix k hk').eval)
            = (Circuit.H q).eval * ((cHadamardPrefix k hk').eval * U_one) *
                U_prev * ((Circuit.H q).eval * (cHadamardPrefix k hk').eval) := by
                simp only [mul_assoc]
          _ = (Circuit.H q).eval * U_one * (cHadamardPrefix k hk').eval *
                (U_prev * (Circuit.H q).eval) * (cHadamardPrefix k hk').eval := by
                rw [hCommHad_One]
                simp only [mul_assoc]
          _ = (Circuit.H q).eval * U_one *
                ((cHadamardPrefix k hk').eval * (Circuit.H q).eval) * U_prev *
                (cHadamardPrefix k hk').eval := by
                rw [← hCommH_Prev]
                simp only [mul_assoc]
          _ = ((Circuit.H q).eval * U_one * (Circuit.H q).eval) *
                ((cHadamardPrefix k hk').eval * U_prev * (cHadamardPrefix k hk').eval) := by
                rw [hCommH_Had]
                simp only [mul_assoc]
      change ((cHadamardPrefix (k + 1) hk).eval * U_pref *
        (cHadamardPrefix (k + 1) hk).eval).1.mulVec (ket γ) = _
      rw [hFactor, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      dsimp only [U_one, U_prev, p_one, p_prev]
      rw [ih hk' γ, singleHad_conj_constPhase_ket q (c q)]
      refine congrArg ket (funext fun j ↦ ?_)
      by_cases hj : j = q
      · rw [hj, Function.update_self]
        dsimp only [q]
        rw [ite_eq_right (Nat.lt_irrefl k), ite_eq_left (Nat.lt_succ_self k)]
      · rw [Function.update_of_ne hj]
        have hjv : j.val ≠ k := Fin.val_ne_of_ne hj
        by_cases hlt : j.val < k
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
set_option exponentiation.threshold 32 in
theorem cHadReg_meas_conj_phase_eq_uLensLoad {n kData : ℕ} (rData : QRegister kData n)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) (L : Slot18Lens kData)
    (bL : Fin 18 → BitAssignment n → ZMod 2) (hbL : ∀ (j : Fin 18) (α₁ α₂ : BitAssignment n),
    (∀ w, (∀ t : Fin 18, w ≠ rMeas t) → α₁ w = α₂ w) → bL j α₁ = bL j α₂) (hTbl : ∀ (g : Fin
    (2 ^ n)) (j : Fin 18), basisBits 18 (L.tbl (rData.extractIndex g)) j = bL j (basisBits n
    g)) : (cHadReg rMeas).eval * diagSignUnitary (fun g ↦ decide ((∑ j : Fin 18, bL j
    (basisBits n g) * basisBits n g (rMeas j)) = 1)) * (cHadReg rMeas).eval =
    (rData.concat rMeas hDM).embedUnitary (uLensLoad L) := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  let g := (basisBitsEquiv n).symm β
  have hKetG : ket β = Pi.single g 1 := rfl
  let t := L.tbl (rData.extractIndex g)
  let U_kick : Unitary (2 ^ n) := diagSignUnitary fun g' ↦
    decide ((∑ j : Fin 18, bL j (basisBits n g') * basisBits n g' (rMeas j)) = 1)
  let U_loc : Unitary (2 ^ 18) := diagSignUnitary fun y ↦
    decide ((∑ j : Fin 18, basisBits 18 t j * basisBits 18 y j) = 1)
  have hHad : (cHadReg rMeas).eval.1 = rMeas.embedMatrix (uHadamardAll 18).1 := by
    rw [cHadReg_eq_cHadamardAll, eval_cHadamardAll, QRegister.embedUnitary_val]
  have hStep1 (ψ : Fin (2 ^ 18) → ℂ) :
      U_kick.1.mulVec (rMeas.tensorState ψ (Pi.single (rMeas.basisSplitEquiv g).2 1)) =
        rMeas.tensorState (U_loc.1.mulVec ψ) (Pi.single (rMeas.basisSplitEquiv g).2 1) := by
    ext i
    set_option backward.isDefEq.respectTransparency true in
    have hGoal : (U_kick.1.mulVec (rMeas.tensorState ψ (Pi.single (rMeas.basisSplitEquiv g).2 1))) i
      =
        rMeas.tensorState (U_loc.1.mulVec ψ) (Pi.single (rMeas.basisSplitEquiv g).2 1) i := by
      dsimp only [U_kick, U_loc, diagSignUnitary]
      rw [Matrix.mulVec_diagonal]
      dsimp only [QRegister.tensorState]
      rw [Matrix.mulVec_diagonal, mul_assoc]
      by_cases henv : (rMeas.basisSplitEquiv i).2 = (rMeas.basisSplitEquiv g).2
      · have hOut := (rMeas.basisSplit_environment_eq_iff i g).mp henv
        have hSum : (∑ j : Fin 18, bL j (basisBits n i) * basisBits n i (rMeas j)) =
            ∑ j : Fin 18, basisBits 18 t j * basisBits 18 (rMeas.extractIndex i) j :=
          Finset.sum_congr rfl fun j _ ↦ by
            rw [hbL j _ _ (fun w hw ↦ hOut w fun ⟨m, hm⟩ ↦ hw m hm.symm),
                ← hTbl g j, QRegister.basisBits_extractIndex]
        have hDec : decide ((∑ j : Fin 18, bL j (basisBits n i) * basisBits n i (rMeas j)) = 1) =
            decide ((∑ j : Fin 18, basisBits 18 t j * basisBits 18 (rMeas.extractIndex i) j) = 1) :=
          decide_eq_decide.mpr (Eq.to_iff (congrArg (· = 1) hSum))
        let env1 : (rMeas.Environment → ZMod 2) → ℂ := Pi.single (rMeas.basisSplitEquiv g).2 1
        exact congrArg (fun b : Bool ↦ (if b = true then (-1 : ℂ) else 1) *
          (ψ (rMeas.extractIndex i) * env1 (rMeas.basisSplitEquiv i).2)) hDec
      · simp [henv]
    exact hGoal
  have hLocKet : ((uHadamardAll 18) * U_loc * (uHadamardAll 18)).1.mulVec
      (Pi.single (rMeas.extractIndex g) 1) =
      Pi.single (xor18 (rMeas.extractIndex g) t) 1 := by
    let γ₀ := basisBits 18 (rMeas.extractIndex g)
    have hγ₀ : (Pi.single (rMeas.extractIndex g) (1 : ℂ) : Fin (2 ^ 18) → ℂ) = ket γ₀ :=
      (congrArg (fun idx ↦
        (Pi.single idx (1 : ℂ) : Fin (2 ^ 18) →
        ℂ)) ((basisBitsEquiv 18).injective ((basisBitsEquiv 18).apply_symm_apply γ₀).symm)).trans
        (p2d_ket_eq_single γ₀).symm
    rw [hγ₀]
    dsimp only [uHadamardAll, U_loc]
    have hConj := cHadamardPrefix_conj_constPhase_ket (basisBits 18 t) 18 le_rfl γ₀
    have hUEq : (diagSignUnitary fun x : Fin (2 ^ 18) ↦
        decide ((∑ i : Fin 18, basisBits 18 t ⟨i.val, by omega⟩ *
          basisBits 18 x ⟨i.val, by omega⟩) = 1)) =
        diagSignUnitary (fun y : Fin (2 ^ 18) ↦
          decide ((∑ j : Fin 18, basisBits 18 t j * basisBits 18 y j) = 1)) :=
      congrArg diagSignUnitary (funext fun _ ↦ rfl)
    rw [hUEq] at hConj
    rw [hConj, p2d_ket_eq_single]
    refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ 18) → ℂ)) ?_
    apply (basisBitsEquiv 18).injective
    funext j
    rw [(basisBitsEquiv 18).apply_symm_apply, ite_eq_left j.isLt]
    change γ₀ j + basisBits 18 t j = basisBits 18 (xor18 (rMeas.extractIndex g) t) j
    rw [basisBits_xor18]
  have hAssoc (v : Fin (2 ^ 18) → ℂ) :
      (uHadamardAll 18).1.mulVec (U_loc.1.mulVec ((uHadamardAll 18).1.mulVec v)) =
        ((uHadamardAll 18) * U_loc * (uHadamardAll 18)).1.mulVec v := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change ((cHadReg rMeas).eval * U_kick * (cHadReg rMeas).eval).1.mulVec (ket β) = _
  rw[hKetG, embedUnitary_uLensLoad_mulVec_single rData rMeas hDM L L.tbl (fun _ ↦ rfl) g,
      Submonoid.coe_mul, Submonoid.coe_mul, hHad, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, rMeas.embedMatrix_mulVec_single_factors, hStep1,
      rMeas.embedMatrix_mulVec_tensorState, hAssoc, hLocKet,
      rMeas.tensorState_single_replaceIndex]
/-- Polymorphic subregister Hadamard conjugation on `p2d_ketPredProj S`: avoids unfolding
  concrete `kSub`. -/
theorem dHadSubConjHole_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kAct kSub : ℕ} [NeZero (2 ^ n)] (rAct : QRegister kAct n)
    (selSub : QRegister kSub kAct) (S : BitAssignment n → Prop) (hS : ∀ β₁ β₂ : BitAssignment
    n, (∀ w ∉ Set.range (rAct.compose selSub).wires, β₁ w = β₂ w) → (S β₁ ↔ S β₂))
    (uLoad : Unitary (2 ^ kAct)) (dLoad : DynamicCircuit Var n) (hdLoad :
    p2d_RealizesConstCleanUnitary (p2d_ketPredProj S) dLoad (rAct.embedUnitary uLoad))
    (hCommLoad : p2d_ketPredProj S * (rAct.embedUnitary uLoad).1 = (rAct.embedUnitary uLoad).1
    * p2d_ketPredProj S) : p2d_RealizesConstCleanUnitary (p2d_ketPredProj S) (.seq (.circuit
    (cHadamardAll (rAct.compose selSub))) (.seq dLoad (.circuit (cHadamardAll (rAct.compose
    selSub))))) (rAct.embedUnitary (uWriteSub selSub uLoad)) := by
  let rH := rAct.compose selSub
  let P := p2d_ketPredProj S
  have hCommHad : P * (cHadamardAll rH).eval.1 = (cHadamardAll rH).eval.1 * P := by
    rw [eval_cHadamardAll, QRegister.embedUnitary_val]
    exact embedMatrix_comm_ketPredProj rH (uHadamardAll kSub).1 S hS
  have hIdem : P * P = P := p2d_ketPredProj_mul_imp (fun _ h ↦ h)
  have hPresC : P * ((cHadamardAll rH).eval.1 * P) = (cHadamardAll rH).eval.1 * P := by
    rw [← mul_assoc, hCommHad, mul_assoc, hIdem]
  have hPresUC : P * (((rAct.embedUnitary uLoad) * (cHadamardAll rH).eval).1 * P) =
      ((rAct.embedUnitary uLoad) * (cHadamardAll rH).eval).1 * P := by
    rw [Submonoid.coe_mul, ← mul_assoc, ← mul_assoc, hCommLoad,
        mul_assoc _ P, hCommHad, mul_assoc, mul_assoc, hIdem, ← mul_assoc]
  refine p2d_RealizesConstCleanUnitary_congr_unitary (p2d_ketPredProj_conjTranspose _)
    (p2d_RealizesConstCleanUnitary_conj_circuit (p2d_ketPredProj_conjTranspose _)
      (cHadamardAll rH) dLoad (rAct.embedUnitary uLoad) hdLoad hPresC hPresUC) ?_
  refine congrArg (fun U : Unitary (2 ^ n) ↦ U.1 * P) ?_
  rw [eval_cHadamardAll_compose rAct selSub, ← rAct.embedUnitary_mul, ← rAct.embedUnitary_mul]
  rfl
/-- Polymorphic commutation of `uLensLoad L` with `p2d_ketPredProj S` for abstract `L :
  Slot18Lens kData`. -/
theorem embedUnitary_uLensLoad_comm_ketPredProj {n kData : ℕ} (rData : QRegister kData n)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) (L : Slot18Lens kData)
    (S : BitAssignment n → Prop) (hSM : ∀ β₁ β₂ : BitAssignment n, (∀ w ∉ Set.range
    rMeas.wires, β₁ w = β₂ w) → (S β₁ ↔ S β₂)) : p2d_ketPredProj S *
    ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1 =
    ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1 * p2d_ketPredProj S := by
  classical
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
  let g := (basisBitsEquiv n).symm β
  let g' := rMeas.replaceIndex g (xor18 (rMeas.extractIndex g) (L.tbl (rData.extractIndex g)))
  have hULKet : ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1.mulVec (ket β) =
      ket (basisBits n g') := by
    rw [p2d_ket_eq_single β,
        embedUnitary_uLensLoad_mulVec_single rData rMeas hDM L L.tbl (fun _ ↦ rfl) g,
        p2d_ket_eq_single]
    exact congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ))
      ((basisBitsEquiv n).symm_apply_apply g').symm
  have hEquiv : S (basisBits n g') ↔ S β :=
    hSM (basisBits n g') β fun w hw ↦ by
      rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
      exact congrFun ((basisBitsEquiv n).apply_symm_apply β) w
  by_cases hβ : S β
  · rw [ite_eq_left hβ, hULKet, p2d_ketPredProj_mul_ket, ite_eq_left (hEquiv.mpr hβ)]
  · rw [ite_eq_right hβ, Matrix.mulVec_zero, hULKet, p2d_ketPredProj_mul_ket,
      ite_eq_right (mt hEquiv.mp hβ)]
theorem rElecSlot_inj {n : ℕ} (rCore : QRegister posCoreWires n)
    {e₁ e₂ : Fin 218} {j₁ j₂ : Fin 18}
    (h : rElecSlot rCore e₁ j₁ = rElecSlot rCore e₂ j₂) : e₁ = e₂ ∧ j₁ = j₂ := by
  simp only [rElecSlot, QRegister.slice_apply] at h
  have hv := congrArg Fin.val (rCore.wires.injective h)
  dsimp only at hv
  have := j₁.isLt; have := j₂.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
/-- `0-T` CNOT fan-in on a single slot `e : Fin 218`, XORing `{j | f j = true ∧ j ≠ j₀}` into
  `j₀`. -/
def cSingleSlotFanInAux {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (e : Fin 218) : ∀ (k : ℕ), k ≤ 18 → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      if h : f ⟨k, hk⟩ = true ∧ (⟨k, hk⟩ : Fin 18) ≠ j₀ then
        cSingleSlotFanInAux f j₀ rCore e k (by omega) ;;ᶜ
        Circuit.CNOT (rElecSlot rCore e ⟨k, hk⟩) (rElecSlot rCore e j₀)
          (fun heq ↦ h.2 (rElecSlot_inj rCore heq).2)
      else
        cSingleSlotFanInAux f j₀ rCore e k (by omega)
/-- `0-T` CNOT fan-in across the first `m ≤ 218` slots of `rCore`. -/
def cSlotParityFanInAux {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) : ∀ (m : ℕ), m ≤ 218 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      cSlotParityFanInAux f j₀ rCore m (by omega) ;;ᶜ
      cSingleSlotFanInAux f j₀ rCore ⟨m, hm⟩ 18 le_rfl
def cSlotParityFanIn {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) : Circuit n :=
  cSlotParityFanInAux f j₀ rCore 218 le_rfl
theorem cSlotParityFanInAux_count {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) :
    ∀ (m : ℕ) (hm : m ≤ 218),
      (cSlotParityFanInAux f j₀ rCore m hm).count TOFF = 0 ∧
      (cSlotParityFanInAux f j₀ rCore m hm).count PrimitiveGate.T = 0
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
      have hSingle : ∀ (k : ℕ) (hk : k ≤ 18),
          (cSingleSlotFanInAux f j₀ rCore ⟨m, hm⟩ k hk).count TOFF = 0 ∧
          (cSingleSlotFanInAux f j₀ rCore ⟨m, hm⟩ k hk).count PrimitiveGate.T = 0 := by
        intro k
        induction k with
        | zero => exact fun _ ↦ ⟨rfl, rfl⟩
        | succ k ih =>
            intro hk
            dsimp only [cSingleSlotFanInAux]
            obtain ⟨h1, h2⟩ := ih (by omega)
            split_ifs <;> simp [Circuit.count, h1, h2]
      dsimp only [cSlotParityFanInAux]
      obtain ⟨h1, h2⟩ := cSlotParityFanInAux_count f j₀ rCore m (by omega)
      obtain ⟨h3, h4⟩ := hSingle 18 le_rfl
      simp [Circuit.count, h1, h2, h3, h4]
/-- Bit assignment after `0-T` CNOT fan-in across the first `m ≤ 218` slots of `rCore`. -/
def fanInBits {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) : ∀ (m : ℕ), m ≤ 218 → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      Function.update (fanInBits f j₀ rCore m (by omega) β) (rElecSlot rCore ⟨m, hm⟩ j₀)
        (β (rElecSlot rCore ⟨m, hm⟩ j₀) +
          ∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then β (rElecSlot rCore ⟨m, hm⟩ j) else 0)
theorem fanInBits_apply_other {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ 218) (w : Wire n),
      (∀ e : Fin m, w ≠ rElecSlot rCore ⟨e.val, by omega⟩ j₀) →
      fanInBits f j₀ rCore m hm β w = β w
  | 0, _, _, _ => rfl
  | m + 1, hm, w, hw => by
      dsimp only [fanInBits]
      rw [Function.update_of_ne (hw ⟨m, Nat.lt_succ_self m⟩)]
      exact fanInBits_apply_other f j₀ rCore β m (by omega) w
        (fun e ↦ hw ⟨e.val, by omega⟩)
theorem fanInBits_apply_slot {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ 218) (e : Fin m),
      fanInBits f j₀ rCore m hm β (rElecSlot rCore ⟨e.val, by omega⟩ j₀) =
        β (rElecSlot rCore ⟨e.val, by omega⟩ j₀) +
          ∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then
            β (rElecSlot rCore ⟨e.val, by omega⟩ j) else 0
  | 0, _, e => Fin.elim0 e
  | m + 1, hm, e => by
      dsimp only [fanInBits]
      by_cases hem : e.val = m
      · have hSlot : (⟨e.val, by omega⟩ : Fin 218) = ⟨m, hm⟩ := Fin.ext hem
        simp only [hSlot, Function.update_self]
      · have hne : rElecSlot rCore ⟨e.val, by omega⟩ j₀ ≠ rElecSlot rCore ⟨m, hm⟩ j₀ :=
          fun heq ↦ hem (congrArg Fin.val (rElecSlot_inj rCore heq).1)
        rw [Function.update_of_ne hne]
        exact fanInBits_apply_slot f j₀ rCore β m (by omega) ⟨e.val, by omega⟩
theorem cSlotParityFanInAux_eval_ket {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) : ∀ (m : ℕ) (hm : m ≤ 218),
    (cSlotParityFanInAux f j₀ rCore m hm).eval.1.mulVec (ket β) = ket
    (fanInBits f j₀ rCore m hm β) := by
  intro m
  induction m with
  | zero =>
      intro hm
      change (1 : Unitary (2 ^ n)).1.mulVec (ket β) = ket β
      rw [OneMemClass.coe_one, Matrix.one_mulVec]
  | succ m ih =>
      intro hm
      let e : Fin 218 := ⟨m, hm⟩
      let β_m := fanInBits f j₀ rCore m (by omega) β
      have hSingle : ∀ (k : ℕ) (hk : k ≤ 18),
          (cSingleSlotFanInAux f j₀ rCore e k hk).eval.1.mulVec (ket β_m) =
            ket (Function.update β_m (rElecSlot rCore e j₀)
              (β_m (rElecSlot rCore e j₀) +
                ∑ j : Fin k, if f ⟨j.val, by omega⟩ = true ∧ (⟨j.val, by omega⟩ : Fin 18) ≠ j₀ then
                  β_m (rElecSlot rCore e ⟨j.val, by omega⟩) else 0)) := by
        intro k
        induction k with
        | zero =>
            intro _
            simp [cSingleSlotFanInAux, Matrix.one_mulVec]
        | succ k ihk =>
            intro hk
            dsimp only [cSingleSlotFanInAux]
            by_cases hc : f ⟨k, hk⟩ = true ∧ (⟨k, hk⟩ : Fin 18) ≠ j₀
            · have hne : rElecSlot rCore e ⟨k, hk⟩ ≠ rElecSlot rCore e j₀ :=
                fun heq ↦ hc.2 (rElecSlot_inj rCore heq).2
              rw [dite_eq_left hc, eval_seq_mulVec, ihk (by omega), ket_CNOT, Function.update_idem,
                  Function.update_self, Function.update_of_ne hne, add_assoc]
              refine congrArg (fun s ↦ ket (Function.update β_m (rElecSlot rCore e j₀)
                (β_m (rElecSlot rCore e j₀) + s))) ?_
              rw [Fin.sum_univ_castSucc]
              dsimp only [Fin.val_castSucc, Fin.val_last]
              rw [ite_eq_left hc]
            · rw [dite_eq_right hc, ihk (by omega)]
              refine congrArg (fun s ↦ ket (Function.update β_m (rElecSlot rCore e j₀)
                (β_m (rElecSlot rCore e j₀) + s))) ?_
              rw [Fin.sum_univ_castSucc]
              dsimp only [Fin.val_castSucc, Fin.val_last]
              rw [ite_eq_right hc, add_zero]
      dsimp only [cSlotParityFanInAux, fanInBits]
      rw [eval_seq_mulVec, ih (by omega), hSingle 18 le_rfl]
      have hPrevNotM : ∀ j : Fin 18, β_m (rElecSlot rCore e j) = β (rElecSlot rCore e j) :=
        fun j ↦ fanInBits_apply_other f j₀ rCore β m (by omega) _ fun e' heq ↦ by
          have hv := congrArg Fin.val (rElecSlot_inj rCore heq).1
          dsimp [e] at hv; omega
      refine congrArg (fun v ↦ ket (Function.update β_m (rElecSlot rCore e j₀) v)) ?_
      rw [hPrevNotM j₀]
      refine congrArg (fun s ↦ β (rElecSlot rCore e j₀) + s) (Finset.sum_congr rfl fun j _ ↦ ?_)
      have hjEq : (⟨j.val, by omega⟩ : Fin 18) = j := Fin.ext rfl
      simp only [hjEq]
      split_ifs with hj
      · exact hPrevNotM j
      · rfl
theorem fanInBits_involutive {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    fanInBits f j₀ rCore 218 le_rfl (fanInBits f j₀ rCore 218 le_rfl β) = β := by
  funext w
  by_cases hex : ∃ e : Fin 218, w = rElecSlot rCore e j₀
  · obtain ⟨e, rfl⟩ := hex
    have hSlot := fanInBits_apply_slot f j₀ rCore (fanInBits f j₀ rCore 218 le_rfl β) 218 le_rfl e
    have hSlotβ := fanInBits_apply_slot f j₀ rCore β 218 le_rfl e
    have heEq : (⟨e.val, by omega⟩ : Fin 218) = e := Fin.ext rfl
    simp only [heEq] at hSlot hSlotβ
    rw [hSlot, hSlotβ]
    have hSame : (∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then
          fanInBits f j₀ rCore 218 le_rfl β (rElecSlot rCore e j) else 0) =
        ∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then β (rElecSlot rCore e j) else 0 :=
      Finset.sum_congr rfl fun j _ ↦ by
        split_ifs with hj
        · exact fanInBits_apply_other f j₀ rCore β 218 le_rfl _
            (fun _ heq ↦ hj.2 (rElecSlot_inj rCore heq).2)
        · rfl
    rw [hSame, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [fanInBits_apply_other f j₀ rCore _ 218 le_rfl w (fun e heq ↦ hex ⟨e, heq⟩),
        fanInBits_apply_other f j₀ rCore β 218 le_rfl w (fun e heq ↦ hex ⟨e, heq⟩)]
/-- 4 zero-T `CZ` gates between `uHi[0..4)` (`rScr[64..68)`) and `rRow4[0..4)` (`rScr[70..74)`). -/
def cCz4RowHi {n mScr : ℕ} (hm : 75 ≤ mScr) (rScr : QRegister mScr n) : Circuit n :=
  let uHi : Fin 4 → Wire n := fun h ↦ rScr ⟨64 + h.val, by omega⟩
  let rRow4 : QRegister 4 n := p2dSubReg rScr 70 4 (by omega)
  have hne : ∀ h : Fin 4, uHi h ≠ rRow4 h := fun h heq ↦ by
    have hr : rRow4 h = rScr ⟨70 + h.val, by omega⟩ :=
      congrArg rScr.wires (Fin.ext (by dsimp [rRow4, p2dSubReg]))
    exact rSub_ne_of_ne rScr (by omega) (by omega) (by omega) (heq.trans hr)
  czCircuit (uHi 0) (rRow4 0) (hne 0) ;;ᶜ
    (czCircuit (uHi 1) (rRow4 1) (hne 1) ;;ᶜ
      (czCircuit (uHi 2) (rRow4 2) (hne 2) ;;ᶜ czCircuit (uHi 3) (rRow4 3) (hne 3)))
theorem cCz4RowHi_count {n mScr : ℕ} (hm : 75 ≤ mScr) (rScr : QRegister mScr n) :
    (cCz4RowHi hm rScr).count TOFF = 0 ∧ (cCz4RowHi hm rScr).count PrimitiveGate.T = 0 := by
  dsimp only [cCz4RowHi]
  simp [Circuit.count_seq, czCircuit_count_toff, czCircuit_count_t]
theorem cCz4RowHi_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (rScr : QRegister mScr n)
    (α : BitAssignment n) (h₀ : ℕ) (hh₀ : h₀ < 4)
    (hHi : ∀ h : Fin 4, α (rScr ⟨64 + h.val, by omega⟩) = if h.val = h₀ then 1 else 0) :
    (cCz4RowHi hm rScr).eval.1.mulVec (ket α) =
      ((-1 : ℂ) ^ (α (p2dSubReg rScr 70 4 (by omega) ⟨h₀, hh₀⟩)).val) • ket α := by
  dsimp only [cCz4RowHi]
  rw[eval_seq_mulVec, ket_czCircuit, Matrix.mulVec_smul, eval_seq_mulVec, ket_czCircuit,
      Matrix.mulVec_smul, eval_seq_mulVec, ket_czCircuit, Matrix.mulVec_smul, ket_czCircuit,
      smul_smul, smul_smul, smul_smul]
  refine congrArg (· • ket α) ?_
  have h0 := hHi 0; have h1 := hHi 1; have h2 := hHi 2; have h3 := hHi 3
  rw [h0, h1, h2, h3]
  rcases (by omega : h₀ = 0 ∨ h₀ = 1 ∨ h₀ = 2 ∨ h₀ = 3) with rfl | rfl | rfl | rfl
  · have hf : (⟨0, hh₀⟩ : Fin 4) = 0 := rfl; rw [hf]; simp
  · have hf : (⟨1, hh₀⟩ : Fin 4) = 1 := rfl; rw [hf]; simp
  · have hf : (⟨2, hh₀⟩ : Fin 4) = 2 := rfl; rw [hf]; simp
  · have hf : (⟨3, hh₀⟩ : Fin 4) = 3 := rfl; rw [hf]; simp
def S_slot0Lens {n kData : ℕ} (rData : QRegister kData n) (L : Slot18Lens kData)
    (β : BitAssignment n) : Prop := L.tbl (rData.extractIndex ((basisBitsEquiv n).symm β)) = 0
end BoothOpt_02_Cached64x4TrueSwapEngine
open MasterZeroHypCompactAndCompactTopBridge (embedMatrix_inj_on_work_zero)
open ZeroHypStageABToUFoldedPass123SegAndCompac (embedUnitary_list_ofFn_prod)
open InterWalkRSum42Hoist (qreg_ext)
namespace StageBTwoElecQftStream218Inner
open PosSlots24BranchConcrete (posCoreWires rElecSlot rPartnerIdx)
open PosSlots24PartnerMux288 hiding ite_pos ite_neg qreg_ext
open PosSlots24PartnerMuxZeroT123 (partnerTblVal216)
open InterWalkRSum42Hoist (qreg_block_apply)
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open DyadicQft64Engine (sysCatEquiv)
open DyadicQft64WalkCircuit (rAxis654 rIdInCat rIdOfCat_concat_rPGOfCat realizes_congr_slice)
open DyadicQft64WalkCircuit288
  (sysCatGenPerm sysCatEquiv_sysCatGenPerm genCatPhasePermUnitary genCatPhasePermUnitary_apply
  apexCatUnitary apexCatUnitary_intertwinesCat)
open CoreQftHadamard140And160
  (rQftCanon128 rWorkCanon128 rSysCanon128 rPGCanon128 rSysCanon128_disjoint_rPGCanon128
  rSysCanon128_disjoint_rWorkCanon128 rPGCanon128_disjoint_rWorkCanon128 CanonStageSpec128)
open InPlaceFullAddSlice InPlaceStepEngine
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix axisProdPrefix stageHPrefixCanonStage128)
open StageAPointPhase128OnStep
  (ForestSlotConfig forestAxisNat xorForestBatchWork xorForestBatchTCost xorForestBatch_spec
  idxForestAx idxForestAx_inj forestTermAxis xorForestBatchFwdDyn128 xorForestBatchInvDyn128
  diag6Unitary w16Exp6 stageW16PrefixCanonStage128 forestCfg0 forestCfg1 forestCfg2 forestCfg3
  forestExp0 forestExp1 forestExp2 forestExp3 forestCfg0_exp_eq forestCfg1_exp_eq forestCfg2_exp_eq
  forestCfg3_exp_eq hL6_le_654 rawActiveTwoElecForestQftStage128 activeTwoElecForestFullQftStage128)
open ForestQft117BundleNoTopBridge (dCanonStage128Fwd dCanonStage128Fwd_realizes)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply)
open PartnerAndAnchorSlot18LensAndMidBA (rElecSlot_ofFin_val)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open ElecHadTrueSwapLocalCompClosure
  (rPartnerIdx_ofFin_val partnerLens216 partnerLens216_tbl_eq partnerTblVal216_eq_extract)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open ZeroHypSlot0CommAndHMidClosure
  (P_slot0 P_slot0_eq_diagonal basisOutcomeProjector_zero_mul_self
  disjoint_embedMatrix_comm_diagonal_of_extract)
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open QRegExt
theorem posCoreWires_eq_4034 : posCoreWires = 4034 := rfl
/-- Selector extracting `posCoreWires` (`4,034`) from `(posCoreWires + 42) + 7` (`= 4,083`). -/
def selCoreInCoreSum42PG7 : QRegister posCoreWires ((posCoreWires + 42) + 7) :=
  QRegister.block 0 posCoreWires (by omega)
/-- Selector extracting `rPG7` (`7`) from `(posCoreWires + 42) + 7` (`= 4,083`). -/
def selPG7InCoreSum42PG7 : QRegister 7 ((posCoreWires + 42) + 7) :=
  QRegister.block (posCoreWires + 42) 7 le_rfl
/-- Concrete Stage-B partner `Slot18Lens` on `(posCoreWires + 42) + 7 = 4,083`. -/
noncomputable abbrev partnerLensOnCoreSum42PG7 : Slot18Lens ((posCoreWires + 42) + 7) :=
  partnerLens216 selCoreInCoreSum42PG7
/-- Subregister selecting `rCore` (`posCoreWires`) inside `((posCoreWires + 42) + 7) + 18`. -/
def rCoreInActB42 : QRegister posCoreWires (((posCoreWires + 42) + 7) + 18) :=
  (selDataInAct ((posCoreWires + 42) + 7)).compose selCoreInCoreSum42PG7
/-- Subregister selecting `rPG7` (`7`) inside `((posCoreWires + 42) + 7) + 18`. -/
def rPG7InActB42 : QRegister 7 (((posCoreWires + 42) + 7) + 18) :=
  (selDataInAct ((posCoreWires + 42) + 7)).compose selPG7InCoreSum42PG7
/-- Subregister selecting `rPartner18` (`18`) inside `((posCoreWires + 42) + 7) + 18`. -/
def rPartner18InActB42 : QRegister 18 (((posCoreWires + 42) + 7) + 18) :=
  selMeasInAct ((posCoreWires + 42) + 7)
/-- Subregister selecting Electron `0` (`18` wires `[0 .. 18)`) inside `((posCoreWires + 42) + 7)
  + 18`. -/
def rElec0InActB42 : QRegister 18 (((posCoreWires + 42) + 7) + 18) :=
  rCoreInActB42.compose (rElecSlot (QRegExt.ofFin posCoreWires) 0)
theorem rCoreInActB42_apply (i : Fin posCoreWires) : (rCoreInActB42 i).val = i.val := by
  simp [rCoreInActB42, selDataInAct_apply,
    selCoreInCoreSum42PG7]
theorem rPG7InActB42_apply (i : Fin 7) :
    (rPG7InActB42 i).val = (posCoreWires + 42) + i.val := by
  simp [rPG7InActB42, selDataInAct_apply,
    selPG7InCoreSum42PG7]
theorem rPartner18InActB42_apply (i : Fin 18) :
    (rPartner18InActB42 i).val = ((posCoreWires + 42) + 7) + i.val := by
  simp [rPartner18InActB42, selMeasInAct_apply]
theorem rElec0InActB42_apply (i : Fin 18) : (rElec0InActB42 i).val = i.val := by
  rw [rElec0InActB42, QRegister.compose_apply, rCoreInActB42_apply, rElecSlot_ofFin_val]
  omega
/-- `(3924 + 3)`-wire system register inside `((posCoreWires + 42) + 7) + 18` placing
`rElec0InActB42` on axes `0..2` (`[0..18)`), `rPartner18InActB42` on axes `3..5` (`[18..36)`),
and non-slot0 core wires `[18..3909)` as clean padding on `[36..3927)`. -/
def rIdSlot0Partner : QRegister (3924 + 3) (((posCoreWires + 42) + 7) + 18) :=
  ⟨⟨fun i ↦
      if h0 : i.val < 18 then
        rElec0InActB42 ⟨i.val, h0⟩
      else if h1 : i.val < 36 then
        rPartner18InActB42 ⟨i.val - 18, by omega⟩
      else
        rCoreInActB42 ⟨i.val - 18, by have := i.isLt; have := posCoreWires_eq_4034; omega⟩,
    fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt; have hP := posCoreWires_eq_4034
      have hv := congrArg Fin.val hab
      by_cases ha0 : a.val < 18
      · simp only [ha0, ↓reduceDIte, rElec0InActB42_apply] at hv
        by_cases hb0 : b.val < 18
        · simp only [hb0, ↓reduceDIte, rElec0InActB42_apply] at hv
          exact Fin.ext hv
        · by_cases hb1 : b.val < 36
          · simp only [hb0, hb1, ↓reduceDIte, rPartner18InActB42_apply] at hv
            omega
          · simp only [hb0, hb1, ↓reduceDIte, rCoreInActB42_apply] at hv
            omega
      · by_cases ha1 : a.val < 36
        · simp only [ha0, ha1, ↓reduceDIte, rPartner18InActB42_apply] at hv
          by_cases hb0 : b.val < 18
          · simp only [hb0, ↓reduceDIte, rElec0InActB42_apply] at hv
            omega
          · by_cases hb1 : b.val < 36
            · simp only [hb0, hb1, ↓reduceDIte, rPartner18InActB42_apply] at hv
              exact Fin.ext (by omega)
            · simp only [hb0, hb1, ↓reduceDIte, rCoreInActB42_apply] at hv
              omega
        · simp only [ha0, ha1, ↓reduceDIte, rCoreInActB42_apply] at hv
          by_cases hb0 : b.val < 18
          · simp only [hb0, ↓reduceDIte, rElec0InActB42_apply] at hv
            omega
          · by_cases hb1 : b.val < 36
            · simp only [hb0, hb1, ↓reduceDIte, rPartner18InActB42_apply] at hv
              omega
            · simp only [hb0, hb1, ↓reduceDIte, rCoreInActB42_apply] at hv
              exact Fin.ext (by omega)⟩⟩
theorem rIdSlot0Partner_apply (i : Fin (3924 + 3)) :
    rIdSlot0Partner i =
      if h0 : i.val < 18 then
        rElec0InActB42 ⟨i.val, h0⟩
      else if h1 : i.val < 36 then
        rPartner18InActB42 ⟨i.val - 18, by omega⟩
      else
        rCoreInActB42 ⟨i.val - 18, by have := i.isLt; have := posCoreWires_eq_4034; omega⟩ :=
  rfl
theorem rIdSlot0Partner_disj_rPG7InActB42 : rIdSlot0Partner.DisjointWires rPG7InActB42 := by
  rw [QRegister.disjoint_iff]
  intro i m h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hm := m.isLt; have hP := posCoreWires_eq_4034
  rw [rPG7InActB42_apply, rIdSlot0Partner_apply] at hv
  by_cases h0 : i.val < 18
  · simp only [h0, ↓reduceDIte, rElec0InActB42_apply] at hv; omega
  · by_cases h1 : i.val < 36
    · simp only [h0, h1, ↓reduceDIte, rPartner18InActB42_apply] at hv; omega
    · simp only [h0, h1, ↓reduceDIte, rCoreInActB42_apply] at hv; omega
/-- `(3924 + 3 + 7)`-wire catalyzed QFT selector inside `((posCoreWires + 42) + 7) + 18` placing
`(rElecSlot 0, rPartner18)` on the first `6` axes (`[0..36)`) and `rPG7` on the `7` catalyst wires.
-/
def rCatSlot0Partner : QRegister (3924 + 3 + 7) (((posCoreWires + 42) + 7) + 18) :=
  rIdSlot0Partner.concat rPG7InActB42 rIdSlot0Partner_disj_rPG7InActB42
/-- Non-slot-0 core subregister (`posCoreWires - 18 = 4,016` wires `[18 .. posCoreWires)`)
inside `((posCoreWires + 42) + 7) + 18`. -/
def rCoreSkip0InActB42 : QRegister (posCoreWires - 18) (((posCoreWires + 42) + 7) + 18) :=
  rCoreInActB42.compose
    (QRegister.block 18 (posCoreWires - 18) (by have := posCoreWires_eq_4034; omega))
theorem rCoreSkip0InActB42_apply (j : Fin (posCoreWires - 18)) :
    (rCoreSkip0InActB42 j).val = 18 + j.val := by
  rw [rCoreSkip0InActB42, QRegister.compose_apply, rCoreInActB42_apply]
  simp
/-- Diagonal entries of `P_slot0 partnerLensOnCoreSum42PG7` indexed purely by
  `rCoreSkip0InActB42`. -/
noncomputable def dPartnerSkip0 (s : Fin (2 ^ (posCoreWires - 18))) : ℂ := if
    partnerLensOnCoreSum42PG7.tbl ((selDataInAct ((posCoreWires + 42) + 7)).extractIndex
    (rCoreSkip0InActB42.replaceIndex 0 s)) = 0 then 1 else 0
/-- `P_slot0 partnerLensOnCoreSum42PG7` is an embedded diagonal matrix supported strictly on
`rCoreSkip0InActB42` (`[18 .. posCoreWires)`). -/
theorem P_slot0_partnerLensOnCoreSum42PG7_eq_embedMatrix_diagonal :
    P_slot0 partnerLensOnCoreSum42PG7 =
      rCoreSkip0InActB42.embedMatrix (Matrix.diagonal dPartnerSkip0) := by
  rw [P_slot0_eq_diagonal, embedMatrix_diagonal_eq rCoreSkip0InActB42 dPartnerSkip0]
  apply congrArg Matrix.diagonal
  funext x
  dsimp only [dPartnerSkip0]
  let y := rCoreSkip0InActB42.replaceIndex 0 (rCoreSkip0InActB42.extractIndex x)
  suffices hTbl : partnerLensOnCoreSum42PG7.tbl ((selDataInAct ((posCoreWires + 42) +
    7)).extractIndex x) =
      partnerLensOnCoreSum42PG7.tbl ((selDataInAct ((posCoreWires + 42) + 7)).extractIndex y) by
    rw [hTbl]
  have hSkip : rCoreSkip0InActB42.extractIndex x = rCoreSkip0InActB42.extractIndex y :=
    (QRegister.extractIndex_replaceIndex rCoreSkip0InActB42 0
      (rCoreSkip0InActB42.extractIndex x)).symm
  rw [partnerLens216_tbl_eq, partnerLens216_tbl_eq,
      ← QRegister.extractIndex_compose (selDataInAct ((posCoreWires + 42) +
        7)) selCoreInCoreSum42PG7 x,
      ← QRegister.extractIndex_compose (selDataInAct ((posCoreWires + 42) +
        7)) selCoreInCoreSum42PG7 y]
  change partnerTblVal216 (rCoreInActB42.extractIndex x) =
    partnerTblVal216 (rCoreInActB42.extractIndex y)
  rw [partnerTblVal216_eq_extract, partnerTblVal216_eq_extract]
  have hHighBits (k : Fin posCoreWires) (hk : 18 ≤ k.val) :
      basisBits posCoreWires (rCoreInActB42.extractIndex x) k =
        basisBits posCoreWires (rCoreInActB42.extractIndex y) k := by
    have hBk (z : Fin (2 ^ (((posCoreWires + 42) + 7) + 18))) :
        basisBits posCoreWires (rCoreInActB42.extractIndex z) k =
          basisBits (posCoreWires - 18) (rCoreSkip0InActB42.extractIndex z)
            ⟨k.val - 18, by have := k.isLt; omega⟩ := by
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      apply congrArg (basisBits _ _)
      ext
      rw [rCoreInActB42_apply, rCoreSkip0InActB42_apply]
      dsimp
      omega
    rw [hBk x, hBk y, hSkip]
  have hPartEq : regVal (rPartnerIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires (rCoreInActB42.extractIndex x)) = regVal
      (rPartnerIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires (rCoreInActB42.extractIndex y)) := by
    unfold regVal _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    dsimp only
    rw [hHighBits _ (by rw [rPartnerIdx_ofFin_val]; omega)]
  apply (basisBitsEquiv 18).injective
  funext q
  change basisBits 18 _ q = basisBits 18 _ q
  rw [QRegister.basisBits_extractIndex (rElecSlot _ _),
      QRegister.basisBits_extractIndex (rElecSlot _ _)]
  refine Eq.trans (hHighBits _ ?_)
    (congrArg (basisBits posCoreWires (rCoreInActB42.extractIndex y)) ?_)
  · rw [rElecSlot_ofFin_val]
    dsimp only
    omega
  · apply Fin.ext
    rw [rElecSlot_ofFin_val, rElecSlot_ofFin_val]
    dsimp only
    rw [hPartEq]
attribute [irreducible] dPartnerSkip0
def IsDiagUnitary {D : ℕ} (U : Unitary D) : Prop := ∃ d : Fin D → ℂ, U.1 = Matrix.diagonal d
theorem isDiagUnitary_embed {N m : ℕ} (r : QRegister m N) {U : Unitary (2 ^ m)}
    (hU : IsDiagUnitary U) : IsDiagUnitary (r.embedUnitary U) := by
  rcases hU with ⟨d, hd⟩
  exact ⟨fun x ↦
    d (r.extractIndex x), by rw [QRegister.embedUnitary_val, hd, embedMatrix_diagonal_eq]⟩
theorem isDiagUnitary_comm_diagonal {D : ℕ} {U : Unitary D} (hU : IsDiagUnitary U)
    (f : Fin D → ℂ) : U.1 * Matrix.diagonal f = Matrix.diagonal f * U.1 := by
  rcases hU with ⟨d, hd⟩
  rw [hd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _
noncomputable def xorForestBatchExplicitCanonStage128 (s off L tB : ℕ) (cfg : ForestSlotConfig s)
    (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128)
    (htB : xorForestBatchTCost s cfg L = tB) : CanonStageSpec128 :=
  let hAll := xorForestBatch_spec () s cfg L hs hL (le_refl (xorForestBatchWork s cfg L))
      rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0 (xorForestBatchWork s cfg L)
      (Nat.zero_add _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
      (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
      (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
      (idxForestAx_inj off L hoff)
  let hRest := @hAll.2.2.2.2 inferInstance inferInstance
  let Φ := Classical.choose hRest
  let hEx2 := Classical.choose_spec hRest
  let uLow := Classical.choose hEx2
  let hSpec := Classical.choose_spec hEx2
  { uCat := apexCatUnitary (3924 + 3) s hs Φ uLow
    uEff := DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
      (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val))
    tCost := tB
    dFwd := xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax
    dInv := xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax
    hToffFwd := hAll.1
    hToffInv := hAll.2.2.1
    hTFwd := hAll.2.1.trans htB
    hTInv := hAll.2.2.2.1.trans htB
    hRealFwd := realizes_congr_slice (Nat.zero_add _ ▸ hwMax)
      (rIdOfCat_concat_rPGOfCat rQftCanon128) hSpec.2.1
    hRealInv := realizes_congr_slice (Nat.zero_add _ ▸ hwMax)
      (rIdOfCat_concat_rPGOfCat rQftCanon128) hSpec.2.2
    hIntertwines := by
      intro N _ rId rPG hdisj U_cat7 hcol0
      have heff : DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
          (fun γ ↦ Φ γ + ((2 ^ s * uLow γ : ℕ) : ℤ)) = DyadicQft64.dyadicDiagUnitary
          (3924 + 3) 7 (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val)) := by
        congr 1
        funext γ
        rw [hSpec.1 γ]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        have ha : off + r.val < 654 := by have := r.isLt; omega
        let b6 : Fin 6 → ZMod 2 := fun q ↦ γ ⟨6 * (off + r.val) + q.val, by omega⟩
        let u6 : Fin 64 := (basisBitsEquiv 6).symm b6
        simp only [forestTermAxis, ha, ↓reduceDIte, idxForestAx]
        change (forestAxisNat s cfg b6 : ℤ) = φ6 u6
        rw [← (basisBitsEquiv 6).apply_symm_apply b6]
        exact hφ6 u6
      rw [← heff]
      exact apexCatUnitary_intertwinesCat s hs rId rPG hdisj U_cat7 hcol0 Φ uLow }
private theorem isDiagUnitary_one_loc {D : ℕ} : IsDiagUnitary (1 : Unitary D) :=
  ⟨fun _ ↦ 1, Matrix.diagonal_one.symm⟩
private theorem isDiagUnitary_mul_loc {D : ℕ} {U₁ U₂ : Unitary D}
    (h1 : IsDiagUnitary U₁) (h2 : IsDiagUnitary U₂) : IsDiagUnitary (U₁ * U₂) := by
  rcases h1 with ⟨d₁, hd₁⟩
  rcases h2 with ⟨d₂, hd₂⟩
  exact ⟨fun x ↦ d₁ x * d₂ x, by rw [Submonoid.coe_mul, hd₁, hd₂, Matrix.diagonal_mul_diagonal]⟩
private theorem isDiagUnitary_list_ofFn_prod_loc {D : ℕ} :
    ∀ {m : ℕ} (g : Fin m → Unitary D),
      (∀ i : Fin m, IsDiagUnitary (g i)) → IsDiagUnitary (List.ofFn g).prod
  | 0, _, _ => by simp [isDiagUnitary_one_loc]
  | m + 1, g, hg => by
      rw [List.ofFn_succ, List.prod_cons]
      exact isDiagUnitary_mul_loc (hg 0)
        (isDiagUnitary_list_ofFn_prod_loc (fun i ↦ g i.succ) (fun i ↦ hg i.succ))
private theorem stageW16Prefix_embed_comm_diagonal_loc {N : ℕ}
    (rCat : QRegister (3924 + 3 + 7) N) (L : ℕ) (hL : L ≤ 654) (k : Fin 5)
    (f : Fin (2 ^ N) → ℂ) :
    (rCat.embedUnitary (stageW16PrefixCanonStage128 L hL k).uCat).1 * Matrix.diagonal f =
      Matrix.diagonal f * (rCat.embedUnitary (stageW16PrefixCanonStage128 L hL k).uCat).1 :=
  isDiagUnitary_comm_diagonal
    (isDiagUnitary_embed rCat
      (isDiagUnitary_embed rIdInCat <|
        isDiagUnitary_list_ofFn_prod_loc _ fun _ ↦
          isDiagUnitary_embed _ ⟨_, rfl⟩)) f
private theorem list_ofFn_prod_comm_diagonal_loc {D : ℕ} (f : Fin D → ℂ) :
    ∀ {L : ℕ} (g : Fin L → Unitary D),
      (∀ i : Fin L, (g i).1 * Matrix.diagonal f = Matrix.diagonal f * (g i).1) →
      ((List.ofFn g).prod).1 * Matrix.diagonal f =
        Matrix.diagonal f * ((List.ofFn g).prod).1
  | 0, _, _ => by simp
  | L + 1, g, hg => by
      rw [List.ofFn_succ, List.prod_cons, Submonoid.coe_mul,
          Matrix.mul_assoc, list_ofFn_prod_comm_diagonal_loc f (fun i ↦ g i.succ) (fun i ↦
            hg i.succ),
          ← Matrix.mul_assoc, hg 0, Matrix.mul_assoc]
private theorem stageHPrefix_embed_comm_diagonal_loc {N kCore : ℕ}
    (rCat : QRegister (3924 + 3 + 7) N) (rCore : QRegister kCore N) (L : ℕ) (hL : L ≤ 654)
    (hNoAxis : ∀ i : Fin L,
    (rCat.compose (rIdInCat.compose (rAxisPrefix L hL i))).DisjointWires rCore) (kf : Fin 6)
    (f : Fin (2 ^ N) → ℂ)
    (hf : ∀ x y : Fin (2 ^ N), rCore.extractIndex x = rCore.extractIndex y → f x = f y) :
    (rCat.embedUnitary (stageHPrefixCanonStage128 L hL kf).uCat).1 * Matrix.diagonal f =
    Matrix.diagonal f * (rCat.embedUnitary (stageHPrefixCanonStage128 L hL kf).uCat).1 := by
  change (rCat.embedUnitary (rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ _)))).1 *
      Matrix.diagonal f =
    Matrix.diagonal f *
      (rCat.embedUnitary (rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ _)))).1
  dsimp only [axisProdPrefix]
  rw [← QRegister.embedUnitary_compose,
      embedUnitary_list_ofFn_prod (rCat.compose rIdInCat)]
  refine list_ofFn_prod_comm_diagonal_loc f _ fun i ↦ ?_
  rw [QRegister.compose_assoc, QRegister.embedUnitary_val]
  exact disjoint_embedMatrix_comm_diagonal_of_extract rCore
    (rCat.compose (rIdInCat.compose (rAxisPrefix L hL i)))
    (hNoAxis i) f hf _
private theorem embedMatrix_genCatPhasePermUnitary_comm_diagonal_loc {N kSys B kCore : ℕ}
    (rAct : QRegister (kSys + B) N) (rCore : QRegister kCore N)
    (hNoPG : ∀ (j : Fin kCore) (m : Fin B), rCore j ≠ rAct (Fin.natAdd kSys m))
    (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ : BitAssignment kSys → Fin (2 ^ B) → ℤ) (f : Fin (2 ^ N) → ℂ)
    (hf : ∀ x y : Fin (2 ^ N), rCore.extractIndex x = rCore.extractIndex y → f x = f y) :
    (rAct.embedUnitary (genCatPhasePermUnitary kSys B e ψ)).1 * Matrix.diagonal f =
    Matrix.diagonal f * (rAct.embedUnitary (genCatPhasePermUnitary kSys B e ψ)).1 := by
  ext x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul,
    QRegister.embedUnitary_val, QRegister.embedMatrix_apply, genCatPhasePermUnitary_apply]
  by_cases henv : (rAct.basisSplitEquiv x).2 = (rAct.basisSplitEquiv y).2
  · by_cases hperm : sysCatGenPerm kSys B e (rAct.extractIndex y) = rAct.extractIndex x
    · have hOut := (rAct.basisSplit_environment_eq_iff x y).mp henv
      have hSys : (sysCatEquiv kSys B (rAct.extractIndex x)).1 =
          (sysCatEquiv kSys B (rAct.extractIndex y)).1 := by
        rw [← hperm, sysCatEquiv_sysCatGenPerm]
      have hCoreEq : rCore.extractIndex x = rCore.extractIndex y := by
        apply (basisBitsEquiv kCore).injective
        funext j
        change basisBits kCore (rCore.extractIndex x) j = basisBits kCore (rCore.extractIndex y) j
        rw [rCore.basisBits_extractIndex, rCore.basisBits_extractIndex]
        by_cases hmem : rCore j ∈ Set.range rAct.wires
        · rcases hmem with ⟨idx, hidx⟩
          revert hidx
          refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
          · intro hidx'
            have hbi := congrFun hSys i
            change basisBits (kSys + B) (rAct.extractIndex x) (Fin.castAdd B i) =
              basisBits (kSys + B) (rAct.extractIndex y) (Fin.castAdd B i) at hbi
            rw [rAct.basisBits_extractIndex, rAct.basisBits_extractIndex, hidx'] at hbi
            exact hbi
          · intro hidx'
            exact absurd hidx'.symm (hNoPG j m)
        · exact hOut (rCore j) hmem
      rw [ite_eq_left henv, ite_eq_left hperm, hf x y hCoreEq, mul_comm (f y)]
    · rw [ite_eq_left henv, ite_eq_right hperm]; simp
  · rw [ite_eq_right henv]; simp
private theorem xorForestBatchExplicit03i_embed_comm_diagonal_loc {N kCore : ℕ}
    (rCat : QRegister (3924 + 3 + 7) N) (rCore : QRegister kCore N)
    (hNoPG : ∀ (j : Fin kCore) (m : Fin 7), rCore j ≠ rCat (Fin.natAdd (3924 + 3) m))
    (s off L tB : ℕ) (cfg : ForestSlotConfig s)
    (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128)
    (htB : xorForestBatchTCost s cfg L = tB) (f : Fin (2 ^ N) → ℂ)
    (hf : ∀ x y : Fin (2 ^ N), rCore.extractIndex x = rCore.extractIndex y → f x = f y) :
    (rCat.embedUnitary
      (xorForestBatchExplicitCanonStage128 s off L tB cfg φ6 hφ6 hs hL hoff hwMax
        htB).uCat).1 *
    Matrix.diagonal f = Matrix.diagonal f *
    (rCat.embedUnitary
      (xorForestBatchExplicitCanonStage128 s off L tB cfg φ6 hφ6 hs hL hoff hwMax
        htB).uCat).1 := by
  dsimp only [xorForestBatchExplicitCanonStage128]
  unfold apexCatUnitary
  exact embedMatrix_genCatPhasePermUnitary_comm_diagonal_loc rCat rCore hNoPG _ _ f hf
/-- Explicit 2-electron (`L = 6`) Hadamard-Forest `CanonStageSpec128` whose `.dFwd` and `.dInv`
are definitionally identical to `activeTwoElecForestFullQftStage128.dFwd` and `.dInv`. -/
noncomputable def activeTwoElecForestExplicitQftStage128 : CanonStageSpec128 :=
  let s3 := xorForestBatchExplicitCanonStage128 3 0 6 15 forestCfg3 forestExp3 forestCfg3_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let s2 := xorForestBatchExplicitCanonStage128 2 0 6 54 forestCfg2 forestExp2 forestCfg2_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let s1 := xorForestBatchExplicitCanonStage128 1 0 6 78 forestCfg1 forestExp1 forestCfg1_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let s0 := xorForestBatchExplicitCanonStage128 0 0 6 44 forestCfg0 forestExp0 forestCfg0_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
  (((stageHPrefixCanonStage128 6 hL6_le_654 5).seq (stageW16PrefixCanonStage128 6 hL6_le_654 4)).seq
    (((stageHPrefixCanonStage128 6 hL6_le_654 4).seq
      ((stageW16PrefixCanonStage128 6 hL6_le_654 3).seq s3)).seq
      (((stageHPrefixCanonStage128 6 hL6_le_654 3).seq
        ((stageW16PrefixCanonStage128 6 hL6_le_654 2).seq s2)).seq
        (((stageHPrefixCanonStage128 6 hL6_le_654 2).seq
          ((stageW16PrefixCanonStage128 6 hL6_le_654 1).seq s1)).seq
          (((stageHPrefixCanonStage128 6 hL6_le_654 1).seq
            ((stageW16PrefixCanonStage128 6 hL6_le_654 0).seq s0)).seq
            (stageHPrefixCanonStage128 6 hL6_le_654 0))))))
private theorem seq_dFwd_congr_loc {A₁ A₂ B₁ B₂ : CanonStageSpec128}
    (hA : A₁.dFwd = A₂.dFwd) (hB : B₁.dFwd = B₂.dFwd) :
    (A₁.seq B₁).dFwd = (A₂.seq B₂).dFwd := by
  change DynamicCircuit.seq A₁.dFwd B₁.dFwd = DynamicCircuit.seq A₂.dFwd B₂.dFwd
  rw [hA, hB]
private theorem activeTwoElecForestExplicitQftStage128_dFwd_eq_loc :
    activeTwoElecForestExplicitQftStage128.dFwd = activeTwoElecForestFullQftStage128.dFwd := by
  have hCongr : rawActiveTwoElecForestQftStage128.dFwd = activeTwoElecForestFullQftStage128.dFwd :=
    rfl
  refine Eq.trans ?_ hCongr
  exact seq_dFwd_congr_loc (seq_dFwd_congr_loc rfl rfl)
    (seq_dFwd_congr_loc (seq_dFwd_congr_loc rfl (seq_dFwd_congr_loc rfl rfl))
      (seq_dFwd_congr_loc (seq_dFwd_congr_loc rfl (seq_dFwd_congr_loc rfl rfl))
        (seq_dFwd_congr_loc (seq_dFwd_congr_loc rfl (seq_dFwd_congr_loc rfl rfl))
          (seq_dFwd_congr_loc (seq_dFwd_congr_loc rfl (seq_dFwd_congr_loc rfl rfl)) rfl))))
attribute [irreducible] xorForestBatchExplicitCanonStage128
private theorem rCat_seq_comm_diagonal_loc {N : ℕ}
    (rCat : QRegister (3924 + 3 + 7) N) (f : Fin (2 ^ N) → ℂ) {S₁ S₂ : CanonStageSpec128}
    (h1 : (rCat.embedUnitary S₁.uCat).1 * Matrix.diagonal f =
    Matrix.diagonal f * (rCat.embedUnitary S₁.uCat).1)
    (h2 : (rCat.embedUnitary S₂.uCat).1 * Matrix.diagonal f =
    Matrix.diagonal f * (rCat.embedUnitary S₂.uCat).1) :
    (rCat.embedUnitary (S₁.seq S₂).uCat).1 * Matrix.diagonal f =
    Matrix.diagonal f * (rCat.embedUnitary (S₁.seq S₂).uCat).1 := by
  change (rCat.embedUnitary (S₂.uCat * S₁.uCat)).1 * Matrix.diagonal f =
    Matrix.diagonal f * (rCat.embedUnitary (S₂.uCat * S₁.uCat)).1
  rw [QRegister.embedUnitary_mul, Submonoid.coe_mul,
      Matrix.mul_assoc, h1, ← Matrix.mul_assoc, h2, Matrix.mul_assoc]
private theorem rCat_activeTwoElecForestExplicitQftStage128_comm_diagonal_loc {N kCore : ℕ}
    (rCat : QRegister (3924 + 3 + 7) N) (rCore : QRegister kCore N)
    (hNoPG : ∀ (j : Fin kCore) (m : Fin 7), rCore j ≠ rCat (Fin.natAdd (3924 + 3) m))
    (hNoAxis : ∀ i : Fin 6,
      (rCat.compose (rIdInCat.compose (rAxisPrefix 6 hL6_le_654 i))).DisjointWires rCore)
    (f : Fin (2 ^ N) → ℂ)
    (hf : ∀ x y : Fin (2 ^ N), rCore.extractIndex x = rCore.extractIndex y → f x = f y) :
    (rCat.embedUnitary activeTwoElecForestExplicitQftStage128.uCat).1 * Matrix.diagonal f =
      Matrix.diagonal f * (rCat.embedUnitary activeTwoElecForestExplicitQftStage128.uCat).1 := by
  dsimp only [activeTwoElecForestExplicitQftStage128]
  exact rCat_seq_comm_diagonal_loc rCat f
    (rCat_seq_comm_diagonal_loc rCat f
      (stageHPrefix_embed_comm_diagonal_loc rCat rCore 6 hL6_le_654 hNoAxis 5 f hf)
      (stageW16Prefix_embed_comm_diagonal_loc rCat 6 hL6_le_654 4 f))
    (rCat_seq_comm_diagonal_loc rCat f
      (rCat_seq_comm_diagonal_loc rCat f
        (stageHPrefix_embed_comm_diagonal_loc rCat rCore 6 hL6_le_654 hNoAxis 4 f hf)
        (rCat_seq_comm_diagonal_loc rCat f
          (stageW16Prefix_embed_comm_diagonal_loc rCat 6 hL6_le_654 3 f)
          (xorForestBatchExplicit03i_embed_comm_diagonal_loc rCat rCore hNoPG 3 0 6 15
            forestCfg3 forestExp3 forestCfg3_exp_eq _ _ _ _ _ f hf)))
      (rCat_seq_comm_diagonal_loc rCat f
        (rCat_seq_comm_diagonal_loc rCat f
          (stageHPrefix_embed_comm_diagonal_loc rCat rCore 6 hL6_le_654 hNoAxis 3 f hf)
          (rCat_seq_comm_diagonal_loc rCat f
            (stageW16Prefix_embed_comm_diagonal_loc rCat 6 hL6_le_654 2 f)
            (xorForestBatchExplicit03i_embed_comm_diagonal_loc rCat rCore hNoPG 2 0 6 54
              forestCfg2 forestExp2 forestCfg2_exp_eq _ _ _ _ _ f hf)))
        (rCat_seq_comm_diagonal_loc rCat f
          (rCat_seq_comm_diagonal_loc rCat f
            (stageHPrefix_embed_comm_diagonal_loc rCat rCore 6 hL6_le_654 hNoAxis 2 f hf)
            (rCat_seq_comm_diagonal_loc rCat f
              (stageW16Prefix_embed_comm_diagonal_loc rCat 6 hL6_le_654 1 f)
              (xorForestBatchExplicit03i_embed_comm_diagonal_loc rCat rCore hNoPG 1 0 6 78
                forestCfg1 forestExp1 forestCfg1_exp_eq _ _ _ _ _ f hf)))
          (rCat_seq_comm_diagonal_loc rCat f
            (rCat_seq_comm_diagonal_loc rCat f
              (stageHPrefix_embed_comm_diagonal_loc rCat rCore 6 hL6_le_654 hNoAxis 1 f hf)
              (rCat_seq_comm_diagonal_loc rCat f
                (stageW16Prefix_embed_comm_diagonal_loc rCat 6 hL6_le_654 0 f)
                (xorForestBatchExplicit03i_embed_comm_diagonal_loc rCat rCore hNoPG 0 0 6 44
                  forestCfg0 forestExp0 forestCfg0_exp_eq _ _ _ _ _ f hf)))
            (stageHPrefix_embed_comm_diagonal_loc rCat rCore 6 hL6_le_654 hNoAxis 0 f hf)))))
attribute [irreducible] activeTwoElecForestExplicitQftStage128
private theorem dCanonStage128Fwd_congr_loc {Var : Type} {n mWork : ℕ}
    {S₁ S₂ : CanonStageSpec128} (h : S₁.dFwd = S₂.dFwd) (hm : 128 ≤ mWork) (v : Var)
    (rCat : QRegister (3924 + 3 + 7) n) (rWork : QRegister mWork n)
    (hCW : rCat.DisjointWires rWork) : dCanonStage128Fwd S₁ hm v rCat rWork hCW =
    dCanonStage128Fwd S₂ hm v rCat rWork hCW := by
  dsimp only [dCanonStage128Fwd]
  rw [h]
private theorem comm_subreg_diagonal_of_realizes_same_circuit_loc {n k m kSub : ℕ}
    (rAct : QRegister k n) (rWork : QRegister m n) (hDisj : rAct.DisjointWires rWork)
    (rSub : QRegister kSub k) {Q₁ Q₂ : Unitary (2 ^ k)} {d : DynamicCircuit Unit n}
    (hReal1 : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork Q₁ d)
    (hReal2 : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork Q₂ d)
    (hComm2 : ∀ (f : Fin (2 ^ k) → ℂ),
    (∀ x y : Fin (2 ^ k), rSub.extractIndex x = rSub.extractIndex y → f x = f y) →
    Q₂.1 * Matrix.diagonal f = Matrix.diagonal f * Q₂.1) (dSub : Fin (2 ^ kSub) → ℂ) :
    Q₁.1 * rSub.embedMatrix (Matrix.diagonal dSub) =
    rSub.embedMatrix (Matrix.diagonal dSub) * Q₁.1 := by
  have hProj1 (c : Fin (2 ^ kSub)) :
      Q₁.1 * rSub.basisOutcomeProjector c = rSub.basisOutcomeProjector c * Q₁.1 := by
    let P := rSub.basisOutcomeProjector c
    have hP2 : Q₂.1 * P = P * Q₂.1 := by
      dsimp only [P]
      rw [QRegister.basisOutcomeProjector_eq_diagonal]
      exact hComm2 _ fun x y hxy ↦ by rw [hxy]
    let M : Observable (Fin (2 ^ n)) := (rAct.compose rSub).basisOutcomeObservable c
    let Pw := rWork.basisOutcomeProjector 0
    obtain ⟨M₁', hwp1, hproj1⟩ := hReal1 M
    obtain ⟨M₂', hwp2, hproj2⟩ := hReal2 M
    have hMval : M.1.1 = rAct.embedMatrix P := by
      rw [(by simp [M] : M.1.1 = (rAct.compose rSub).basisOutcomeProjector c)]; dsimp only [P]
      have hFun :
          (fun z : Fin (2 ^ n) ↦
            if rSub.extractIndex (rAct.extractIndex z) = c then (1 : ℂ) else 0) =
          (fun z : Fin (2 ^ n) ↦ if (rAct.compose rSub).extractIndex z = c then (1 : ℂ) else 0) :=
            by
        funext z
        rw [QRegister.extractIndex_compose]
      rw [QRegister.basisOutcomeProjector_eq_diagonal,
          QRegister.basisOutcomeProjector_eq_diagonal,
          embedMatrix_diagonal_eq, hFun]
    rw [congrFun (hwp1.symm.trans hwp2) default, hMval] at hproj1
    rw [hMval] at hproj2
    have hEq :
        Pw * ((rAct.embedUnitary Q₁).1ᴴ * rAct.embedMatrix P * (rAct.embedUnitary Q₁).1) * Pw =
        Pw * ((rAct.embedUnitary Q₂).1ᴴ * rAct.embedMatrix P * (rAct.embedUnitary Q₂).1) * Pw :=
      hproj1.symm.trans hproj2
    have hSimp (Q : Unitary (2 ^ k)) :
        Pw * ((rAct.embedUnitary Q).1ᴴ * rAct.embedMatrix P * (rAct.embedUnitary Q).1) * Pw =
          rAct.embedMatrix (Q.1ᴴ * P * Q.1) * Pw := by
      rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose,
          ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
          ← QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct rWork hDisj,
          Matrix.mul_assoc, basisOutcomeProjector_zero_mul_self]
    rw [hSimp Q₁, hSimp Q₂] at hEq
    have hConj : Q₁.1ᴴ * P * Q₁.1 = Q₂.1ᴴ * P * Q₂.1 :=
      embedMatrix_inj_on_work_zero rAct rWork hDisj hEq
    have hQ2 : Q₂.1ᴴ * Q₂.1 = 1 := by
      rw [← star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp Q₂.2
    have hQ1 : Q₁.1 * Q₁.1ᴴ = 1 := by
      rw [← star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp Q₁.2
    have hRhs : Q₂.1ᴴ * P * Q₂.1 = P := by
      rw [Matrix.mul_assoc, ← hP2, ← Matrix.mul_assoc, hQ2, Matrix.one_mul]
    rw [hRhs] at hConj
    calc
      Q₁.1 * P = Q₁.1 * (Q₁.1ᴴ * P * Q₁.1) := by rw [hConj]
      _ = (Q₁.1 * Q₁.1ᴴ) * P * Q₁.1 := by simp only [Matrix.mul_assoc]
      _ = P * Q₁.1 := by rw [hQ1, Matrix.one_mul]
  rw [embedMatrix_diagonal_eq rSub dSub]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hEx : rSub.extractIndex i = rSub.extractIndex j
  · rw [hEx, mul_comm]
  · have hij := congrFun (congrFun (hProj1 (rSub.extractIndex i)) i) j
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
        ite_eq_left rfl, ite_eq_right (Ne.symm hEx), mul_zero, one_mul] at hij
    rw [← hij, zero_mul, mul_zero]
private theorem rCoreSkip0InActB42_ne_rCatSlot0Partner_natAdd_loc
    (j : Fin (posCoreWires - 18)) (m : Fin 7) :
    rCoreSkip0InActB42 j ≠ rCatSlot0Partner (Fin.natAdd (3924 + 3) m) := by
  intro h
  have hv := congrArg Fin.val h
  rw [rCoreSkip0InActB42_apply, rCatSlot0Partner, QRegister.concat_apply_right,
      rPG7InActB42_apply] at hv
  have := j.isLt
  have := posCoreWires_eq_4034
  omega
private theorem rCatSlot0Partner_rAxisPrefix6_disj_rCoreSkip0InActB42_loc (i : Fin 6) :
    (rCatSlot0Partner.compose (rIdInCat.compose (rAxisPrefix 6 hL6_le_654 i))).DisjointWires
      rCoreSkip0InActB42 := by
  rw [QRegister.disjoint_iff]
  intro q j h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hq := q.isLt
  have hj := j.isLt
  have hP := posCoreWires_eq_4034
  rw [rCoreSkip0InActB42_apply] at hv
  have hIdIdx : rIdInCat (rAxisPrefix 6 hL6_le_654 i q) =
      Fin.castAdd 7 ⟨6 * i.val + q.val, by omega⟩ := by
    ext
    simp [rIdInCat, rAxisPrefix, rAxis654]
  rw [QRegister.compose_apply, QRegister.compose_apply, hIdIdx, rCatSlot0Partner,
      QRegister.concat_apply_left, rIdSlot0Partner_apply] at hv
  dsimp only at hv
  by_cases h18 : 6 * i.val + q.val < 18
  · simp only [h18, ↓reduceDIte, rElec0InActB42_apply] at hv
    omega
  · have h36 : 6 * i.val + q.val < 36 := by omega
    simp only [h18, h36, ↓reduceDIte, rPartner18InActB42_apply] at hv
    omega
/-- `rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat` commutes with any
diagonal matrix on `rCoreSkip0InActB42`. -/
theorem rCatSlot0Partner_uQft2_comm_rCoreSkip0_diagonal
    (dSkip : Fin (2 ^ (posCoreWires - 18)) → ℂ) : (rCatSlot0Partner.embedUnitary
    activeTwoElecForestFullQftStage128.uCat).1 * rCoreSkip0InActB42.embedMatrix
    (Matrix.diagonal dSkip) = rCoreSkip0InActB42.embedMatrix (Matrix.diagonal dSkip) *
    (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat).1 := by
  let nAmb := (((posCoreWires + 42) + 7) + 18) + 128
  let rAct : QRegister (((posCoreWires + 42) + 7) + 18) nAmb :=
    QRegister.block 0 (((posCoreWires + 42) + 7) + 18) (by omega)
  let rWork : QRegister 128 nAmb :=
    QRegister.block (((posCoreWires + 42) + 7) + 18) 128 le_rfl
  have hAW : rAct.DisjointWires rWork :=
    QRegister.block_disjoint_of_le 0 (((posCoreWires + 42) + 7) + 18)
      (((posCoreWires + 42) + 7) + 18) 128 (by omega) le_rfl (by omega)
  let rCat := rAct.compose rCatSlot0Partner
  have hCW : rCat.DisjointWires rWork := hAW.compose_left rCatSlot0Partner
  have hReal1 := (dCanonStage128Fwd_realizes activeTwoElecForestFullQftStage128
    (le_refl 128) () rCat rWork hCW).widenActive
  have hReal2 := (dCanonStage128Fwd_realizes activeTwoElecForestExplicitQftStage128
    (le_refl 128) () rCat rWork hCW).widenActive
  rw [dCanonStage128Fwd_congr_loc activeTwoElecForestExplicitQftStage128_dFwd_eq_loc] at hReal2
  exact comm_subreg_diagonal_of_realizes_same_circuit_loc
    rAct rWork hAW rCoreSkip0InActB42 hReal1 hReal2
    (fun f hf ↦ rCat_activeTwoElecForestExplicitQftStage128_comm_diagonal_loc
      rCatSlot0Partner rCoreSkip0InActB42
      rCoreSkip0InActB42_ne_rCatSlot0Partner_natAdd_loc
      rCatSlot0Partner_rAxisPrefix6_disj_rCoreSkip0InActB42_loc f hf)
    dSkip
end StageBTwoElecQftStream218Inner
open ZeroHypStageABToUFoldedPass123SegAndCompac (uHeadPhase80Mod4Eff)
open ZeroHypCatState48StageABMidCoreReductionAn (catState48)
open SingleBarrelPass123Fold
  (qft_mul_uTrailCliffordXor80_comm_uBarrelFast uTrailCliffordXor80_comm_uBarrelFast)
namespace MidUnitaryConjZeroRoot
open SpecsAux.PhaseGradCatalystCore (IntertwinesCat intertwinesCat_of_disjoint)
open Dyadic128CoulombMath (orbitCount47905)
open HoistedSwapSelectBridge (unitaryConj embedUnitary_inv_eq)
open FullSysCatSegmentBridge
  (fullSysCoreWires fullSysBEWires coreElecCosetB1Block fullSysQftCoreUnitary IntertwinesLocalCat
  FullSysQft654Bundle FullSysSelectOracleBundle)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open CoinDispatchedBarrel288 (uBarrelFast)
open PosSlots24PartnerMuxZeroT123 (uPosTailAndSlack)
open PosSlots24SemanticBridge (pos24TailSign pos24_coreWires80_eq castUnitaryPow2)
open PosHeadMod4_15476 (diagonalSignUnitaryN_tail_mul_uHeadPhaseMod4)
open PosPostPrep80MergedVep (uSwapCore3967 uSwapCore3967_mul_self)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (U_cat_B_normalized_col_zero_singleCat)
open SingleCatClosure
  (intertwinesCat_topCatSlice_of_localCat intertwinesCat_congr_ops singleCat_seven_le_of_48)
open PolymorphicTopClosure (intertwinesCat_mul_gen)
open Barrel3PassSelectStitch
  (rCat80 rCoreSeg r654Seg rQSeg h654Seg_disj_Cat80 hCoreSeg_disj_Cat80 uTrailCliffordXor80)
open SelStitchHelper (coreQftHadamardPrunedBundle128_eq_ideal654)
open Leaf2PosMod4WidthCore (uPosPhase80Mod4Eff pos24TailMag30Aux uPosPhase80Mod4OfB)
/-! Effective `fullSysCoreWires 80` Tail+Slack unitary (`uSwapCore3967`-conjugated `uPosTailAndSlack
true`). -/
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
noncomputable def uPosTail80Mod4Eff (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ (fullSysCoreWires 80)) :=
    (uSwapCore3967 * castUnitaryPow2 pos24_coreWires80_eq.symm (uPosTailAndSlack true tailSign
    tailMag30)) * uSwapCore3967
/-- Effective `fullSysCoreWires 80` Tail+Slack unitary at `B`-bit midpoint precision (`6 ≤ B ≤
  27`). -/
noncomputable def uPosTail80Mod4OfB (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  uPosTail80Mod4Eff pos24TailSign (pos24TailMag30Aux B hB6 hB27)
theorem uPosPhase80Mod4Eff_eq_tail_mul_head_zeroHyp (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : uPosPhase80Mod4Eff tailSign tailMag30 =
    uPosTail80Mod4Eff tailSign tailMag30 * uHeadPhase80Mod4Eff := by
  have hCast : ∀ {k₁ k₂ : ℕ} (hk : k₁ = k₂) (A B : Unitary (2 ^ k₁)),
      castUnitaryPow2 hk (A * B) = castUnitaryPow2 hk A * castUnitaryPow2 hk B := by
    intro _ _ hk _ _
    subst hk
    rfl
  have hConj : ∀ (S T H : Unitary (2 ^ (fullSysCoreWires 80))), S * S = 1 →
      (S * (T * H)) * S = ((S * T) * S) * ((S * H) * S) := fun S T H hS ↦ by
    calc (S * (T * H)) * S = S * T * (S * S) * H * S := by
          rw [hS, mul_one]
          simp only [_root_.mul_assoc]
      _ = ((S * T) * S) * ((S * H) * S) := by simp only [_root_.mul_assoc]
  unfold uPosPhase80Mod4Eff uPosTail80Mod4Eff uHeadPhase80Mod4Eff
  rw [← diagonalSignUnitaryN_tail_mul_uHeadPhaseMod4 true tailSign tailMag30, hCast]
  exact hConj _ _ _ uSwapCore3967_mul_self
theorem uPosPhase80Mod4OfB_eq_tail_mul_head_zeroHyp (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (_j : Fin 10) : uPosPhase80Mod4OfB B hB6 hB27 = uPosTail80Mod4OfB B hB6 hB27 *
    uHeadPhase80Mod4Eff ∧ True := ⟨uPosPhase80Mod4Eff_eq_tail_mul_head_zeroHyp pos24TailSign
    (pos24TailMag30Aux B hB6 hB27), trivial⟩
/-- Middle QFT-conjugated `uPass2` segment unitary on `fullSysBEWires 80 + 48`. -/
noncomputable def uQftConjPass2Seg (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (uPass2 : Unitary (2 ^ (fullSysCoreWires 80))) : Unitary (2 ^ (fullSysBEWires 80 + 48))
    := (rQSeg selOra).embedUnitary qft.uQftCat⁻¹ * (rCoreSeg.embedUnitary uPass2 * (rQSeg
    selOra).embedUnitary qft.uQftCat)
/-- **`QSP-SCHED`-Polymorphic `uPosPhase80Mod4OfB B_p` `catState48` Reduction (0 unproven
  holes)**. -/
theorem rhs_stageAB_mid_ofB_mul_catState48_eq_tail_mul_head_zeroHyp
    (ora : FullSysSelectOracleBundle 80 48)
    (B_p : ℕ) (hB6 : 6 ≤ B_p) (hB27 : B_p ≤ 27) :
    let B := uBarrelFast (le_refl 80)
    let Q := fullSysQftCoreUnitary ora.hmPay coreQftHadamardPrunedBundle128
    let QC := Q * uTrailCliffordXor80
    let uPos := uPosPhase80Mod4OfB B_p hB6 hB27
    let D_tail := uPosTail80Mod4OfB B_p hB6 hB27
    let D_head := uHeadPhase80Mod4Eff
    unitaryConj Q (unitaryConj B uPos) =
      unitaryConj B (unitaryConj Q D_tail) * unitaryConj B (unitaryConj Q D_head) ∧
    unitaryConj QC (unitaryConj B uPos) =
      unitaryConj B (unitaryConj QC D_tail) * unitaryConj B (unitaryConj QC D_head) ∧
    (uQftConjPass2Seg coreQftHadamardPrunedBundle128 ora (unitaryConj B uPos)).1 * catState48 =
      (rCoreSeg.embedUnitary (unitaryConj B (unitaryConj Q D_tail)) *
        rCoreSeg.embedUnitary (unitaryConj B (unitaryConj Q D_head))).1 * catState48 ∧
    (rCoreSeg.embedUnitary uTrailCliffordXor80⁻¹ *
      (uQftConjPass2Seg coreQftHadamardPrunedBundle128 ora (unitaryConj B uPos) *
        rCoreSeg.embedUnitary uTrailCliffordXor80)).1 * catState48 =
      (rCoreSeg.embedUnitary (unitaryConj B (unitaryConj QC D_tail)) *
        rCoreSeg.embedUnitary (unitaryConj B (unitaryConj QC D_head))).1 * catState48 := by
  intro B Q QC uPos D_tail D_head
  have hPos : uPos = D_tail * D_head :=
    (uPosPhase80Mod4OfB_eq_tail_mul_head_zeroHyp B_p hB6 hB27 0).1
  have hPay : ora.hmPay = (by decide : 6 ≤ 80) := Subsingleton.elim _ _
  have hQCB : QC * B = B * QC := by
    dsimp only [QC, Q, B]
    rw [hPay]
    exact qft_mul_uTrailCliffordXor80_comm_uBarrelFast
      coreQftHadamardPrunedBundle128 coreQftHadamardPrunedBundle128_eq_ideal654
  have hQB : Q * B = B * Q := by
    let X := uTrailCliffordXor80
    have hXB : X * B = B * X := uTrailCliffordXor80_comm_uBarrelFast
    calc
      Q * B = Q * B * (X * X⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = Q * (B * X) * X⁻¹ := by simp only [mul_assoc]
      _ = (QC * B) * X⁻¹ := by
          rw [← hXB]
          dsimp only [QC, X]
          simp only [mul_assoc]
      _ = B * Q * (X * X⁻¹) := by
          rw [hQCB]
          dsimp only [QC, X]
          simp only [mul_assoc]
      _ = B * Q := by rw [mul_inv_cancel, mul_one]
  have hDist : ∀ (P M₁ M₂ : Unitary (2 ^ (fullSysCoreWires 80))),
      unitaryConj P (M₁ * M₂) = unitaryConj P M₁ * unitaryConj P M₂ := fun P M₁ M₂ ↦ by
    unfold unitaryConj
    calc P⁻¹ * (M₁ * M₂) * P = P⁻¹ * M₁ * (P * P⁻¹) * M₂ * P := by simp [mul_assoc]
      _ = (P⁻¹ * M₁ * P) * (P⁻¹ * M₂ * P) := by simp only [mul_assoc]
  have hSwap : ∀ {P : Unitary (2 ^ (fullSysCoreWires 80))}
    (M : Unitary (2 ^ (fullSysCoreWires 80))),
      P * B = B * P → unitaryConj P (unitaryConj B M) = unitaryConj B (unitaryConj P M) :=
    fun {P} M hPB ↦ by
      have hBPinv : B⁻¹ * P⁻¹ = P⁻¹ * B⁻¹ := by
        rw [← mul_inv_rev P B, hPB, mul_inv_rev B P]
      unfold unitaryConj
      calc P⁻¹ * (B⁻¹ * M * B) * P = P⁻¹ * B⁻¹ * M * (B * P) := by simp only [mul_assoc]
        _ = B⁻¹ * P⁻¹ * M * (P * B) := by rw [← hBPinv, hPB]
        _ = B⁻¹ * (P⁻¹ * M * P) * B := by simp only [mul_assoc]
  have hSplitQ : unitaryConj Q (unitaryConj B uPos) =
      unitaryConj B (unitaryConj Q D_tail) * unitaryConj B (unitaryConj Q D_head) := by
    rw [hPos, hSwap _ hQB, hDist Q, hDist B]
  have hSplitQC : unitaryConj QC (unitaryConj B uPos) =
      unitaryConj B (unitaryConj QC D_tail) * unitaryConj B (unitaryConj QC D_head) := by
    rw [hPos, hSwap _ hQCB, hDist QC, hDist B]
  have iCore : ∀ W : Unitary (2 ^ (fullSysCoreWires 80)),
      IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
        (rCat80.basisOutcomeProjector 0) (rCoreSeg.embedUnitary W).1 (rCoreSeg.embedUnitary W).1 :=
    fun W ↦ by
      rw [QRegister.embedUnitary_val]
      exact intertwinesCat_of_disjoint rCoreSeg rCat80 hCoreSeg_disj_Cat80 _ W.1
  let qft := coreQftHadamardPrunedBundle128
  have h654 : r654Seg ora = rCoreSeg.compose (coreElecCosetB1Block ora.hmPay) := by
    apply qreg_ext
    intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · change (r654Seg ora) (Fin.castAdd 3 i) =
        rCoreSeg ((coreElecCosetB1Block ora.hmPay) (Fin.castAdd 3 i))
      unfold r654Seg coreElecCosetB1Block
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      rfl
    · change (r654Seg ora) (Fin.natAdd 3924 j) =
        rCoreSeg ((coreElecCosetB1Block ora.hmPay) (Fin.natAdd 3924 j))
      unfold r654Seg coreElecCosetB1Block
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
      rfl
  have hQftCore : (r654Seg ora).embedUnitary qft.uQft654 = rCoreSeg.embedUnitary Q := by
    rw [h654, QRegister.embedUnitary_compose]
    rfl
  let hLoc := qft.hIntertwinesQft (U_cat_B_normalized 7) (U_cat_B_normalized_col_zero_singleCat 7)
  have iQft : IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
      (rCat80.basisOutcomeProjector 0)
      ((rQSeg ora).embedUnitary qft.uQftCat).1 (rCoreSeg.embedUnitary Q).1 := by
    have i0 := intertwinesCat_topCatSlice_of_localCat (singleCat_seven_le_of_48 le_rfl)
      (r654Seg ora) rCat80 (h654Seg_disj_Cat80 ora) qft.uQftCat qft.uQft654 hLoc
    unfold rQSeg
    rw [← hQftCore, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact i0
  have iQftInv : IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
      (rCat80.basisOutcomeProjector 0)
      ((rQSeg ora).embedUnitary qft.uQftCat⁻¹).1 (rCoreSeg.embedUnitary Q⁻¹).1 := by
    have i0 := intertwinesCat_topCatSlice_of_localCat (singleCat_seven_le_of_48 le_rfl)
      (r654Seg ora) rCat80 (h654Seg_disj_Cat80 ora) qft.uQftCat⁻¹ qft.uQft654⁻¹
      (IntertwinesLocalCat.inv hLoc)
    unfold rQSeg
    rw [embedUnitary_inv_eq rCoreSeg Q, ← hQftCore, ← embedUnitary_inv_eq,
        QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact i0
  have iMid : IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
      (rCat80.basisOutcomeProjector 0) (uQftConjPass2Seg qft ora (unitaryConj B uPos)).1
      (rCoreSeg.embedUnitary (unitaryConj Q (unitaryConj B uPos))).1 := by
    refine intertwinesCat_congr_ops (intertwinesCat_mul_gen iQftInv (intertwinesCat_mul_gen
      (iCore (unitaryConj B uPos)) iQft)) ?_ ?_
    · simp only [uQftConjPass2Seg, Submonoid.coe_mul]
    · unfold unitaryConj
      simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc]
  have hCat : ∀ {M₁ M₂ : Operator (2 ^ (fullSysBEWires 80 + 48))},
      IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
        (rCat80.basisOutcomeProjector 0) M₁ M₂ →
      M₁ * catState48 = M₂ * catState48 := fun {M₁ M₂} h ↦ by
    dsimp only [catState48]
    rw [← Matrix.mul_assoc M₁, ← Matrix.mul_assoc M₂, h.1, h.2.1]
  refine ⟨hSplitQ, hSplitQC, ?_, ?_⟩
  · rw [hCat iMid, ← QRegister.embedUnitary_mul, ← hSplitQ]
  · have iTrail : IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
      (rCat80.basisOutcomeProjector 0) (rCoreSeg.embedUnitary uTrailCliffordXor80⁻¹ *
      (uQftConjPass2Seg qft ora (unitaryConj B uPos) * rCoreSeg.embedUnitary
      uTrailCliffordXor80)).1 (rCoreSeg.embedUnitary (unitaryConj QC (unitaryConj B uPos))).1
      := by
      refine intertwinesCat_congr_ops (intertwinesCat_mul_gen (iCore uTrailCliffordXor80⁻¹)
        (intertwinesCat_mul_gen iMid (iCore uTrailCliffordXor80))) ?_ ?_
      · simp only [Submonoid.coe_mul]
      · rw [← Submonoid.coe_mul, ← Submonoid.coe_mul,
            ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
        refine congrArg (fun U ↦ (rCoreSeg.embedUnitary U).1) ?_
        unfold unitaryConj
        rw [_root_.mul_inv_rev Q uTrailCliffordXor80]
        simp only [QC, mul_assoc]
    rw [hCat iTrail, ← QRegister.embedUnitary_mul, ← hSplitQC]
end MidUnitaryConjZeroRoot
set_option maxRecDepth 65536
open StageBTwoElecQftStream218Inner
  (posCoreWires_eq_4034 selCoreInCoreSum42PG7 selPG7InCoreSum42PG7 partnerLensOnCoreSum42PG7)
namespace StageBPartnerTrueSwapStream218Closure
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires)
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open PosSlots24PartnerMux288 (sandPhase18)
open PosSlots24Barrel3Pass (rDataElec dataActiveSlot)
open MidKickSub33 (pos24TailMag30MidpointB)
open PosPostPrep80MergedVepS3 (uSwapCore3967)
open InterWalkRSum42Hoist (qreg_block_apply)
open Barrel3PassSelectStitch (rCat80 rCoreSeg hCoreSeg_disj_Cat80)
open SingleCatSpine (rTopCatSlice)
open Leaf4Ext48TopStitch (disj_of_val_ne)
open QRegExt
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot partnerLens216)
open ZeroHypSlot0CommAndHMidClosure
  (P_slot0 restrictOfCommSlot0 mul_comm_P_slot0 inv_comm_P_slot0 diagSignUnitary_embed_comm_P_slot0)
open StageAPointPhase128OnStep (activeTwoElecForestFullQftStage128)
open StageBTwoElecQftStream218Inner
  (rCatSlot0Partner rIdSlot0Partner_apply rPG7InActB42_apply dPartnerSkip0
  P_slot0_partnerLensOnCoreSum42PG7_eq_embedMatrix_diagonal
  rCatSlot0Partner_uQft2_comm_rCoreSkip0_diagonal rCoreInActB42_apply rElec0InActB42_apply
  rPartner18InActB42_apply)
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
theorem lensSwapFin_eq_two_replaceIndex {Idx : Type*} {kData : ℕ}
    (L : Slot18Lens kData)
    (idxOf : Fin (2 ^ kData) → Idx)
    (slotReg : Idx → QRegister 18 kData)
    (hTbl : ∀ d, L.tbl d = (slotReg (idxOf d)).extractIndex d)
    (hUpd : ∀ d v, L.updSlot d v = (slotReg (idxOf d)).replaceIndex d v)
    (z : Fin (2 ^ (kData + 18))) :
    let d := (selDataInAct kData).extractIndex z
    let s := idxOf d
    let rSlot := (selDataInAct kData).compose (slotReg s)
    let rMeas := selMeasInAct kData
    ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L z =
      rMeas.replaceIndex (rSlot.replaceIndex z (rMeas.extractIndex z)) (rSlot.extractIndex z) := by
  intro d s rSlot rMeas
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.lensSwapFin, lensSwapPerm,
    ZeroHypElecHadHCompAndPass123Closure.splitDM]
  rw [PureCnotLoadAndSlot18LensRealizes.joinDM_eq_replaceIndex_pair z]
  change rMeas.replaceIndex
    ((selDataInAct kData).replaceIndex z (L.updSlot d (rMeas.extractIndex z)))
      (L.tbl d) = _
  rw [hUpd, hTbl,
      ElecHadTrueSwapHCompClosure.replaceIndex_compose_eq
        (selDataInAct kData) (slotReg s) z (rMeas.extractIndex z),
      ← QRegister.extractIndex_compose (selDataInAct kData) (slotReg s) z]
theorem embedMatrix_injective {k N : ℕ} (r : QRegister k N)
    {A B : Operator (2 ^ k)} (h : r.embedMatrix A = r.embedMatrix B) : A = B := by
  ext x y
  let i := r.replaceIndex ⟨0, Nat.two_pow_pos N⟩ x
  let j := r.replaceIndex ⟨0, Nat.two_pow_pos N⟩ y
  have hij := congrFun (congrFun h i) j
  have henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2 := by
    dsimp only [i, j]
    rw [r.basisSplitEquiv_replaceIndex, r.basisSplitEquiv_replaceIndex]
  rw [QRegister.embedMatrix_apply, QRegister.embedMatrix_apply, ite_eq_left henv,
      r.extractIndex_replaceIndex _ x, r.extractIndex_replaceIndex _ y] at hij
  simpa only [mul_one] using hij
/-- Subregister `(rSub, rMeas18)` (`kSub + 18`) inside `kData + 18`. -/
def selSubPartnerInAct {kSub kData : ℕ} (selSub : QRegister kSub kData) : QRegister
    (kSub + 18) (kData + 18) := ((selDataInAct kData).compose selSub).concat
    (selMeasInAct kData) ((selDataInAct_disj_selMeasInAct kData).compose_left selSub)
theorem matrix_eq_of_mulVec_single_part3 {D : ℕ} {A B : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ j : Fin D, A.mulVec (Pi.single j 1) = B.mulVec (Pi.single j 1)) : A = B := by
  ext i j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun (h j) i
theorem uLensSwap_partnerLens216_eq_embed {kSub kData : ℕ} (selSub : QRegister kSub kData)
    (selCoreSub : QRegister posCoreWires kSub) (selCore : QRegister posCoreWires kData)
    (hCoreComp : selSub.compose selCoreSub = selCore) : uLensSwap (partnerLens216 selCore) =
    (selSubPartnerInAct selSub).embedUnitary (uLensSwap (partnerLens216 selCoreSub)) := by
  let rSP := selSubPartnerInAct selSub
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner,
      PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
  apply Subtype.ext
  apply matrix_eq_of_mulVec_single_part3
  intro g
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
    ZeroHypElecHadHCompAndPass123Closure.permUnitary]
  rw [QRegister.embedUnitary_val]
  dsimp only
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.embedMatrix_permMatrix_mulVec_single]
  have hPerm : (ZeroHypElecHadHCompAndPass123Closure.permMatrix
      (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selCore))).mulVec
        (Pi.single g 1) =
      Pi.single (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selCore) g) 1 :=
        by
    funext i
    rw [Matrix.mulVec_single_one]
    change (if i = _ then (1 : ℂ) else 0) = (Pi.single _ (1 : ℂ) : _ → ℂ) i
    by_cases h : i = ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selCore) g
    · simp [h]
    · simp [h]
  change (ZeroHypElecHadHCompAndPass123Closure.permMatrix
    (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selCore))).mulVec
      (Pi.single g 1) = _
  rw [hPerm]
  refine congrArg (fun idx ↦ Pi.single idx (1 : ℂ)) ?_
  have hDComp : rSP.compose (selDataInAct kSub) = (selDataInAct kData).compose selSub := by
    apply qreg_ext
    intro q
    rw [QRegister.compose_apply, selDataInAct_apply q]
    dsimp only [rSP, selSubPartnerInAct]
    rw [QRegister.concat_apply_left]
  have hMComp : rSP.compose (selMeasInAct kSub) = selMeasInAct kData := by
    apply qreg_ext
    intro j
    rw [QRegister.compose_apply, selMeasInAct_apply (kData := kSub) j]
    dsimp only [rSP, selSubPartnerInAct]
    rw [QRegister.concat_apply_right]
  let z0 := rSP.extractIndex g
  have hSlotEq : partnerActiveSlot selCoreSub ((selDataInAct kSub).extractIndex z0) =
      partnerActiveSlot selCore ((selDataInAct kData).extractIndex g) := by
    have hCoreExtr : selCoreSub.extractIndex ((selDataInAct kSub).extractIndex z0) =
        selCore.extractIndex ((selDataInAct kData).extractIndex g) := by
      dsimp only [z0]
      rw [← QRegister.extractIndex_compose, ← QRegister.extractIndex_compose,
          ← QRegister.compose_assoc, hDComp, QRegister.compose_assoc, hCoreComp,
          QRegister.extractIndex_compose]
    apply Fin.ext
    dsimp only [partnerActiveSlot, dataActiveSlot]
    rw [hCoreExtr]
  have hSlotRegComp : ∀ s' : Fin 218,
      rSP.compose ((selDataInAct kSub).compose (rDataElec selCoreSub s')) =
        (selDataInAct kData).compose (rDataElec selCore s') := fun s' ↦ by
    rw [← QRegister.compose_assoc, hDComp]
    dsimp only [rDataElec]
    rw [← QRegister.compose_assoc, QRegister.compose_assoc _ selSub selCoreSub, hCoreComp,
      QRegister.compose_assoc]
  rw [lensSwapFin_eq_two_replaceIndex (partnerLens216 selCore)
        (partnerActiveSlot selCore) (rDataElec selCore) (fun _ ↦ rfl) (fun _ _ ↦ rfl) g,
      lensSwapFin_eq_two_replaceIndex (partnerLens216 selCoreSub)
        (partnerActiveSlot selCoreSub) (rDataElec selCoreSub) (fun _ ↦ rfl) (fun _ _ ↦ rfl) z0,
      hSlotEq]
  let s := partnerActiveSlot selCore ((selDataInAct kData).extractIndex g)
  let rSlot0 := (selDataInAct kSub).compose (rDataElec selCoreSub s)
  let rMeas0 := selMeasInAct kSub
  have hOuterInner : ∀ {k₁ k₂ N : ℕ} (rOut : QRegister k₁ N) (rIn : QRegister k₂ k₁)
      (x : Fin (2 ^ N)) (y : Fin (2 ^ k₁)) (v : Fin (2 ^ k₂)), rOut.replaceIndex x
      (rIn.replaceIndex y v) = (rOut.compose rIn).replaceIndex (rOut.replaceIndex x y) v := by
    intro _ _ _ rOut rIn x y v
    rw [← ElecHadTrueSwapHCompClosure.replaceIndex_compose_eq,
        QRegister.extractIndex_replaceIndex, QRegister.replaceIndex_replaceIndex]
  rw
    [hOuterInner rSP rMeas0 g (rSlot0.replaceIndex z0 (rMeas0.extractIndex z0))
    (rSlot0.extractIndex z0),
      hOuterInner rSP rSlot0 g z0 (rMeas0.extractIndex z0)]
  dsimp only [z0]
  rw[QRegister.replaceIndex_extractIndex, ← QRegister.extractIndex_compose rSP rMeas0 g,
      ← QRegister.extractIndex_compose rSP rSlot0 g, hMComp, hSlotRegComp s]
private theorem P_slot0_partnerLens216_eq_embed {kSub kData : ℕ}
    (selSub : QRegister kSub kData) (selCoreSub : QRegister posCoreWires kSub)
    (selCore : QRegister posCoreWires kData) (hCoreComp : selSub.compose selCoreSub = selCore)
    : P_slot0 (partnerLens216 selCore) = (selSubPartnerInAct selSub).embedMatrix
    (P_slot0 (partnerLens216 selCoreSub)) := by
  let rSP := selSubPartnerInAct selSub
  have hMComp : rSP.compose (selMeasInAct kSub) = selMeasInAct kData := by
    apply qreg_ext
    intro j
    rw [QRegister.compose_apply, selMeasInAct_apply (kData := kSub) j]
    dsimp only [rSP, selSubPartnerInAct]
    rw [QRegister.concat_apply_right]
  have hPm : rSP.embedMatrix ((selMeasInAct kSub).basisOutcomeProjector 0) =
      (selMeasInAct kData).basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hMComp,
      ← QRegister.basisOutcomeProjector]
  dsimp only [P_slot0]
  rw [uLensSwap_partnerLens216_eq_embed selSub selCoreSub selCore hCoreComp, ← hPm,
      QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
theorem comm_P_slot0_partnerLens216_embed {kSub kData : ℕ} (selSub : QRegister kSub kData)
    (selCoreSub : QRegister posCoreWires kSub) (selCore : QRegister posCoreWires kData)
    (hCoreComp : selSub.compose selCoreSub = selCore) (uSub : Unitary (2 ^ (kSub + 18)))
    (hComm0 : uSub.1 * P_slot0 (partnerLens216 selCoreSub) = P_slot0 (partnerLens216
    selCoreSub) * uSub.1) : ((selSubPartnerInAct selSub).embedUnitary uSub).1 * P_slot0
    (partnerLens216 selCore) = P_slot0 (partnerLens216 selCore) *
    ((selSubPartnerInAct selSub).embedUnitary uSub).1 := by
  rw [QRegister.embedUnitary_val,
    P_slot0_partnerLens216_eq_embed selSub selCoreSub selCore hCoreComp,
      ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul, hComm0]
theorem comm_P_slot0_partnerLens216_of_embed {kSub kData : ℕ} (selSub : QRegister kSub kData)
    (selCoreSub : QRegister posCoreWires kSub) (selCore : QRegister posCoreWires kData)
    (hCoreComp : selSub.compose selCoreSub = selCore) (uSub : Unitary (2 ^ (kSub + 18)))
    (hComm : ((selSubPartnerInAct selSub).embedUnitary uSub).1 * P_slot0 (partnerLens216
    selCore) = P_slot0 (partnerLens216 selCore) * ((selSubPartnerInAct selSub).embedUnitary
    uSub).1) : uSub.1 * P_slot0 (partnerLens216 selCoreSub) = P_slot0
    (partnerLens216 selCoreSub) * uSub.1 := by
  apply embedMatrix_injective (selSubPartnerInAct selSub)
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul,
      ← P_slot0_partnerLens216_eq_embed selSub selCoreSub selCore hCoreComp,
      ← QRegister.embedUnitary_val]
  exact hComm
def selCoreInCorePG7 : QRegister posCoreWires (posCoreWires + 7) :=
  QRegister.block 0 posCoreWires (by omega)
def selPG7InCorePG7 : QRegister 7 (posCoreWires + 7) := QRegister.block posCoreWires 7 le_rfl
def selCorePG7InCoreSum42PG7 : QRegister (posCoreWires + 7) ((posCoreWires + 42) + 7) :=
  selCoreInCoreSum42PG7.concat selPG7InCoreSum42PG7
    (disj_of_val_ne fun i m ↦ by
      simp [selCoreInCoreSum42PG7, selPG7InCoreSum42PG7]
      omega)
noncomputable abbrev partnerLensOnCore : Slot18Lens posCoreWires :=
  partnerLens216 (QRegExt.idReg posCoreWires)
noncomputable abbrev partnerLensOnCorePG7 : Slot18Lens (posCoreWires + 7) :=
  partnerLens216 selCoreInCorePG7
theorem selCorePG7_compose_core :
    selCorePG7InCoreSum42PG7.compose selCoreInCorePG7 = selCoreInCoreSum42PG7 := by
  apply qreg_ext
  intro i
  have h : selCoreInCorePG7 i = Fin.castAdd 7 i := by
    ext
    simp [selCoreInCorePG7]
  rw [QRegister.compose_apply, h, selCorePG7InCoreSum42PG7, QRegister.concat_apply_left]
theorem selCorePG7_compose_pg7 :
    selCorePG7InCoreSum42PG7.compose selPG7InCorePG7 = selPG7InCoreSum42PG7 := by
  apply qreg_ext
  intro m
  have h : selPG7InCorePG7 m = Fin.natAdd posCoreWires m := by
    ext
    simp [selPG7InCorePG7]
  rw [QRegister.compose_apply, h, selCorePG7InCoreSum42PG7, QRegister.concat_apply_right]
noncomputable def uSandCoreP (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    Unitary (2 ^ (posCoreWires + 18)) := ((selDataInAct posCoreWires).concat (selMeasInAct
    posCoreWires) (selDataInAct_disj_selMeasInAct posCoreWires)).embedUnitary (diagSignUnitary
    (sandPhase18 slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign
    (pos24TailMag30MidpointB B hB1 (by omega)))))
theorem uSandCoreP_comm_P_slot0 (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uSandCoreP B hB1 hB27 slot2SwappedTo0).1 * P_slot0 partnerLensOnCore =
      P_slot0 partnerLensOnCore * (uSandCoreP B hB1 hB27 slot2SwappedTo0).1 :=
  diagSignUnitary_embed_comm_P_slot0 partnerLensOnCore _ _
def rCatSlot0PartnerCorePG7 : QRegister (3924 + 3 + 7) ((posCoreWires + 7) + 18) where
  wires :=
    ⟨fun idx ↦
      if h0 : idx.val < 18 then
        selDataInAct (posCoreWires + 7) (selCoreInCorePG7 ⟨idx.val, by
          have :=
          posCoreWires_eq_4034; omega⟩)
      else if h1 : idx.val < 36 then
        selMeasInAct (posCoreWires + 7) ⟨idx.val - 18, by omega⟩
      else if h2 : idx.val < 3924 + 3 then
        selDataInAct (posCoreWires + 7) (selCoreInCorePG7 ⟨idx.val - 18, by
          have :=
          posCoreWires_eq_4034; omega⟩)
      else
        selDataInAct (posCoreWires + 7) (selPG7InCorePG7 ⟨idx.val - (3924 + 3), by
          have :=
          idx.isLt; omega⟩),
     fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt; have hP := posCoreWires_eq_4034
      have hv := congrArg Fin.val hab
      apply Fin.ext
      by_cases ha0 : a.val < 18 <;> by_cases hb0 : b.val < 18
      · simp only [ha0, hb0, ↓reduceDIte, selDataInAct_apply, Fin.val_castAdd,
          selCoreInCorePG7, qreg_block_apply] at hv; omega
      · by_cases hb1 : b.val < 36 <;> by_cases hb2 : b.val < 3924 + 3 <;>
          simp only [ha0, hb0, hb1, hb2, ↓reduceDIte, selDataInAct_apply, selMeasInAct_apply,
            Fin.val_castAdd, Fin.val_natAdd, selCoreInCorePG7, selPG7InCorePG7,
              qreg_block_apply] at hv <;> omega
      · by_cases ha1 : a.val < 36 <;> by_cases ha2 : a.val < 3924 + 3 <;>
          simp only [ha0, hb0, ha1, ha2, ↓reduceDIte, selDataInAct_apply, selMeasInAct_apply,
            Fin.val_castAdd, Fin.val_natAdd, selCoreInCorePG7, selPG7InCorePG7,
              qreg_block_apply] at hv <;> omega
      · by_cases ha1 : a.val < 36 <;> by_cases hb1 : b.val < 36 <;>
          by_cases ha2 : a.val < 3924 + 3 <;> by_cases hb2 : b.val < 3924 + 3 <;>
          simp only [ha0, hb0, ha1, hb1, ha2, hb2, ↓reduceDIte, selDataInAct_apply,
            selMeasInAct_apply,
            Fin.val_castAdd, Fin.val_natAdd, selCoreInCorePG7, selPG7InCorePG7,
              qreg_block_apply] at hv <;> omega⟩
theorem selSubPartner_corePG7_compose_rCat :
    (selSubPartnerInAct selCorePG7InCoreSum42PG7).compose rCatSlot0PartnerCorePG7 =
      rCatSlot0Partner := by
  have hP := posCoreWires_eq_4034
  apply qreg_ext
  intro idx
  have hi := idx.isLt
  rw [QRegister.compose_apply]
  by_cases h2 : idx.val < 3924 + 3
  · conv_rhs =>
      rw [show idx = Fin.castAdd 7 ⟨idx.val, h2⟩ from rfl,
          rCatSlot0Partner, QRegister.concat_apply_left, rIdSlot0Partner_apply]
    by_cases h0 : idx.val < 18
    · rw [dite_eq_left h0]
      have hL : rCatSlot0PartnerCorePG7 idx =
          Fin.castAdd 18 (selCoreInCorePG7 ⟨idx.val, by omega⟩) := by
        ext
        simp [rCatSlot0PartnerCorePG7, h0, selDataInAct_apply]
      apply Fin.ext
      rw [hL, selSubPartnerInAct, QRegister.concat_apply_left, rElec0InActB42_apply,
          QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          ← QRegister.compose_apply selCorePG7InCoreSum42PG7 selCoreInCorePG7,
          selCorePG7_compose_core]
      simp [selCoreInCoreSum42PG7]
    · by_cases h1 : idx.val < 36
      · rw [dite_eq_right h0, dite_eq_left h1]
        have hL : rCatSlot0PartnerCorePG7 idx =
            Fin.natAdd (posCoreWires + 7) ⟨idx.val - 18, by omega⟩ := by
          ext
          simp [rCatSlot0PartnerCorePG7, h0, h1, selMeasInAct_apply]
        apply Fin.ext
        rw [hL, selSubPartnerInAct, QRegister.concat_apply_right, rPartner18InActB42_apply,
            selMeasInAct_apply, Fin.val_natAdd]
      · rw [dite_eq_right h0, dite_eq_right h1]
        have hL : rCatSlot0PartnerCorePG7 idx =
            Fin.castAdd 18 (selCoreInCorePG7 ⟨idx.val - 18, by omega⟩) := by
          ext
          simp [rCatSlot0PartnerCorePG7, h0, h1, h2, selDataInAct_apply]
        apply Fin.ext
        rw [hL, selSubPartnerInAct, QRegister.concat_apply_left, rCoreInActB42_apply,
            QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
            ← QRegister.compose_apply selCorePG7InCoreSum42PG7 selCoreInCorePG7,
            selCorePG7_compose_core]
        simp [selCoreInCoreSum42PG7]
  · have h0 : ¬ idx.val < 18 := by omega
    have h1 : ¬ idx.val < 36 := by omega
    let m : Fin 7 := ⟨idx.val - (3924 + 3), by omega⟩
    have hL : rCatSlot0PartnerCorePG7 idx = Fin.castAdd 18 (selPG7InCorePG7 m) := by
      ext
      simp [rCatSlot0PartnerCorePG7, h0, h1, h2, selDataInAct_apply, m]
    have hx : idx = Fin.natAdd (3924 + 3) m := by
      ext
      dsimp [m]
      omega
    apply Fin.ext
    rw[hx, rCatSlot0Partner, QRegister.concat_apply_right, ← hx, hL, selSubPartnerInAct,
        QRegister.concat_apply_left, QRegister.compose_apply, selDataInAct_apply,
        Fin.val_castAdd, ← QRegister.compose_apply selCorePG7InCoreSum42PG7 selPG7InCorePG7,
        selCorePG7_compose_pg7, rPG7InActB42_apply m]
    simp [selPG7InCoreSum42PG7]
noncomputable def uQft2CorePG7P : Unitary (2 ^ ((posCoreWires + 7) + 18)) :=
  rCatSlot0PartnerCorePG7.embedUnitary activeTwoElecForestFullQftStage128.uCat
noncomputable def uInnerCorePG7P (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : Unitary (2 ^ ((posCoreWires + 7) + 18)) := uQft2CorePG7P⁻¹ *
    ((selSubPartnerInAct selCoreInCorePG7).embedUnitary (uSandCoreP B hB1 hB27
    slot2SwappedTo0) * uQft2CorePG7P)
theorem uInnerCorePG7P_comm_P_slot0 (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uInnerCorePG7P B hB1 hB27 slot2SwappedTo0).1 * P_slot0 partnerLensOnCorePG7 =
      P_slot0 partnerLensOnCorePG7 * (uInnerCorePG7P B hB1 hB27 slot2SwappedTo0).1 := by
  have hQft : uQft2CorePG7P.1 * P_slot0 partnerLensOnCorePG7 =
      P_slot0 partnerLensOnCorePG7 * uQft2CorePG7P.1 := by
    refine comm_P_slot0_partnerLens216_of_embed selCorePG7InCoreSum42PG7 selCoreInCorePG7
      selCoreInCoreSum42PG7 selCorePG7_compose_core uQft2CorePG7P ?_
    unfold uQft2CorePG7P
    rw [← QRegister.embedUnitary_compose (selSubPartnerInAct selCorePG7InCoreSum42PG7)
          rCatSlot0PartnerCorePG7 activeTwoElecForestFullQftStage128.uCat,
        selSubPartner_corePG7_compose_rCat]
    change (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat).1 * P_slot0
      partnerLensOnCoreSum42PG7 = P_slot0 partnerLensOnCoreSum42PG7 *
      (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat).1
    rw [P_slot0_partnerLensOnCoreSum42PG7_eq_embedMatrix_diagonal]
    exact rCatSlot0Partner_uQft2_comm_rCoreSkip0_diagonal dPartnerSkip0
  exact mul_comm_P_slot0 _ (inv_comm_P_slot0 _ hQft) (mul_comm_P_slot0 _
    (comm_P_slot0_partnerLens216_embed selCoreInCorePG7 (QRegExt.idReg posCoreWires)
    selCoreInCorePG7 rfl _ (uSandCoreP_comm_P_slot0 B hB1 hB27 slot2SwappedTo0)) hQft)
noncomputable def uStageBCorePG7Raw (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    Unitary (2 ^ (posCoreWires + 7)) :=
  restrictOfCommSlot0 partnerLensOnCorePG7
    (uInnerCorePG7P B (by omega) hB27 true) (uInnerCorePG7P_comm_P_slot0 B (by omega) hB27 true)
set_option exponentiation.threshold 4200 in
noncomputable def uStageBCorePG7 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : Unitary
    (2 ^ (fullSysCoreWires 80 + 7)) := selCoreInCorePG7.embedUnitary uSwapCore3967 *
    (uStageBCorePG7Raw B hB6 hB27 * selCoreInCorePG7.embedUnitary uSwapCore3967)
def rCoreTopCat7InSeg : QRegister (fullSysCoreWires 80 + 7) (fullSysBEWires 80 + 48) :=
  rCoreSeg.concat (rCat80.compose (rTopCatSlice 7 48 (by decide)))
    (hCoreSeg_disj_Cat80.compose_right _)
/-- Canonical `4,119`-wire segment Stage-B catalyzed unitary (`fullSysBEWires 80 + 48`). -/
noncomputable def uStageBSeg (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  rCoreTopCat7InSeg.embedUnitary (uStageBCorePG7 B hB6 hB27)
end StageBPartnerTrueSwapStream218Closure
open SingleBarrelPass123Fold (rSpectatorElec3906)
namespace BoothOpt_09_ButterflyPass13ThreeBarrelAdap
open ButterflyBarrelSlot0Conj (spectatorElecReg ActsAsIdOnSpectatorWires PreservesHigh3924On)
open FullSysCatSegmentBridge (fullSysCoreWires)
open Barrel3PassCommuteHelpers (flipElec0Bit5Fn)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open MomSlot0LocalAndMomCombine288 (phaseDiagUnitary_val_eq_diag)
open Pass1InnerAndIdx128 (slot0LocalXorBit5PhaseBit uSlot0LocalXorBit5_eq_phaseDiagUnitary)
open Pass1Leaf273 (hm22_80)
open Leaf1Pass1And3Width204
  (rCoreBlock4 t4WinPerm t4WinPerm_apply uApexShift4 uPass1InnerT4 uSlot4ApexCatT4 uSlot4AxisCatT4)
open SelectPass13Gen (commutesWithReg_diagonal_of_agreeOutside)
open SingleBarrelPass123Fold
  (rSpectatorElec3906Cat4 rCoreBlock4_compose_rSpectatorElec3906
  slot0LocalPhaseBit_congr_outside_spectator3906
  commutesWithReg_rSpectatorElec3906Cat4_uSlot4ApexCatT4)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open SpecsAux SpecsAux.SpecMirror
open QRegExt
private theorem spectatorElecReg_rCoreBlock4_eq :
    spectatorElecReg (rCoreBlock4 80) = rSpectatorElec3906Cat4 := by
  apply qreg_ext
  intro t
  ext
  simp [spectatorElecReg, rCoreBlock4, rSpectatorElec3906Cat4, QRegister.block]
/-- `0`-hypothesis `ActsAsIdOnSpectatorWires` for `uSlot4ApexCatT4 hm22_80`. -/
private theorem actsAsIdOnSpectatorWires_uSlot4ApexCatT4 :
    ActsAsIdOnSpectatorWires (rCoreBlock4 80) (uSlot4ApexCatT4 hm22_80) := by
  intro A
  rw [spectatorElecReg_rCoreBlock4_eq]
  exact commutesWithReg_rSpectatorElec3906Cat4_uSlot4ApexCatT4 A
/-- `0`-hypothesis `ActsAsIdOnSpectatorWires` for `(uSlot4ApexCatT4 hm22_80)⁻¹` (`Pass 3` inner). -/
theorem actsAsIdOnSpectatorWires_uSlot4ApexCatT4_inv :
    ActsAsIdOnSpectatorWires (rCoreBlock4 80) (uSlot4ApexCatT4 hm22_80)⁻¹ :=
  actsAsIdOnSpectatorWires_uSlot4ApexCatT4.inv
/-- `0`-hypothesis `ActsAsIdOnSpectatorWires` for `uPass1InnerT4` (`Pass 1` inner). -/
theorem actsAsIdOnSpectatorWires_uPass1InnerT4 :
    ActsAsIdOnSpectatorWires (rCoreBlock4 80) uPass1InnerT4 := by
  unfold uPass1InnerT4
  refine ActsAsIdOnSpectatorWires.mul ?_ actsAsIdOnSpectatorWires_uSlot4ApexCatT4
  intro A
  rw [spectatorElecReg_rCoreBlock4_eq, ← rCoreBlock4_compose_rSpectatorElec3906,
      QRegister.embedUnitary_val, QRegister.embedMatrix_compose,
      ← (rCoreBlock4 80).embedMatrix_mul, ← (rCoreBlock4 80).embedMatrix_mul]
  refine congrArg (rCoreBlock4 80).embedMatrix ?_
  rw [uSlot0LocalXorBit5_eq_phaseDiagUnitary, phaseDiagUnitary_val_eq_diag]
  refine commutesWithReg_diagonal_of_agreeOutside rSpectatorElec3906 _ ?_ A
  intro i j ho
  unfold slot0LocalXorBit5PhaseBit
  refine congrArg (fun b : ZMod 2 ↦ (-1 : ℂ) ^ b.val)
    (slot0LocalPhaseBit_congr_outside_spectator3906 lambdaSlot0TeHi fun q hq ↦ ?_)
  have hqq (hLt : q.val < fullSysCoreWires 80) :
      (⟨q.val, hLt⟩ : Wire (fullSysCoreWires 80)) = q := Fin.ext rfl
  rw [hqq]
  dsimp only [flipElec0Bit5Fn]
  rw [ho q hq]
/-- `0`-hypothesis `PreservesHigh3924On` for `uSlot4ApexCatT4 hm22_80`. -/
private theorem preservesHigh3924On_uSlot4ApexCatT4 :
    PreservesHigh3924On (rCoreBlock4 80) (uSlot4ApexCatT4 hm22_80) := by
  have hShift : ∀ δ : BitAssignment (fullSysCoreWires 80) → ℤ,
      PreservesHigh3924On (rCoreBlock4 80) (uApexShift4 (fullSysCoreWires 80) δ) := fun δ ↦ by
    unfold uApexShift4
    refine PreservesHigh3924On.mul ?_ (PreservesHigh3924On.of_diagonal _ _ _ rfl)
    intro w _ b
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, BridgeFermionicComm.permutationUnitary_apply]
    by_cases hij : i = t4WinPerm (fullSysCoreWires 80) δ j
    · subst hij
      simp only [↓reduceIte, one_mul, mul_one]
      have hq : (rCoreBlock4 80) w = Fin.castAdd 4 w := Fin.ext (Nat.zero_add w.val)
      have hEx : (QRegister.singleton ((rCoreBlock4 80) w)).extractIndex
          (t4WinPerm (fullSysCoreWires 80) δ j) =
          (QRegister.singleton ((rCoreBlock4 80) w)).extractIndex j := by
        apply (basisBitsEquiv 1).injective
        funext u
        change basisBits 1 _ u = basisBits 1 _ u
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        change basisBits (fullSysCoreWires 80 + 4) (t4WinPerm (fullSysCoreWires 80) δ j)
          ((rCoreBlock4 80) w) = basisBits (fullSysCoreWires 80 + 4) j ((rCoreBlock4 80) w)
        rw [hq, t4WinPerm_apply (fullSysCoreWires 80) δ j,
            JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
        let p := DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 j
        have hj : j = (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4).symm (p.1, p.2) := by
          dsimp only [p]
          rw [Prod.mk.eta, Equiv.symm_apply_apply]
        conv_rhs => rw [hj, JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
      rw [hEx]
    · simp [hij]
  have hAx : ∀ w : Fin 3, PreservesHigh3924On (rCoreBlock4 80) (uSlot4AxisCatT4 false hm22_80 w) :=
    fun w ↦ by
      unfold uSlot4AxisCatT4
      refine PreservesHigh3924On.mul (hShift _) ?_
      apply PreservesHigh3924On.of_diagonal (rCoreBlock4 80)
      exact (QRegister.embedUnitary_val _ _).trans (embedMatrix_diagonal_eq (rCoreBlock4 80) _)
  unfold uSlot4ApexCatT4
  exact (hAx 2).mul ((hAx 1).mul (hAx 0))
/-- `0`-hypothesis `PreservesHigh3924On` for `(uSlot4ApexCatT4 hm22_80)⁻¹` (`Pass 3` inner). -/
theorem preservesHigh3924On_uSlot4ApexCatT4_inv : PreservesHigh3924On (rCoreBlock4 80)
    (uSlot4ApexCatT4 hm22_80)⁻¹ := preservesHigh3924On_uSlot4ApexCatT4.inv
/-- `0`-hypothesis `PreservesHigh3924On` for `uPass1InnerT4` (`Pass 1` inner). -/
theorem preservesHigh3924On_uPass1InnerT4 :
    PreservesHigh3924On (rCoreBlock4 80) uPass1InnerT4 := by
  unfold uPass1InnerT4
  refine PreservesHigh3924On.mul ?_ preservesHigh3924On_uSlot4ApexCatT4
  apply PreservesHigh3924On.of_diagonal (rCoreBlock4 80)
  rw [QRegister.embedUnitary_val, uSlot0LocalXorBit5_eq_phaseDiagUnitary,
      phaseDiagUnitary_val_eq_diag, embedMatrix_diagonal_eq]
end BoothOpt_09_ButterflyPass13ThreeBarrelAdap
namespace CoinBarrelPureCnotLoad
open CoinDispatchedBarrel288
/-! Self-inverse property `(uBarrelFast (le_refl 80))⁻¹ = uBarrelFast (le_refl 80)`. -/
open SpecsAux SpecsAux.SpecMirror
@[simp] theorem uBarrelFast80_inv : (uBarrelFast (le_refl 80))⁻¹ = uBarrelFast (le_refl 80) :=
  uBarrelFast_inv (le_refl 80)
end CoinBarrelPureCnotLoad
end SharedScope
end SlimStageBOuterDepsC1

noncomputable section SlimStageBOuterDepsC2

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
section SharedScope
local instance (priority := 1000000) instNeZeroAux0c2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority :=
  1000000) instGroupUnitaryFast_SlimStageBOuterDepsC2 (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_SlimStageBOuterDepsC2 (D : ℕ) : Semigroup (Operator.Unitary D)
  :=
  MulMemClass.toSemigroup _
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
namespace BarrelPass2AndHeld3PassSelectStitch
section ImplK2
set_option maxRecDepth 131072
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires disjointWires_compose_of_disjoint)
open CoinDispatchedBarrel288 (uBarrelFast)
open InterWalkRSum42Hoist
  (qreg_ext kFull80 rAct0 rSegOrig rSegFull rCTFull rCoreFull rPG48Full E_rawStream42
  hCoreFull_disj_PG48Full FixesLow3924 h3924_core h3924_cat)
open Pass1Leaf273 (hm22_80)
open Barrel3PassSelectStitch (rCTSeg rCoreSeg rSegFull_compose_rCTSeg)
open Leaf1Pass1And3Width204
  (compose_selCT4InCT_eq rCoreBlock4 selCT4InCT uPass1InnerT4 uSlot4ApexCatT4)
open Leaf4Ext48TopStitch (CommutesWithReg rCtrl3InCore rCtrl3InCoreCat rPGIdle rPGIdleOrig)
open SelectHoistLemmas (rCtrl3InSeg)
open SelectExtStitch (rCoreFull_compose_rCtrl3InCore)
open SelectPass13Gen
  (rT4Full hCoreFull_disj_rT4Full commutesWithReg_rCtrl3InCoreCat4_uSlot4ApexCatT4)
open Width136KIdle12ZeroPenaltyBridge (rCT4Full_disj_rExt42Idle12)
open HeldStreamFoldedPass123Bridge
  (rCTSeg_comm_E_rawStream42_of_preservesRaw fixesLow3924_uSlot4ApexCatT4
  isLow3924Prefix_selCT4InCT)
open Barrel3PassCommuteHelpers (uSlot0LocalXorBit5)
open InterWalkRSum42Hoist
  (PreservesRawStream42 fixesLow3924_embedMatrix_prefix isLow3924Prefix_block0)
open SelectHoistLemmas (rSegFull_compose_rCtrl3InSeg rSegFull_eq_rAct0_compose_rSegOrig)
open HeldStreamFoldedPass123Bridge
  (preservesRawStream42_embedMatrix_prefix fixesLow3924_uSlot0LocalXorBit5)
/-- Unbarreled `Pass 1` inner segment unitary `(selCT4InCT 80).embedUnitary uPass1InnerT4`. -/
noncomputable abbrev uPass1InnerSeg : Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  rCTSeg.embedUnitary ((selCT4InCT 80).embedUnitary uPass1InnerT4)
/-- Unbarreled `Pass 3` inner segment unitary `(selCT4InCT 80).embedUnitary (uSlot4ApexCatT4
  hm22_80)⁻¹`. -/
noncomputable abbrev uPass3InnerSeg : Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  rCTSeg.embedUnitary ((selCT4InCT 80).embedUnitary (uSlot4ApexCatT4 hm22_80)⁻¹)
/-- Clean-`rWork`-only adapter for any `T4`-seam `(rC, rT4, rWork)` circuit (`0` active wires
  borrowed). -/
noncomputable def stepT4CleanRWork {mWork : ℕ} (dT4 : ∀ {Var : Type} {n : ℕ}, Var → (rC :
    QRegister (fullSysCoreWires 80) n) → (rT4 : QRegister 4 n) → (rRest : QRegister mWork n)
    → rC.DisjointWires rT4 → rC.DisjointWires rRest → rT4.DisjointWires rRest → DynamicCircuit
    Var n) {Var : Type} {n : ℕ} (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
    dT4 v (rAct.compose rCoreFull) (rAct.compose rT4Full) rWork
    (disjointWires_compose_of_disjoint rAct hCoreFull_disj_rT4Full)
    (hDisj.compose_left rCoreFull) (hDisj.compose_left rT4Full)
open SelectExtStitch (commutesWithReg_unitary_inv_ext)
open SelectPass13Gen
  (rCoreBlock4_compose_rCtrl3InCore commutesWithReg_rCtrl3InCore_uSlot0LocalXorBit5)
open HeldStreamFoldedPass123Bridge (h3924_ct4)
theorem selCT4InCT_comm_rCtrl3InSeg_and_rPGIdle12
    (u4 : Unitary (2 ^ (fullSysCoreWires 80 + 4)))
    (hu4 : CommutesWithReg (rCtrl3InCoreCat 4) u4.1) : CommutesWithReg rCtrl3InSeg
    (rCTSeg.embedUnitary ((selCT4InCT 80).embedUnitary u4)).1 ∧ CommutesWithReg
    (rPGIdleOrig 12 (by decide)) (rSegOrig.embedUnitary (rCTSeg.embedUnitary ((selCT4InCT
    80).embedUnitary u4))).1 := by
  have hComp4 : (rCTSeg.compose (selCT4InCT 80)).compose (rCtrl3InCoreCat 4) = rCtrl3InSeg := by
    apply qreg_ext; intro t
    exact rSegFull.wires.injective (by
      have hc : rCtrl3InCoreCat 4 t = rCoreBlock4 80 (rCtrl3InCore t) := by
        ext; simp [rCtrl3InCoreCat, rCtrl3InCore, rCoreBlock4, QRegister.block]
      change rSegFull (rCTSeg (selCT4InCT 80 (rCtrl3InCoreCat 4 t))) = rSegFull (rCtrl3InSeg t)
      rw [hc]
      have hEqCT4 := compose_selCT4InCT_eq rCoreFull rPG48Full hCoreFull_disj_PG48Full
      change (rSegFull.compose rCTSeg) (selCT4InCT 80 (rCoreBlock4 80 (rCtrl3InCore t))) =
        (rSegFull.compose rCtrl3InSeg) t
      rw [rSegFull_compose_rCTSeg, rSegFull_compose_rCtrl3InSeg,
        ← rCoreFull_compose_rCtrl3InCore]
      change (rCTFull.compose (selCT4InCT 80)) (rCoreBlock4 80 (rCtrl3InCore t)) = _
      rw [hEqCT4]
      have hb : rCoreBlock4 80 (rCtrl3InCore t) = Fin.castAdd 4 (rCtrl3InCore t) := by
        ext; simp [rCoreBlock4, QRegister.block]
      rw [hb, QRegister.concat_apply_left]; rfl)
  refine ⟨?_, ?_⟩
  · rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, ← hComp4]
    exact CommutesWithReg.embedMatrix _ hu4
  · have hDisjOrig : (rSegOrig.compose (rCTSeg.compose (selCT4InCT 80))).DisjointWires
        (rPGIdleOrig 12 (by decide)) := by
      rw [QRegister.disjoint_iff]; intro i q h
      have hAct := congrArg rAct0 h
      change (rAct0.compose (rSegOrig.compose (rCTSeg.compose (selCT4InCT 80)))) i =
        (rPGIdle 12 (by decide)) q at hAct
      rw [← QRegister.compose_assoc, ← rSegFull_eq_rAct0_compose_rSegOrig,
        ← QRegister.compose_assoc, rSegFull_compose_rCTSeg] at hAct
      exact rCT4Full_disj_rExt42Idle12.ne i (Fin.natAdd 42 q)
        (by
          simpa only [Leaf4Ext48TopStitch.rExt42IdleFull,
          QRegister.concat_apply_right] using hAct)
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint hDisjOrig u4.1
theorem uPass1InnerSeg_and_uPass3InnerSeg_comm_rawStream_ctrl3_idle12 :
    ((rSegFull.embedUnitary uPass1InnerSeg).1 * E_rawStream42 = E_rawStream42 *
    (rSegFull.embedUnitary uPass1InnerSeg).1 ∧ CommutesWithReg rCtrl3InSeg uPass1InnerSeg.1 ∧
    CommutesWithReg (rPGIdleOrig 12 (by decide)) (rSegOrig.embedUnitary uPass1InnerSeg).1) ∧
    ((rSegFull.embedUnitary uPass3InnerSeg).1 * E_rawStream42 = E_rawStream42 *
    (rSegFull.embedUnitary uPass3InnerSeg).1 ∧ CommutesWithReg rCtrl3InSeg uPass3InnerSeg.1 ∧
    CommutesWithReg (rPGIdleOrig 12 (by decide)) (rSegOrig.embedUnitary uPass3InnerSeg).1)
    := by
  have hS0Raw : PreservesRawStream42 h3924_ct4 ((rCoreBlock4 80).embedUnitary
      (uSlot0LocalXorBit5 (le_refl 80)
      LiteralKineticAndMidpoint128.lambdaSlot0TeHi)).1 :=
      (fixesLow3924_embedMatrix_prefix (isLow3924Prefix_block0 h3924_core _ _)
      fixesLow3924_uSlot0LocalXorBit5).preservesRawStream42
  have hP1Raw : PreservesRawStream42 h3924_cat ((selCT4InCT 80).embedUnitary uPass1InnerT4).1 := by
    rw [QRegister.embedUnitary_val]
    refine preservesRawStream42_embedMatrix_prefix isLow3924Prefix_selCT4InCT ?_
    unfold uPass1InnerT4
    exact hS0Raw.mul fixesLow3924_uSlot4ApexCatT4.preservesRawStream42
  have hP3Raw : PreservesRawStream42 h3924_cat
      ((selCT4InCT 80).embedUnitary (uSlot4ApexCatT4 hm22_80)⁻¹).1 := by
    rw [QRegister.embedUnitary_val]
    have hInv : FixesLow3924 h3924_ct4 ((uSlot4ApexCatT4 hm22_80)⁻¹).1 :=
      fixesLow3924_uSlot4ApexCatT4.unitary_inv
    exact preservesRawStream42_embedMatrix_prefix isLow3924Prefix_selCT4InCT
      hInv.preservesRawStream42
  have hP1C : CommutesWithReg (rCtrl3InCoreCat 4) uPass1InnerT4.1 := by
    unfold uPass1InnerT4
    have hS0C : CommutesWithReg (rCtrl3InCoreCat 4) ((rCoreBlock4 80).embedUnitary
        (uSlot0LocalXorBit5 (le_refl 80)
        LiteralKineticAndMidpoint128.lambdaSlot0TeHi)).1 := by
      rw [QRegister.embedUnitary_val, ← rCoreBlock4_compose_rCtrl3InCore]
      exact CommutesWithReg.embedMatrix (rCoreBlock4 80)
        commutesWithReg_rCtrl3InCore_uSlot0LocalXorBit5
    rw [Submonoid.coe_mul]
    exact hS0C.mul commutesWithReg_rCtrl3InCoreCat4_uSlot4ApexCatT4
  have hP3C : CommutesWithReg (rCtrl3InCoreCat 4) ((uSlot4ApexCatT4 hm22_80)⁻¹).1 :=
    commutesWithReg_unitary_inv_ext commutesWithReg_rCtrl3InCoreCat4_uSlot4ApexCatT4
  obtain ⟨h1C, h1I⟩ := selCT4InCT_comm_rCtrl3InSeg_and_rPGIdle12 uPass1InnerT4 hP1C
  obtain ⟨h3C, h3I⟩ := selCT4InCT_comm_rCtrl3InSeg_and_rPGIdle12 (uSlot4ApexCatT4 hm22_80)⁻¹ hP3C
  exact ⟨⟨rCTSeg_comm_E_rawStream42_of_preservesRaw hP1Raw, h1C, h1I⟩,
         ⟨rCTSeg_comm_E_rawStream42_of_preservesRaw hP3Raw, h3C, h3I⟩⟩
/-- Segment-level 6-step Single-Barrel Form-A folded unitary
`B_fast * (P3_in * (uStageBSeg * (uStageASeg * (P1_in * B_fast))))` on `fullSysBEWires 80 + 48`. -/
noncomputable def uSingleBarrelFolded6Seg
    (uStageASeg uStageBSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))) :
    Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  let uB := rCoreSeg.embedUnitary (uBarrelFast (le_refl 80))
  uB * (uPass3InnerSeg * (uStageBSeg * (uStageASeg * (uPass1InnerSeg * uB))))
/-- Full `kFull80` 6-step Single-Barrel Form-A folded unitary wrapping arbitrary stream-assisted
`uStageAFull` and `uStageBFull`. -/
noncomputable def uSingleBarrelFolded6Full
    (uStageAFull uStageBFull : Unitary (2 ^ kFull80)) : Unitary (2 ^ kFull80) :=
  let uBFull := rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))
  uBFull * (rSegFull.embedUnitary uPass3InnerSeg *
    (uStageBFull * (uStageAFull * (rSegFull.embedUnitary uPass1InnerSeg * uBFull))))
end ImplK2
end BarrelPass2AndHeld3PassSelectStitch
open HoistedSwapSelectBridge (unitaryConj)
open ZeroHypStageABToUFoldedPass123SegAndCompac (uHeadPhase80Mod4Eff)
open ZeroHypCatState48StageABMidCoreReductionAn (catState48)
set_option maxRecDepth 65536
namespace SingleBarrel8StepClean
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore (IntertwinesCat)
open FullSysCatSegmentBridge
  (FullSysSelectOracleBundle fullSysCoreWires fullSysBEWires fullSysQftCoreUnitary iSlot0 iSlot1
  iSlot2)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (U_cat_B_normalized_col_zero_singleCat rTopCatSlice)
open SingleCatClosure (intertwinesCat_topCatSlice_of_localCat)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open InterWalkRSum42Hoist (kFull80 rSegOrig rSegFull embedUnitary_inv_symm)
open Barrel3PassSelectStitch (hm6_80 rCoreSeg rCTSeg rCat80 hCoreSeg_disj_Cat80 uTrailCliffordXor80)
open Pass1Leaf273
  (hm22_80 uPass1Cat uPass1Eff uPass1Cat_intertwinesLocal uPass3Cat uPass3Eff
  uPass3Cat_intertwinesLocal col0_eq_phaseGradKet48)
open Leaf1Pass1And3Width204
  (selCT4InCT rCoreBlock4 embed_selCT4InCT_uPass1CatT4 embed_selCT4InCT_uSlot4ApexCatT4)
open CoinDispatchedBarrel288 (uBarrelFast uBarrelFast_comm_high_wire)
open Leaf4Ext48TopStitch (CommutesWithReg rPGIdleOrig)
open SelectHoistLemmas (rCtrl3InSeg pCoinSlack010Seg)
open SelStitchHelper
  (selCT4InCT_compose_rCoreBlock4 rCTSeg_compose_rCoreInCT80 comm_pCoinSlack010Core_of_comm_coin3
  pCoinSlack010CT4_eq_slot1_mul uSlot4ApexCatT4_inv_mul_slot1_one uPass1Cat_mul_pCoinSlack010Seg)
open HeldStreamFoldedPass123Bridge (E_rawSegExt E_rawCtrl3Ext)
open SingleBarrel7StepSelectAux (uFoldedPass123Seg)
open CoinBarrelPureCnotLoad (uBarrelFast80_inv)
open BarrelPass2AndHeld3PassSelectStitch (uPass1InnerSeg uPass3InnerSeg uSingleBarrelFolded6Seg)
open MidUnitaryConjZeroRoot
  (uPosTail80Mod4OfB rhs_stageAB_mid_ofB_mul_catState48_eq_tail_mul_head_zeroHyp)
section Part1B_Ghost334AndSingleBarrel6Step
theorem unitaryConj_eq_inv_mul {d : ℕ} (A B : Unitary d) :
    unitaryConj A B = A⁻¹ * B * A := rfl
/-- Pushes `U_cat * P_Cat0` rightward past any operator satisfying `IntertwinesCat`. -/
theorem mul_catOp_of_intertwinesCat {N : ℕ} {U_cat P_Cat0 A_cat A_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff) : A_cat * (U_cat * P_Cat0) =
    (U_cat * P_Cat0) * A_eff := by
  calc A_cat * (U_cat * P_Cat0)
    _ = A_cat * U_cat * P_Cat0 := (Matrix.mul_assoc A_cat U_cat P_Cat0).symm
    _ = U_cat * A_eff * P_Cat0 := hA.1
    _ = U_cat * (A_eff * P_Cat0) := Matrix.mul_assoc U_cat A_eff P_Cat0
    _ = U_cat * (P_Cat0 * A_eff) := by rw [hA.2.2]
    _ = (U_cat * P_Cat0) * A_eff := (Matrix.mul_assoc U_cat P_Cat0 A_eff).symm
theorem unitaryConj_fixes_proj {d : ℕ} (A B : Unitary d) (P : Matrix (Fin d) (Fin d) ℂ)
    (hComm : A.1 * P = P * A.1) (hFix : B.1 * P = P) : (unitaryConj A B).1 * P = P := by
  have hInvP : (A⁻¹).1 * (A.1 * P) = P := by
    rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
      Matrix.one_mul]
  calc (unitaryConj A B).1 * P
    _ = (A⁻¹).1 * (B.1 * (A.1 * P)) := by
      simp only [unitaryConj, Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (A⁻¹).1 * ((B.1 * P) * A.1) := by rw [hComm]; simp only [Matrix.mul_assoc]
    _ = (A⁻¹).1 * (A.1 * P) := by rw [hFix, ← hComm]
    _ = P := hInvP
theorem mul_fixes_proj {d : ℕ} {A B : Unitary d} {P : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.1 * P = P) (hB : B.1 * P = P) : (A * B).1 * P = P := by
  rw [Submonoid.coe_mul, Matrix.mul_assoc, hB, hA]
theorem rCTSeg_eq_concat_topCat48 : (rCoreSeg.concat (rCat80.compose (rTopCatSlice 48 48
    (le_refl 48))) (hCoreSeg_disj_Cat80.compose_right _)) = rCTSeg := rfl
theorem rCTSeg_selCT4_rCoreBlock4_eq_rCoreSeg :
    (rCTSeg.compose (selCT4InCT 80)).compose (rCoreBlock4 80) = rCoreSeg := by
  rw [QRegister.compose_assoc, selCT4InCT_compose_rCoreBlock4, rCTSeg_compose_rCoreInCT80]
theorem rCTSeg_mul_catState48_of_local (uCat : Unitary (2 ^ (fullSysCoreWires 80 + 48)))
    (uEff : Unitary (2 ^ (fullSysCoreWires 80))) (hLoc :
    FullSysCatSegmentBridge.IntertwinesLocalCat (U_cat_B_normalized
    48) uCat uEff) : (rCTSeg.embedUnitary uCat).1 * catState48 =
    (rCoreSeg.embedUnitary uEff).1 * catState48 := by
  have hTop := intertwinesCat_topCatSlice_of_localCat (le_refl 48) rCoreSeg rCat80
    hCoreSeg_disj_Cat80 uCat uEff hLoc
  rw [rCTSeg_eq_concat_topCat48, ← rCTSeg.embedUnitary_val, ← rCoreSeg.embedUnitary_val] at hTop
  exact (mul_catOp_of_intertwinesCat hTop).trans (rCoreSeg_comm_catState48 uEff).symm
theorem rCTSeg_embedUnitary_uPass1Cat_eq : rCTSeg.embedUnitary uPass1Cat =
    (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))⁻¹ *
    (uPass1InnerSeg * rCoreSeg.embedUnitary (uBarrelFast (le_refl 80))) := by
  rw [← embed_selCT4InCT_uPass1CatT4]
  unfold Leaf1Pass1And3Width204.uPass1CatT4 uPass1InnerSeg
  rw [unitaryConj_eq_inv_mul]
  have hB : rCTSeg.embedUnitary ((selCT4InCT 80).embedUnitary ((rCoreBlock4 80).embedUnitary
      (uBarrelFast (le_refl 80)))) = rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)) := by
    rw [← QRegister.embedUnitary_compose rCTSeg,
      ← QRegister.embedUnitary_compose (rCTSeg.compose (selCT4InCT 80)),
      rCTSeg_selCT4_rCoreBlock4_eq_rCoreSeg]
  simp only [QRegister.embedUnitary_mul, ← embedUnitary_inv_symm, hB, mul_assoc]
theorem group_barrel_conj_split {G : Type*} [Group G] (B K3 VB VA : G) (hBInv : B⁻¹ = B) : B *
    (K3 * (VB * (VA * B))) = (B⁻¹ * K3 * B) * ((B⁻¹ * VB * B) * (B⁻¹ * VA * B)) := by
  have hBB : B * B = 1 := by nth_rw 2 [← hBInv]; exact mul_inv_cancel B
  simp only [hBInv]
  calc B * (K3 * (VB * (VA * B)))
    _ = B * K3 * 1 * VB * 1 * VA * B := by simp only [mul_one, mul_assoc]
    _ = (B * K3 * B) * ((B * VB * B) * (B * VA * B)) := by rw [← hBB]; simp only [mul_assoc]
theorem group_factor_right_conj {G : Type*} [Group G] (B P3 VB VA P1 : G) : B *
    (P3 * (VB * (VA * (P1 * B)))) = (B * (P3 * (VB * (VA * B)))) * (B⁻¹ * (P1 * B)) := by
  calc B * (P3 * (VB * (VA * (P1 * B))))
    _ = B * P3 * VB * VA * 1 * (P1 * B) := by simp only [mul_one, mul_assoc]
    _ = (B * (P3 * (VB * (VA * B)))) * (B⁻¹ * (P1 * B)) := by
          rw [← mul_inv_cancel B]; simp only [mul_assoc]
theorem unitary_assoc_7 {d : ℕ} (P3 TrI QI P2 Q Tr P1 : Unitary d) : P3 *
    (TrI * (QI * (P2 * (Q * (Tr * P1))))) = (P3 * (TrI * ((QI * (P2 * Q)) * Tr))) * P1 := by
  simp only [mul_assoc]
/-- Schedule-polymorphic 6-step Single-Barrel `catState48` reduction (`6 ≤ B_p ≤ 27`). -/
theorem uSingleBarrelFolded6Seg_mul_catState48_eq_Mod4OfB
    (selOra : FullSysSelectOracleBundle 80 48) (B_p : ℕ) (hB6 : 6 ≤ B_p) (hB27 : B_p ≤ 27)
    (uStageASeg uStageBSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))) (hACat48 : uStageASeg.1
    * catState48 = (rCoreSeg.embedUnitary (unitaryConj qftCliffordCore80
    uHeadPhase80Mod4Eff)).1 * catState48) (hBCat48 : uStageBSeg.1 * catState48 =
    (rCoreSeg.embedUnitary (unitaryConj qftCliffordCore80 (uPosTail80Mod4OfB B_p hB6
    hB27))).1 * catState48) : (uSingleBarrelFolded6Seg uStageASeg uStageBSeg).1 * catState48 =
    (uFoldedPass123Seg coreQftHadamardPrunedBundle128 selOra
    (Leaf2PosMod4WidthCore.uPosPhase80Mod4OfB B_p hB6
    hB27)).1 * catState48 := by
  let B := uBarrelFast (le_refl 80)
  let K3 := (NuclearTwistRealizes.uSlot4KickCore hm22_80)⁻¹
  let VA := unitaryConj qftCliffordCore80 uHeadPhase80Mod4Eff
  let VB := unitaryConj qftCliffordCore80 (uPosTail80Mod4OfB B_p hB6 hB27)
  have hP1Cat : (rCTSeg.embedUnitary uPass1Cat).1 * catState48 =
      (rCoreSeg.embedUnitary uPass1Eff).1 * catState48 :=
    rCTSeg_mul_catState48_of_local uPass1Cat uPass1Eff
      (uPass1Cat_intertwinesLocal (U_cat_B_normalized 48)
        (U_cat_B_normalized_col_zero_singleCat 48))
  have hP3Cat : (rCTSeg.embedUnitary uPass3Cat).1 * catState48 =
      (rCoreSeg.embedUnitary uPass3Eff).1 * catState48 :=
    rCTSeg_mul_catState48_of_local uPass3Cat uPass3Eff
      (uPass3Cat_intertwinesLocal (U_cat_B_normalized 48)
        (U_cat_B_normalized_col_zero_singleCat 48))
  have hP3InCat : uPass3InnerSeg.1 * catState48 = (rCoreSeg.embedUnitary K3).1 * catState48 := by
    have hEmb : uPass3InnerSeg =
        rCTSeg.embedUnitary (JunctionApexCSA288.uSlot4ApexCat hm22_80)⁻¹ := by
      unfold uPass3InnerSeg
      rw [← embedUnitary_inv_symm, embed_selCT4InCT_uSlot4ApexCatT4]
    rw [hEmb]
    exact rCTSeg_mul_catState48_of_local _ K3
      (NuclearTwistRealizes.intertwinesLocalCat_to_fullSys
      ((JunctionApexCSA288.uSlot4ApexCat_intertwinesLocal hm22_80
      (U_cat_B_normalized 48) (col0_eq_phaseGradKet48 (U_cat_B_normalized 48)
      (U_cat_B_normalized_col_zero_singleCat 48))).inv))
  have hLhsFact : uSingleBarrelFolded6Seg uStageASeg uStageBSeg =
      (rCoreSeg.embedUnitary B * (uPass3InnerSeg * (uStageBSeg * (uStageASeg *
        rCoreSeg.embedUnitary B)))) * rCTSeg.embedUnitary uPass1Cat := by
    rw [rCTSeg_embedUnitary_uPass1Cat_eq]
    exact group_factor_right_conj (rCoreSeg.embedUnitary B) uPass3InnerSeg uStageBSeg uStageASeg
      uPass1InnerSeg
  have hG2Cat : (rCoreSeg.embedUnitary B * (uPass3InnerSeg * (uStageBSeg * (uStageASeg *
      rCoreSeg.embedUnitary B)))).1 * catState48 =
      (rCoreSeg.embedUnitary (B * (K3 * (VB * (VA * B))))).1 * catState48 :=
      mul_catState48_comp rfl (mul_catState48_comp hP3InCat (mul_catState48_comp hBCat48
      (mul_catState48_comp hACat48 rfl)))
  have hQCEq : fullSysQftCoreUnitary selOra.hmPay coreQftHadamardPrunedBundle128 *
      uTrailCliffordXor80 = qftCliffordCore80 := by
    unfold qftCliffordCore80 qftCoreUnitary80
    rw [show selOra.hmPay = hm6_80 from Subsingleton.elim _ _]
  have hMid05b :=
    (rhs_stageAB_mid_ofB_mul_catState48_eq_tail_mul_head_zeroHyp selOra B_p hB6 hB27).2.2.2
  rw [hQCEq, ← QRegister.embedUnitary_mul] at hMid05b
  let uPos := Leaf2PosMod4WidthCore.uPosPhase80Mod4OfB B_p hB6 hB27
  let X₂ := rCoreSeg.embedUnitary uTrailCliffordXor80⁻¹ *
    (MidUnitaryConjZeroRoot.uQftConjPass2Seg
      coreQftHadamardPrunedBundle128 selOra (unitaryConj B uPos) *
      rCoreSeg.embedUnitary uTrailCliffordXor80)
  have hRhsFact : uFoldedPass123Seg coreQftHadamardPrunedBundle128 selOra uPos =
      (rCTSeg.embedUnitary uPass3Cat * X₂) * rCTSeg.embedUnitary uPass1Cat := unitary_assoc_7
      (rCTSeg.embedUnitary uPass3Cat) (rCoreSeg.embedUnitary uTrailCliffordXor80⁻¹)
      ((Barrel3PassSelectStitch.rQSeg selOra).embedUnitary
      coreQftHadamardPrunedBundle128.uQftCat⁻¹) (rCoreSeg.embedUnitary (unitaryConj B uPos))
      ((Barrel3PassSelectStitch.rQSeg selOra).embedUnitary
      coreQftHadamardPrunedBundle128.uQftCat) (rCoreSeg.embedUnitary uTrailCliffordXor80)
      (rCTSeg.embedUnitary uPass1Cat)
  have hG1Cat : (rCTSeg.embedUnitary uPass3Cat * X₂).1 * catState48 =
      (rCoreSeg.embedUnitary (uPass3Eff * (unitaryConj B VB * unitaryConj B VA))).1 * catState48 :=
    mul_catState48_comp hP3Cat hMid05b
  have hCoreEq : B * (K3 * (VB * (VA * B))) = uPass3Eff * (unitaryConj B VB * unitaryConj B VA) :=
    by
    have hP3Eff : uPass3Eff = unitaryConj B K3 := by unfold uPass3Eff; rfl
    rw [hP3Eff, unitaryConj_eq_inv_mul B K3, unitaryConj_eq_inv_mul B VB,
      unitaryConj_eq_inv_mul B VA]
    exact group_barrel_conj_split B K3 VB VA uBarrelFast80_inv
  rw [hLhsFact, hRhsFact, mul_catState48_comp hG2Cat hP1Cat, mul_catState48_comp hG1Cat hP1Cat,
    hCoreEq]
theorem uPass3InnerSeg_mul_pCoinSlack010Seg :
    uPass3InnerSeg.1 * pCoinSlack010Seg = pCoinSlack010Seg := by
  unfold uPass3InnerSeg pCoinSlack010Seg
  rw [← QRegister.embedUnitary_compose, ← rCTSeg_selCT4_rCoreBlock4_eq_rCoreSeg,
    QRegister.embedMatrix_compose, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul]
  apply congrArg (rCTSeg.compose (selCT4InCT 80)).embedMatrix
  rw [pCoinSlack010CT4_eq_slot1_mul, ← Matrix.mul_assoc, uSlot4ApexCatT4_inv_mul_slot1_one]
/-- `uSingleBarrelFolded6Seg` fixes `pCoinSlack010Seg` whenever `uStageASeg` and `uStageBSeg` do. -/
theorem uSingleBarrelFolded6Seg_mul_pCoinSlack010Seg
    (uStageASeg uStageBSeg : Unitary (2 ^ (fullSysBEWires 80 + 48)))
    (hASlack : uStageASeg.1 * pCoinSlack010Seg = pCoinSlack010Seg)
    (hBSlack : uStageBSeg.1 * pCoinSlack010Seg = pCoinSlack010Seg) :
    (uSingleBarrelFolded6Seg uStageASeg uStageBSeg).1 * pCoinSlack010Seg = pCoinSlack010Seg := by
  let B := uBarrelFast (le_refl 80)
  let uB := rCoreSeg.embedUnitary B
  have hBInv : uB⁻¹ = uB := by
    dsimp only [uB, B]; rw [embedUnitary_inv_symm, uBarrelFast80_inv]
  have hFact : uSingleBarrelFolded6Seg uStageASeg uStageBSeg = unitaryConj uB
      (uPass3InnerSeg * (uStageBSeg * uStageASeg)) * rCTSeg.embedUnitary uPass1Cat := by
    rw [rCTSeg_embedUnitary_uPass1Cat_eq, unitaryConj_eq_inv_mul]
    have h := group_factor_right_conj uB uPass3InnerSeg uStageBSeg uStageASeg uPass1InnerSeg
    simpa only [uSingleBarrelFolded6Seg, uB, B, hBInv, mul_assoc] using h
  have hBComm : uB.1 * pCoinSlack010Seg = pCoinSlack010Seg * uB.1 := by
    dsimp only [uB, B]; unfold pCoinSlack010Seg
    rw [QRegister.embedUnitary_val, ← rCoreSeg.embedMatrix_mul, ← rCoreSeg.embedMatrix_mul]
    apply congrArg rCoreSeg.embedMatrix
    exact comm_pCoinSlack010Core_of_comm_coin3
      (uBarrelFast_comm_high_wire (le_refl 80)
        (FullSysCatSegmentBridge.iSlot2 80) (by dsimp [FullSysCatSegmentBridge.iSlot2]; omega) 0)
      (uBarrelFast_comm_high_wire (le_refl 80)
        (FullSysCatSegmentBridge.iSlot1 80) (by dsimp [FullSysCatSegmentBridge.iSlot1]; omega) 1)
      (uBarrelFast_comm_high_wire (le_refl 80)
        (FullSysCatSegmentBridge.iSlot0 80) (by dsimp [FullSysCatSegmentBridge.iSlot0]; omega) 0)
  have hMidSlack : (uPass3InnerSeg * (uStageBSeg * uStageASeg)).1 * pCoinSlack010Seg =
      pCoinSlack010Seg :=
    mul_fixes_proj uPass3InnerSeg_mul_pCoinSlack010Seg (mul_fixes_proj hBSlack hASlack)
  rw [hFact]
  exact mul_fixes_proj (unitaryConj_fixes_proj uB _ pCoinSlack010Seg hBComm hMidSlack)
    uPass1Cat_mul_pCoinSlack010Seg
/-- Inner `FoldedPass123` bundle at `(mWork = 179, k_idle = 11)` supporting distinct full-width
unitaries `uFoldedCtrlFull` (`Ctrl`) and `uFoldedCatFull` (`Cat`) over a common `uFoldedSeg`. -/
structure SlimFoldedPass123Bundle11 (mWork : ℕ)
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27)
    (tFoldCtrl tFoldCat : Fin 10 → ℕ) where
  uFoldedCtrlFull : Fin 10 → Configuration → Unitary (2 ^ kFull80)
  uFoldedCatFull : Fin 10 → Configuration → Unitary (2 ^ kFull80)
  uFoldedSeg : Fin 10 → Configuration → Unitary (2 ^ (fullSysBEWires 80 + 48))
  hInterRawCtrl : ∀ j c,
    (uFoldedCtrlFull j c).1 * E_rawCtrl3Ext 11 (by decide) =
      E_rawCtrl3Ext 11 (by decide) * (rSegFull.embedUnitary (uFoldedSeg j c)).1
  hInterRawCat : ∀ j c,
    (uFoldedCatFull j c).1 * E_rawSegExt 11 (by decide) =
      E_rawSegExt 11 (by decide) * (rSegFull.embedUnitary (uFoldedSeg j c)).1
  hCtrl3Seg : ∀ j c, CommutesWithReg rCtrl3InSeg (uFoldedSeg j c).1
  hIdle11Seg : ∀ j c,
    CommutesWithReg (rPGIdleOrig 11 (by decide)) (rSegOrig.embedUnitary (uFoldedSeg j c)).1
  hSlackSeg : ∀ j c, (uFoldedSeg j c).1 * pCoinSlack010Seg = pCoinSlack010Seg
  hCat48 : ∀ (selOra : FullSysSelectOracleBundle 80 48) (j : Fin 10) (c : Configuration),
    (uFoldedSeg j c).1 * catState48 =
      (uFoldedPass123Seg coreQftHadamardPrunedBundle128 selOra
        (Leaf2PosMod4WidthCore.uPosPhase80Mod4OfB
          (B j) (hB6 j) (hB27 j))).1 * catState48
/-- `mWork = 179` specialization of `SlimFoldedPass123Bundle11`. -/
abbrev FoldedPass123Bundle179_11 (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j)
    (hB27 : ∀ j, B j ≤ 27) (tFoldCtrl tFoldCat : Fin 10 → ℕ) : Type :=
    SlimFoldedPass123Bundle11 179 B hB6 hB27 tFoldCtrl tFoldCat
end Part1B_Ghost334AndSingleBarrel6Step
end SingleBarrel8StepClean
open MeasureBranchHadamardSem (ket eval_seq_mulVec)
open ClassicalPerm (TOFF)
namespace BoothOpt_Anchor218CachedTrueSwapOuter
section Part1_Engine218
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open OctahedralOrbit hiding ket eval_seq_mulVec ket_H ket_X ket_CNOT ket_TOFF matrix_ext_ket
  ket_projector_zero
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open AnchorSwap0Split133 MultiBankWStateRouter
open BoothOpt_02_Cached64x4TrueSwapEngine
/-- Row-3 anchor clamping of an `8`-bit index into `{0 .. 217}`:
maps `0 .. 217` identically and maps `218 .. 255` (`h₀ = 3, 26 ≤ l₀`) to row-3 anchor `192`. -/
def clampRow3Idx218 (v : ℕ) : ℕ := if v < 218 then v else 192
theorem clampRow3Idx218_lt (v : ℕ) : clampRow3Idx218 v < 218 := by
  dsimp only [clampRow3Idx218]; split_ifs <;> omega
/-- Row-loaded bit value for row `r : Fin 4` of the `64 × 4` `218`-slot table (`off = 0, KRem =
  26`). -/
def rowBit218 {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    (β : BitAssignment n) (l₀ : ℕ) (_hl₀ : l₀ < 64) (r : Fin 4) : ZMod 2 :=
  if hr3 : r.val < 3 then
    β (rElecSlot rCore ⟨64 * r.val + l₀, by omega⟩ j)
  else if hlt26 : l₀ < 26 then
    β (rElecSlot rCore ⟨192 + l₀, by omega⟩ j)
  else
    β (rElecSlot rCore ⟨192, by decide⟩ j)
theorem rowBit218_at_active {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    (β : BitAssignment n) (v₀ : ℕ) (hv₀ : v₀ < 256) :
    rowBit218 rCore j β (v₀ % 64) (Nat.mod_lt _ (by decide)) ⟨v₀ / 64, by omega⟩ =
    β (rElecSlot rCore ⟨clampRow3Idx218 v₀, clampRow3Idx218_lt v₀⟩ j) := by
  let l₀ := v₀ % 64
  let h₀ := v₀ / 64
  have hdiv : 64 * h₀ + l₀ = v₀ := Nat.div_add_mod v₀ 64
  dsimp only [rowBit218, clampRow3Idx218]
  by_cases hh3 : h₀ < 3
  · rw [dite_eq_left hh3]
    have hlt218 : v₀ < 218 := by omega
    exact congrArg (fun e ↦ β (rElecSlot rCore e j))
      (Fin.ext (by dsimp; rw [ite_eq_left hlt218]; omega))
  · have hh_eq : h₀ = 3 := by omega
    rw [dite_eq_right hh3]
    by_cases hlt26 : l₀ < 26
    · have hlt218 : v₀ < 218 := by omega
      rw [dite_eq_left hlt26]
      exact congrArg (fun e ↦
        β (rElecSlot rCore e j)) (Fin.ext (by dsimp; rw [ite_eq_left hlt218]; omega))
    · have hge218 : ¬ v₀ < 218 := by omega
      rw [dite_eq_right hlt26]
      exact congrArg (fun e ↦ β (rElecSlot rCore e j))
        (Fin.ext (by dsimp; rw [ite_eq_right hge218]))
/-- Loads the 4 `218`-slot row bits for bit `j : Fin 18` into `rScr[70 .. 74)` (`128*3 + 52 = 436
  T`),
temporarily computing and uncomputing row-3 tail parity (`K = 26`) on clean wire `rScr 69`. -/
def cLoad4Rows218 {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : Circuit n :=
  let uLo : Fin 64 → Wire n := fun l ↦ rScr ⟨l.val, by omega⟩
  let wPar : Wire n := rScr ⟨69, by omega⟩
  let rRow4 : QRegister 4 n := p2dSubReg rScr 70 4 (by omega)
  let c0 := cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
    (rElecSlot rCore ⟨0, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨1 + i.val, by omega⟩ j)
    (rRow4 ⟨0, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ rCore_ne_rSub hCS _ _ _)
    (rCore_ne_rSub hCS _ _ _)
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let c1 := cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
    (rElecSlot rCore ⟨64, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨65 + i.val, by omega⟩ j)
    (rRow4 ⟨1, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ rCore_ne_rSub hCS _ _ _)
    (rCore_ne_rSub hCS _ _ _)
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let c2 := cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
    (rElecSlot rCore ⟨128, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨129 + i.val, by omega⟩ j)
    (rRow4 ⟨2, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ rCore_ne_rSub hCS _ _ _)
    (rCore_ne_rSub hCS _ _ _)
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let cPar := cXorTailParity 64 26 (by decide) (by decide) uLo wPar
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let c3 := cLoadRowAnchored1Bit 64 26 (by decide) (by decide) uLo wPar
    (rElecSlot rCore ⟨192, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
    (rRow4 ⟨3, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ rCore_ne_rSub hCS _ _ _)
    (rCore_ne_rSub hCS _ _ _)
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  c0 ;;ᶜ (c1 ;;ᶜ (c2 ;;ᶜ (cPar ;;ᶜ (c3 ;;ᶜ cPar))))
theorem cLoad4Rows218_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (β : BitAssignment n) (hRow0 : ∀ r : Fin 4, β (p2dSubReg rScr 70 4 (by omega) r) = 0)
    (hPar0 : β (rScr ⟨69, by omega⟩) = 0) (l₀ : ℕ) (hl₀ : l₀ < 64)
    (hLo : ∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0) :
    (cLoad4Rows218 hm j rCore rScr hCS).eval.1.mulVec (ket β) =
      ket (p2d_writeReg β (p2dSubReg rScr 70 4 (by omega)) (rowBit218 rCore j β l₀ hl₀)) := by
  let uLo : Fin 64 → Wire n := fun l ↦ rScr ⟨l.val, by omega⟩
  let wPar : Wire n := rScr ⟨69, by omega⟩
  let rRow4 : QRegister 4 n := p2dSubReg rScr 70 4 (by omega)
  let vals := rowBit218 rCore j β l₀ hl₀
  have hBnd64 (α : BitAssignment n) (hα : ∀ l : Fin 64, α (uLo l) = if l.val = l₀ then 1 else 0) :
      α (uLo 0) = if (l₀ = 0 ∨ 64 ≤ l₀) then 1 else 0 := by
    rw [hα 0]; dsimp
    by_cases h0 : l₀ = 0
    · subst h0; simp
    · rw [ite_eq_right (Ne.symm h0), ite_eq_right (by omega)]
  have hFullRow (r : ℕ) (hr : r < 3) (α : BitAssignment n)
      (hαCore : ∀ e : Fin 218, α (rElecSlot rCore e j) = β (rElecSlot rCore e j))
      (hαOut : α (rRow4 ⟨r, by omega⟩) = 0)
      (hαLo : ∀ l : Fin 64, α (uLo l) = if l.val = l₀ then 1 else 0) :
      (cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
        (rElecSlot rCore ⟨64 * r, by omega⟩ j)
        (fun i ↦ rElecSlot rCore ⟨64 * r + 1 + i.val, by omega⟩ j) (rRow4 ⟨r, by omega⟩)
        (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega))
        (fun _ ↦ rCore_ne_rSub hCS _ _ _) (rCore_ne_rSub hCS _ _ _)
        (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
        (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))).eval.1.mulVec (ket α) =
      ket (Function.update α (rRow4 ⟨r, by omega⟩) (vals ⟨r, by omega⟩)) := by
    rw [cLoadRowAnchored1Bit_eval_ket 64 64 (by decide) le_rfl uLo (uLo 0)
      (rElecSlot rCore ⟨64 * r, by omega⟩ j)
      (fun i ↦ rElecSlot rCore ⟨64 * r + 1 + i.val, by omega⟩ j) (rRow4 ⟨r, by omega⟩) _ _ _ _ _
      (fun i₁ i₂ h ↦ Fin.ext (by
        by_contra hne; exact rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega) h))
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm) (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      α hαOut l₀ hl₀ hαLo (hBnd64 α hαLo)]
    refine congrArg (fun b ↦ ket (Function.update α (rRow4 ⟨r, by omega⟩) b)) ?_
    dsimp only [vals, rowBit218]; rw [dite_eq_left hr]
    by_cases h0 : l₀ = 0
    · rw [dite_eq_left h0, hαCore]
      exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
    · rw [dite_eq_right h0, dite_eq_left hl₀, hαCore]
      exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
  let β0 := Function.update β (rRow4 ⟨0, by decide⟩) (vals ⟨0, by decide⟩)
  let β1 := Function.update β0 (rRow4 ⟨1, by decide⟩) (vals ⟨1, by decide⟩)
  let β2 := Function.update β1 (rRow4 ⟨2, by decide⟩) (vals ⟨2, by decide⟩)
  have hRowNeCore : ∀ (r : Fin 4) (e : Fin 218), rElecSlot rCore e j ≠ rRow4 r :=
    fun _ _ ↦ rCore_ne_rSub hCS _ _ _
  have hRowNeLo : ∀ (r : Fin 4) (l : Fin 64), uLo l ≠ rRow4 r :=
    fun _ _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega)
  have hRowNePar : ∀ (r : Fin 4), wPar ≠ rRow4 r :=
    fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega)
  have hRowNe (a b : Fin 4) (hab : a ≠ b) : rRow4 a ≠ rRow4 b := rRow4.wires.injective.ne hab
  have hUpd01 (w : Wire n) (h0 : w ≠ rRow4 ⟨0, by decide⟩) (h1 : w ≠ rRow4 ⟨1, by decide⟩) :
      β1 w = β w := (Function.update_of_ne h1 _ _).trans (Function.update_of_ne h0 _ _)
  have hUpd2 (w : Wire n) (h0 : w ≠ rRow4 ⟨0, by decide⟩) (h1 : w ≠ rRow4 ⟨1, by decide⟩)
      (h2 : w ≠ rRow4 ⟨2, by decide⟩) : β2 w = β w :=
    (Function.update_of_ne h2 _ _).trans (hUpd01 w h0 h1)
  have hStep0 := hFullRow 0 (by decide) β (fun _ ↦ rfl) (hRow0 ⟨0, by decide⟩) hLo
  have hStep1 := hFullRow 1 (by decide) β0 (fun e ↦ Function.update_of_ne (hRowNeCore _ e) _ _)
    ((Function.update_of_ne (hRowNe ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)) _ _).trans
      (hRow0 ⟨1, by decide⟩))
    (fun l ↦ (Function.update_of_ne (hRowNeLo _ l) _ _).trans (hLo l))
  have hStep2 := hFullRow 2 (by decide) β1
    (fun e ↦ hUpd01 _ (hRowNeCore _ e) (hRowNeCore _ e))
    ((hUpd01 _ (hRowNe ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide))
      (hRowNe ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide))).trans (hRow0 ⟨2, by decide⟩))
    (fun l ↦ (hUpd01 _ (hRowNeLo _ l) (hRowNeLo _ l)).trans (hLo l))
  have hβ2_par : β2 wPar = 0 := (hUpd2 _ (hRowNePar _) (hRowNePar _) (hRowNePar _)).trans hPar0
  have hβ2_lo : ∀ l : Fin 64, β2 (uLo l) = if l.val = l₀ then 1 else 0 :=
    fun l ↦ (hUpd2 _ (hRowNeLo _ l) (hRowNeLo _ l) (hRowNeLo _ l)).trans (hLo l)
  have hβ2_core : ∀ e : Fin 218, β2 (rElecSlot rCore e j) = β (rElecSlot rCore e j) :=
    fun e ↦ hUpd2 _ (hRowNeCore _ e) (hRowNeCore _ e) (hRowNeCore _ e)
  have hβ2_r3 : β2 (rRow4 ⟨3, by decide⟩) = 0 :=
    (hUpd2 _ (hRowNe ⟨3, by decide⟩ ⟨0, by decide⟩ (by decide))
      (hRowNe ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide))
      (hRowNe ⟨3, by decide⟩ ⟨2, by decide⟩ (by decide))).trans (hRow0 ⟨3, by decide⟩)
  let bnd26 : ZMod 2 := if (l₀ = 0 ∨ 26 ≤ l₀) then 1 else 0
  let β3 := Function.update β2 wPar bnd26
  have hPar1 : (cXorTailParity 64 26 (by decide) (by decide) uLo wPar (fun _ ↦ rSub_ne_of_ne
      rScr (by omega) (by omega) (by omega))).eval.1.mulVec (ket β2) = ket β3 := by
    rw [cXorTailParity_eval_ket 64 26 (by decide) (by decide) uLo wPar _ β2 l₀ hl₀ hβ2_lo,
        hβ2_par, zero_add]
  have hβ3_lo : ∀ l : Fin 64, β3 (uLo l) = if l.val = l₀ then 1 else 0 := fun l ↦
    (Function.update_of_ne (rSub_ne_of_ne rScr (by omega) (by omega) (by omega)) _ _).trans
      (hβ2_lo l)
  have hStep3 : (cLoadRowAnchored1Bit 64 26 (by decide) (by decide) uLo wPar
        (rElecSlot rCore ⟨192, by decide⟩ j) (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
        (rRow4 ⟨3, by decide⟩) (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega))
        (fun _ ↦ rCore_ne_rSub hCS _ _ _) (rCore_ne_rSub hCS _ _ _)
        (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
        (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))).eval.1.mulVec (ket β3) =
      ket (Function.update β3 (rRow4 ⟨3, by decide⟩) (vals ⟨3, by decide⟩)) := by
    rw [cLoadRowAnchored1Bit_eval_ket 64 26 (by decide) (by decide) uLo wPar
      (rElecSlot rCore ⟨192, by decide⟩ j) (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
      (rRow4 ⟨3, by decide⟩) _ _ _ _ _
      (fun i₁ i₂ h ↦ Fin.ext (by
        by_contra hne; exact rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega) h))
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm) (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      β3 ((Function.update_of_ne (hRowNePar _).symm _ _).trans hβ2_r3)
      l₀ hl₀ hβ3_lo (Function.update_self _ _ _)]
    refine congrArg (fun b ↦ ket (Function.update β3 (rRow4 ⟨3, by decide⟩) b)) ?_
    have hCore3 : ∀ e : Fin 218, β3 (rElecSlot rCore e j) = β (rElecSlot rCore e j) := fun e ↦
      (Function.update_of_ne (rCore_ne_rSub hCS _ _ _) _ _).trans (hβ2_core e)
    dsimp only [vals, rowBit218]; rw [dite_eq_right (by decide : ¬ ((3 : ℕ) < 3))]
    by_cases h0 : l₀ = 0
    · rw [dite_eq_left h0, dite_eq_left (by omega : l₀ < 26), hCore3]
      exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
    · rw [dite_eq_right h0]
      by_cases hlt26 : l₀ < 26
      · rw [dite_eq_left hlt26, dite_eq_left hlt26, hCore3]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right hlt26, dite_eq_right hlt26, hCore3]
  let β4 := Function.update β3 (rRow4 ⟨3, by decide⟩) (vals ⟨3, by decide⟩)
  have hβ4_lo : ∀ l : Fin 64, β4 (uLo l) = if l.val = l₀ then 1 else 0 := fun l ↦
    (Function.update_of_ne (hRowNeLo _ l) _ _).trans (hβ3_lo l)
  have hPar2 : (cXorTailParity 64 26 (by decide) (by decide) uLo wPar
      (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))).eval.1.mulVec (ket β4) =
      ket (Function.update β4 wPar (β4 wPar + bnd26)) :=
    cXorTailParity_eval_ket 64 26 (by decide) (by decide) uLo wPar _ β4 l₀ hl₀ hβ4_lo
  dsimp only [cLoad4Rows218]
  rw [eval_seq_mulVec, hStep0, eval_seq_mulVec, hStep1, eval_seq_mulVec, hStep2,
      eval_seq_mulVec, hPar1, eval_seq_mulVec, hStep3, hPar2]
  have hβ4_par : β4 wPar + bnd26 = 0 := by
    dsimp [β4, β3]
    rw [Function.update_of_ne (hRowNePar _), Function.update_self, CharTwo.add_self_eq_zero]
  rw [hβ4_par]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hwPar : w = wPar
  · subst hwPar
    rw [Function.update_self, p2d_writeReg_apply_of_not_mem _ _ _ _
      (fun ⟨r, hr⟩ ↦ hRowNePar r hr.symm), hPar0]
  · rw [Function.update_of_ne hwPar]
    by_cases hwRow : w ∈ Set.range rRow4.wires
    · obtain ⟨r, rfl⟩ := hwRow
      rw [p2d_writeReg_apply_reg]
      have hr4 : ∀ x : Fin 4,
          x = ⟨0, by decide⟩ ∨ x = ⟨1, by decide⟩ ∨ x = ⟨2, by decide⟩ ∨ x = ⟨3, by decide⟩ := by
        decide
      rcases hr4 r with rfl | rfl | rfl | rfl
      · dsimp only [β4, β3, β2, β1, β0]
        rw [Function.update_of_ne (hRowNe ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide)),
            Function.update_of_ne (hRowNePar _).symm,
            Function.update_of_ne (hRowNe ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)),
            Function.update_of_ne (hRowNe ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)),
            Function.update_self]
      · dsimp only [β4, β3, β2, β1]
        rw [Function.update_of_ne (hRowNe ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide)),
            Function.update_of_ne (hRowNePar _).symm,
            Function.update_of_ne (hRowNe ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)),
            Function.update_self]
      · dsimp only [β4, β3, β2]
        rw [Function.update_of_ne (hRowNe ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)),
            Function.update_of_ne (hRowNePar _).symm, Function.update_self]
      · exact Function.update_self _ _ _
    · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hwRow]
      exact (Function.update_of_ne (fun h ↦ hwRow ⟨_, h.symm⟩) _ _).trans
        ((Function.update_of_ne hwPar _ _).trans (hUpd2 _ (fun h ↦ hwRow ⟨_, h.symm⟩)
          (fun h ↦ hwRow ⟨_, h.symm⟩) (fun h ↦ hwRow ⟨_, h.symm⟩)))
/-- Zero-`T` CZ phase-fix circuit for a single `218`-slot anchored row (`W = 64`). -/
def cFixSingleRow218 {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (r : Fin 4) : Circuit n :=
  let uLo : Fin 64 → Wire n := fun l ↦ rScr ⟨l.val, by omega⟩
  if hr3 : r.val < 3 then
    cFixRowAnchored1BitAux 64 64 (by decide) le_rfl uLo
      (rElecSlot rCore ⟨64 * r.val, by omega⟩ j)
      (fun i ↦ rElecSlot rCore ⟨64 * r.val + 1 + i.val, by omega⟩ j)
      (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      64 le_rfl
  else
    cFixRowAnchored1BitAux 64 26 (by decide) (by decide) uLo
      (rElecSlot rCore ⟨192, by decide⟩ j)
      (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
      (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      64 le_rfl
theorem cFixSingleRow218_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (r : Fin 4) (β : BitAssignment n) (l₀ : ℕ) (hl₀ : l₀ < 64)
    (hLo : ∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0) :
    (cFixSingleRow218 hm j rCore rScr hCS r).eval.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (rowBit218 rCore j β l₀ hl₀ r).val) • ket β := by
  dsimp only [cFixSingleRow218, rowBit218]
  by_cases hr3 : r.val < 3
  · rw [dite_eq_left hr3, dite_eq_left hr3, cFixRowAnchored1BitAux_eval_ket]
    refine congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ z.val) • ket β) ?_
    rw [Finset.sum_eq_single ⟨l₀, hl₀⟩]
    · rw [hLo ⟨l₀, hl₀⟩]; dsimp; rw [ite_eq_left rfl, one_mul]
      by_cases h0 : l₀ = 0
      · rw [dite_eq_left h0]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right h0, dite_eq_left hl₀]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
    · intro l _ hne
      rw [hLo l]; dsimp
      have hvne : l.val ≠ l₀ := fun hv ↦ hne (Fin.ext hv)
      rw [ite_eq_right hvne, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · rw [dite_eq_right hr3, dite_eq_right hr3, cFixRowAnchored1BitAux_eval_ket]
    refine congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ z.val) • ket β) ?_
    rw [Finset.sum_eq_single ⟨l₀, hl₀⟩]
    · rw [hLo ⟨l₀, hl₀⟩]; dsimp; rw [ite_eq_left rfl, one_mul]
      by_cases h0 : l₀ = 0
      · rw [dite_eq_left h0, dite_eq_left (by omega : l₀ < 26)]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right h0]
        by_cases hlt26 : l₀ < 26
        · rw [dite_eq_left hlt26, dite_eq_left hlt26]
          exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
        · rw [dite_eq_right hlt26, dite_eq_right hlt26]
    · intro l _ hne
      rw [hLo l]; dsimp
      have hvne : l.val ≠ l₀ := fun hv ↦ hne (Fin.ext hv)
      rw [ite_eq_right hvne, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
/-- Zero-`T` 4-row measurement-branch phase-fix circuit for the `218`-slot table. -/
def cBranchFix4Rows218Aux {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool) :
    (k : ℕ) → (hk : k ≤ 4) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let prev := cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k (by omega)
      if fRow ⟨k, hk⟩ then
        prev ;;ᶜ cFixSingleRow218 hm j rCore rScr hCS ⟨k, hk⟩
      else
        prev
theorem cBranchFix4Rows218Aux_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool)
    (β : BitAssignment n) (l₀ : ℕ) (hl₀ : l₀ < 64)
    (hLo : ∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0) :
    ∀ (k : ℕ) (hk : k ≤ 4),
      (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k hk).eval.1.mulVec (ket β) =
        (∏ r : Fin k,
          if fRow ⟨r.val, by omega⟩ then
            (-1 : ℂ) ^ (rowBit218 rCore j β l₀ hl₀ ⟨r.val, by omega⟩).val
          else 1) • ket β
  | 0, _ => by simp [cBranchFix4Rows218Aux]
  | k + 1, hk => by
      dsimp only [cBranchFix4Rows218Aux]
      by_cases hf : fRow ⟨k, hk⟩
      · rw [ite_eq_left hf, eval_seq_mulVec,
            cBranchFix4Rows218Aux_eval_ket hm j rCore rScr hCS fRow β l₀ hl₀ hLo k (by omega),
            Matrix.mulVec_smul, cFixSingleRow218_eval_ket hm j rCore rScr hCS ⟨k, hk⟩ β l₀ hl₀ hLo,
            smul_smul, Fin.prod_univ_castSucc]
        dsimp only [Fin.val_last, Fin.val_castSucc]
        rw [ite_eq_left hf]
      · rw [ite_eq_right hf,
            cBranchFix4Rows218Aux_eval_ket hm j rCore rScr hCS fRow β l₀ hl₀ hLo k (by omega),
            Fin.prod_univ_castSucc]
        dsimp only [Fin.val_last, Fin.val_castSucc]
        rw [ite_eq_right hf, mul_one]
noncomputable def dZKick1BitHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (j₀ : Fin 18) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : DynamicCircuit Var n :=
  let rRow4 : QRegister 4 n := p2dSubReg rScr 70 4 (by omega)
  .seq (.circuit (cLoad4Rows218 hm j₀ rCore rScr hCS ;;ᶜ cCz4RowHi hm rScr))
    (DynCircuitExt.measureXResetAndBranch v 4 rRow4
      (fun fRow ↦ .circuit (cBranchFix4Rows218Aux hm j₀ rCore rScr hCS fRow 4 le_rfl)))
noncomputable def dFixHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (f : Fin 18 → Bool) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : DynamicCircuit Var n :=
  match findTrueBitAux f 18 le_rfl with
  | none => .identity
  | some j₀ =>
      let cFan := cSlotParityFanIn f j₀ rCore
      .seq (.circuit cFan)
        (.seq (dZKick1BitHole218 hm v j₀ rCore rScr hCS) (.circuit cFan))
end Part1_Engine218
section Part1E_PebbledAnchor218
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensLoadPerm lensWritePerm lensSwapPerm)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply selDataInAct_disj_selMeasInAct
  concat_compose_selDataInAct concat_compose_selMeasInAct)
open PartnerAndAnchorSlot18LensAndMidBA (liftSlot18Lens)
open ElecHadTrueSwapLocalCompClosure (extractPair liftPairIdx uLensLoad uLensWrite uLensSwap)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 P_slot0_eq_diagonal)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (unitary_ext_mulVec_single)
open PosSlots24Barrel3Pass (permUnitary_apply)
theorem embedUnitary_permUnitary_mulVec_single {m N : ℕ}
    (r : QRegister m N) (e : Equiv.Perm (Fin (2 ^ m))) (g : Fin (2 ^ N)) :
    (r.embedUnitary (Operator.permutationUnitary e)).1.mulVec (Pi.single g 1) =
      Pi.single (r.replaceIndex g (e (r.extractIndex g))) 1 := by
  ext i
  have hCol : ((r.embedUnitary (Operator.permutationUnitary e)).1.mulVec (Pi.single g 1)) i =
      (r.embedMatrix (Operator.permutationUnitary e).1) i g := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, QRegister.embedUnitary_val]
  rw [hCol, QRegister.embedMatrix_apply]
  by_cases henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv g).2
  · rw [ite_eq_left henv, permUnitary_apply]
    by_cases hex : r.extractIndex i = e (r.extractIndex g)
    · have hi : i = r.replaceIndex g (e (r.extractIndex g)) := by
        apply r.basisSplitEquiv.injective
        rw [r.basisSplitEquiv_replaceIndex]
        exact Prod.ext (by simpa [QRegister.basisSplitEquiv_apply_fst] using hex) henv
      subst hi; simp
    · have hne : i ≠ r.replaceIndex g (e (r.extractIndex g)) := by
        intro h; subst h; exact hex (r.extractIndex_replaceIndex g _)
      simp [hex, hne]
  · have hne : i ≠ r.replaceIndex g (e (r.extractIndex g)) := by
      intro h; subst h
      rw [r.basisSplitEquiv_replaceIndex] at henv
      exact henv rfl
    simp [henv, hne]
theorem permUnitary_mulVec_single {D : ℕ} (e : Equiv.Perm (Fin D)) (g : Fin D) :
    (Operator.permutationUnitary e).1.mulVec (Pi.single g 1) = Pi.single (e g) 1 := by
  ext i
  have hCol : ((Operator.permutationUnitary e).1.mulVec (Pi.single g 1)) i =
      (Operator.permutationUnitary e).1 i g := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hCol, permUnitary_apply]
  by_cases hi : i = e g
  · subst hi; simp
  · simp [hi]
theorem concat_replaceIndex_liftPairIdx {n k : ℕ}
    (rD : QRegister k n) (rM : QRegister 18 n) (hDM : rD.DisjointWires rM)
    (F : Fin (2 ^ k) × Fin (2 ^ 18) → Fin (2 ^ k) × Fin (2 ^ 18))
    (g : Fin (2 ^ n)) :
    let p := F (rD.extractIndex g, rM.extractIndex g)
    (rD.concat rM hDM).replaceIndex g (liftPairIdx F ((rD.concat rM hDM).extractIndex g)) =
      rM.replaceIndex (rD.replaceIndex g p.1) p.2 := by
  intro p
  let rDM := rD.concat rM hDM
  have hex : extractPair (rDM.extractIndex g) = (rD.extractIndex g, rM.extractIndex g) := by
    dsimp only [extractPair]
    rw [← QRegister.extractIndex_compose, concat_compose_selDataInAct,
        ← QRegister.extractIndex_compose, concat_compose_selMeasInAct]
  dsimp only [liftPairIdx]
  rw [hex]
  change rDM.replaceIndex g ((selMeasInAct k).replaceIndex ((selDataInAct k).replaceIndex
    (rDM.extractIndex g) p.1) p.2) = rM.replaceIndex (rD.replaceIndex g p.1) p.2
  apply eq_of_basisBits_eq; intro w
  by_cases hwDM : w ∈ Set.range rDM.wires
  · obtain ⟨u, rfl⟩ := hwDM
    rw [QRegister.basisBits_replaceIndex_apply]
    refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) u
    · have hd : Fin.castAdd 18 i = selDataInAct k i := (selDataInAct_apply i).symm
      have hnotM_loc : selDataInAct k i ∉ Set.range (selMeasInAct k).wires :=
        fun ⟨m', hm'⟩ ↦ (selDataInAct_disj_selMeasInAct k).ne i m' hm'.symm
      have hrD : rDM (Fin.castAdd 18 i) = rD i := QRegister.concat_apply_left rD rM hDM i
      have hnotM : rD i ∉ Set.range rM.wires := fun ⟨m', hm'⟩ ↦ hDM.ne i m' hm'.symm
      rw [hrD, hd, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM_loc,
          QRegister.basisBits_replaceIndex_apply,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM,
          QRegister.basisBits_replaceIndex_apply]
    · have hm : Fin.natAdd k m = selMeasInAct k m := (selMeasInAct_apply m).symm
      have hrM : rDM (Fin.natAdd k m) = rM m := QRegister.concat_apply_right rD rM hDM m
      rw [hrM, hm, QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
  · have hnotM : w ∉ Set.range rM.wires := fun ⟨m, hm⟩ ↦
      hwDM ⟨Fin.natAdd k m, (QRegister.concat_apply_right rD rM hDM m).trans hm⟩
    have hnotD : w ∉ Set.range rD.wires := fun ⟨i, hi⟩ ↦
      hwDM ⟨Fin.castAdd 18 i, (QRegister.concat_apply_left rD rM hDM i).trans hi⟩
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwDM,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotD]
theorem concat_compose_selLiftAct {n k₁ k₂ : ℕ} (rData : QRegister k₂ n)
    (sel : QRegister k₁ k₂) (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) :
    (rData.concat rMeas hDM).compose (selLiftAct sel) = (rData.compose sel).concat rMeas
    (hDM.compose_left sel) := by
  apply QRegister.ext (Function.Embedding.ext fun u ↦ ?_)
  refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) u
  · change (rData.concat rMeas hDM) (selLiftAct sel (Fin.castAdd 18 i)) =
      ((rData.compose sel).concat rMeas (hDM.compose_left sel)) (Fin.castAdd 18 i)
    dsimp only [selLiftAct]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hd : selDataInAct k₂ (sel i) = Fin.castAdd 18 (sel i) := selDataInAct_apply (sel i)
    change (rData.concat rMeas hDM) (selDataInAct k₂ (sel i)) = rData (sel i)
    rw [hd, QRegister.concat_apply_left]
  · change (rData.concat rMeas hDM) (selLiftAct sel (Fin.natAdd k₁ m)) =
      ((rData.compose sel).concat rMeas (hDM.compose_left sel)) (Fin.natAdd k₁ m)
    dsimp only [selLiftAct]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
    have hm : selMeasInAct k₂ m = Fin.natAdd k₂ m := selMeasInAct_apply m
    rw [hm, QRegister.concat_apply_right]
theorem compose_replaceIndex_eq {n k₁ k₂ : ℕ} (outer : QRegister k₂ n)
    (inner : QRegister k₁ k₂) (g : Fin (2 ^ n)) (v : Fin (2 ^ k₁)) :
    (outer.compose inner).replaceIndex g v = outer.replaceIndex g
    (inner.replaceIndex (outer.extractIndex g) v) := by
  apply eq_of_basisBits_eq; intro w
  by_cases hwO : w ∈ Set.range outer.wires
  · obtain ⟨u, rfl⟩ := hwO
    rw [QRegister.basisBits_replaceIndex_apply]
    by_cases huI : u ∈ Set.range inner.wires
    · obtain ⟨i, rfl⟩ := huI
      rw [QRegister.basisBits_replaceIndex_apply]
      exact QRegister.basisBits_replaceIndex_apply (outer.compose inner) g v i
    · have hnot : outer u ∉ Set.range (outer.compose inner).wires :=
        fun ⟨i, hi⟩ ↦ huI ⟨i, outer.wires.injective hi⟩
      rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ huI,
          QRegister.basisBits_extractIndex]
  · have hnot : w ∉ Set.range (outer.compose inner).wires := fun ⟨i, hi⟩ ↦ hwO ⟨inner i, hi⟩
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwO]
theorem uLensLoad_liftSlot18Lens {k₁ k₂ : ℕ} (sel : QRegister k₁ k₂) (L : Slot18Lens k₁) :
    (selLiftAct sel).embedUnitary (uLensLoad L) = uLensLoad (liftSlot18Lens sel L) := by
  refine unitary_ext_mulVec_single fun g ↦ ?_
  dsimp only [uLensLoad]
  rw [embedUnitary_permUnitary_mulVec_single, permUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ (k₂ + 18)) → ℂ)) ?_
  change (selLiftAct sel).replaceIndex g
      (liftPairIdx (lensLoadPerm L) ((selLiftAct sel).extractIndex g)) =
    liftPairIdx (lensLoadPerm (liftSlot18Lens sel L)) g
  dsimp only [selLiftAct]
  rw
    [concat_replaceIndex_liftPairIdx ((selDataInAct k₂).compose sel) (selMeasInAct k₂) _
    (lensLoadPerm L) g]
  dsimp only [liftPairIdx, extractPair, lensLoadPerm, liftSlot18Lens]
  rw [QRegister.replaceIndex_extractIndex, QRegister.replaceIndex_extractIndex,
      ← QRegister.extractIndex_compose (selDataInAct k₂) sel g]
theorem uLensWrite_liftSlot18Lens {k₁ k₂ : ℕ} (sel : QRegister k₁ k₂) (L : Slot18Lens k₁) :
    (selLiftAct sel).embedUnitary (uLensWrite L) = uLensWrite (liftSlot18Lens sel L) := by
  refine unitary_ext_mulVec_single fun g ↦ ?_
  dsimp only [uLensWrite]
  rw [embedUnitary_permUnitary_mulVec_single, permUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ (k₂ + 18)) → ℂ)) ?_
  change (selLiftAct sel).replaceIndex g
      (liftPairIdx (lensWritePerm L) ((selLiftAct sel).extractIndex g)) =
    liftPairIdx (lensWritePerm (liftSlot18Lens sel L)) g
  dsimp only [selLiftAct]
  rw
    [concat_replaceIndex_liftPairIdx ((selDataInAct k₂).compose sel) (selMeasInAct k₂) _
    (lensWritePerm L) g]
  dsimp only [liftPairIdx, extractPair, lensWritePerm, liftSlot18Lens]
  rw [compose_replaceIndex_eq (selDataInAct k₂) sel g,
      ← QRegister.extractIndex_compose (selDataInAct k₂) sel g]
theorem uLensSwap_liftSlot18Lens {k₁ k₂ : ℕ} (sel : QRegister k₁ k₂) (L : Slot18Lens k₁) :
    (selLiftAct sel).embedUnitary (uLensSwap L) = uLensSwap (liftSlot18Lens sel L) := by
  refine unitary_ext_mulVec_single fun g ↦ ?_
  dsimp only [uLensSwap]
  rw [embedUnitary_permUnitary_mulVec_single, permUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ (k₂ + 18)) → ℂ)) ?_
  change (selLiftAct sel).replaceIndex g
      (liftPairIdx (lensSwapPerm L) ((selLiftAct sel).extractIndex g)) =
    liftPairIdx (lensSwapPerm (liftSlot18Lens sel L)) g
  dsimp only [selLiftAct]
  rw
    [concat_replaceIndex_liftPairIdx ((selDataInAct k₂).compose sel) (selMeasInAct k₂) _
    (lensSwapPerm L) g]
  dsimp only [liftPairIdx, extractPair, lensSwapPerm, liftSlot18Lens]
  rw [compose_replaceIndex_eq (selDataInAct k₂) sel g,
      ← QRegister.extractIndex_compose (selDataInAct k₂) sel g]
theorem P_slot0_liftSlot18Lens {k₁ k₂ : ℕ} (sel : QRegister k₁ k₂) (L : Slot18Lens k₁) :
    (selLiftAct sel).embedMatrix (P_slot0 L) = P_slot0 (liftSlot18Lens sel L) := by
  dsimp only [P_slot0]
  rw [(selLiftAct sel).embedMatrix_mul, (selLiftAct sel).embedMatrix_mul,
      ← QRegister.embedUnitary_val, uLensSwap_liftSlot18Lens]
  have hMeas : (selLiftAct sel).compose (selMeasInAct k₁) = selMeasInAct k₂ := by
    dsimp only [selLiftAct]
    exact concat_compose_selMeasInAct ((selDataInAct k₂).compose sel) (selMeasInAct k₂) _
  rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hMeas,
      ← QRegister.basisOutcomeProjector]
theorem P_slot0_conjTranspose {kData : ℕ} (L : Slot18Lens kData) :
    (P_slot0 L)ᴴ = P_slot0 L := by
  rw [P_slot0_eq_diagonal L, Matrix.diagonal_conjTranspose]
  apply congrArg Matrix.diagonal; funext xy
  rw [Pi.star_apply]
  by_cases h : L.tbl ((selDataInAct kData).extractIndex xy) = 0
  · rw [ite_eq_left h, star_one]
  · rw [ite_eq_right h, star_zero]
end Part1E_PebbledAnchor218
section Part2_AnchorFrameAndPass13
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open HoistBorrow42ProjBridge (RealizesOnProj)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_compose_of_disjoint disjointWires_concat_left)
open SingleCatClosure (compose_concat_eq_singleCat)
open InterWalkRSum42Hoist
  (kFull80 rCoreFull rPG48Full rSegFull rCTFull hCoreFull_disj_PG48Full qreg_ext)
open StageADeconstrCore (selDataInAct)
open ButterflyBarrelSlot0Conj (ActsAsIdOnSpectatorWires PreservesHigh3924On)
open BoothOpt_09_ButterflyPass13ThreeBarrelAdap
  (actsAsIdOnSpectatorWires_uPass1InnerT4 preservesHigh3924On_uPass1InnerT4
  actsAsIdOnSpectatorWires_uSlot4ApexCatT4_inv preservesHigh3924On_uSlot4ApexCatT4_inv)
open Pass1Leaf273 (hm22_80)
open Barrel3PassSelectStitch (rCTSeg rCoreInCT80 rCoreSeg rSegFull_compose_rCTSeg)
open Leaf1Pass1And3Width204
  (compose_selCT4InCT_eq rCoreBlock4 selCT4InCT uPass1InnerT4 uSlot4ApexCatT4)
open SelStitchHelper (selCT4InCT_compose_rCoreBlock4 rCTSeg_compose_rCoreInCT80)
open SingleBarrelPass123FoldOnStep
  (dFoldedPass3InnerT4 count_dFoldedPass3InnerT4_toff count_dFoldedPass3InnerT4_t
  dFoldedPass3InnerT4_realizes)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
open SelectPass13Gen (rT4Full hCoreFull_disj_rT4Full)
open BarrelPass2AndHeld3PassSelectStitch (uPass1InnerSeg uPass3InnerSeg stepT4CleanRWork)
open Leaf1Pass1And3OptAux
  (dSlot4AndSlot0FusedT4_130_584 count_dSlot4AndSlot0FusedT4_130_584_toff
  count_dSlot4AndSlot0FusedT4_130_584_t dSlot4AndSlot0FusedT4_130_584_realizes)
theorem rEmbCT4_compose_rCoreBlock4 :
    (rSegFull.compose (rCTSeg.compose (selCT4InCT 80))).compose (rCoreBlock4 80) = rCoreFull := by
  calc (rSegFull.compose (rCTSeg.compose (selCT4InCT 80))).compose (rCoreBlock4 80)
      = rSegFull.compose (rCTSeg.compose ((selCT4InCT 80).compose (rCoreBlock4 80))) := by
          apply qreg_ext; intro i; rfl
    _ = rSegFull.compose (rCTSeg.compose rCoreInCT80) := by
          rw [selCT4InCT_compose_rCoreBlock4]
    _ = rSegFull.compose rCoreSeg := by rw [rCTSeg_compose_rCoreInCT80]
    _ = rCoreFull := rSegFull_compose_rCoreSeg_eq
theorem uSlot0MeasSwap_conj_embed_ct4_eq (u4 : Unitary (2 ^ (fullSysCoreWires 80 + 4)))
    (hSpec : ActsAsIdOnSpectatorWires (rCoreBlock4 80) u4)
    (hHigh : PreservesHigh3924On (rCoreBlock4 80) u4) :
    let U := rSegFull.embedUnitary (rCTSeg.embedUnitary ((selCT4InCT 80).embedUnitary u4))
    uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U * uSlot0MeasSwap =
      uAnchorFrame U := by
  intro U
  let rEmb := rSegFull.compose (rCTSeg.compose (selCT4InCT 80))
  have hUEq : U = rEmb.embedUnitary u4 := by
    dsimp only [U, rEmb]
    rw [← QRegister.embedUnitary_compose rCTSeg (selCT4InCT 80) u4,
        ← QRegister.embedUnitary_compose rSegFull (rCTSeg.compose (selCT4InCT 80)) u4]
  have hS : ActsAsIdOnSpectatorWires rCoreFull U := by
    rw [← rEmbCT4_compose_rCoreBlock4, hUEq]
    exact actsAsIdOnSpectatorWires_embed rEmb (rCoreBlock4 80) hSpec
  have hH : PreservesHigh3924On rCoreFull U := by
    rw [← rEmbCT4_compose_rCoreBlock4, hUEq]
    exact preservesHigh3924On_embed rEmb (rCoreBlock4 80) hHigh
  exact uSlot0MeasSwap_conj_eq_uAnchorFrame U hS hH
/-- `+0 T` anchor-frame `Pass 1` (`584 T`, `TOFF = 0`, `130 ≤ mWork`). -/
noncomputable def dPass1Anchor {mWork : ℕ} (hm130 : 130 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) : DynamicCircuit
    Var n := stepT4CleanRWork (fun v' rC rT4 rRest hCT4 hCR hTR ↦
    dSlot4AndSlot0FusedT4_130_584 hm130 v' rC rT4 rRest hCT4 hCR hTR) v
    (rActAnchorSubst rAct rAnchor18 hAA) rWork (rActAnchorSubst_disj_of_disj hAA hAW hAnW)
/-- `+0 T` anchor-frame `Pass 3` (`140 T`, `TOFF = 0`, `13 ≤ mWork`). -/
noncomputable def dPass3Anchor {mWork : ℕ} (hm13 : 13 ≤ mWork) {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) : DynamicCircuit Var n := stepT4CleanRWork (fun v'
    rC rT4 rRest hCT4 hCR hTR ↦ dFoldedPass3InnerT4 hm13 v' rC rT4 rRest hCT4 hCR hTR) v
    (rActAnchorSubst rAct rAnchor18 hAA) rWork (rActAnchorSubst_disj_of_disj hAA hAW hAnW)
@[simp] theorem dPass1Anchor_count_toff {mWork : ℕ} (hm130 : 130 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dPass1Anchor hm130 v rAct rAnchor18 rWork hAA hAW hAnW).count TOFF = 0 := by
  unfold dPass1Anchor stepT4CleanRWork
  exact count_dSlot4AndSlot0FusedT4_130_584_toff hm130 v _ _ _ _ _ _
@[simp] theorem dPass1Anchor_count_t {mWork : ℕ} (hm130 : 130 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dPass1Anchor hm130 v rAct rAnchor18 rWork hAA hAW hAnW).count T = 584 := by
  unfold dPass1Anchor stepT4CleanRWork
  exact count_dSlot4AndSlot0FusedT4_130_584_t hm130 v _ _ _ _ _ _
@[simp] theorem dPass3Anchor_count_toff {mWork : ℕ} (hm13 : 13 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dPass3Anchor hm13 v rAct rAnchor18 rWork hAA hAW hAnW).count TOFF = 0 := by
  unfold dPass3Anchor stepT4CleanRWork
  exact count_dFoldedPass3InnerT4_toff hm13 v _ _ _ _ _ _
@[simp] theorem dPass3Anchor_count_t {mWork : ℕ} (hm13 : 13 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dPass3Anchor hm13 v rAct rAnchor18 rWork hAA hAW hAnW).count T = 140 := by
  unfold dPass3Anchor stepT4CleanRWork
  exact count_dFoldedPass3InnerT4_t hm13 v _ _ _ _ _ _
theorem stepT4Anchor_realizesOnProj {mWork : ℕ}
    (u4 : Unitary (2 ^ (fullSysCoreWires 80 + 4)))
    (dT4 : ∀ {Var : Type} {n : ℕ},
      Var → (rC : QRegister (fullSysCoreWires 80) n) → (rT4 : QRegister 4 n) →
      (rRest : QRegister mWork n) →
      rC.DisjointWires rT4 → rC.DisjointWires rRest → rT4.DisjointWires rRest →
        DynamicCircuit Var n)
    (hReal : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
      (v : Var) (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n)
      (rRest : QRegister mWork n) (hCT4 : rC.DisjointWires rT4)
      (hCR : rC.DisjointWires rRest) (hTR : rT4.DisjointWires rRest),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        (rC.concat rT4 hCT4) rRest u4 (dT4 v rC rT4 rRest hCT4 hCR hTR))
    (hSpec : ActsAsIdOnSpectatorWires (rCoreBlock4 80) u4)
    (hHigh : PreservesHigh3924On (rCoreBlock4 80) u4)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_loc : Operator (2 ^ (kFull80 + 18))) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    let U := rSegFull.embedUnitary (rCTSeg.embedUnitary ((selCT4InCT 80).embedUnitary u4))
    RealizesOnProj
      ((rAct.concat rAnchor18 hAA).embedMatrix E_loc * rWork.basisOutcomeProjector 0)
      ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame U))
      (stepT4CleanRWork dT4 v (rActAnchorSubst rAct rAnchor18 hAA) rWork
        (rActAnchorSubst_disj_of_disj hAA hAW hAnW)) := by
  intro U
  let rSubst := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  have hRaw := hReal v (rSubst.compose rCoreFull) (rSubst.compose rT4Full) rWork
    (disjointWires_compose_of_disjoint rSubst hCoreFull_disj_rT4Full)
    (hSubW.compose_left rCoreFull) (hSubW.compose_left rT4Full)
  have eCT4 : (rSubst.compose rCoreFull).concat (rSubst.compose rT4Full)
        (disjointWires_compose_of_disjoint rSubst hCoreFull_disj_rT4Full) =
      (rAct.concat rAnchor18 hAA).compose
        ((selSubstSlot0 rSlot0InFull).compose (rSegFull.compose (rCTSeg.compose (selCT4InCT 80))))
          := by
    have e1 : (rSubst.compose rCoreFull).concat (rSubst.compose rT4Full)
        (disjointWires_compose_of_disjoint rSubst hCoreFull_disj_rT4Full) = rSubst.compose
        (rCTFull.compose (selCT4InCT 80)) := (compose_concat_eq_singleCat rSubst rCoreFull
        rT4Full hCoreFull_disj_rT4Full).trans (congrArg (rSubst.compose ·)
        (compose_selCT4InCT_eq rCoreFull rPG48Full hCoreFull_disj_PG48Full).symm)
    rw [e1, ← rSegFull_compose_rCTSeg]
    dsimp only [rSubst, rActAnchorSubst]
    rw [← concat_compose_selSubstSlot0 rSlot0InFull rAct rAnchor18 hAA]
    apply qreg_ext; intro i; rfl
  rw [eCT4] at hRaw
  have hWide := hRaw.widenActive
  have hUEq : ((selSubstSlot0 rSlot0InFull).compose
      (rSegFull.compose (rCTSeg.compose (selCT4InCT 80)))).embedUnitary u4 = uAnchorFrame U := by
    calc ((selSubstSlot0 rSlot0InFull).compose
            (rSegFull.compose (rCTSeg.compose (selCT4InCT 80)))).embedUnitary u4
        = (selSubstSlot0 rSlot0InFull).embedUnitary U := by
            dsimp only [U]
            rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
                ← QRegister.embedUnitary_compose]
            rfl
      _ = uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U * uSlot0MeasSwap :=
            Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull U.1)
      _ = uAnchorFrame U := uSlot0MeasSwap_conj_embed_ct4_eq u4 hSpec hHigh
  rw [hUEq] at hWide
  exact RealizesOnProj.of_clean_embed (disjointWires_concat_left hAA hAW hAnW) E_loc hWide
theorem dPass1Anchor_realizesOnProj {mWork : ℕ} (hm130 : 130 ≤ mWork) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_loc : Operator (2 ^ (kFull80 + 18))) (v : Var) (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) : RealizesOnProj ((rAct.concat rAnchor18
    hAA).embedMatrix E_loc * rWork.basisOutcomeProjector 0) ((rAct.concat rAnchor18
    hAA).embedUnitary (uAnchorFrame (rSegFull.embedUnitary uPass1InnerSeg)))
    (dPass1Anchor hm130 v rAct rAnchor18 rWork hAA hAW hAnW) := stepT4Anchor_realizesOnProj
    uPass1InnerT4 _ (fun v' rC rT4 rRest hCT4 hCR hTR ↦ dSlot4AndSlot0FusedT4_130_584_realizes
    hm130 v' rC rT4 rRest hCT4 hCR hTR) actsAsIdOnSpectatorWires_uPass1InnerT4
    preservesHigh3924On_uPass1InnerT4 E_loc v rAct rAnchor18 rWork hAA hAW hAnW
theorem dPass3Anchor_realizesOnProj {mWork : ℕ} (hm13 : 13 ≤ mWork) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (E_loc : Operator (2 ^ (kFull80 + 18)))
    (v : Var) (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) : RealizesOnProj
    ((rAct.concat rAnchor18 hAA).embedMatrix E_loc * rWork.basisOutcomeProjector 0)
    ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame (rSegFull.embedUnitary
    uPass3InnerSeg))) (dPass3Anchor hm13 v rAct rAnchor18 rWork hAA hAW hAnW) :=
    stepT4Anchor_realizesOnProj (uSlot4ApexCatT4 hm22_80)⁻¹ _ (fun v' rC rT4 rRest hCT4 hCR
    hTR ↦ dFoldedPass3InnerT4_realizes hm13 v' rC rT4 rRest hCT4 hCR hTR)
    actsAsIdOnSpectatorWires_uSlot4ApexCatT4_inv preservesHigh3924On_uSlot4ApexCatT4_inv E_loc
    v rAct rAnchor18 rWork hAA hAW hAnW
end Part2_AnchorFrameAndPass13
section Part3_Anchor6StepAndBundle179_11
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysBEWires)
open InterWalkRSum42Hoist (kFull80 rAct0 rCoreFull rSegOrig rSegFull E_rawStream42)
open StageADeconstrCore (selDataInAct)
open CoinDispatchedBarrel288 (uBarrelFast)
open Leaf4Ext48TopStitch (CommutesWithReg rPGIdle rPGIdleOrig)
open SelectHoistLemmas
  (rCtrl3InSeg pCoinSlack010Seg rSegFull_eq_rAct0_compose_rSegOrig
  commutesWithReg_rCtrl3InSeg_rCoreSeg)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
open Leaf2PosMod4WidthCore (commutesWithReg_rCtrl3InCore_uBarrelFast)
open Barrel3PassSelectStitch (rCoreSeg)
open HeldStreamFoldedPass123Bridge (E_rawCtrl3Ext E_rawSegExt)
open CoinBarrelPureCnotLoad (uBarrelFast_comm_E_rawStream42)
open MidUnitaryConjZeroRoot (uPosTail80Mod4OfB)
open BarrelPass2AndHeld3PassSelectStitch
  (uPass1InnerSeg uPass3InnerSeg rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt
  rawStream_core_intertwine_to_rawCtrl3Ext_and_rawSegExt
  uPass1InnerSeg_and_uPass3InnerSeg_comm_rawStream_ctrl3_idle12 uSingleBarrelFolded6Full
  uSingleBarrelFolded6Seg)
open SingleBarrel8StepClean (qftCliffordCore80 commutesWithReg_rPGIdleOrig11_of_12)
theorem uAnchorLensSwap_mul_data_P_anc0 {E_ext : Operator (2 ^ kFull80)}
    (hBE : (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 * E_ext =
      E_ext * (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1) :
    uAnchorLensSwap.1 * ((selDataInAct kFull80).embedMatrix E_ext * P_anc0) =
      E_anchorLoc E_ext * uBarrelFastAct.1 := by
  have hBCommE : uBarrelFastAct.1 * (selDataInAct kFull80).embedMatrix E_ext =
      (selDataInAct kFull80).embedMatrix E_ext * uBarrelFastAct.1 := by
    rw [uBarrelFastAct_eq_embedData_rCoreFull, QRegister.embedUnitary_val,
        ← (selDataInAct kFull80).embedMatrix_mul, hBE, (selDataInAct kFull80).embedMatrix_mul]
  have hBCommP : uBarrelFastAct.1 * P_anc0 = P_anc0 * uBarrelFastAct.1 := by
    rw [uBarrelFastAct_eq_embedData_rCoreFull, QRegister.embedUnitary_val]
    exact selDataInAct_embedMatrix_comm_P_anc0 _
  rw [uAnchorLensSwap_eq_uBarrelFastAct_conj, Submonoid.coe_mul]
  calc ((uBarrelFastAct * uSlot0MeasSwap).1 * uBarrelFastAct.1) *
          ((selDataInAct kFull80).embedMatrix E_ext * P_anc0)
      = (uBarrelFastAct * uSlot0MeasSwap).1 *
          ((uBarrelFastAct.1 * (selDataInAct kFull80).embedMatrix E_ext) * P_anc0) := by
          simp only [Matrix.mul_assoc]
    _ = (uBarrelFastAct * uSlot0MeasSwap).1 *
          ((selDataInAct kFull80).embedMatrix E_ext * (uBarrelFastAct.1 * P_anc0)) := by
          rw [hBCommE]; simp only [Matrix.mul_assoc]
    _ = E_anchorLoc E_ext * uBarrelFastAct.1 := by
          rw [hBCommP]; unfold E_anchorLoc; simp only [Matrix.mul_assoc]
theorem uAnchorLensSwap_conj_uAnchorFrame_four (U_A U_B : Unitary (2 ^ kFull80)) :
    uAnchorLensSwap * (uAnchorFrame (rSegFull.embedUnitary uPass3InnerSeg) * (uAnchorFrame U_B
    * (uAnchorFrame U_A * (uAnchorFrame (rSegFull.embedUnitary uPass1InnerSeg) *
    uAnchorLensSwap)))) = (selDataInAct kFull80).embedUnitary
    (uSingleBarrelFolded6Full U_A U_B) := by
  let U_P1 := rSegFull.embedUnitary uPass1InnerSeg
  let U_P3 := rSegFull.embedUnitary uPass3InnerSeg
  let M := U_P3 * (U_B * (U_A * U_P1))
  have hFour : uAnchorFrame U_P3 * (uAnchorFrame U_B * (uAnchorFrame U_A * uAnchorFrame U_P1)) =
      uAnchorFrame M := by
    rw [uAnchorFrame_mul, uAnchorFrame_mul, uAnchorFrame_mul]
  have hBFull : rCoreFull.embedUnitary (uBarrelFast (le_refl 80)) =
      rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80))) := by
    rw [← QRegister.embedUnitary_compose, rSegFull_compose_rCoreSeg_eq]
  calc uAnchorLensSwap *
          (uAnchorFrame U_P3 *
            (uAnchorFrame U_B * (uAnchorFrame U_A * (uAnchorFrame U_P1 * uAnchorLensSwap))))
      = uAnchorLensSwap *
          (uAnchorFrame U_P3 * (uAnchorFrame U_B * (uAnchorFrame U_A * uAnchorFrame U_P1))) *
          uAnchorLensSwap := by simp only [mul_assoc]
    _ = (uAnchorLensSwap * (uBarrelFastAct * uSlot0MeasSwap)) *
          (selDataInAct kFull80).embedUnitary M *
          ((uSlot0MeasSwap * uBarrelFastAct) * uAnchorLensSwap) := by
          rw [hFour]; unfold uAnchorFrame; simp only [mul_assoc]
    _ = uBarrelFastAct * (selDataInAct kFull80).embedUnitary M * uBarrelFastAct := by
          rw [uAnchorLensSwap_mul_uBarrelFastAct_mul_uSlot0MeasSwap,
              uSlot0MeasSwap_mul_uBarrelFastAct_mul_uAnchorLensSwap]
    _ = (selDataInAct kFull80).embedUnitary (uSingleBarrelFolded6Full U_A U_B) := by
          rw [uBarrelFastAct_eq_embedData_rCoreFull, hBFull,
              ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
          dsimp only [M, U_P1, U_P3, uSingleBarrelFolded6Full]
          simp only [mul_assoc]
theorem uBarrelFast_comm_E_rawCtrl3Ext_and_E_rawSegExt {k_idle : ℕ} (hk : k_idle ≤ 48) :
    (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 * E_rawCtrl3Ext k_idle hk =
      E_rawCtrl3Ext k_idle hk * (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 ∧
    (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 * E_rawSegExt k_idle hk =
      E_rawSegExt k_idle hk * (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 := by
  have hBFull : rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80))) =
      rCoreFull.embedUnitary (uBarrelFast (le_refl 80)) := by
    rw [← QRegister.embedUnitary_compose, rSegFull_compose_rCoreSeg_eq]
  have hRaw : (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 * E_rawStream42 =
      E_rawStream42 *
        (rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1 := by
    rw [← hBFull]; exact uBarrelFast_comm_E_rawStream42
  have hPair := rawStream_core_intertwine_to_rawCtrl3Ext_and_rawSegExt hk
    (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 (uBarrelFast (le_refl 80))
    hRaw commutesWithReg_rCtrl3InCore_uBarrelFast
  rwa [hBFull] at hPair
theorem uSingleBarrelFolded6Full_intertwines_rawStream_and_ext11
    (U_A U_B : Unitary (2 ^ kFull80))
    (uStageASeg uStageBSeg : Unitary (2 ^ (fullSysBEWires 80 + 48)))
    (hARaw : U_A.1 * E_rawStream42 = E_rawStream42 * (rSegFull.embedUnitary uStageASeg).1)
    (hBRaw : U_B.1 * E_rawStream42 = E_rawStream42 * (rSegFull.embedUnitary uStageBSeg).1)
    (hACtrl3 : CommutesWithReg rCtrl3InSeg uStageASeg.1)
    (hBCtrl3 : CommutesWithReg rCtrl3InSeg uStageBSeg.1)
    (hAIdle11 : CommutesWithReg (rPGIdleOrig 11 (by decide)) (rSegOrig.embedUnitary uStageASeg).1)
    (hBIdle11 : CommutesWithReg (rPGIdleOrig 11 (by decide)) (rSegOrig.embedUnitary uStageBSeg).1) :
    let uFoldSeg := uSingleBarrelFolded6Seg uStageASeg uStageBSeg
    (uSingleBarrelFolded6Full U_A U_B).1 * E_rawStream42 =
      E_rawStream42 * (rSegFull.embedUnitary uFoldSeg).1 ∧
    CommutesWithReg rCtrl3InSeg uFoldSeg.1 ∧
    CommutesWithReg (rPGIdleOrig 11 (by decide)) (rSegOrig.embedUnitary uFoldSeg).1 ∧
    (uSingleBarrelFolded6Full U_A U_B).1 * E_rawCtrl3Ext 11 (by decide) =
      E_rawCtrl3Ext 11 (by decide) * (rSegFull.embedUnitary uFoldSeg).1 ∧
    (uSingleBarrelFolded6Full U_A U_B).1 * E_rawSegExt 11 (by decide) =
      E_rawSegExt 11 (by decide) * (rSegFull.embedUnitary uFoldSeg).1 := by
  intro uFoldSeg
  obtain ⟨⟨hP1Raw, hP1C, hP1I12⟩, ⟨hP3Raw, hP3C, hP3I12⟩⟩ :=
    uPass1InnerSeg_and_uPass3InnerSeg_comm_rawStream_ctrl3_idle12
  have hP1I := commutesWithReg_rPGIdleOrig11_of_12 hP1I12
  have hP3I := commutesWithReg_rPGIdleOrig11_of_12 hP3I12
  have hBBarRaw : (rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1
      * E_rawStream42 = E_rawStream42 * (rSegFull.embedUnitary (rCoreSeg.embedUnitary
      (uBarrelFast (le_refl 80)))).1 := uBarrelFast_comm_E_rawStream42
  have hBBarC : CommutesWithReg rCtrl3InSeg (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80))).1 :=
    commutesWithReg_rCtrl3InSeg_rCoreSeg commutesWithReg_rCtrl3InCore_uBarrelFast
  have hBBarI : CommutesWithReg (rPGIdleOrig 11 (by decide))
      (rSegOrig.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1 := by
    have hDisjOrig : (rSegOrig.compose rCoreSeg).DisjointWires (rPGIdleOrig 11 (by decide)) := by
      rw [QRegister.disjoint_iff]; intro i q h
      have hAct := congrArg rAct0 h
      change (rAct0.compose (rSegOrig.compose rCoreSeg)) i = (rPGIdle 11 (by decide)) q at hAct
      rw [← QRegister.compose_assoc, ← rSegFull_eq_rAct0_compose_rSegOrig,
          rSegFull_compose_rCoreSeg_eq] at hAct
      exact (CoinBarrelPureCnotLoad.rCoreFull_disj_rPGIdle
        11 (by decide)).ne i q hAct
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint hDisjOrig _
  have hFullRaw : (uSingleBarrelFolded6Full U_A U_B).1 * E_rawStream42 =
      E_rawStream42 * (rSegFull.embedUnitary uFoldSeg).1 := by
    unfold uSingleBarrelFolded6Full uFoldSeg uSingleBarrelFolded6Seg
    simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    calc _ = (rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1 *
          ((rSegFull.embedUnitary uPass3InnerSeg).1 *
            (U_B.1 * (U_A.1 * ((rSegFull.embedUnitary uPass1InnerSeg).1 *
              ((rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1 *
                E_rawStream42))))) := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hBBarRaw, ← Matrix.mul_assoc (rSegFull.embedUnitary uPass1InnerSeg).1, hP1Raw,
              Matrix.mul_assoc E_rawStream42, ← Matrix.mul_assoc U_A.1, hARaw,
              Matrix.mul_assoc E_rawStream42, ← Matrix.mul_assoc U_B.1, hBRaw,
              Matrix.mul_assoc E_rawStream42,
                ← Matrix.mul_assoc (rSegFull.embedUnitary uPass3InnerSeg).1,
              hP3Raw, Matrix.mul_assoc E_rawStream42,
              ← Matrix.mul_assoc (rSegFull.embedUnitary (rCoreSeg.embedUnitary _)).1, hBBarRaw]
          simp only [Matrix.mul_assoc]
  have hFoldC : CommutesWithReg rCtrl3InSeg uFoldSeg.1 := by
    unfold uFoldSeg uSingleBarrelFolded6Seg
    simp only [Submonoid.coe_mul]
    exact hBBarC.mul (hP3C.mul (hBCtrl3.mul (hACtrl3.mul (hP1C.mul hBBarC))))
  have hFoldI : CommutesWithReg (rPGIdleOrig 11 (by decide)) (rSegOrig.embedUnitary uFoldSeg).1 :=
    by
    unfold uFoldSeg uSingleBarrelFolded6Seg
    simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    exact hBBarI.mul (hP3I.mul (hBIdle11.mul (hAIdle11.mul (hP1I.mul hBBarI))))
  obtain ⟨hExtCtrl, hExtCat⟩ :=
    rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (uSingleBarrelFolded6Full U_A U_B).1 uFoldSeg hFullRaw hFoldC hFoldI
  exact ⟨hFullRaw, hFoldC, hFoldI, hExtCtrl, hExtCat⟩
/-- Anchor-frame Stage-B input bundle at `(mWork = 179, k_idle = 11)` (`rAnchor18` + `161` clean
  wires). -/
structure StageBAnchorInput179_11
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27)
    (tBCtrl tBCat : Fin 10 → ℕ) where
  uStageBSeg : Fin 10 → Unitary (2 ^ (fullSysBEWires 80 + 48))
  uStageBCtrlFull : Fin 10 → Unitary (2 ^ kFull80)
  uStageBCatFull : Fin 10 → Unitary (2 ^ kFull80)
  hBCtrlRaw : ∀ j, (uStageBCtrlFull j).1 * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary (uStageBSeg j)).1
  hBCatRaw : ∀ j, (uStageBCatFull j).1 * E_rawStream42 =
    E_rawStream42 * (rSegFull.embedUnitary (uStageBSeg j)).1
  hBCtrl3 : ∀ j, CommutesWithReg rCtrl3InSeg (uStageBSeg j).1
  hBIdle11 : ∀ j,
    CommutesWithReg (rPGIdleOrig 11 (by decide)) (rSegOrig.embedUnitary (uStageBSeg j)).1
  hBSlack010 : ∀ j, (uStageBSeg j).1 * pCoinSlack010Seg = pCoinSlack010Seg
  hBCat48 : ∀ j, (uStageBSeg j).1 * catState48 =
    (rCoreSeg.embedUnitary
      (unitaryConj qftCliffordCore80 (uPosTail80Mod4OfB (B j) (hB6 j) (hB27 j)))).1 *
    catState48
end Part3_Anchor6StepAndBundle179_11
end BoothOpt_Anchor218CachedTrueSwapOuter
namespace StageBFastInnerPartnerShift
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open AnchorSwap0Split133 MultiBankWStateRouter
open FullConcrete7StepAndTrueSwapSelect (cHadamardAll count_cHadamardAll_toff count_cHadamardAll_t)
open BoothOpt_02_Cached64x4TrueSwapEngine
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (selHadOfPosCore)
/-- Maps classical variable annotations of a `DynamicCircuit` to `Unit` for `Fintype`-free gate
  counting. -/
noncomputable def toUnitVar {Var : Type} {n : ℕ} : DynamicCircuit Var n → DynamicCircuit Unit
    n := dynMapReindex (fun u _ ↦ u ()) (fun c ↦ .circuit c) (fun _ r ↦ .measure () r)
theorem toUnitVar_circuit {Var : Type} {n : ℕ} (c : Circuit n) :
    toUnitVar (Var := Var) (.circuit c) = .circuit c := rfl
theorem toUnitVar_measure {Var : Type} {n : ℕ} (v : Var) (r : QRegister 1 n) :
    toUnitVar (.measure v r) = .measure () r := rfl
theorem toUnitVar_seq {Var : Type} {n : ℕ} (p₁ p₂ : DynamicCircuit Var n) :
    toUnitVar (.seq p₁ p₂) = .seq (toUnitVar p₁) (toUnitVar p₂) := rfl
theorem toUnitVar_dynQIfVar {Var : Type} {n : ℕ} (v : Var) (t f : DynamicCircuit Var n) :
    toUnitVar (dynQIfVar v t f) = dynQIfVar () (toUnitVar t) (toUnitVar f) := rfl
theorem count_toUnitVar {Var : Type} {n a : ℕ} (g : PrimitiveGate a) :
    ∀ d : DynamicCircuit Var n, (toUnitVar d).count g = d.count g := by
  intro d; induction d with
  | circuit _ => rfl
  | measure _ _ => rfl
  | qIf _ _ _ iht ihf => dsimp only [toUnitVar, DynamicCircuit.count] at *; rw [iht, ihf]
  | seq _ _ ih₁ ih₂ => dsimp only [toUnitVar, DynamicCircuit.count] at *; rw [ih₁, ih₂]
theorem toUnitVar_measureXResetAndBranch {Var : Type} {n : ℕ} (v : Var) :
    ∀ (b : ℕ) (r : QRegister b n) (cont : (Fin b → Bool) → DynamicCircuit Var n),
      toUnitVar (DynCircuitExt.measureXResetAndBranch v b r cont) =
        DynCircuitExt.measureXResetAndBranch () b r (fun f ↦ toUnitVar (cont f))
  | 0, _, _ => by simp only [DynCircuitExt.measureXResetAndBranch]
  | b + 1, r, cont => by
      simp only [DynCircuitExt.measureXResetAndBranch, toUnitVar_circuit, toUnitVar_measure,
        toUnitVar_seq, toUnitVar_dynQIfVar]
      rw [toUnitVar_measureXResetAndBranch v b, toUnitVar_measureXResetAndBranch v b]
theorem count_measureXResetAndBranch_TOFF_le_noFintype {Var : Type} {n : ℕ}
    (v : Var) (b : ℕ) (r : QRegister b n) (cont : (Fin b → Bool) → DynamicCircuit Var n) (B : ℕ)
    (h : ∀ f, (cont f).count TOFF ≤ B) :
    (DynCircuitExt.measureXResetAndBranch v b r cont).count TOFF ≤ B := by
  rw [← count_toUnitVar TOFF, toUnitVar_measureXResetAndBranch]
  exact DynCircuitExt.count_measureXResetAndBranch_TOFF_le () b r _ B
    fun f ↦ by rw [count_toUnitVar]; exact h f
theorem count_measureXResetAndBranch_T_le_noFintype {Var : Type} {n : ℕ}
    (v : Var) (b : ℕ) (r : QRegister b n) (cont : (Fin b → Bool) → DynamicCircuit Var n) (B : ℕ)
    (h : ∀ f, (cont f).count T ≤ B) :
    (DynCircuitExt.measureXResetAndBranch v b r cont).count T ≤ B := by
  rw [← count_toUnitVar T, toUnitVar_measureXResetAndBranch]
  exact DynCircuitExt.count_measureXResetAndBranch_T_le () b r _ B
    fun f ↦ by rw [count_toUnitVar]; exact h f
theorem rElecSlot_ofFin_val_local (e : Fin 218) (j : Fin 18) :
    (rElecSlot (QRegExt.ofFin posCoreWires) e j).val = 18 * e.val + j.val := rfl
/-- Loads the 4 `218`-slot row bits (`0 .. 217`) for bit `j : Fin 18` into `rScr[70 .. 74)` (`436
  T`),
temporarily computing and uncomputing row-3 tail parity (`KRem = 26`) on clean wire `rScr 69`. -/
abbrev cLoad4Rows218 {n mScr : ℕ} :=
  @BoothOpt_Anchor218CachedTrueSwapOuter.cLoad4Rows218 n mScr
theorem cLoad4Rows218_count_toff {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (cLoad4Rows218 hm j rCore rScr hCS).count TOFF = 0 := by
  dsimp only [cLoad4Rows218, BoothOpt_Anchor218CachedTrueSwapOuter.cLoad4Rows218]
  simp only [Circuit.count_seq, cLoadRowAnchored1Bit_count_toff, cXorTailParity_count_toff]
theorem cLoad4Rows218_count_t {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (cLoad4Rows218 hm j rCore rScr hCS).count T = 436 := by
  dsimp only [cLoad4Rows218, BoothOpt_Anchor218CachedTrueSwapOuter.cLoad4Rows218]
  simp only [Circuit.count_seq, cLoadRowAnchored1Bit_count_t, cXorTailParity_count_t]
/-- Zero-`T` CZ phase-fix circuit for a single `218`-slot row (`W = 64`). -/
abbrev cFixSingleRow218 {n mScr : ℕ} :=
  @BoothOpt_Anchor218CachedTrueSwapOuter.cFixSingleRow218 n mScr
/-- Zero-`T` branch-conditioned CZ phase-fix over the first `k` of 4 rows (`218`-slot table). -/
abbrev cBranchFix4Rows218Aux {n mScr : ℕ} :=
  @BoothOpt_Anchor218CachedTrueSwapOuter.cBranchFix4Rows218Aux n mScr
theorem cBranchFix4Rows218Aux_count_toff {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool) :
    ∀ (k : ℕ) (hk : k ≤ 4),
      (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k hk).count TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cBranchFix4Rows218Aux,
        BoothOpt_Anchor218CachedTrueSwapOuter.cBranchFix4Rows218Aux]
      by_cases hf : fRow ⟨k, hk⟩
      · rw [ite_eq_left hf, Circuit.count_seq,
            cBranchFix4Rows218Aux_count_toff hm j rCore rScr hCS fRow k]
        dsimp only [cFixSingleRow218,
          BoothOpt_Anchor218CachedTrueSwapOuter.cFixSingleRow218]
        by_cases hr3 : k < 3
        · rw [dite_eq_left hr3, cFixRowAnchored1BitAux_count_toff]
        · rw [dite_eq_right hr3, cFixRowAnchored1BitAux_count_toff]
      · rw [ite_eq_right hf]
        exact cBranchFix4Rows218Aux_count_toff hm j rCore rScr hCS fRow k (by omega)
theorem cBranchFix4Rows218Aux_count_t {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool) :
    ∀ (k : ℕ) (hk : k ≤ 4),
      (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k hk).count T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cBranchFix4Rows218Aux,
        BoothOpt_Anchor218CachedTrueSwapOuter.cBranchFix4Rows218Aux]
      by_cases hf : fRow ⟨k, hk⟩
      · rw [ite_eq_left hf, Circuit.count_seq,
            cBranchFix4Rows218Aux_count_t hm j rCore rScr hCS fRow k]
        dsimp only [cFixSingleRow218,
          BoothOpt_Anchor218CachedTrueSwapOuter.cFixSingleRow218]
        by_cases hr3 : k < 3
        · rw [dite_eq_left hr3, cFixRowAnchored1BitAux_count_t]
        · rw [dite_eq_right hr3, cFixRowAnchored1BitAux_count_t]
      · rw [ite_eq_right hf]
        exact cBranchFix4Rows218Aux_count_t hm j rCore rScr hCS fRow k (by omega)
/-- Single-bit (`444 T`, `TOFF = 0`) phase-kick dynamic circuit at `.hole` for
  `shiftedPartnerLens218`. -/
noncomputable def dKick1Bit218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) : DynamicCircuit Var n :=
  let uHi : Fin 4 → Wire n := fun h ↦ rScr ⟨64 + h.val, by omega⟩
  let rRow4 : QRegister 4 n := p2dSubReg rScr 70 4 (by omega)
  let rSel1 : QRegister 1 n := p2dSubReg rScr 74 1 (by omega)
  let wSel : Wire n := rScr ⟨74, by omega⟩
  let cSel := cLoadRowAnchored1Bit 4 4 (by decide) le_rfl uHi (uHi 0)
    (rScr ⟨70, by omega⟩) (fun i ↦ rScr ⟨71 + i.val, by omega⟩) wSel
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let cCz := czCircuit wSel (rMeas j) (hMS.ne j ⟨74, by omega⟩).symm
  let cFixSel : Circuit n :=
    cFixRowAnchored1BitAux 4 4 (by decide) le_rfl uHi
      (rScr ⟨70, by omega⟩) (fun i ↦ rScr ⟨71 + i.val, by omega⟩)
      (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
      (fun _ _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
      4 le_rfl
  let step1 : DynamicCircuit Var n :=
    .seq (.circuit (cLoad4Rows218 hm j rCore rScr hCS ;;ᶜ (cSel ;;ᶜ cCz)))
      (DynCircuitExt.measureXResetAndBranch v 1 rSel1
        (fun fSel ↦ if fSel 0 then .circuit cFixSel else .identity))
  .seq step1
    (DynCircuitExt.measureXResetAndBranch v 4 rRow4
      (fun fRow ↦ .circuit (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow 4 le_rfl)))
theorem dKick1Bit218_count_toff {Var : Type}
    {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dKick1Bit218 hm v j rCore rMeas rScr hCS hMS).count TOFF = 0 := by
  dsimp only [dKick1Bit218, DynamicCircuit.count]
  rw [Circuit.count_seq, Circuit.count_seq, cLoad4Rows218_count_toff,
      cLoadRowAnchored1Bit_count_toff, czCircuit_count_toff]
  have h1 : (DynCircuitExt.measureXResetAndBranch (Var := Var) v 1 (p2dSubReg rScr 74 1 hm)
      (fun fSel ↦ if fSel 0 then
        .circuit (cFixRowAnchored1BitAux 4 4 (by decide) le_rfl
          (fun h : Fin 4 ↦ rScr ⟨64 + h.val, by omega⟩)
          (rScr ⟨70, by omega⟩) (fun i ↦ rScr ⟨71 + i.val, by omega⟩)
          (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
          (fun _ _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega)) 4 le_rfl)
       else .identity)).count TOFF = 0 :=
    Nat.le_zero.mp (count_measureXResetAndBranch_TOFF_le_noFintype v 1 _ _ 0 fun fSel ↦ by
      cases fSel 0 <;> simp [cFixRowAnchored1BitAux_count_toff])
  have h2 : (DynCircuitExt.measureXResetAndBranch (Var := Var) v 4 (p2dSubReg rScr 70 4 (by omega))
      (fun fRow ↦
        .circuit (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow 4 le_rfl))).count TOFF = 0 :=
    Nat.le_zero.mp (count_measureXResetAndBranch_TOFF_le_noFintype v 4 _ _ 0 fun fRow ↦ by
      simp [DynamicCircuit.count, cBranchFix4Rows218Aux_count_toff])
  rw [h1, h2]
theorem dKick1Bit218_count_t {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dKick1Bit218 hm v j rCore rMeas rScr hCS hMS).count T = 444 := by
  dsimp only [dKick1Bit218, DynamicCircuit.count]
  rw [Circuit.count_seq, Circuit.count_seq, cLoad4Rows218_count_t,
      cLoadRowAnchored1Bit_count_t, czCircuit_count_t]
  have h1 : (DynCircuitExt.measureXResetAndBranch (Var := Var) v 1 (p2dSubReg rScr 74 1 hm)
      (fun fSel ↦ if fSel 0 then
        .circuit (cFixRowAnchored1BitAux 4 4 (by decide) le_rfl
          (fun h : Fin 4 ↦ rScr ⟨64 + h.val, by omega⟩)
          (rScr ⟨70, by omega⟩) (fun i ↦ rScr ⟨71 + i.val, by omega⟩)
          (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
          (fun _ _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega)) 4 le_rfl)
       else .identity)).count T = 0 :=
    Nat.le_zero.mp (count_measureXResetAndBranch_T_le_noFintype v 1 _ _ 0 fun fSel ↦ by
      cases fSel 0 <;> simp [cFixRowAnchored1BitAux_count_t])
  have h2 : (DynCircuitExt.measureXResetAndBranch (Var := Var) v 4 (p2dSubReg rScr 70 4 (by omega))
      (fun fRow ↦
        .circuit (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow 4 le_rfl))).count T = 0 :=
    Nat.le_zero.mp (count_measureXResetAndBranch_T_le_noFintype v 4 _ _ 0 fun fRow ↦ by
      simp [DynamicCircuit.count, cBranchFix4Rows218Aux_count_t])
  rw [h1, h2]
/-- Recursive prefix phase-kick circuit at `.hole` for `k ≤ 18` bits (`444 * k` `T` gates). -/
noncomputable def dPhaseKickHole218Aux {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (k : ℕ), k ≤ 18 → DynamicCircuit Var n
  | 0, _ => .identity
  | k + 1, hk =>
      .seq (dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS k (by omega))
           (dKick1Bit218 hm v ⟨k, hk⟩ rCore rMeas rScr hCS hMS)
/-- Full `18`-bit phase-kick dynamic circuit at `.hole` (`7,992 T`, `TOFF = 0`). -/
noncomputable def dPhaseKickHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) : DynamicCircuit Var n :=
  dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS 18 le_rfl
theorem dPhaseKickHole218Aux_count_toff {Var : Type}
    {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      (dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS k hk).count TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [dPhaseKickHole218Aux, DynamicCircuit.count]
      rw [dPhaseKickHole218Aux_count_toff hm v rCore rMeas rScr hCS hMS k (by omega),
          dKick1Bit218_count_toff]
theorem dPhaseKickHole218_count_toff {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dPhaseKickHole218 hm v rCore rMeas rScr hCS hMS).count TOFF = 0 :=
    dPhaseKickHole218Aux_count_toff hm v rCore rMeas rScr hCS hMS 18 le_rfl
theorem dPhaseKickHole218Aux_count_t {Var : Type}
    {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      (dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS k hk).count T = 444 * k
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [dPhaseKickHole218Aux, DynamicCircuit.count]
      rw [dPhaseKickHole218Aux_count_t hm v rCore rMeas rScr hCS hMS k (by omega),
          dKick1Bit218_count_t]
      omega
theorem dPhaseKickHole218_count_t {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dPhaseKickHole218 hm v rCore rMeas rScr hCS hMS).count T = 7992 :=
    dPhaseKickHole218Aux_count_t hm v rCore rMeas rScr hCS hMS 18 le_rfl
/-- Hadamard-conjugated load dynamic circuit at `.hole` (`7,992 T`, `TOFF = 0`). -/
noncomputable def dLoadHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) : DynamicCircuit Var n :=
  .seq (.circuit (cHadReg rMeas))
    (.seq (dPhaseKickHole218 hm v rCore rMeas rScr hCS hMS) (.circuit (cHadReg rMeas)))
theorem dLoadHole218_count_toff {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dLoadHole218 hm v rCore rMeas rScr hCS hMS).count TOFF = 0 := by
  dsimp only [dLoadHole218, DynamicCircuit.count]
  rw [cHadReg_count_toff, dPhaseKickHole218_count_toff]
theorem dLoadHole218_count_t {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dLoadHole218 hm v rCore rMeas rScr hCS hMS).count T = 7992 := by
  dsimp only [dLoadHole218, DynamicCircuit.count]
  rw [cHadReg_count_t, dPhaseKickHole218_count_t, zero_add, add_zero]
/-- Hadamard-conjugated write dynamic circuit at `.hole` (`7,992 T`, `TOFF = 0`). -/
noncomputable def dWriteHole218 {Var : Type} {n kData mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    DynamicCircuit Var n :=
  let rH := (rData.concat rMeas hDM).compose (selHadOfPosCore selCore)
  .seq (.circuit (cHadamardAll rH))
    (.seq (dLoadHole218 hm v (rData.compose selCore) rMeas rScr hCS hMS)
          (.circuit (cHadamardAll rH)))
theorem dWriteHole218_count_toff {Var : Type} {n kData mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dWriteHole218 hm v rData selCore rMeas rScr hDM hCS hMS).count TOFF = 0 := by
  dsimp only [dWriteHole218, DynamicCircuit.count]
  rw [count_cHadamardAll_toff, dLoadHole218_count_toff]
theorem dWriteHole218_count_t {Var : Type} {n kData mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dWriteHole218 hm v rData selCore rMeas rScr hDM hCS hMS).count T = 7992 := by
  dsimp only [dWriteHole218, DynamicCircuit.count]
  rw [count_cHadamardAll_t, dLoadHole218_count_t, zero_add, add_zero]
/-- Hole pre-circuit `dPreHole218` (`15,984 T`, `TOFF = 0`): `dLoadHole218 ;; dWriteHole218`. -/
noncomputable def dPreHole218 {Var : Type} {n kData mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    DynamicCircuit Var n := .seq
    (dLoadHole218 hm v (rData.compose selCore) rMeas rScr hCS hMS)
    (dWriteHole218 hm v rData selCore rMeas rScr hDM hCS hMS)
theorem dPreHole218_count_toff {Var : Type} {n kData mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dPreHole218 hm v rData selCore rMeas rScr hDM hCS hMS).count TOFF = 0 := by
  dsimp only [dPreHole218, DynamicCircuit.count]
  rw [dLoadHole218_count_toff, dWriteHole218_count_toff]
theorem dPreHole218_count_t {Var : Type} {n kData mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dPreHole218 hm v rData selCore rMeas rScr hDM hCS hMS).count T = 15984 := by
  dsimp only [dPreHole218, DynamicCircuit.count]
  rw [dLoadHole218_count_t, dWriteHole218_count_t]
theorem semigroup_comm2_idem {M : Type*} [Semigroup M] (P K W Q : M) (hPK : P * K = K * P)
    (hPW : P * W = W * P) (hPQ : P * Q = Q) : P * (K * W * Q) = K * W * Q := by
  calc
    P * (K * W * Q) = (P * K) * (W * Q) := by simp only [mul_assoc]
    _ = K * ((P * W) * Q) := by rw [hPK]; simp only [mul_assoc]
    _ = K * (W * (P * Q)) := by rw [hPW]; simp only [mul_assoc]
    _ = K * W * Q := by rw [hPQ]; simp only [mul_assoc]
theorem monoid_invol_conj {M : Type*} [Monoid M] (S Pm : M) (hS2 : S * S = 1) :
    S * (S * Pm * S) = Pm * S := by
  rw [← mul_assoc, ← mul_assoc, hS2, one_mul]
theorem semigroup_write_conj {M : Type*} [Semigroup M] (W S Pm T : M)
    (hWS : (W * S) * Pm = T * Pm) : W * (S * Pm * S) = T * Pm * S := by
  rw [← mul_assoc, ← mul_assoc, hWS]
theorem matrix_post_core {I : Type*} [Fintype I]
    (c : ℂ) (UF K W P0 ST Pm S : Matrix I I ℂ)
    (hWP : W * P0 = ST * Pm * S) (hTab : UF * K * ST * Pm = c • Pm) (hSP : Pm * S = S * P0) :
    UF * K * (W * P0) = c • (S * P0) := by
  calc
    UF * K * (W * P0) = (UF * K * ST * Pm) * S := by rw [hWP]; simp only [mul_assoc]
    _ = (c • Pm) * S := by rw [hTab]
    _ = c • (S * P0) := by rw [Matrix.smul_mul, hSP]
theorem matrix_post_tail {I : Type*} [Fintype I] (c : ℂ)
    (UF K W Ppost P0 Pbase S : Matrix I I ℂ) (hPost : Ppost = P0 * Pbase)
    (hCore : UF * K * (W * P0) = c • (S * P0)) : (UF * K * W) * Ppost = c • (S * Ppost) := by
  have hAssoc : (UF * K * W) * (P0 * Pbase) = (UF * K * (W * P0)) * Pbase := by
    simp only [mul_assoc]
  rw [hPost, hAssoc, hCore, Matrix.smul_mul, mul_assoc]
end StageBFastInnerPartnerShift
end SharedScope
end
end SlimStageBOuterDepsC2

noncomputable section SlimStageBOuterDepsD
set_option maxRecDepth 131072

set_option backward.isDefEq.respectTransparency false
section SharedScope
local instance (priority := 1000000) instNeZeroK12 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority :=
  1000000) instGroupUnitaryFast_SlimStageBOuterDepsD (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_SlimStageBOuterDepsD (D : ℕ) : Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open Operator QProg Matrix Real
open scoped Matrix BigOperators
namespace StageBFastInnerPartnerShift
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open AnchorSwap0Split133 MultiBankWStateRouter
open BoothOpt_02_Cached64x4TrueSwapEngine
/-! Row-loaded bit value for row `r : Fin 4` of the `64 × 4` `218`-slot table (`0 .. 217`, `KRem =
26`). -/
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
abbrev rowBit218 {n : ℕ} := @BoothOpt_Anchor218CachedTrueSwapOuter.rowBit218 n
theorem rowBit218_at_active {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    (β : BitAssignment n) (s₀ : Fin 218) :
    rowBit218 rCore j β (s₀.val % 64) (Nat.mod_lt _ (by decide))
        ⟨s₀.val / 64, by have := s₀.isLt; omega⟩ =
      β (rElecSlot rCore s₀ j) := by
  have h := BoothOpt_Anchor218CachedTrueSwapOuter.rowBit218_at_active
    rCore j β s₀.val (by have := s₀.isLt; omega)
  exact h.trans (congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (ite_eq_left s₀.isLt)))
abbrev cLoad4Rows218_eval_ket {n mScr : ℕ} :=
  @BoothOpt_Anchor218CachedTrueSwapOuter.cLoad4Rows218_eval_ket n mScr
abbrev cBranchFix4Rows218Aux_eval_ket {n mScr : ℕ} :=
  @BoothOpt_Anchor218CachedTrueSwapOuter.cBranchFix4Rows218Aux_eval_ket n mScr
/-- Single-bit `Z` kick dynamic circuit at `.hole` (`436 T`, `TOFF = 0`). -/
noncomputable abbrev dZKick1BitHole218 {Var : Type} {n mScr : ℕ} :=
  @BoothOpt_Anchor218CachedTrueSwapOuter.dZKick1BitHole218 Var n mScr
/-- Classical-branch phase-fix dynamic circuit at `.hole` (`≤ 436 T`, `TOFF = 0`) for outcome `f
  : Fin 18 → Bool`. -/
noncomputable abbrev dFixHole218 {Var : Type} {n mScr : ℕ} :=
  @BoothOpt_Anchor218CachedTrueSwapOuter.dFixHole218 Var n mScr
private theorem dFixHole218_counts {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (f : Fin 18 → Bool) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (dFixHole218 hm v f rCore rScr hCS).count TOFF = 0 ∧
    (dFixHole218 hm v f rCore rScr hCS).count T ≤ 436 := by
  dsimp only [dFixHole218, BoothOpt_Anchor218CachedTrueSwapOuter.dFixHole218]
  cases findTrueBitAux f 18 le_rfl with
  | none => exact ⟨rfl, Nat.zero_le 436⟩
  | some j₀ =>
      change ((DynamicCircuit.circuit (cSlotParityFanIn f j₀ rCore)).seq
        ((BoothOpt_Anchor218CachedTrueSwapOuter.dZKick1BitHole218 hm v j₀ rCore rScr hCS).seq
          (DynamicCircuit.circuit (cSlotParityFanIn f j₀ rCore)))).count PrimitiveGate.TOFF = 0 ∧
        ((DynamicCircuit.circuit (cSlotParityFanIn f j₀ rCore)).seq
        ((BoothOpt_Anchor218CachedTrueSwapOuter.dZKick1BitHole218 hm v j₀ rCore rScr hCS).seq
          (DynamicCircuit.circuit (cSlotParityFanIn f j₀ rCore)))).count PrimitiveGate.T ≤ 436
      dsimp only [BoothOpt_Anchor218CachedTrueSwapOuter.dZKick1BitHole218]
      let cont : (Fin 4 → Bool) → DynamicCircuit Var n :=
        fun fRow ↦ .circuit (cBranchFix4Rows218Aux hm j₀ rCore rScr hCS fRow 4 le_rfl)
      have h1 : (DynCircuitExt.measureXResetAndBranch v 4
          (p2dSubReg rScr 70 4 (by omega)) cont).count PrimitiveGate.TOFF = 0 :=
        Nat.le_zero.mp (count_measureXResetAndBranch_TOFF_le_noFintype v 4 _ cont 0 fun fRow ↦ by
          simp [cont, DynamicCircuit.count, cBranchFix4Rows218Aux_count_toff])
      have h2 : (DynCircuitExt.measureXResetAndBranch v 4
          (p2dSubReg rScr 70 4 (by omega)) cont).count PrimitiveGate.T = 0 :=
        Nat.le_zero.mp (count_measureXResetAndBranch_T_le_noFintype v 4 _ cont 0 fun fRow ↦ by
          simp [cont, DynamicCircuit.count, cBranchFix4Rows218Aux_count_t])
      obtain ⟨hFanToff0, hFanT⟩ := cSlotParityFanInAux_count f j₀ rCore 218 le_rfl
      obtain ⟨hCzToff0, hCzT⟩ := cCz4RowHi_count hm rScr
      have hFanToff : (cSlotParityFanInAux f j₀ rCore 218 le_rfl).count PrimitiveGate.TOFF = 0 :=
        hFanToff0
      have hCzToff : (cCz4RowHi hm rScr).count PrimitiveGate.TOFF = 0 := hCzToff0
      have hLToff : (BoothOpt_Anchor218CachedTrueSwapOuter.cLoad4Rows218
          hm j₀ rCore rScr hCS).count PrimitiveGate.TOFF = 0 :=
            cLoad4Rows218_count_toff hm j₀ rCore rScr hCS
      have hLT : (BoothOpt_Anchor218CachedTrueSwapOuter.cLoad4Rows218
          hm j₀ rCore rScr hCS).count PrimitiveGate.T = 436 :=
            cLoad4Rows218_count_t hm j₀ rCore rScr hCS
      dsimp only [cont, cBranchFix4Rows218Aux] at h1 h2
      simp only [DynamicCircuit.count, Circuit.count_seq, cSlotParityFanIn,
        hFanToff, hFanT, hLToff, hLT, hCzToff, hCzT, h1, h2]
      exact ⟨trivial, by omega⟩
theorem dFixHole218_count_toff {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (f : Fin 18 → Bool) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (dFixHole218 hm v f rCore rScr hCS).count TOFF = 0 :=
  (dFixHole218_counts (Var := Var) hm v f rCore rScr hCS).1
theorem dFixHole218_count_t_le {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (f : Fin 18 → Bool) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (dFixHole218 hm v f rCore rScr hCS).count T ≤ 436 :=
  (dFixHole218_counts (Var := Var) hm v f rCore rScr hCS).2
/-- Hole post-circuit `dPostHole218` (`≤ 8,428 T`, `TOFF = 0`). -/
noncomputable def dPostHole218 {Var : Type} {n kData mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    DynamicCircuit Var n := .seq (dWriteHole218 hm v rData selCore rMeas rScr hDM hCS hMS)
    (DynCircuitExt.measureXResetAndBranch v 18 rMeas (fun f ↦ dFixHole218 hm v f
    (rData.compose selCore) rScr hCS))
end StageBFastInnerPartnerShift
namespace BoothOpt_FastAnchorOuterAndStageBShave
open MeasureBranchHadamardSem
  (ket bitSign sqrtHalf bit_cases eval_seq_mulVec ket_H ket_X ket_CNOT ket_TOFF matrix_ext_ket)
open CoinDispatchedBarrel288.Internal (CliffProg)
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open AnchorSwap0Split133 MultiBankWStateRouter ParticleOneHotWState
open BoothOpt_02_Cached64x4TrueSwapEngine (CliffWritesAbove cliffWritesAbove_comm_embedUnitary)
open HermitianMat SpecsAux SpecsAux.SpecMirror
open PosSlots24Barrel3Pass CoinDispatchedBarrel288 FastCoinBarrelDecoder279
open Pass1BarrelIdxLoad273 BoothOpt_02_Cached64x4TrueSwapEngine
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
section DiagCtxWGImpl
open MeasureBranchHadamardSem (ket_projector_zero ket_projector_one)
/-- Decidable pairwise disjointness predicate on `Wire M` for a coherent zero-gated
`Pow2` W-state router. -/
def DisjWCohGate1 {D N M : ℕ} (wHas : Wire M) (wIdx : Fin D → Wire M) (wOut : Fin N → Wire M)
    (qEnc : Wire M) : Prop := (∀ j, wHas ≠ wOut j) ∧ wHas ≠ qEnc ∧ (∀ d j, wIdx d ≠ wOut j) ∧
    (∀ d, wIdx d ≠ qEnc) ∧ Function.Injective wOut ∧ (∀ j, wOut j ≠ qEnc)
theorem wRouterDisj_onRegister {D N M n : ℕ} (rComb : QRegister M n) {wHas : Wire M}
    {wIdx : Fin D → Wire M} {wOut : Fin N → Wire M} {qEnc : Wire M}
    (hd : DisjWCohGate1 wHas wIdx wOut qEnc) : WRouterDisj (rComb wHas)
    (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc) := ⟨fun j ↦
    rComb.wires.injective.ne (hd.1 j), rComb.wires.injective.ne hd.2.1, fun d j ↦
    rComb.wires.injective.ne (hd.2.2.1 d j), fun d ↦ rComb.wires.injective.ne (hd.2.2.2.1 d),
    fun _ _ hij ↦ rComb.wires.injective.ne (hd.2.2.2.2.1.ne hij), fun j ↦
    rComb.wires.injective.ne (hd.2.2.2.2.2 j)⟩
theorem wInj_w1Of {D n : ℕ} {wOut : Fin (2 ^ D) → Wire n}
    (hInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) :
    WInj (fun (_ : Fin 1) p ↦ wOut p) := fun b₁ p₁ b₂ p₂ heq ↦
  ⟨Subsingleton.elim b₁ b₂, Decidable.byContradiction fun hne ↦ hInj p₁ p₂ hne heq⟩
/-- Pre-measurement circuit for coherent zero-gated W-shift round `d < D` (`2 T`, `0` Toffoli). -/
def cCohShiftPre {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc) (hOutQ : ∀ p, wOut p ≠ qEnc)
    (d : ℕ) (hd : d < D) : Circuit n :=
  cnotOddToEnc 1 D (fun _ p ↦ wOut p) qEnc (fun _ p ↦ hOutQ p) d ;;ᶜ
  Circuit.X wHas ;;ᶜ
  chGateCirc wHas qEnc hHasQ ;;ᶜ
  Circuit.X wHas ;;ᶜ
  Circuit.CNOT (wIdx ⟨d, hd⟩) qEnc (hIdxQ ⟨d, hd⟩)
/-- Level `d < D` coherent zero-gated Z-measurement shift step (`2 T`, `0` Toffoli). -/
def wCohShiftLevel {Var : Type} {D n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (hHasQ : wHas ≠ qEnc)
    (hIdxQ : ∀ d, wIdx d ≠ qEnc) (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j)
    (hOutQ : ∀ p, wOut p ≠ qEnc) (d : ℕ) (hd : d < D) : DynamicCircuit Var n := .seq
    (.circuit (cCohShiftPre wHas wIdx wOut qEnc hHasQ hIdxQ hOutQ d hd)) (zResetFixupDyn v
    qEnc (barrelSwap 1 D (fun _ p ↦ wOut p) (wInj_w1Of hOutInj) d))
/-- First `m ≤ D` levels of `wCohShiftLevel` (`2 * m` `T`, `0` Toffoli). -/
def wCohShiftLevels {Var : Type} {D n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc)
    (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) (hOutQ : ∀ p, wOut p ≠ qEnc) :
    (m : ℕ) → m ≤ D → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | d + 1, hd =>
      .seq (wCohShiftLevels v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d
        (Nat.le_of_succ_le hd))
        (wCohShiftLevel v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d hd)
/-- Forward coherent zero-gated `Pow2` W-state one-hot router
(`2 * (2 ^ (k + 1) + k)` `T`, `0` Toffoli). -/
noncomputable def wStateComputeCohGate1 (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (qEnc : Wire n) : DynamicCircuit Var n :=
  if h : WRouterDisjProp wHas wIdx wOut qEnc then
    let hw := wInj_w1Of h.2.2.2.2.1
    .seq
      (.circuit (Circuit.CNOT wHas (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩) (h.1 _) ;;ᶜ
        wTreePrefix 1 (k + 1) (fun _ p ↦ wOut p) hw (k + 1) le_rfl))
      (wCohShiftLevels v wHas wIdx wOut qEnc h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (k + 1) le_rfl)
  else
    .circuit (seqNat (2 * (2 ^ (k + 1) + k)) fun _ _ ↦ Circuit.T wHas)
/-- MBU uncomputation for coherent zero-gated `Pow2` W-state one-hot router (`0 T`, `0` Toffoli). -/
noncomputable def wStateUncomputeCohGate1 (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) :
    DynamicCircuit Var n := if h : WRouterOutDisj wHas wIdx wOut then wUncompTreeDyn v 1
    (k + 1) wIdx (fun _ p ↦ wOut p) (wInj_w1Of h.2.2) (fun d _ p ↦ h.2.1 d p) (.circuit
    (Circuit.CNOT wHas (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩) (h.1 _))) (k + 1) le_rfl else
    .circuit .identity
/-- Operator mapping computational basis kets at coherent shift level `d ≤ D`
(`wSuperVec` on `wHas = 1`, `ket δ` on `wHas = 0`). -/
private noncomputable def wCohSuperOp {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (d : ℕ) (hd : d ≤ D) : Operator (2 ^ n) :=
    mkVecOp fun δ ↦ if (∀ p : Fin (2 ^ D), δ (wOut p) = 0) ∧ δ qEnc = 0 then if δ wHas = 1
    then wSuperVec (fun _ ↦ (0 : Fin 1)) wIdx (fun _ p ↦ wOut p) qEnc δ d hd else ket δ else 0

private theorem subspaceStep_wCohShiftLevel {Var : Type} [Fintype Var] [DecidableEq Var]
    {D n : ℕ} [NeZero (2 ^ n)] (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (hd : WRouterDisj wHas wIdx wOut qEnc)
    (d : ℕ) (hdLt : d < D) : SubspaceStep
    (wCohSuperOp wHas wIdx wOut qEnc d (Nat.le_of_lt hdLt))
    (wCohSuperOp wHas wIdx wOut qEnc (d + 1) hdLt) (wCohShiftLevel v wHas wIdx wOut qEnc
    hd.has_ne_q hd.idx_ne_q hd.out_inj hd.out_ne_q d hdLt) := by
  let w : Fin 1 → Fin (2 ^ D) → Wire n := fun _ p ↦ wOut p
  have hw : WInj w := wInj_w1Of hd.out_inj
  let cPre := cCohShiftPre wHas wIdx wOut qEnc hd.has_ne_q hd.idx_ne_q hd.out_ne_q d hdLt
  let cB := barrelSwap 1 D w hw d
  have hkd : D - d = D - (d + 1) + 1 := by omega
  let e : Fin (2 ^ (D - (d + 1))) ⊕ Fin (2 ^ (D - (d + 1))) ≃ Fin (2 ^ (D - d)) :=
    (finTwoMulEquiv (2 ^ (D - (d + 1)))).trans (finCongr (by rw [hkd, Nat.pow_succ]; ring))
  have hEv (q : Fin (2 ^ (D - (d + 1)))) : 2 * q.val < 2 ^ (D - d) := (e (.inl q)).isLt
  have hOd (q : Fin (2 ^ (D - (d + 1)))) : 2 * q.val + 1 < 2 ^ (D - d) := (e (.inr q)).isLt
  have hev (q : Fin (2 ^ (D - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true := by
    simp only [decide_eq_true_eq]
    omega
  have hod (q : Fin (2 ^ (D - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true := by
    simp only [decide_eq_true_eq]
    omega
  let pIn (δ : BitAssignment n) {hi : ℕ} (hhi : hi < 2 ^ (D - d)) : Fin (2 ^ D) :=
    ⟨idxValPrefix wIdx δ d (Nat.le_of_lt hdLt) + 2 ^ d * hi,
      shift_pos_lt (Nat.le_of_lt hdLt) (idxValPrefix_lt_two_pow wIdx δ d (Nat.le_of_lt hdLt)) hhi⟩
  let pOut (δ : BitAssignment n) (q : Fin (2 ^ (D - (d + 1)))) : Fin (2 ^ D) :=
    ⟨idxValPrefix wIdx δ (d + 1) hdLt + 2 ^ (d + 1) * q.val,
      shift_pos_lt hdLt (idxValPrefix_lt_two_pow wIdx δ (d + 1) hdLt) q.isLt⟩
  have hpOut0 (δ : BitAssignment n) (hu0 : δ (wIdx ⟨d, hdLt⟩) = 0)
      (q : Fin (2 ^ (D - (d + 1)))) : pIn δ (hEv q) = pOut δ q :=
    Fin.ext (by dsimp [pIn, pOut, idxValPrefix]; rw [ite_eq_right (by rw [hu0]; decide)]; ring)
  have hpOut1 (δ : BitAssignment n) (hu1 : δ (wIdx ⟨d, hdLt⟩) = 1)
      (q : Fin (2 ^ (D - (d + 1)))) : pIn δ (hOd q) = pOut δ q :=
    Fin.ext (by dsimp [pIn, pOut, idxValPrefix]; rw [ite_eq_left hu1]; ring)
  have hPreAct (δ : BitAssignment n) (hHas1 : δ wHas = 1)
      (hw0 : ∀ p, δ (wOut p) = 0) (hq0 : δ qEnc = 0) {hi : ℕ} (hhi : hi < 2 ^ (D - d)) :
      cPre.eval.1.mulVec (ket (Function.update δ (wOut (pIn δ hhi)) 1)) =
        ket (Function.update (Function.update δ (wOut (pIn δ hhi)) 1) qEnc
          ((if decide (hi % 2 = 1) then (1 : ZMod 2) else 0) + δ (wIdx ⟨d, hdLt⟩))) := by
    let pS := pIn δ hhi
    have h1 : cPre.eval.1.mulVec (ket (Function.update δ (w 0 pS) 1)) =
        (cnotOddToEnc 1 D w qEnc (fun _ p ↦ hd.out_ne_q p) d ;;ᶜ
          Circuit.CNOT (wIdx ⟨d, hdLt⟩) qEnc (hd.idx_ne_q ⟨d, hdLt⟩)).eval.1.mulVec
          (ket (Function.update δ (w 0 pS) 1)) := by
      dsimp only [cPre, cCohShiftPre]
      simp only [eval_seq_mulVec]
      rw [cnotOddToEnc_mulVec_ket w qEnc hw (fun _ p ↦ hd.out_ne_q p) d δ (fun _ p ↦
        hw0 p) hq0 0 pS]
      let β₁ := Function.update (Function.update δ (w 0 pS) 1) qEnc
        (if pS.val.testBit d then 1 else 0)
      have hβ₁Has : β₁ wHas = 1 := by
        dsimp only [β₁, w]
        rw [Function.update_of_ne hd.has_ne_q, Function.update_of_ne (hd.has_ne_out pS), hHas1]
      rw [show Function.update (Function.update δ (w 0 pS) 1) qEnc _ = β₁ from rfl,
        ket_X, hβ₁Has, show (1 : ZMod 2) + 1 = 0 from rfl,
        chGateCirc_mulVec_ket_zero wHas qEnc hd.has_ne_q _ (Function.update_self _ _ _),
        ket_X, Function.update_idem, Function.update_self, zero_add,
        (congrArg (Function.update β₁ wHas) hβ₁Has.symm).trans (Function.update_eq_self wHas β₁)]
    exact h1.trans (cnotOddAndIdx_mulVec_ket wIdx w qEnc hw (fun _ p ↦ hd.out_ne_q p)
      hd.idx_ne_q (fun d' _ p ↦ hd.idx_ne_out d' p) d hdLt δ (fun _ p ↦ hw0 p) hq0 0 hhi)
  have stepSplit (F : Operator (2 ^ n)) (hActPt : ∀ (δ : BitAssignment n) (_hw0 : ∀ p, δ (wOut
      p) = 0) (_hq0 : δ qEnc = 0) (q : Fin (2 ^ (D - (d + 1)))), F.mulVec (ket
      (Function.update (Function.update δ (wOut (pIn δ (hEv q))) 1) qEnc (δ (wIdx ⟨d,
      hdLt⟩)))) + F.mulVec (ket (Function.update (Function.update δ (wOut (pIn δ (hOd q))) 1)
      qEnc (1 + δ (wIdx ⟨d, hdLt⟩)))) = ket (Function.update δ (wOut (pOut δ q)) 1)) (hInact :
      ∀ (δ : BitAssignment n), (∀ p, δ (wOut p) = 0) → δ qEnc = 0 → F.mulVec (ket δ) +
      F.mulVec (ket (Function.update δ qEnc 1)) = ket δ) : F * (cPre.eval.1 * wCohSuperOp wHas
      wIdx wOut qEnc d (Nat.le_of_lt hdLt)) = sqrtHalf • wCohSuperOp wHas wIdx wOut qEnc
      (d + 1) hdLt := by
    apply matrix_ext_ket
    intro δ
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, wCohSuperOp, mkVecOp_mulVec_ket]
    by_cases hV : (∀ p : Fin (2 ^ D), δ (wOut p) = 0) ∧ δ qEnc = 0
    · have ⟨hw0, hq0⟩ := hV
      rw [ite_eq_left hV, ite_eq_left hV]
      rcases bit_cases (δ wHas) with hHas0 | hHas1
      · have hne1 : ¬ (δ wHas = 1) := by rw [hHas0]; decide
        rw [ite_eq_right hne1, ite_eq_right hne1]
        have hPre0 : cPre.eval.1.mulVec (ket δ) =
            sqrtHalf • (ket δ + ket (Function.update δ qEnc 1)) := by
          dsimp only [cPre, cCohShiftPre]
          simp only [eval_seq_mulVec]
          rw [cnotOddToEnc_mulVec_ket_zero (fun (_ : Fin 1) p ↦ wOut p) qEnc
            (fun _ p ↦ hd.out_ne_q p) d δ (fun _ p ↦ hw0 p)]
          let δ₁ := Function.update δ wHas 1
          have hq1 : δ₁ qEnc = 0 := (Function.update_of_ne hd.has_ne_q.symm 1 δ).trans hq0
          rw [ket_X, hHas0, zero_add, show Function.update δ wHas 1 = δ₁ from rfl,
            chGateCirc_mulVec_ket_one wHas qEnc hd.has_ne_q δ₁ (Function.update_self _ _ _),
            ket_H qEnc δ₁, hq1, show bitSign (0 : ZMod 2) = (1 : ℂ) from rfl, one_smul,
            update_eq_self_of_zero hq1]
          simp only [δ₁, Matrix.mulVec_smul, Matrix.mulVec_add, ket_X,
            Function.update_comm hd.has_ne_q, Function.update_idem, Function.update_self,
            CharTwo.add_self_eq_zero, update_eq_self_of_zero hHas0,
            update_eq_self_of_zero ((Function.update_of_ne hd.has_ne_q 1 δ).trans hHas0)]
          refine congrArg (sqrtHalf • ·) ?_
          rcases bit_cases (δ (wIdx ⟨d, hdLt⟩)) with hu0 | hu1
          · rw [ket_CNOT_ctrl_zero _ hu0,
              ket_CNOT_ctrl_zero _ ((Function.update_of_ne (hd.idx_ne_q ⟨d, hdLt⟩) 1 δ).trans hu0)]
          · rw [ket_CNOT, hq0, hu1, zero_add, ket_CNOT, Function.update_self,
              Function.update_of_ne (hd.idx_ne_q ⟨d, hdLt⟩), hu1,
              CharTwo.add_self_eq_zero, Function.update_idem, update_eq_self_of_zero hq0, add_comm]
        rw [hPre0, Matrix.mulVec_smul, Matrix.mulVec_add, hInact δ hw0 hq0]
      · rw [ite_eq_left hHas1, ite_eq_left hHas1]
        dsimp only [wSuperVec]
        have hV' : (∀ (b : Fin 1) (p : Fin (2 ^ D)), δ (wOut p) = 0) ∧ δ qEnc = 0 :=
          ⟨fun _ p ↦ hw0 p, hq0⟩
        rw [ite_eq_left hV', ite_eq_left hV',
          Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_sum,
          show sqrtHalf ^ (D - d) = sqrtHalf * sqrtHalf ^ (D - (d + 1)) by
            rw [hkd, _root_.pow_succ'],
          smul_smul]
        refine congrArg ((sqrtHalf * sqrtHalf ^ (D - (d + 1))) • ·) ?_
        rw [← e.sum_comp, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        change F.mulVec (cPre.eval.1.mulVec (ket (Function.update δ (wOut (pIn δ (hEv q))) 1))) +
          F.mulVec (cPre.eval.1.mulVec (ket (Function.update δ (wOut (pIn δ (hOd q))) 1))) =
          ket (Function.update δ (wOut (pOut δ q)) 1)
        rw [hPreAct δ hHas1 hw0 hq0 (hEv q), ite_eq_right (hev q), zero_add,
          hPreAct δ hHas1 hw0 hq0 (hOd q), ite_eq_left (hod q)]
        exact hActPt δ hw0 hq0 q
    · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  have hqId (δ : BitAssignment n) (hq0 : δ qEnc = 0) (p : Fin (2 ^ D)) :
      Function.update (Function.update δ (wOut p) 1) qEnc 0 = Function.update δ (wOut p) 1 :=
    update_eq_self_of_zero ((Function.update_of_ne (hd.out_ne_q p).symm 1 δ).trans hq0)
  let P₀ := (QRegister.singleton qEnc).basisOutcomeProjector 0
  let F₁ := cB.eval.1 * (Circuit.X qEnc).eval.1 *
    (QRegister.singleton qEnc).basisOutcomeProjector 1
  have hF₁_0 (δ : BitAssignment n) (p : Fin (2 ^ D)) :
      F₁.mulVec (ket (Function.update (Function.update δ (wOut p) 1) qEnc 0)) = 0 := by
    dsimp only [F₁]
    rw [← Matrix.mulVec_mulVec, ket_projector_one, Function.update_self,
      ite_eq_right zero_ne_one, Matrix.mulVec_zero]
  have hF₁_1 (δ : BitAssignment n) (hq0 : δ qEnc = 0) (p : Fin (2 ^ D)) :
      F₁.mulVec (ket (Function.update (Function.update δ (wOut p) 1) qEnc 1)) =
        cB.eval.1.mulVec (ket (Function.update δ (wOut p) 1)) := by
    dsimp only [F₁]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector_one, Function.update_self,
      ite_eq_left rfl, ket_X, Function.update_self, CharTwo.add_self_eq_zero,
      Function.update_idem, hqId δ hq0]
  refine subspaceStep_seq_zResetFixup v qEnc cB
    (subspaceStep_of_circuit (Var := Var)
      (wCohSuperOp wHas wIdx wOut qEnc d (Nat.le_of_lt hdLt)) cPre)
    (stepSplit P₀ ?_ ?_) (stepSplit F₁ ?_ ?_)
  · intro δ _hw0 hq0 q
    dsimp only [P₀]
    rcases bit_cases (δ (wIdx ⟨d, hdLt⟩)) with hu0 | hu1
    · rw [hu0, add_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
        ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero, add_zero, hqId δ hq0,
        hpOut0 δ hu0 q]
    · rw [hu1, CharTwo.add_self_eq_zero, ket_projector_zero, Function.update_self,
        ite_eq_right one_ne_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
        zero_add, hqId δ hq0, hpOut1 δ hu1 q]
  · intro δ _hw0 hq0
    dsimp only [P₀]
    rw [ket_projector_zero, ite_eq_left hq0, ket_projector_zero, Function.update_self,
      ite_eq_right one_ne_zero, add_zero]
  · intro δ hw0 hq0 q
    let lo := idxValPrefix wIdx δ d (Nat.le_of_lt hdLt)
    have hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow wIdx δ d (Nat.le_of_lt hdLt)
    have hpLo : lo + 2 ^ d * (2 * q.val) < 2 ^ D := (pIn δ (hEv q)).isLt
    have htbLo : (lo + 2 ^ d * (2 * q.val)).testBit d = false := by
      rw [testBit_lo_add_mul_two_pow hlo]
      simp only [decide_eq_false_iff_not]
      omega
    have hpHi : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d < 2 ^ D := by
      rw [show (lo + 2 ^ d * (2 * q.val)) + 2 ^ d = lo + 2 ^ d * (2 * q.val + 1) by ring]
      exact (pIn δ (hOd q)).isLt
    have hpLoEq : (⟨lo + 2 ^ d * (2 * q.val), hpLo⟩ : Fin (2 ^ D)) = pIn δ (hEv q) := rfl
    have hpHiEq : (⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi⟩ : Fin (2 ^ D)) = pIn δ (hOd q) :=
      Fin.ext (by dsimp [pIn, lo]; ring)
    rcases bit_cases (δ (wIdx ⟨d, hdLt⟩)) with hu0 | hu1
    · rw [hu0, add_zero, hF₁_0, hF₁_1 δ hq0, zero_add]
      simpa only [cB, w, ↓reduceIte, hpLoEq, hpHiEq, hpOut0 δ hu0 q] using
        barrelSwap_mulVec_ket_pair w hw d δ (fun _ p ↦ hw0 p) 0 hpLo htbLo hpHi true
    · rw [hu1, CharTwo.add_self_eq_zero, hF₁_1 δ hq0, hF₁_0, add_zero]
      simpa only [cB, w, Bool.false_eq_true, ↓reduceIte, hpLoEq, hpHiEq, hpOut1 δ hu1 q] using
        barrelSwap_mulVec_ket_pair w hw d δ (fun _ p ↦ hw0 p) 0 hpLo htbLo hpHi false
  · intro δ hw0 hq0
    dsimp only [F₁, cB]
    rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector_one,
        ite_eq_right (hq0.trans_ne zero_ne_one), Matrix.mulVec_zero, Matrix.mulVec_zero,
        zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector_one,
        Function.update_self, ite_eq_left rfl, ket_X, Function.update_idem,
        Function.update_self, CharTwo.add_self_eq_zero, update_eq_self_of_zero hq0,
        barrelSwap_mulVec_ket_zero w hw d δ (fun _ p ↦ hw0 p)]

/-- Symmetric clean-ancilla context extending `DiagCtxW` with coherent zero-gated
`Pow2` W-state routers. -/
inductive DiagCtxWG (M : ℕ) where
  | hole : DiagCtxWG M
  | cliffConj (c : CliffProg M) (K : DiagCtxWG M) : DiagCtxWG M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (K : DiagCtxWG M) : DiagCtxWG M
  | wStateTree (k : ℕ) (wIdx : Fin (k + 1) → Wire M) (wOut : Fin (2 ^ (k + 1)) → Wire M)
      (qEnc : Wire M) (hd : DisjWUncond wIdx wOut qEnc)
      (K : DiagCtxWG M) : DiagCtxWG M
  | wStateTreeCohGate1 (k : ℕ) (wHas : Wire M) (wIdx : Fin (k + 1) → Wire M)
      (wOut : Fin (2 ^ (k + 1)) → Wire M) (qEnc : Wire M)
      (hd : DisjWCohGate1 wHas wIdx wOut qEnc)
      (K : DiagCtxWG M) : DiagCtxWG M
namespace DiagCtxWG
/-- Forward classical bit-state map of a `DiagCtxWG M` context. -/
def fwdBits {M : ℕ} : DiagCtxWG M → BitAssignment M → BitAssignment M
  | .hole, γ => γ
  | .cliffConj c K, γ => K.fwdBits (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      K.fwdBits (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut _ _ K, γ =>
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.fwdBits (Function.update γ (wOut j) (γ (wOut j) + 1))
  | .wStateTreeCohGate1 _ wHas wIdx wOut _ _ K, γ =>
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.fwdBits (Function.update γ (wOut j) (γ (wOut j) + γ wHas))
/-- Clean-ancilla precondition along `DiagCtxWG M`. -/
def ValidAt {M : ℕ} : DiagCtxWG M → BitAssignment M → Prop
  | .hole, _ => True
  | .cliffConj c K, γ => K.ValidAt (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      γ anc = 0 ∧ K.ValidAt (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut qEnc _ K, γ =>
      ((∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0) ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.ValidAt (Function.update γ (wOut j) (γ (wOut j) + 1))
  | .wStateTreeCohGate1 _ wHas wIdx wOut qEnc _ K, γ =>
      ((∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0) ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.ValidAt (Function.update γ (wOut j) (γ (wOut j) + γ wHas))
/-- Combined clean-ancilla + hole-invariant precondition along `DiagCtxWG M`. -/
def ValidAtWith {M : ℕ} (InvHole : BitAssignment M → Prop) :
    DiagCtxWG M → BitAssignment M → Prop
  | .hole, γ => InvHole γ
  | .cliffConj c K, γ => ValidAtWith InvHole K (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      γ anc = 0 ∧ ValidAtWith InvHole K (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut qEnc _ K, γ =>
      (∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0 ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      ValidAtWith InvHole K (Function.update γ (wOut j) (γ (wOut j) + 1))
  | .wStateTreeCohGate1 _ wHas wIdx wOut qEnc _ K, γ =>
      (∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0 ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      ValidAtWith InvHole K (Function.update γ (wOut j) (γ (wOut j) + γ wHas))
theorem validAtWith_of_validAt {M : ℕ} {InvHole : BitAssignment M → Prop} :
    ∀ (K : DiagCtxWG M) {γ : BitAssignment M},
      K.ValidAt γ → InvHole (K.fwdBits γ) → K.ValidAtWith InvHole γ
  | .hole, _, _, hI => hI
  | .cliffConj _ K, _, hV, hI => validAtWith_of_validAt K hV hI
  | .tempAnd _ _ _ _ _ _ K, _, ⟨h0, hV⟩, hI =>
      ⟨h0, validAtWith_of_validAt K hV hI⟩
  | .wStateTree _ _ _ _ _ K, _, ⟨⟨hOut0, hq0⟩, hV⟩, hI =>
      ⟨hOut0, hq0, validAtWith_of_validAt K hV hI⟩
  | .wStateTreeCohGate1 _ _ _ _ _ _ K, _, ⟨⟨hOut0, hq0⟩, hV⟩, hI =>
      ⟨hOut0, hq0, validAtWith_of_validAt K hV hI⟩
/-- Exact `T`-gate count added by a `DiagCtxWG M` wrapper. -/
def countT {M : ℕ} : DiagCtxWG M → ℕ
  | .hole => 0
  | .cliffConj _ K => K.countT
  | .tempAnd _ _ _ _ _ _ K => 4 + K.countT
  | .wStateTree k _ _ _ _ K => 4 * (2 ^ k - 1) + K.countT
  | .wStateTreeCohGate1 k _ _ _ _ _ K => 2 * (2 ^ (k + 1) + k) + K.countT
theorem wStateTreeCohGate1_step {M : ℕ} (k : ℕ) (wHas : Wire M) (wIdx : Fin (k + 1) → Wire M)
    (wOut : Fin (2 ^ (k + 1)) → Wire M) (qEnc : Wire M)
    (hd : DisjWCohGate1 wHas wIdx wOut qEnc) (body : DiagCtxWG M) (γ : BitAssignment M)
    (hOut0 : ∀ j : Fin (2 ^ (k + 1)), γ (wOut j) = 0) (hq0 : γ qEnc = 0) : ∃ γ' :
    BitAssignment M, (DiagCtxWG.wStateTreeCohGate1 k wHas wIdx wOut qEnc hd body).fwdBits γ =
    body.fwdBits γ' ∧ (body.ValidAt γ' → (DiagCtxWG.wStateTreeCohGate1 k wHas wIdx wOut qEnc
    hd body).ValidAt γ) ∧ (∀ j : Fin (2 ^ (k + 1)), γ' (wOut j) = if j.val = bitsVal (fun i :
    Fin (k + 1) ↦ γ (wIdx i)) then γ wHas else 0) ∧
    (∀ w : Wire M, (∀ j : Fin (2 ^ (k + 1)), w ≠ wOut j) → γ' w = γ w) := by
  let j₀ : Fin (2 ^ (k + 1)) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
  have hj₀ : j₀.val = bitsVal (fun i : Fin (k + 1) ↦ γ (wIdx i)) :=
    idxValD_eq_bitsVal (k + 1) wIdx γ
  refine ⟨Function.update γ (wOut j₀) (γ (wOut j₀) + γ wHas), rfl, fun hV ↦ ⟨⟨hOut0, hq0⟩, hV⟩,
    fun j ↦ ?_, fun w hw ↦ Function.update_of_ne (hw j₀) _ _⟩
  by_cases hj : j.val = bitsVal (fun i : Fin (k + 1) ↦ γ (wIdx i))
  · rw [ite_eq_left hj, Fin.ext (hj.trans hj₀.symm), Function.update_self, hOut0 j₀, zero_add]
  · rw [ite_eq_right hj,
      Function.update_of_ne (fun h ↦ hj ((congrArg Fin.val (hd.2.2.2.2.1 h)).trans hj₀)), hOut0 j]
end DiagCtxWG
/-- Dynamic-circuit lowering of `DiagCtxWG M` around `inner`. -/
noncomputable def toDynWG {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) : DiagCtxWG M → DynamicCircuit Var n
  | .hole => inner
  | .cliffConj c K =>
      .seq (.circuit (c.onRegister rComb).toCircuit)
        (.seq (toDynWG v rComb inner K) (.circuit (c.inv.onRegister rComb).toCircuit))
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      .seq (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
              (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a))
        (.seq (toDynWG v rComb inner K)
          (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂)))
  | .wStateTree k wIdx wOut qEnc _ K =>
      .seq (wStateComputeUncondPow2 k v
              (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc))
        (.seq (toDynWG v rComb inner K)
          (wStateUncomputeUncondPow2 k v (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))))
  | .wStateTreeCohGate1 k wHas wIdx wOut qEnc _ K =>
      .seq (wStateComputeCohGate1 k v (rComb wHas)
              (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc))
        (.seq (toDynWG v rComb inner K)
          (wStateUncomputeCohGate1 k v (rComb wHas)
            (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))))
private theorem toDynWG_counts {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) (K : DiagCtxWG M) : (toDynWG v rComb inner K).count T =
    K.countT + inner.count T ∧ (toDynWG v rComb inner K).count TOFF = inner.count TOFF := by
  induction K with
  | hole => exact ⟨by simp [toDynWG, DiagCtxWG.countT], rfl⟩
  | cliffConj c K ih =>
      exact ⟨by
          simp [toDynWG, DiagCtxWG.countT, DynamicCircuit.count,
          CliffProg.toCircuit_count_t (c.onRegister rComb),
          CliffProg.toCircuit_count_t (c.inv.onRegister rComb), ih.1],
        by simp [toDynWG, DynamicCircuit.count,
          CliffProg.toCircuit_count_toff (c.onRegister rComb),
          CliffProg.toCircuit_count_toff (c.inv.onRegister rComb), ih.2]⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K ih =>
      change 4 + ((toDynWG v rComb inner K).count T + 0) = 4 + K.countT + inner.count T ∧
        0 + ((toDynWG v rComb inner K).count TOFF + 0) = inner.count TOFF
      rw [ih.1, ih.2]
      exact ⟨by omega, by omega⟩
  | wStateTree k wIdx wOut qEnc _ K ih =>
      obtain ⟨t1, f1⟩ := count_wStateComputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc)
      obtain ⟨t2, f2⟩ := count_wStateUncomputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
      dsimp only [toDynWG, DiagCtxWG.countT, DynamicCircuit.count]
      rw [t1, f1, t2, f2, ih.1, ih.2]
      exact ⟨by omega, by omega⟩
  | wStateTreeCohGate1 k wHas wIdx wOut qEnc hd K ih =>
      have h : WRouterDisjProp (rComb wHas) (fun d ↦ rComb (wIdx d))
          (fun l ↦ rComb (wOut l)) (rComb qEnc) := (wRouterDisj_onRegister rComb hd).disjProp
      have hShift : ∀ (m : ℕ) (hm : m ≤ k + 1),
          (wCohShiftLevels v (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
            (rComb qEnc) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 m hm).count T = 2 * m ∧
          (wCohShiftLevels v (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
            (rComb qEnc) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 m hm).count TOFF = 0 := by
        intro m
        induction m with
        | zero => exact fun _ ↦ ⟨rfl, rfl⟩
        | succ d ihS =>
            intro hdLt
            obtain ⟨t0, f0⟩ := ihS (Nat.le_of_succ_le hdLt)
            obtain ⟨to_, fo_⟩ := count_cnotOddToEnc 1 (k + 1) (fun _ p ↦ rComb (wOut p))
              (rComb qEnc) (fun _ p ↦ h.2.2.2.2.2 p) d
            obtain ⟨tc, fc⟩ := count_chGateCirc (rComb wHas) (rComb qEnc) h.2.1
            obtain ⟨tb, fb⟩ := count_barrelSwap 1 (k + 1) (fun _ p ↦ rComb (wOut p))
              (wInj_w1Of h.2.2.2.2.1) d
            refine ⟨?_, ?_⟩
            · simp [wCohShiftLevels, wCohShiftLevel, cCohShiftPre, DynamicCircuit.count,
                Circuit.count_seq, Circuit.X, Circuit.CNOT, count_zResetFixupDyn_t, t0, to_, tc, tb]
              omega
            · simp [wCohShiftLevels, wCohShiftLevel, cCohShiftPre, DynamicCircuit.count,
                Circuit.count_seq, Circuit.X, Circuit.CNOT, count_zResetFixupDyn_toff, f0, fo_, fc,
                fb]
      obtain ⟨tt, tf⟩ := count_wTreePrefix 1 (k + 1) (fun _ p ↦ rComb (wOut p))
        (wInj_w1Of h.2.2.2.2.1) (k + 1) le_rfl
      obtain ⟨st, sf⟩ := hShift (k + 1) le_rfl
      have hOutD : WRouterOutDisj (rComb wHas) (fun d ↦ rComb (wIdx d))
          (fun l ↦ rComb (wOut l)) := ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩
      obtain ⟨ut, uf⟩ := count_wUncompTreeDyn_opt v 1 (k + 1) (fun d ↦ rComb (wIdx d))
        (fun _ l ↦ rComb (wOut l)) (wInj_w1Of hOutD.2.2) (fun d _ l ↦ hOutD.2.1 d l)
        (.circuit (Circuit.CNOT (rComb wHas) (rComb (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩))
          (hOutD.1 _))) (k + 1) le_rfl
      dsimp only [toDynWG, DiagCtxWG.countT, wStateComputeCohGate1, wStateUncomputeCohGate1]
      rw [dite_eq_left h, dite_eq_left hOutD]
      dsimp only [DynamicCircuit.count]
      rw [Circuit.count_seq, Circuit.count_seq, tt, tf, st, sf, ut, uf, ih.1, ih.2]
      have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      refine ⟨?_, ?_⟩
      · simp [DynamicCircuit.count, Circuit.CNOT]
        omega
      · simp [DynamicCircuit.count, Circuit.CNOT]
theorem toDynWG_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) (K : DiagCtxWG M) : (toDynWG v rComb inner K).count TOFF =
    inner.count TOFF := (toDynWG_counts v rComb inner K).2
theorem toDynWG_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) (K : DiagCtxWG M) : (toDynWG v rComb inner K).count T =
    K.countT + inner.count T := (toDynWG_counts v rComb inner K).1
/-- `DiagCtxWG M` predicate certifying all wires written by `toDynWG` have index `≥ base`. -/
def DiagCtxWGWritesAbove {M : ℕ} (base : ℕ) : DiagCtxWG M → Prop
  | .hole => True
  | .cliffConj c K => CliffWritesAbove base c ∧ DiagCtxWGWritesAbove base K
  | .tempAnd _ _ anc _ _ _ K => base ≤ anc.val ∧ DiagCtxWGWritesAbove base K
  | .wStateTree _ _ wOut _ _ K =>
      (∀ l, base ≤ (wOut l).val) ∧ DiagCtxWGWritesAbove base K
  | .wStateTreeCohGate1 _ _ _ wOut _ _ K =>
      (∀ l, base ≤ (wOut l).val) ∧ DiagCtxWGWritesAbove base K
/-- Semantic commutation predicate for `DiagCtxWG M` with `U₀ : Unitary (2 ^ n)`. -/
def DiagCtxWGCommutesWith {M n : ℕ} (rComb : QRegister M n) (U₀ : Unitary (2 ^ n)) :
    DiagCtxWG M → Prop
  | .hole => True
  | .cliffConj c K₁ =>
      (c.inv.onRegister rComb).toCircuit.eval * U₀ = U₀ * (c.inv.onRegister rComb).toCircuit.eval ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ =>
      let cToff := Circuit.gate TOFF (QRegister.triple (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
          (rComb.wires.injective.ne h₂a))
      cToff.eval * U₀ = U₀ * cToff.eval ∧
      (∀ g' g : Fin (2 ^ n), U₀.1 g' g ≠ 0 →
        basisBits n g' (rComb anc) = basisBits n g (rComb anc)) ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
  | .wStateTree k wIdx wOut _ hd K₁ =>
      let hdN := wUncondDisjProp_onRegister rComb hd
      let uOH := uOneHotUncond (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) hdN.1
      uOH * U₀ = U₀ * uOH ∧
      (∀ (l : Fin (2 ^ (k + 1))) (g' g : Fin (2 ^ n)), U₀.1 g' g ≠ 0 →
        basisBits n g' (rComb (wOut l)) = basisBits n g (rComb (wOut l))) ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
  | .wStateTreeCohGate1 k wHas wIdx wOut _ hd K₁ =>
      let hdN := wRouterDisj_onRegister rComb hd
      let uOH := uOneHotToggle (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
        hdN.has_ne_out hdN.idx_ne_out
      uOH * U₀ = U₀ * uOH ∧
      (∀ (l : Fin (2 ^ (k + 1))) (g' g : Fin (2 ^ n)), U₀.1 g' g ≠ 0 →
        basisBits n g' (rComb (wOut l)) = basisBits n g (rComb (wOut l))) ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
private theorem cliffWritesAbove_inv_local {M : ℕ} {base : ℕ} :
    ∀ {c : CliffProg M}, CliffWritesAbove base c → CliffWritesAbove base c.inv
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨cliffWritesAbove_inv_local h₂, cliffWritesAbove_inv_local h₁⟩
private theorem embedUnitary_pres_not_mem {n kAct : ℕ} (rAct : QRegister kAct n)
    (V : Unitary (2 ^ kAct)) {w : Wire n} (hw : w ∉ Set.range rAct.wires) (g' g : Fin (2 ^ n))
    (hnz : (rAct.embedUnitary V).1 g' g ≠ 0) : basisBits n g' w = basisBits n g w := by
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
  split_ifs at hnz with henv
  · exact ((rAct.basisSplit_environment_eq_iff g' g).mp henv) w hw
  · simp at hnz
theorem diagCtxWGWritesAbove_to_commutesWith {M n kAct : ℕ}
    (rAct : QRegister kAct n) (V : Unitary (2 ^ kAct))
    (rComb : QRegister M n) (base : ℕ)
    (hOutNotAct : ∀ idx : Wire M, base ≤ idx.val → rComb idx ∉ Set.range rAct.wires)
    (hCombPres : ∀ (idx : Wire M) (g : Fin (2 ^ n)) (y : Fin (2 ^ kAct)),
      V.1 y (rAct.extractIndex g) ≠ 0 →
      basisBits n (rAct.replaceIndex g y) (rComb idx) = basisBits n g (rComb idx)) :
    ∀ {K : DiagCtxWG M}, DiagCtxWGWritesAbove base K →
      DiagCtxWGCommutesWith rComb (rAct.embedUnitary V) K
  | .hole, _ => trivial
  | .cliffConj _ _, ⟨hc, hK⟩ =>
      ⟨cliffWritesAbove_comm_embedUnitary rAct V rComb base hOutNotAct hCombPres
        (cliffWritesAbove_inv_local hc),
       diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a _, ⟨hanc, hK⟩ =>
      ⟨comm_embedUnitary_of_update_outside rAct V
          (Circuit.gate TOFF (QRegister.triple (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
            (rComb.wires.injective.ne h₂a)))
          (rComb anc) (hOutNotAct anc hanc) (fun β ↦ β (rComb c₁) * β (rComb c₂))
          (ket_TOFF (rComb c₁) (rComb c₂) (rComb anc) (rComb.wires.injective.ne h₁₂)
            (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a))
          (fun g y hnz ↦ by rw [hCombPres c₁ g y hnz, hCombPres c₂ g y hnz]),
       embedUnitary_pres_not_mem rAct V (hOutNotAct anc hanc),
       diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
  | .wStateTree _ wIdx wOut _ hd _, ⟨hOut, hK⟩ =>
      ⟨comm_embedUnitary_uOneHotUncond rAct V
          (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
          (wUncondDisjProp_onRegister rComb hd).1
          (fun l ↦ hOutNotAct (wOut l) (hOut l))
          (fun d g y hnz ↦ hCombPres (wIdx d) g y hnz),
       fun l ↦ embedUnitary_pres_not_mem rAct V (hOutNotAct (wOut l) (hOut l)),
       diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
  | .wStateTreeCohGate1 k wHas wIdx wOut _ hd _, ⟨hOut, hK⟩ => by
      have hdN := wRouterDisj_onRegister rComb hd
      let wHasN := rComb wHas
      let wIdxN : Fin (k + 1) → Wire n := fun d ↦ rComb (wIdx d)
      let wOutN : Fin (2 ^ (k + 1)) → Wire n := fun l ↦ rComb (wOut l)
      have hOutNot : ∀ j : Fin (2 ^ (k + 1)), wOutN j ∉ Set.range rAct.wires :=
        fun j ↦ hOutNotAct (wOut j) (hOut j)
      refine ⟨Subtype.ext (matrix_ext_ket fun β ↦ ?_),
        fun l ↦ embedUnitary_pres_not_mem rAct V (hOutNot l),
        diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
      obtain ⟨g, rfl⟩ : ∃ g, basisBits n g = β := (basisBitsEquiv n).surjective β
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      let j₀ : Fin (2 ^ (k + 1)) := ⟨idxValD wIdxN (basisBits n g), idxValD_lt_two_pow _ _⟩
      let β' := Function.update (basisBits n g) (wOutN j₀)
        (basisBits n g (wOutN j₀) + basisBits n g wHasN)
      let g' := (basisBitsEquiv n).symm β'
      have hg' : basisBits n g' = β' := (basisBitsEquiv n).apply_symm_apply β'
      have hExEq : rAct.extractIndex g' = rAct.extractIndex g :=
        (basisBitsEquiv kAct).injective <| funext fun i ↦ by
          change basisBits kAct (rAct.extractIndex g') i = basisBits kAct (rAct.extractIndex g) i
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hg']
          exact Function.update_of_ne (fun h ↦ hOutNot j₀ ⟨i, h⟩) _ _
      rw [uOneHotToggle_mulVec_ket wHasN wIdxN wOutN hdN.has_ne_out hdN.idx_ne_out (basisBits n g),
        show toggleOneHotBits wHasN wIdxN wOutN (basisBits n g) = β' from
          dite_eq_left (idxValD_lt_two_pow wIdxN (basisBits n g)),
        ← single_eq_ket_basisBits g, p2d_ket_eq_single β', QRegister.embedUnitary_val,
        embedMatrix_mulVec_single_sum rAct V.1 g, embedMatrix_mulVec_single_sum rAct V.1 g',
        hExEq, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      by_cases hnz : V.1 y (rAct.extractIndex g) = 0
      · simp [hnz]
      · rw [Matrix.mulVec_smul]
        refine congrArg (V.1 y (rAct.extractIndex g) • ·) ?_
        let gy := rAct.replaceIndex g y
        have hLtGy : idxValD wIdxN (basisBits n gy) < 2 ^ (k + 1) :=
          idxValD_lt_two_pow wIdxN (basisBits n gy)
        have hjEq : (⟨idxValD wIdxN (basisBits n gy), hLtGy⟩ : Fin (2 ^ (k + 1))) = j₀ :=
          Fin.ext <| by
            dsimp only [j₀]
            rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
            exact congrArg bitsVal (funext fun d ↦ hCombPres (wIdx d) g y hnz)
        rw [single_eq_ket_basisBits gy, single_eq_ket_basisBits (rAct.replaceIndex g' y),
          uOneHotToggle_mulVec_ket wHasN wIdxN wOutN hdN.has_ne_out hdN.idx_ne_out (basisBits n gy),
          show toggleOneHotBits wHasN wIdxN wOutN (basisBits n gy) =
              Function.update (basisBits n gy) (wOutN j₀)
                (basisBits n g (wOutN j₀) + basisBits n g wHasN) by
            dsimp only [toggleOneHotBits, gy]
            rw [dite_eq_left hLtGy, hjEq,
              rAct.basisBits_replaceIndex_of_not_mem g y _ (hOutNot j₀),
              hCombPres wHas g y hnz]]
        refine congrArg ket (funext fun q ↦ ?_)
        by_cases hqD : q ∈ Set.range rAct.wires
        · obtain ⟨i, rfl⟩ := hqD
          dsimp only [gy]
          rw [Function.update_of_ne (fun h ↦ hOutNot j₀ ⟨i, h⟩),
            QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
        · rw [rAct.basisBits_replaceIndex_of_not_mem g' y q hqD, hg']
          by_cases hqw : q = wOutN j₀
          · subst hqw
            simp only [β', Function.update_self]
          · simp only [β', gy, Function.update_of_ne hqw,
              rAct.basisBits_replaceIndex_of_not_mem g y q hqD]

private theorem ketPredProj_step_ket {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (g : BitAssignment n → BitAssignment n)
    (hM : ∀ α, S₁ α → M.mulVec (ket α) = ket (g α)) (hS : ∀ α, S₁ α → S₂ (g α)) :
    p2d_ketPredProj S₂ * (M * p2d_ketPredProj S₁) = M * p2d_ketPredProj S₁ := by
  classical
  refine matrix_ext_ket fun α ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
  by_cases hα : S₁ α
  · rw [ite_eq_left hα, hM α hα, p2d_ketPredProj_mul_ket, ite_eq_left (hS α hα)]
  · rw [ite_eq_right hα, Matrix.mulVec_zero, Matrix.mulVec_zero]

open Classical in
theorem realizes_toDynWG_commutes_above {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (base : ℕ) (v : Var) (rComb : QRegister M n)
    (S_ext : BitAssignment n → Prop) (hExt : ∀ β₁ β₂ : BitAssignment n, (∀ w : Wire n, (∀ idx
    : Wire M, base ≤ idx.val → w ≠ rComb idx) → β₁ w = β₂ w) → (S_ext β₁ ↔ S_ext β₂))
    (InvHole : BitAssignment M → Prop) (inner : DynamicCircuit Var n) (U₀ : Unitary (2 ^ n))
    (hInner : p2d_RealizesConstCleanUnitary (p2d_ketPredProj fun β ↦ S_ext β ∧ InvHole (fun
    idx ↦ β (rComb idx))) inner U₀) : ∀ (K : DiagCtxWG M) (Inv : BitAssignment M → Prop),
    DiagCtxWGWritesAbove base K → DiagCtxWGCommutesWith rComb U₀ K →
    (∀ γ : BitAssignment M, Inv γ → K.ValidAtWith InvHole γ) → p2d_RealizesConstCleanUnitary
    (p2d_ketPredProj fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx)))
    (toDynWG v rComb inner K) U₀ := by
  have hReadWrite (β : BitAssignment n) (f : BitAssignment M) :
      (fun idx ↦ writeRegProg β rComb f (rComb idx)) = f :=
    funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
  have hWriteSelf (β : BitAssignment n) :
      writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β := by
    funext w
    by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm
      exact writeRegProg_apply_reg _ _ _ _
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
  have hWriteIdem (β : BitAssignment n) (f g : BitAssignment M) :
      writeRegProg (writeRegProg β rComb f) rComb g = writeRegProg β rComb g := by
    funext w
    by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm
      simp [writeRegProg_apply_reg]
    · simp [writeRegProg_apply_of_not_mem _ _ _ _ hm]
  have hReadUpd (β : BitAssignment n) (a : Wire M) (x : ZMod 2) :
      (fun idx ↦ Function.update β (rComb a) x (rComb idx)) =
        Function.update (fun idx ↦ β (rComb idx)) a x := by
    funext idx
    by_cases h : idx = a
    · subst h
      simp [Function.update_self]
    · simp [Function.update_of_ne h, Function.update_of_ne (rComb.wires.injective.ne h)]
  have hExtUpd (β : BitAssignment n) {a : Wire M} (ha : base ≤ a.val) (x : ZMod 2) :
      S_ext (Function.update β (rComb a) x) ↔ S_ext β :=
    hExt _ _ fun w hw ↦ Function.update_of_ne (hw a ha) _ _
  have hWStep (k : ℕ) (wIdx : Fin (k + 1) → Wire M) (wOut : Fin (2 ^ (k + 1)) → Wire M)
      (qEnc : Wire M) (dComp dBody dUnc : DynamicCircuit Var n) (uOH : Unitary (2 ^ n))
      (bit : BitAssignment M → ZMod 2) (Inv Inv₁ : BitAssignment M → Prop)
      (hOutW : ∀ l, base ≤ (wOut l).val)
      (hCommOH : uOH * U₀ = U₀ * uOH)
      (hPresOut : ∀ (l : Fin (2 ^ (k + 1))) (g' g : Fin (2 ^ n)), U₀.1 g' g ≠ 0 →
        basisBits n g' (rComb (wOut l)) = basisBits n g (rComb (wOut l)))
      (hImp : ∀ γ : BitAssignment M, Inv γ →
        (∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0 ∧
        Inv₁ (Function.update γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩)
          (γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩) + bit γ)))
      (huOH : ∀ β : BitAssignment n, uOH.1.mulVec (ket β) =
        ket (Function.update β
          (rComb (wOut ⟨idxValD (fun d ↦ rComb (wIdx d)) β,
            idxValD_lt_two_pow (fun d ↦ rComb (wIdx d)) β⟩))
          (β (rComb (wOut ⟨idxValD (fun d ↦ rComb (wIdx d)) β,
            idxValD_lt_two_pow (fun d ↦ rComb (wIdx d)) β⟩)) + bit (fun idx ↦ β (rComb idx)))))
      (hBody : p2d_RealizesConstCleanUnitary
        (p2d_ketPredProj fun β ↦ S_ext β ∧ Inv₁ (fun idx ↦ β (rComb idx))) dBody U₀)
      (hComp : ∀ P₀, SupportedOn (ValidWUncondIn (fun l ↦ rComb (wOut l)) (rComb qEnc)) P₀ →
        SubspaceStep P₀ (uOH.1 * P₀) dComp)
      (hUnc : ∀ R, SupportedOn (ValidWUncondClean (fun l ↦ rComb (wOut l))) R →
        SubspaceStep (uOH.1 * R) R dUnc) :
      p2d_RealizesConstCleanUnitary
        (p2d_ketPredProj fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx)))
        (.seq dComp (.seq dBody dUnc)) U₀ := by
    let wIdxN : Fin (k + 1) → Wire n := fun d ↦ rComb (wIdx d)
    let wOutN : Fin (2 ^ (k + 1)) → Wire n := fun l ↦ rComb (wOut l)
    let S₀ : BitAssignment n → Prop := fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx))
    let S₁ : BitAssignment n → Prop := fun β ↦ S_ext β ∧ Inv₁ (fun idx ↦ β (rComb idx))
    let P₀ := p2d_ketPredProj S₀
    have hSuppIn : SupportedOn (ValidWUncondIn wOutN (rComb qEnc)) P₀ :=
      supportedOn_of_ketPredProj_mul_eq
        (p2d_ketPredProj_mul_imp (S₁ := S₀) (S₂ := ValidWUncondIn wOutN (rComb qEnc))
          fun β hs ↦ ⟨(hImp _ hs.2).1, (hImp _ hs.2).2.1⟩)
    have hP₁_uOH : p2d_ketPredProj S₁ * (uOH.1 * P₀) = uOH.1 * P₀ :=
      ketPredProj_step_ket _ (fun β _ ↦ huOH β) fun β hs ↦ by
        have hjEq : (⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩ : Fin (2 ^ (k + 1))) =
            ⟨idxValD wIdx (fun idx ↦ β (rComb idx)), idxValD_lt_two_pow wIdx _⟩ :=
          Fin.ext <| by
            dsimp only
            rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
        dsimp only [S₁, wOutN]
        rw [hjEq, hExtUpd β (hOutW _), hReadUpd]
        exact ⟨hs.1, (hImp _ hs.2).2.2⟩
    have hComm_op : U₀.1 * (uOH.1 * P₀) = uOH.1 * (U₀.1 * P₀) := by
      rw [← Matrix.mul_assoc, show U₀.1 * uOH.1 = (U₀ * uOH).1 from rfl, ← hCommOH,
        Submonoid.coe_mul, Matrix.mul_assoc]
    have hCleanProj : p2d_ketPredProj (ValidWUncondClean wOutN) * (U₀.1 * P₀) = U₀.1 * P₀ := by
      rw [← Matrix.mul_assoc,
        ketPredProj_comm_of_preserves (ValidWUncondClean wOutN) U₀
          (fun i j hnz ↦ forall_congr' fun l ↦ by rw [hPresOut l i j hnz]),
        Matrix.mul_assoc,
        p2d_ketPredProj_mul_imp (S₁ := S₀) (S₂ := ValidWUncondClean wOutN)
          (fun β hs ↦ (hImp _ hs.2).1)]
    exact SubspaceStep.toConstCleanUnitary (p2d_ketPredProj_conjTranspose S₀)
      ((hComp P₀ hSuppIn).seq ((subspaceStep_congr_out
        (SubspaceStep.ofConstCleanUnitary (p2d_ketPredProj_conjTranspose S₁) hBody hP₁_uOH)
        hComm_op).seq (hUnc (U₀.1 * P₀) (supportedOn_of_ketPredProj_mul_eq hCleanProj))))
  intro K
  induction K with
  | hole =>
      intro Inv _ _ hImp
      exact p2d_RealizesConstCleanUnitary_mono_proj (p2d_ketPredProj_conjTranspose _)
        (p2d_ketPredProj_conjTranspose _)
        (p2d_ketPredProj_mul_imp fun β ⟨hE, hI⟩ ↦ ⟨hE, hImp _ hI⟩) hInner
  | cliffConj c K₁ ih =>
      intro Inv ⟨hcW, hKW⟩ ⟨hCommPost, hComm₁⟩ hImp
      let cPre := (c.onRegister rComb).toCircuit
      let cPost := (c.inv.onRegister rComb).toCircuit
      have hcKet (c₀ : CliffProg M) (β : BitAssignment n) :
          (c₀.onRegister rComb).toCircuit.eval.1.mulVec (ket β) =
            ket (writeRegProg β rComb (c₀.eval (fun idx ↦ β (rComb idx)))) :=
        (eval_onRegister_prog_ket rComb (.cliff c₀) β).trans
          (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
      have hExtCliff (β : BitAssignment n) :
          S_ext (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) ↔ S_ext β :=
        hExt _ _ fun w hw ↦ by
          by_cases hm : w ∈ Set.range rComb.wires
          · obtain ⟨idx, rfl⟩ := hm
            rw [writeRegProg_apply_reg]
            exact hcW.eval_lt (fun i ↦ β (rComb i)) idx
              (Nat.lt_of_not_ge fun hge ↦ hw idx hge rfl)
          · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
      let S₁ : BitAssignment n → Prop := fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx))
      let S₂ : BitAssignment n → Prop :=
        fun β ↦ S_ext β ∧ K₁.ValidAtWith InvHole (fun idx ↦ β (rComb idx))
      have hclean1 : p2d_ketPredProj S₂ * (cPre.eval.1 * p2d_ketPredProj S₁) =
          cPre.eval.1 * p2d_ketPredProj S₁ :=
        ketPredProj_step_ket _ (fun β _ ↦ hcKet c β) fun β hs ↦ by
          dsimp only [S₂]
          rw [hExtCliff, hReadWrite]
          exact ⟨hs.1, hImp _ hs.2⟩
      have hSeq := p2d_RealizesConstCleanUnitary_seq_proj (p2d_ketPredProj_conjTranspose S₁)
          (p2d_ketPredProj_conjTranspose S₂) (p2d_RealizesConstCleanUnitary_circuit _ cPre)
          (p2d_RealizesConstCleanUnitary_seq_proj (p2d_ketPredProj_conjTranspose S₂)
          Matrix.conjTranspose_one (ih (K₁.ValidAtWith InvHole) hKW hComm₁ fun _ h ↦ h)
          (p2d_RealizesConstCleanUnitary_circuit 1 cPost) (Matrix.one_mul _)) hclean1
      have hPostPre : cPost.eval * cPre.eval = 1 :=
        Subtype.ext <| matrix_ext_ket fun β ↦ by
          dsimp only [cPre, cPost]
          simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec,
            Matrix.one_mulVec,
            hcKet c, hcKet c.inv, hReadWrite, hWriteIdem, CliffProg.inv_eval, hWriteSelf]
      have hConjEq : (cPost.eval * U₀) * cPre.eval = U₀ := by
        rw [hCommPost, mul_assoc, hPostPre, mul_one]
      rwa [hConjEq] at hSeq
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro Inv ⟨hancW, hKW⟩ ⟨hCommToff, hPresAnc, hComm₁⟩ hImp
      let cToff := Circuit.gate TOFF (QRegister.triple (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
          (rComb.wires.injective.ne h₂a))
      have hToffSq : cToff.eval * cToff.eval = 1 :=
        Subtype.ext <| matrix_ext_ket fun β ↦ by
          change (cToff ;;ᶜ cToff).eval.1.mulVec (ket β) = (1 : Matrix _ _ ℂ).mulVec (ket β)
          rw [eval_seq_mulVec, Matrix.one_mulVec]
          dsimp only [cToff]
          rw [ket_TOFF, ket_TOFF, Function.update_idem, Function.update_self,
            Function.update_of_ne (rComb.wires.injective.ne h₁a),
            Function.update_of_ne (rComb.wires.injective.ne h₂a),
            add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
      have hConjEq : cToff.eval * U₀ * cToff.eval = U₀ := by
        rw [mul_assoc, ← hCommToff, ← mul_assoc, hToffSq, one_mul]
      have hStep := p2d_RealizesConstCleanUnitary_withTempAnd v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        (S_pre := fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx)))
        (S_post := fun β ↦ S_ext β ∧ K₁.ValidAtWith InvHole (fun idx ↦ β (rComb idx)))
        (fun β hS ↦ (hImp _ hS.2).1)
        (fun β hS ↦ by
          rw [hExtUpd β hancW, hReadUpd]
          exact ⟨hS.1, (hImp _ hS.2).2⟩)
        (ih (K₁.ValidAtWith InvHole) hKW hComm₁ fun _ h ↦ h)
        (fun β hS ↦ by
          rw [hConjEq]
          exact singleton_proj_zero_mulVec_of_preserves (rComb anc) U₀ hPresAnc β (hImp _ hS.2).1)
      rwa [hConjEq] at hStep
  | wStateTree k wIdx wOut qEnc hd K₁ ih =>
      intro Inv ⟨hOutW, hKW⟩ ⟨hCommOH, hPresOut, hComm₁⟩ hImp
      have hdN := wUncondDisjProp_onRegister rComb hd
      exact hWStep k wIdx wOut qEnc _ _ _ (uOneHotUncond (fun d ↦ rComb (wIdx d)) (fun l ↦
        rComb (wOut l)) hdN.1) (fun _ ↦ 1) Inv (K₁.ValidAtWith InvHole) hOutW hCommOH hPresOut
        hImp (uOneHotUncond_mulVec_ket _ _ hdN.1)
        (ih (K₁.ValidAtWith InvHole) hKW hComm₁ fun _ h ↦ h)
        (subspaceStep_wStateComputeUncondPow2 k v _ _ _ hdN)
        (subspaceStep_wStateUncomputeUncondPow2 k v _ _ ⟨hdN.1, hdN.2.2.1⟩)
  | wStateTreeCohGate1 k wHas wIdx wOut qEnc hd K₁ ih =>
      intro Inv ⟨hOutW, hKW⟩ ⟨hCommOH, hPresOut, hComm₁⟩ hImp
      have hdN := wRouterDisj_onRegister rComb hd
      let wHasN := rComb wHas
      let wIdxN : Fin (k + 1) → Wire n := fun d ↦ rComb (wIdx d)
      let wOutN : Fin (2 ^ (k + 1)) → Wire n := fun l ↦ rComb (wOut l)
      let qEncN := rComb qEnc
      let w : Fin 1 → Fin (2 ^ (k + 1)) → Wire n := fun _ p ↦ wOutN p
      have hw : WInj w := wInj_w1Of hdN.out_inj
      let p0 : Fin (2 ^ (k + 1)) := ⟨0, Nat.two_pow_pos (k + 1)⟩
      exact hWStep k wIdx wOut qEnc _ _ _
        (uOneHotToggle wHasN wIdxN wOutN hdN.has_ne_out hdN.idx_ne_out)
        (fun γ ↦ γ wHas) Inv (K₁.ValidAtWith InvHole) hOutW hCommOH hPresOut hImp
        (fun β ↦ (uOneHotToggle_mulVec_ket _ _ _ hdN.has_ne_out hdN.idx_ne_out β).trans
          (congrArg ket (dite_eq_left (idxValD_lt_two_pow _ β))))
        (ih (K₁.ValidAtWith InvHole) hKW hComm₁ fun _ h ↦ h)
        (fun R hSupp ↦ by
          have hdP : WRouterDisjProp wHasN wIdxN wOutN qEncN := hdN.disjProp
          dsimp only [wStateComputeCohGate1]
          rw [dite_eq_left hdP]
          let cTree := Circuit.CNOT wHasN (wOutN p0) (hdP.1 p0) ;;ᶜ
            wTreePrefix 1 (k + 1) w hw (k + 1) le_rfl
          have hTreeEq : cTree.eval.1 * R =
              wCohSuperOp wHasN wIdxN wOutN qEncN 0 (Nat.zero_le (k + 1)) * R :=
            hSupp _ _ fun δ hV ↦ by
              dsimp only [cTree, wCohSuperOp]
              rw [mkVecOp_mulVec_ket, ite_eq_left ⟨hV.1, hV.2⟩, eval_seq_mulVec]
              rcases bit_cases (δ wHasN) with hHas0 | hHas1
              · rw [ite_eq_right (by rw [hHas0]; decide), ket_CNOT_ctrl_zero _ hHas0,
                  wTreePrefix_mulVec_ket_zero w hw δ (fun _ p ↦ hV.1 p) (k + 1) le_rfl]
              · rw [ite_eq_left hHas1, ket_CNOT, hV.1 p0, hHas1, zero_add]
                exact wSuperVec_bot_pub (fun _ ↦ (0 : Fin 1)) wIdxN w hw qEncN δ
                  (fun _ p ↦ hV.1 p) hV.2
          have hTopEq : wCohSuperOp wHasN wIdxN wOutN qEncN (k + 1) le_rfl * R =
              (uOneHotToggle wHasN wIdxN wOutN hdN.has_ne_out hdN.idx_ne_out).1 * R :=
            hSupp _ _ fun δ hV ↦ by
              have hLt : idxValD wIdxN δ < 2 ^ (k + 1) := idxValD_lt_two_pow wIdxN δ
              dsimp only [wCohSuperOp]
              rw [mkVecOp_mulVec_ket, uOneHotToggle_mulVec_ket]
              dsimp only [toggleOneHotBits]
              rw [ite_eq_left ⟨hV.1, hV.2⟩, dite_eq_left hLt, hV.1 ⟨idxValD wIdxN δ, hLt⟩, zero_add]
              rcases bit_cases (δ wHasN) with hHas0 | hHas1
              · rw [ite_eq_right (by rw [hHas0]; decide), hHas0, update_eq_self_of_zero (hV.1 _)]
              · rw [ite_eq_left hHas1, hHas1]
                exact wSuperVec_top_pub (fun _ ↦ (0 : Fin 1)) wIdxN w qEncN δ
                  (fun _ p ↦ hV.1 p) hV.2
          have hLevels : ∀ (m : ℕ) (hm : m ≤ k + 1), SubspaceStep
              (wCohSuperOp wHasN wIdxN wOutN qEncN 0 (Nat.zero_le (k + 1)))
              (wCohSuperOp wHasN wIdxN wOutN qEncN m hm) (wCohShiftLevels v wHasN wIdxN wOutN
              qEncN hdN.has_ne_q hdN.idx_ne_q hdN.out_inj hdN.out_ne_q m hm) := by
            intro m
            induction m with
            | zero =>
                intro _
                simpa only [wCohShiftLevels, Circuit.eval_identity, Submonoid.coe_one,
                  Matrix.one_mul] using
                  subspaceStep_of_circuit (Var := Var)
                    (wCohSuperOp wHasN wIdxN wOutN qEncN 0 (Nat.zero_le (k + 1)))
                    (.identity : Circuit n)
            | succ d ihL =>
                exact fun hdLt ↦ (ihL (Nat.le_of_succ_le hdLt)).seq
                  (subspaceStep_wCohShiftLevel v wHasN wIdxN wOutN qEncN hdN d hdLt)
          exact subspaceStep_congr_out
            ((subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R cTree) hTreeEq).seq
              (subspaceStep_mul_right R (hLevels (k + 1) le_rfl))) hTopEq)
        (fun R_clean hSupp ↦ by
          have hOutD : WRouterOutDisj wHasN wIdxN wOutN :=
            ⟨hdN.has_ne_out, hdN.idx_ne_out, hdN.out_inj⟩
          dsimp only [wStateUncomputeCohGate1]
          rw [dite_eq_left hOutD]
          let cRoot := Circuit.CNOT wHasN (wOutN p0) (hOutD.1 p0)
          let P := ValidWUncondClean wOutN
          let act : BitAssignment n → Prop := fun δ ↦ δ wHasN = 1
          let idOp : Operator (2 ^ n) :=
            mkVecOp fun δ ↦ if P δ ∧ ∀ b p, δ (w b p) = 0 then ket δ else 0
          have hRootEq : cRoot.eval.1 *
              oneHotOptPreOp P act (fun _ ↦ (0 : Fin 1)) wIdxN w 0 (Nat.zero_le (k + 1)) = idOp :=
                by
            apply matrix_ext_ket
            intro δ
            simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, idOp, mkVecOp_mulVec_ket,
              oneHotOptPreVec]
            by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
            · rw [ite_eq_left hV, ite_eq_left hV]
              rcases bit_cases (δ wHasN) with hHas0 | hHas1
              · rw [ite_eq_right (by dsimp [act]; rw [hHas0]; decide)]
                exact ket_CNOT_ctrl_zero _ hHas0
              · rw [ite_eq_left hHas1,
                  show (⟨idxValPrefix wIdxN δ 0 _, _⟩ : Fin (2 ^ (k + 1))) = p0 from rfl]
                dsimp only [cRoot, w]
                rw [ket_CNOT, Function.update_self, Function.update_of_ne (hOutD.1 p0),
                  hHas1, CharTwo.add_self_eq_zero, Function.update_idem,
                  update_eq_self_of_zero (hV.1 p0)]
            · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero]
          have sTree := subspaceStep_mul_right R_clean
            (subspaceStep_wUncompTreeDyn_opt v P act (fun _ ↦ (0 : Fin 1))
              wIdxN w hw (fun d _ p ↦ hOutD.2.1 d p)
              (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ cRoot) hRootEq)
              (k + 1) le_rfl)
          have hInEq : (uOneHotToggle wHasN wIdxN wOutN hdN.has_ne_out hdN.idx_ne_out).1 * R_clean =
              oneHotOptPreOp P act (fun _ ↦ (0 : Fin 1)) wIdxN w (k + 1) le_rfl * R_clean :=
            hSupp _ _ fun δ hClean ↦ by
              have hLt : idxValD wIdxN δ < 2 ^ (k + 1) := idxValD_lt_two_pow wIdxN δ
              rw [uOneHotToggle_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket]
              dsimp only [toggleOneHotBits, oneHotOptPreVec]
              rw [dite_eq_left hLt, ite_eq_left ⟨hClean, fun _ p ↦ hClean p⟩, hClean _, zero_add]
              rcases bit_cases (δ wHasN) with hHas0 | hHas1
              · rw [ite_eq_right (by dsimp [act]; rw [hHas0]; decide), hHas0,
                  update_eq_self_of_zero (hClean _)]
              · rw [ite_eq_left hHas1, hHas1]
                rfl
          have hOutEq : idOp * R_clean = R_clean :=
            (hSupp idOp 1 fun δ hClean ↦ by
              rw [mkVecOp_mulVec_ket, ite_eq_left ⟨hClean, fun _ p ↦ hClean p⟩,
                Matrix.one_mulVec]).trans (Matrix.one_mul R_clean)
          exact subspaceStep_congr_out (subspaceStep_congr_in hInEq sTree) hOutEq)
end DiagCtxWGImpl
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_concat_left)
open Pass1BarrelIdxPebbled273
  (progLoadInternal68 progLoadInternal68_stats progPrefix60 progPrefix60_stats progLoadSuffix8
  progOutMux_68 progOutMux_68_wf progOutMux_68_end progEnFromOrtho_68 progEnFromOrtho_68_wf
  outMux68Sym_ok enFromOrtho68Sym_ok muxSrcWire68 evalBool_progPrefix60_spec
  evalBool_progLoadInternal68_spec rawPebble isAndTarget isAndTarget_ge rawPebble_of_not_andTarget
  permOfProg permOfProg_spec pebBitFnGen)
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open ElecHadTrueSwapHCompClosure (uWriteSub)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_disj_selMeasInAct concat_compose_selDataInAct
  concat_compose_selMeasInAct)
open PartnerAndAnchorSlot18LensAndMidBA (mkSlot18LensOfSlotReg)
open ElecHadTrueSwapLocalCompClosure
  (uLensLoad uLensWrite uLensSwap uLensWrite_mul_uLensSwap_projZero_eq_setTableOp)
open ZeroHypSlot0CommAndHMidClosure (P_slot0)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap
  (selPosInFullSys rFullSysElecSlot selHadOfPosCore rDataElec_mem_selHadOfPosCore
  selMeasInAct_mem_selHadOfPosCore uWriteSub_uLensLoad_eq_uLensWrite_of_slotReg)
open StageBFastInnerPartnerShift
  (cLoad4Rows218 cBranchFix4Rows218Aux dKick1Bit218 dPhaseKickHole218Aux dPhaseKickHole218
  dLoadHole218 dWriteHole218 dWriteHole218_count_toff dWriteHole218_count_t dPreHole218
  count_measureXResetAndBranch_TOFF_le_noFintype count_measureXResetAndBranch_T_le_noFintype
  semigroup_comm2_idem monoid_invol_conj semigroup_write_conj matrix_post_core matrix_post_tail
  cBranchFix4Rows218Aux_eval_ket cLoad4Rows218_eval_ket dFixHole218 dFixHole218_count_t_le
  dFixHole218_count_toff dPostHole218 dZKick1BitHole218 rowBit218 rowBit218_at_active)
/-- Active `.hole` invariant on `n` qubits for a generic `218`-slot `64 × 4` W-state context. -/
def invHoleSlot218 {n kData mScr : ℕ} (hm : 75 ≤ mScr)
    (rData : QRegister kData n) (sFn : BitAssignment kData → Fin 218)
    (rScr : QRegister mScr n) (β : BitAssignment n) : Prop :=
  let s₀ := sFn (fun u ↦ β (rData u))
  (∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = s₀.val % 64 then 1 else 0) ∧
  (∀ h : Fin 4, β (rScr ⟨64 + h.val, by omega⟩) = if h.val = s₀.val / 64 then 1 else 0) ∧
  β (rScr ⟨69, by omega⟩) = 0 ∧
  (∀ r : Fin 4, β (p2dSubReg rScr 70 4 (by omega) r) = 0) ∧
  β (rScr ⟨74, by omega⟩) = 0
private theorem neg_one_pow_zmod2_sq (x : ZMod 2) :
    (-1 : ℂ) ^ x.val * (-1 : ℂ) ^ x.val = 1 := by
  rcases bit_cases x with hv | hv
  · simp [hv]
  · simp [hv]

private theorem ketPredProj_pres_of_comm {n : ℕ} (S : BitAssignment n → Prop)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hComm : p2d_ketPredProj S * M = M * p2d_ketPredProj S) :
    p2d_ketPredProj S * (M * p2d_ketPredProj S) = M * p2d_ketPredProj S := by
  rw [← mul_assoc, hComm, mul_assoc, p2d_ketPredProj_mul_imp (fun _ h ↦ h)]

private theorem ketPredProj_comm_of_ket_map {n : ℕ} (S : BitAssignment n → Prop)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (c : BitAssignment n → ℂ)
    (g : BitAssignment n → BitAssignment n) (hM : ∀ α, M.mulVec (ket α) = c α • ket (g α))
    (hS : ∀ α, S (g α) ↔ S α) : p2d_ketPredProj S * M = M * p2d_ketPredProj S := by
  classical
  refine matrix_ext_ket fun α ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket,
      hM α, Matrix.mulVec_smul, p2d_ketPredProj_mul_ket]
  by_cases hα : S α
  · rw [ite_eq_left hα, hM α, ite_eq_left ((hS α).mpr hα)]
  · rw [ite_eq_right hα, Matrix.mulVec_zero, ite_eq_right (mt (hS α).mp hα), smul_zero]

private theorem ketPredProj_comm_diagSignUnitary {n : ℕ} (S : BitAssignment n → Prop)
    (b : Fin (2 ^ n) → Bool) : p2d_ketPredProj S * (diagSignUnitary b).1 =
    (diagSignUnitary b).1 * p2d_ketPredProj S := ketPredProj_comm_of_ket_map S _ _ (fun α ↦ α)
    (diagSignUnitary_mulVec_ket b) fun _ ↦ Iff.rfl

private theorem ketPredProj_conj_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (S : BitAssignment n → Prop) (c : Circuit n) (d : DynamicCircuit Var n)
    (U : Unitary (2 ^ n)) (hd : p2d_RealizesConstCleanUnitary (p2d_ketPredProj S) d U) (hCommC
    : p2d_ketPredProj S * c.eval.1 = c.eval.1 * p2d_ketPredProj S)
    (hCommU : p2d_ketPredProj S * U.1 = U.1 * p2d_ketPredProj S) :
    p2d_RealizesConstCleanUnitary (p2d_ketPredProj S)
    (.seq (.circuit c) (.seq d (.circuit c))) (c.eval * U * c.eval) :=
  p2d_RealizesConstCleanUnitary_conj_circuit (p2d_ketPredProj_conjTranspose S) c d U hd
    (ketPredProj_pres_of_comm S c.eval.1 hCommC)
    (ketPredProj_pres_of_comm S (U * c.eval).1
      (by rw [Submonoid.coe_mul, ← mul_assoc, hCommU, mul_assoc, hCommC, ← mul_assoc]))

/-- Shared register, lens, and invariant context for `218`-slot `.hole` realization proofs. -/
structure HoleCtx218 (n kData mScr : ℕ) where
  hm : 75 ≤ mScr
  rData : QRegister kData n
  selCore : QRegister posCoreWires kData
  sFn : BitAssignment kData → Fin 218
  L : Slot18Lens kData
  rMeas : QRegister 18 n
  rScr : QRegister mScr n
  hDM : rData.DisjointWires rMeas
  hDS : rData.DisjointWires rScr
  hMS : rMeas.DisjointWires rScr
  hsFn_had : ∀ γ₁ γ₂ : BitAssignment kData,
    (∀ u : Wire kData, selDataInAct kData u ∉ Set.range (selHadOfPosCore selCore).wires →
      γ₁ u = γ₂ u) → sFn γ₁ = sFn γ₂
  hTblBit : ∀ (g : Fin (2 ^ n)) (j : Fin 18),
    basisBits 18 (L.tbl (rData.extractIndex g)) j =
      basisBits n g (rElecSlot (rData.compose selCore)
        (sFn (fun u ↦ basisBits n g (rData u))) j)
  hWriteEq : uWriteSub (selHadOfPosCore selCore) (uLensLoad L) = uLensWrite L
  S_ext : BitAssignment n → Prop
  hExtAct : ∀ β₁ β₂ : BitAssignment n,
    (∀ w ∉ Set.range (rData.concat rMeas hDM).wires, β₁ w = β₂ w) → (S_ext β₁ ↔ S_ext β₂)

abbrev HoleCtx218.rCore {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr) :=
  C.rData.compose C.selCore

abbrev HoleCtx218.rAct {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr) :=
  C.rData.concat C.rMeas C.hDM

abbrev HoleCtx218.hCS {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr) :
    C.rCore.DisjointWires C.rScr := C.hDS.compose_left C.selCore

abbrev HoleCtx218.S_base {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr)
    (β : BitAssignment n) : Prop := C.S_ext β ∧ invHoleSlot218 C.hm C.rData C.sFn C.rScr β

noncomputable abbrev HoleCtx218.P_base {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr) :=
  p2d_ketPredProj C.S_base

abbrev HoleCtx218.rRow4 {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr) : QRegister 4 n :=
  p2dSubReg C.rScr 70 4 (by have := C.hm; omega)

private theorem HoleCtx218.scrNe {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr)
    {a b : ℕ} {ha : a < mScr} {hb : b < mScr} (hne : a ≠ b := by omega) :
    C.rScr ⟨a, ha⟩ ≠ C.rScr ⟨b, hb⟩ :=
  rSub_ne_of_ne C.rScr ha hb hne

private theorem HoleCtx218.inv_congr {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr)
    {β₁ β₂ : BitAssignment n} (hSlot : C.sFn (fun u ↦ β₁ (C.rData u)) = C.sFn (fun u ↦ β₂
    (C.rData u))) (hScr : ∀ k : Fin mScr, β₁ (C.rScr k) = β₂ (C.rScr k)) : invHoleSlot218 C.hm
    C.rData C.sFn C.rScr β₁ ↔ invHoleSlot218 C.hm C.rData C.sFn C.rScr β₂ := by
  have hSub : ∀ r : Fin 4,
      β₁ (p2dSubReg C.rScr 70 4 (by have := C.hm; omega) r) =
        β₂ (p2dSubReg C.rScr 70 4 (by have := C.hm; omega) r) :=
    fun r ↦ hScr ⟨70 + r.val, by have := C.hm; omega⟩
  dsimp only [invHoleSlot218]
  simp only [hSlot, hScr, hSub]

private theorem HoleCtx218.congr_meas {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr)
    (β₁ β₂ : BitAssignment n) (h : ∀ w ∉ Set.range C.rMeas.wires, β₁ w = β₂ w) : C.S_base β₁ ↔
    C.S_base β₂ := and_congr (C.hExtAct β₁ β₂ fun w hw ↦ h w fun ⟨j, hj⟩ ↦ hw ⟨Fin.natAdd
    kData j, (QRegister.concat_apply_right C.rData C.rMeas C.hDM j).trans hj⟩) (C.inv_congr
    (congrArg C.sFn (funext fun u ↦ h (C.rData u) fun ⟨j, hj⟩ ↦ C.hDM.ne u j hj.symm)) (fun k
    ↦ h _ fun ⟨j, hj⟩ ↦ C.hMS.ne j k hj))

private theorem HoleCtx218.comm_uLensLoad {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr) :
    C.P_base * (C.rAct.embedUnitary (uLensLoad C.L)).1 =
      (C.rAct.embedUnitary (uLensLoad C.L)).1 * C.P_base :=
  embedUnitary_uLensLoad_comm_ketPredProj C.rData C.rMeas C.hDM C.L C.S_base C.congr_meas

private theorem HoleCtx218.congr_had {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr)
    (β₁ β₂ : BitAssignment n) (h : ∀ w ∉ Set.range (C.rAct.compose (selHadOfPosCore
    C.selCore)).wires, β₁ w = β₂ w) : C.S_base β₁ ↔ C.S_base β₂ := by
  let selH := selHadOfPosCore C.selCore
  refine and_congr (C.hExtAct β₁ β₂ fun w hw ↦ h w fun ⟨idx, hidx⟩ ↦ hw ⟨selH idx, hidx⟩)
    (C.inv_congr ?_ fun k ↦
      h _ fun ⟨idx, hidx⟩ ↦ (disjointWires_concat_left C.hDM C.hDS C.hMS).ne (selH idx) k hidx)
  refine C.hsFn_had _ _ fun u hu ↦ h (C.rData u) fun ⟨idx, hidx⟩ ↦
    hu ⟨idx, C.rAct.wires.injective ?_⟩
  exact hidx.trans
    (congrArg (fun r : QRegister kData n ↦
      r u) (concat_compose_selDataInAct C.rData C.rMeas C.hDM)).symm

private theorem HoleCtx218.writeRow_scr_out {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr)
    (β : BitAssignment n) (vals : Fin 4 → ZMod 2) (k : Fin mScr) (hk : k.val < 70 ∨ 74 ≤ k.val) :
    p2d_writeReg β C.rRow4 vals (C.rScr k) = β (C.rScr k) :=
  p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ by
    have hm := C.hm
    have := r.isLt
    have hrEq : C.rRow4 r = C.rScr ⟨70 + r.val, by omega⟩ :=
      congrArg C.rScr.wires (Fin.ext (by dsimp [HoleCtx218.rRow4, p2dSubReg]))
    have hv := congrArg Fin.val (C.rScr.wires.injective (hr.symm.trans hrEq))
    dsimp only at hv
    omega

open Classical in
private theorem HoleCtx218.uncompute_4Rows218_realizes {Var : Type} [Fintype Var]
    [DecidableEq Var] {n kData mScr : ℕ} [NeZero (2 ^ n)] (C : HoleCtx218 n kData mScr)
    (v : Var) (j : Fin 18) (dPre : DynamicCircuit Var n) (U_pre U_tgt : Unitary (2 ^ n))
    (phase : BitAssignment n → ℂ) (hdPre : p2d_RealizesConstCleanUnitary C.P_base dPre U_pre)
    (hUpre : ∀ β : BitAssignment n, invHoleSlot218 C.hm C.rData C.sFn C.rScr β →
    U_pre.1.mulVec (ket β) = phase β • ket (p2d_writeReg β C.rRow4 (rowBit218 C.rCore j β
    ((C.sFn (fun u ↦ β (C.rData u))).val % 64) (Nat.mod_lt _ (by decide))))) (hUtgt : ∀ β :
    BitAssignment n, invHoleSlot218 C.hm C.rData C.sFn C.rScr β → U_tgt.1.mulVec (ket β) =
    phase β • ket β) : p2d_RealizesConstCleanUnitary C.P_base (.seq dPre
    (DynCircuitExt.measureXResetAndBranch v 4 C.rRow4 (fun fRow ↦ .circuit
    (cBranchFix4Rows218Aux C.hm j C.rCore C.rScr C.hCS fRow 4 le_rfl)))) U_tgt := by
  have hm := C.hm
  let P_lo := p2d_ketPredProj (fun α : BitAssignment n ↦
    ∃ l₀ < 64, ∀ l : Fin 64, α (C.rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0)
  refine p2d_RealizesConstCleanUnitary_seq_measureXReset v C.rRow4
    (p2d_ketPredProj_conjTranspose _) (p2d_ketPredProj_conjTranspose _) hdPre (fun fRow ↦
    p2d_RealizesConstCleanUnitary_circuit P_lo (cBranchFix4Rows218Aux C.hm j C.rCore C.rScr
    C.hCS fRow 4 le_rfl)) (fun fRow ↦ matrix_ext_ket fun β ↦ ?_)
    (fun fRow ↦ matrix_ext_ket fun β ↦ ?_)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        p2d_ketPredProj_mul_ket]
    by_cases hβ : C.S_base β
    · rw [ite_eq_left hβ, hUpre β hβ.2, Matrix.mulVec_smul, p2d_xResetKraus_mulVec_ket,
          p2d_writeReg_reset_zero_of_zero β C.rRow4 _ hβ.2.2.2.2.1,
          smul_smul, Matrix.mulVec_smul, p2d_ketPredProj_mul_ket,
          ite_eq_left ⟨_, Nat.mod_lt _ (by decide), hβ.2.1⟩]
    · simp [hβ]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
    by_cases hβ : C.S_base β
    · rw [ite_eq_left hβ, hUpre β hβ.2, hUtgt β hβ.2, Matrix.mulVec_smul,
        p2d_xResetKraus_mulVec_ket]
      let s₀ := C.sFn (fun u ↦ β (C.rData u))
      have hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
      let vals := rowBit218 C.rCore j β (s₀.val % 64) hl₀
      have hReadVals : ∀ b : Fin 4,
          p2d_writeReg β C.rRow4
            (rowBit218 C.rCore j β ((C.sFn (fun u ↦ β (C.rData u))).val % 64)
              (Nat.mod_lt _ (by decide))) (C.rRow4 b) = vals b :=
        fun b ↦ p2d_writeReg_apply_reg β C.rRow4 vals b
      simp only [hReadVals]
      rw [p2d_writeReg_reset_zero_of_zero β C.rRow4 vals hβ.2.2.2.2.1,
          smul_smul, Matrix.mulVec_smul,
          cBranchFix4Rows218Aux_eval_ket C.hm j C.rCore C.rScr C.hCS fRow β (s₀.val % 64) hl₀ hβ.2.1
            4 le_rfl]
      simp only [smul_smul]
      refine congrArg (· • ket β) ?_
      have hProdSq : (∏ b : Fin 4, if fRow b then (-1 : ℂ) ^ (vals b).val else 1) *
          (∏ r : Fin 4,
            if fRow ⟨r.val, by omega⟩ then (-1 : ℂ) ^ (vals ⟨r.val, by omega⟩).val else 1) = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun b _ ↦ ?_
        have hbEq : (⟨b.val, by omega⟩ : Fin 4) = b := rfl
        rw [hbEq]
        by_cases hfb : fRow b
        · rw [ite_eq_left hfb]
          exact neg_one_pow_zmod2_sq (vals b)
        · simp [hfb]
      dsimp only [vals] at hProdSq ⊢
      linear_combination ((((√(1 / 2)) ^ 4 : ℝ) : ℂ) * phase β) * hProdSq
    · simp [hβ]

private theorem basisBits_symm_218 {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBitsEquiv q).symm β) = β :=
  (basisBitsEquiv q).apply_symm_apply β

/-- Single-bit phase-kick target unitary for bit `j` of `C.sFn`. -/
private noncomputable def HoleCtx218.uKick1Bit {n kData mScr : ℕ}
    (C : HoleCtx218 n kData mScr) (j : Fin 18) : Unitary (2 ^ n) :=
  diagSignUnitary fun g ↦
    let β := basisBits n g
    decide (β (rElecSlot C.rCore (C.sFn (fun u ↦ β (C.rData u))) j) * β (C.rMeas j) = 1)

private theorem HoleCtx218.uKick1Bit_ket {n kData mScr : ℕ} (C : HoleCtx218 n kData mScr)
    (j : Fin 18) (β : BitAssignment n) : (C.uKick1Bit j).1.mulVec (ket β) = ((-1 : ℂ) ^ (β
    (rElecSlot C.rCore (C.sFn (fun u ↦ β (C.rData u))) j) * β (C.rMeas j)).val) • ket β := by
  dsimp only [uKick1Bit]
  rw [diagSignUnitary_mulVec_ket]
  simp only [basisBits_symm_218 β, ite_decide_eq_one_zmod2]

open Classical in
private theorem HoleCtx218.dKick1Bit218_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (C : HoleCtx218 n kData mScr) (v : Var) (j : Fin 18) :
    p2d_RealizesConstCleanUnitary C.P_base
    (dKick1Bit218 C.hm v j C.rCore C.rMeas C.rScr C.hCS C.hMS) (C.uKick1Bit j) := by
  have hm := C.hm
  let uHi : Fin 4 → Wire n := fun h ↦ C.rScr ⟨64 + h.val, by omega⟩
  let rSel1 : QRegister 1 n := p2dSubReg C.rScr 74 1 (by omega)
  let wSel : Wire n := C.rScr ⟨74, by omega⟩
  let cLoad4 := cLoad4Rows218 C.hm j C.rCore C.rScr C.hCS
  let cSel := cLoadRowAnchored1Bit 4 4 (by decide) le_rfl uHi (uHi 0)
    (C.rScr ⟨70, by omega⟩) (fun i ↦ C.rScr ⟨71 + i.val, by omega⟩) wSel
    (fun _ ↦ C.scrNe) (fun _ ↦ C.scrNe) C.scrNe (fun _ ↦ C.scrNe) C.scrNe
  let cCz := czCircuit wSel (C.rMeas j) (C.hMS.ne j ⟨74, by omega⟩).symm
  let cFixSel : Circuit n :=
    cFixRowAnchored1BitAux 4 4 (by decide) le_rfl uHi
      (C.rScr ⟨70, by omega⟩) (fun i ↦ C.rScr ⟨71 + i.val, by omega⟩)
      (fun _ ↦ C.scrNe) (fun _ _ ↦ C.scrNe) 4 le_rfl
  let U_mid : Unitary (2 ^ n) := cLoad4.eval * C.uKick1Bit j
  let P_hi := p2d_ketPredProj (fun α : BitAssignment n ↦
    ∃ h₀ < 4, ∀ h : Fin 4, α (uHi h) = if h.val = h₀ then 1 else 0)
  have hSel1_0 : rSel1 0 = wSel := congrArg C.rScr.wires (Fin.ext (by dsimp [rSel1, p2dSubReg]))
  have hResetSel (α₁ : BitAssignment n) (h0 : α₁ wSel = 0) (x : ZMod 2) :
      p2d_writeReg (Function.update α₁ wSel x) rSel1 (fun _ ↦ 0) = α₁ := by
    funext w
    by_cases hw : w = wSel
    · subst hw
      rw [← hSel1_0, p2d_writeReg_apply_reg, hSel1_0, h0]
    · rw [p2d_writeReg_apply_of_not_mem _ _ _ _
            (fun ⟨t, ht⟩ ↦ by
              fin_cases t
              exact hw (ht.symm.trans hSel1_0)),
          Function.update_of_ne hw]
  have hRowDite (β : BitAssignment n) (vals : Fin 4 → ZMod 2) (q : ℕ) (hq : q < 4) :
      (let α₁ := p2d_writeReg β C.rRow4 vals
       if h0 : q = 0 then α₁ (C.rScr ⟨70, by omega⟩)
       else if hlt : q < 4 then α₁ (C.rScr ⟨71 + (q - 1), by omega⟩)
       else α₁ (C.rScr ⟨70, by omega⟩)) = vals ⟨q, hq⟩ := by
    have hRow (r : Fin 4) : p2d_writeReg β C.rRow4 vals (C.rScr ⟨70 + r.val, by omega⟩) = vals r :=
      by
      rw [show C.rScr ⟨70 + r.val, by omega⟩ = C.rRow4 r from
        congrArg C.rScr.wires (Fin.ext (by dsimp [HoleCtx218.rRow4, p2dSubReg]))]
      exact p2d_writeReg_apply_reg β C.rRow4 vals r
    dsimp only
    by_cases h0 : q = 0
    · rw [dite_eq_left h0,
          show (⟨70, by omega⟩ : Fin mScr) = ⟨70 + (0 : Fin 4).val, by omega⟩ from rfl, hRow 0]
      exact congrArg vals (Fin.ext (by dsimp; omega))
    · rw [dite_eq_right h0, dite_eq_left hq,
          show (⟨71 + (q - 1), by omega⟩ : Fin mScr) = ⟨70 + q, by omega⟩ from
            Fin.ext (by dsimp; omega),
          hRow ⟨q, hq⟩]
  have hcPre_eval : ∀ (β : BitAssignment n), invHoleSlot218 C.hm C.rData C.sFn C.rScr β →
      let s₀ := C.sFn (fun u ↦ β (C.rData u))
      have hs := s₀.isLt
      let hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
      let vals := rowBit218 C.rCore j β (s₀.val % 64) hl₀
      (cLoad4 ;;ᶜ (cSel ;;ᶜ cCz)).eval.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (β (rElecSlot C.rCore s₀ j) * β (C.rMeas j)).val) •
          ket (Function.update (p2d_writeReg β C.rRow4 vals) wSel (vals ⟨s₀.val / 64, by omega⟩)) :=
            by
    intro β ⟨hLo, hHi, hPar0, hRow0, hSel0⟩ s₀ hs hl₀ vals
    let α₁ := p2d_writeReg β C.rRow4 vals
    have hh₀ : s₀.val / 64 < 4 := by omega
    have hα₁_hi : ∀ h : Fin 4, α₁ (uHi h) = if h.val = s₀.val / 64 then 1 else 0 :=
      fun h ↦
        have hh := h.isLt
        (C.writeRow_scr_out β vals ⟨64 + h.val, by omega⟩
          (Or.inl (show 64 + h.val < 70 by omega))).trans (hHi h)
    have hα₁_bnd : α₁ (uHi 0) = if (s₀.val / 64 = 0 ∨ 4 ≤ s₀.val / 64) then 1 else 0 := by
      rw [hα₁_hi 0]
      dsimp
      by_cases h0 : s₀.val / 64 = 0
      · rw [ite_eq_left h0.symm, ite_eq_left (Or.inl h0)]
      · rw [ite_eq_right (Ne.symm h0), ite_eq_right (by omega)]
    have hα₁_sel0 : α₁ wSel = 0 :=
      (C.writeRow_scr_out β vals ⟨74, by omega⟩ (Or.inr le_rfl)).trans hSel0
    let actVal := vals ⟨s₀.val / 64, hh₀⟩
    have hSelKet : cSel.eval.1.mulVec (ket α₁) = ket (Function.update α₁ wSel actVal) := by
      rw [cLoadRowAnchored1Bit_eval_ket 4 4 (by decide) le_rfl uHi (uHi 0)
        (C.rScr ⟨70, by omega⟩) (fun i ↦ C.rScr ⟨71 + i.val, by omega⟩) wSel _ _ _ _ _
        (fun i₁ i₂ h ↦ Fin.ext (by
          have := congrArg Fin.val (C.rScr.wires.injective h)
          dsimp at this
          omega))
        (fun _ _ ↦ C.scrNe) (fun _ ↦ C.scrNe)
        α₁ hα₁_sel0 (s₀.val / 64) hh₀ hα₁_hi hα₁_bnd]
      exact congrArg (fun b ↦ ket (Function.update α₁ wSel b)) (hRowDite β vals (s₀.val / 64) hh₀)
    have hMeasα₁ : Function.update α₁ wSel actVal (C.rMeas j) = β (C.rMeas j) := by
      rw [Function.update_of_ne (C.hMS.ne j ⟨74, by omega⟩)]
      exact p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦
        C.hMS.ne j ⟨70 + r.val, by omega⟩ (hr.symm.trans
          (congrArg C.rScr.wires (Fin.ext (by dsimp [HoleCtx218.rRow4, p2dSubReg]))))
    rw [eval_seq_mulVec,
      cLoad4Rows218_eval_ket C.hm j C.rCore C.rScr C.hCS β hRow0 hPar0 (s₀.val % 64) hl₀ hLo,
        eval_seq_mulVec, hSelKet, ket_czCircuit, Function.update_self, hMeasα₁]
    exact congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ (z * β (C.rMeas j)).val) •
      ket (Function.update α₁ wSel actVal)) (rowBit218_at_active C.rCore j β s₀)
  have hUmid : ∀ β : BitAssignment n, invHoleSlot218 C.hm C.rData C.sFn C.rScr β →
      U_mid.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (β (rElecSlot C.rCore (C.sFn (fun u ↦ β (C.rData u))) j) * β (C.rMeas j)).val) •
          ket (p2d_writeReg β C.rRow4
            (rowBit218 C.rCore j β ((C.sFn (fun u ↦ β (C.rData u))).val % 64)
              (Nat.mod_lt _ (by decide)))) := fun β hInv ↦ by
    change (cLoad4.eval.1 * (C.uKick1Bit j).1).mulVec (ket β) = _
    rw [← Matrix.mulVec_mulVec, C.uKick1Bit_ket, Matrix.mulVec_smul,
        cLoad4Rows218_eval_ket C.hm j C.rCore C.rScr C.hCS β hInv.2.2.2.1 hInv.2.2.1 _ _ hInv.1]
  have hStep1 : p2d_RealizesConstCleanUnitary C.P_base
      (.seq (.circuit (cLoad4 ;;ᶜ (cSel ;;ᶜ cCz)))
        (DynCircuitExt.measureXResetAndBranch v 1 rSel1
          (fun fSel ↦ if fSel 0 then .circuit cFixSel else .identity)))
      U_mid := by
    refine p2d_RealizesConstCleanUnitary_seq_measureXReset v rSel1
      (U_fix := fun fSel ↦ if fSel 0 then cFixSel.eval else 1)
      (p2d_ketPredProj_conjTranspose _) (p2d_ketPredProj_conjTranspose _)
      (p2d_RealizesConstCleanUnitary_circuit _ _)
      (fun fSel ↦ by
        cases hf : fSel 0
        · simpa [hf] using p2d_RealizesConstCleanUnitary_circuit (Var := Var) P_hi Circuit.identity
        · simpa [hf] using p2d_RealizesConstCleanUnitary_circuit (Var := Var) P_hi cFixSel)
      (fun fSel ↦ matrix_ext_ket fun β ↦ ?_)
      (fun fSel ↦ matrix_ext_ket fun β ↦ ?_)
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          p2d_ketPredProj_mul_ket]
      by_cases hβ : C.S_base β
      · rw [ite_eq_left hβ, hcPre_eval β hβ.2, Matrix.mulVec_smul, p2d_xResetKraus_mulVec_ket,
            hResetSel _ ((C.writeRow_scr_out β _ ⟨74,
              by omega⟩ (Or.inr le_rfl)).trans hβ.2.2.2.2.2),
            smul_smul, Matrix.mulVec_smul, p2d_ketPredProj_mul_ket, ite_eq_left]
        exact ⟨(C.sFn (fun u ↦ β (C.rData u))).val / 64,
          by have := (C.sFn (fun u ↦ β (C.rData u))).isLt; omega,
          fun h ↦
            have hh := h.isLt
            (C.writeRow_scr_out β _ ⟨64 + h.val, by omega⟩
              (Or.inl (show 64 + h.val < 70 by omega))).trans (hβ.2.2.1 h)⟩
      · simp [hβ]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
      by_cases hβ : C.S_base β
      · rw [ite_eq_left hβ]
        let s₀ := C.sFn (fun u ↦ β (C.rData u))
        have hs := s₀.isLt
        have hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
        have hh₀ : s₀.val / 64 < 4 := by omega
        let vals := rowBit218 C.rCore j β (s₀.val % 64) hl₀
        let α₁ := p2d_writeReg β C.rRow4 vals
        have hα₁_sel0 : α₁ wSel = 0 :=
          (C.writeRow_scr_out β vals ⟨74, by omega⟩ (Or.inr le_rfl)).trans hβ.2.2.2.2.2
        have hα₁_hi : ∀ h : Fin 4, α₁ (uHi h) = if h.val = s₀.val / 64 then 1 else 0 :=
          fun h ↦
            have hh := h.isLt
            (C.writeRow_scr_out β vals ⟨64 + h.val, by omega⟩
              (Or.inl (show 64 + h.val < 70 by omega))).trans (hβ.2.2.1 h)
        rw [hcPre_eval β hβ.2, Matrix.mulVec_smul, p2d_xResetKraus_mulVec_ket,
            Fin.prod_univ_one, hSel1_0, Function.update_self, hResetSel α₁ hα₁_sel0, smul_smul,
            Matrix.mulVec_smul, hUmid β hβ.2, smul_smul]
        cases hf0 : fSel 0
        · simp only [Bool.false_eq_true, ↓reduceIte, OneMemClass.coe_one, Matrix.one_mulVec,
            mul_one]
          exact congrArg (· • ket α₁) (mul_comm _ _)
        · simp only [↓reduceIte]
          rw [cFixRowAnchored1Bit_eval_ket 4 4 (by decide) le_rfl uHi
                (C.rScr ⟨70, by omega⟩) (fun i ↦ C.rScr ⟨71 + i.val, by omega⟩) _ _
                α₁ (s₀.val / 64) hh₀ hα₁_hi, smul_smul, hRowDite β vals (s₀.val / 64) hh₀]
          refine congrArg (· • ket α₁) ?_
          have hSq := neg_one_pow_zmod2_sq (vals ⟨s₀.val / 64, hh₀⟩)
          dsimp only [vals, s₀] at hSq ⊢
          linear_combination
            (((√(1 / 2)) ^ 1 : ℝ) : ℂ) *
              (-1 : ℂ) ^ (β (rElecSlot C.rCore (C.sFn (fun u ↦ β (C.rData u))) j) *
                β (C.rMeas j)).val * hSq
      · simp [hβ]
  exact C.uncompute_4Rows218_realizes v j _ U_mid (C.uKick1Bit j)
    (fun β ↦
      (-1 : ℂ) ^ (β (rElecSlot C.rCore (C.sFn (fun u ↦ β (C.rData u))) j) * β (C.rMeas j)).val)
    hStep1 hUmid (fun β _ ↦ C.uKick1Bit_ket j β)

/-- Prefix phase-kick unitary on the first `k` bits of `C.rMeas` from `C.sFn`. -/
private noncomputable def HoleCtx218.uKickPrefix {n kData mScr : ℕ}
    (C : HoleCtx218 n kData mScr) (k : ℕ) (hk : k ≤ 18) : Unitary (2 ^ n) :=
  diagSignUnitary fun g ↦
    let β := basisBits n g
    let s₀ := C.sFn (fun u ↦ β (C.rData u))
    decide ((∑ j : Fin k,
      β (rElecSlot C.rCore s₀ ⟨j.val, by omega⟩) * β (C.rMeas ⟨j.val, by omega⟩)) = 1)

open Classical in
private theorem HoleCtx218.dLoadHole218_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (C : HoleCtx218 n kData mScr) (v : Var) :
    p2d_RealizesConstCleanUnitary C.P_base
      (dLoadHole218 C.hm v C.rCore C.rMeas C.rScr C.hCS C.hMS)
      (C.rAct.embedUnitary (uLensLoad C.L)) := by
  have hAux : ∀ (k : ℕ) (hk : k ≤ 18), p2d_RealizesConstCleanUnitary C.P_base
      (dPhaseKickHole218Aux C.hm v C.rCore C.rMeas C.rScr C.hCS C.hMS k hk)
      (C.uKickPrefix k hk) := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hU0 : C.uKickPrefix 0 hk = (Circuit.identity (n := n)).eval := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [uKickPrefix, diagSignUnitary]
          · simp [uKickPrefix, diagSignUnitary, hij]
        rw [hU0]
        simpa [dPhaseKickHole218Aux] using
          p2d_RealizesConstCleanUnitary_circuit (Var := Var) C.P_base Circuit.identity
    | succ k ih =>
        intro hk
        have hSeq := p2d_RealizesConstCleanUnitary_seq_proj
          (p2d_ketPredProj_conjTranspose _) (p2d_ketPredProj_conjTranspose _)
          (ih (by omega)) (C.dKick1Bit218_realizes v ⟨k, hk⟩)
          (ketPredProj_pres_of_comm _ _ (ketPredProj_comm_diagSignUnitary _ _))
        refine p2d_RealizesConstCleanUnitary_congr_unitary (p2d_ketPredProj_conjTranspose _) hSeq
          (matrix_ext_ket fun β ↦ ?_)
        rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
        by_cases hβ : C.S_base β
        · rw [ite_eq_left hβ, uKickPrefix, diagSignUnitary_mulVec_ket, Matrix.mulVec_smul,
              C.uKick1Bit_ket, smul_smul, uKickPrefix, diagSignUnitary_mulVec_ket]
          simp only [basisBits_symm_218 β, ite_decide_eq_one_zmod2]
          refine congrArg (· • ket β) ?_
          rw [Fin.sum_univ_castSucc]
          dsimp only [Fin.val_castSucc, Fin.val_last]
          rw [← TempPhaseProg.neg_one_pow_zmod2_mul, mul_comm]
        · simp [hβ]
  have hConj := ketPredProj_conj_circuit _ (cHadReg C.rMeas)
      (dPhaseKickHole218 C.hm v C.rCore C.rMeas C.rScr C.hCS C.hMS) (C.uKickPrefix 18 le_rfl)
      (hAux 18 le_rfl) (cHadReg_preserves_ketPredProj C.rMeas _ fun β₁ β₂ h ↦ C.congr_meas β₁
      β₂ fun w hw ↦ h w fun j hj ↦ hw ⟨j, hj.symm⟩) (ketPredProj_comm_diagSignUnitary _ _)
  have hCM : C.rCore.DisjointWires C.rMeas := C.hDM.compose_left C.selCore
  have hLoadEq : (cHadReg C.rMeas).eval * C.uKickPrefix 18 le_rfl * (cHadReg C.rMeas).eval =
      C.rAct.embedUnitary (uLensLoad C.L) :=
    cHadReg_meas_conj_phase_eq_uLensLoad C.rData C.rMeas C.hDM C.L
      (fun j α ↦ α (rElecSlot C.rCore (C.sFn (fun u ↦ α (C.rData u))) j))
      (fun j α₁ α₂ h ↦ by
        have hData : (fun u ↦ α₁ (C.rData u)) = (fun u ↦ α₂ (C.rData u)) :=
          funext fun u ↦ h (C.rData u) fun t ↦ C.hDM.ne u t
        rw [hData]
        refine h _ fun t ↦ ?_
        simp only [rElecSlot, QRegister.slice_apply]
        exact hCM.ne _ t)
      C.hTblBit
  exact p2d_RealizesConstCleanUnitary_congr_unitary (p2d_ketPredProj_conjTranspose _) hConj
    (congrArg (fun U : Unitary (2 ^ n) ↦ U.1 * _) hLoadEq)

private theorem HoleCtx218.dWriteHole218_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (C : HoleCtx218 n kData mScr) (v : Var) :
    p2d_RealizesConstCleanUnitary C.P_base (dWriteHole218 C.hm v C.rData C.selCore C.rMeas
    C.rScr C.hDM C.hCS C.hMS) (C.rAct.embedUnitary (uLensWrite C.L)) :=
    p2d_RealizesConstCleanUnitary_congr_unitary (p2d_ketPredProj_conjTranspose _)
    (dHadSubConjHole_realizes C.rAct (selHadOfPosCore C.selCore) C.S_base C.congr_had
    (uLensLoad C.L) (dLoadHole218 C.hm v C.rCore C.rMeas C.rScr C.hCS C.hMS)
    (C.dLoadHole218_realizes v) C.comm_uLensLoad) (congrArg (fun U : Unitary (2 ^ (kData +
    18)) ↦ (C.rAct.embedUnitary U).1 * _) C.hWriteEq)


theorem dPreHole218_slot_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (sFn : BitAssignment kData → Fin 218) (L : Slot18Lens kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDS : rData.DisjointWires rScr)
    (hMS : rMeas.DisjointWires rScr)
    (hsFn_had : ∀ γ₁ γ₂ : BitAssignment kData,
      (∀ u : Wire kData, selDataInAct kData u ∉ Set.range (selHadOfPosCore selCore).wires →
        γ₁ u = γ₂ u) →
      sFn γ₁ = sFn γ₂)
    (hTblBit : ∀ (g : Fin (2 ^ n)) (j : Fin 18),
      basisBits 18 (L.tbl (rData.extractIndex g)) j =
        basisBits n g (rElecSlot (rData.compose selCore)
          (sFn (fun u ↦ basisBits n g (rData u))) j))
    (hWriteEq : uWriteSub (selHadOfPosCore selCore) (uLensLoad L) = uLensWrite L)
    (S_ext : BitAssignment n → Prop)
    (hExtAct : ∀ β₁ β₂ : BitAssignment n,
      (∀ w ∉ Set.range (rData.concat rMeas hDM).wires, β₁ w = β₂ w) →
      (S_ext β₁ ↔ S_ext β₂)) :
    let rCore := rData.compose selCore
    let rAct := rData.concat rMeas hDM
    let hCS : rCore.DisjointWires rScr := hDS.compose_left selCore
    let P_hole := p2d_ketPredProj (fun β ↦ S_ext β ∧ invHoleSlot218 hm rData sFn rScr β)
    p2d_RealizesConstCleanUnitary P_hole
      (dPreHole218 hm v rData selCore rMeas rScr hDM hCS hMS)
      (rAct.embedUnitary (uLensWrite L * uLensLoad L)) := by
  intro _ rAct _ _
  let C : HoleCtx218 n kData mScr :=
    ⟨hm, rData, selCore, sFn, L, rMeas, rScr, hDM, hDS, hMS, hsFn_had, hTblBit, hWriteEq, S_ext,
      hExtAct⟩
  exact p2d_RealizesConstCleanUnitary_congr_unitary (p2d_ketPredProj_conjTranspose _)
    (p2d_RealizesConstCleanUnitary_seq_proj
      (p2d_ketPredProj_conjTranspose _) (p2d_ketPredProj_conjTranspose _)
      (C.dLoadHole218_realizes v) (C.dWriteHole218_realizes v)
      (ketPredProj_pres_of_comm _ _ C.comm_uLensLoad))
    (by rw [rAct.embedUnitary_mul, Submonoid.coe_mul])

/-- Tests whether decoder wire `w` is allocated by an `.andAlloc` instruction in `p` starting at
`cur` and is never subsequently modified (`progUntouched w (cur + 1) rest`). -/
private def isFinalAndTarget : List DecStep → ℕ → ℕ → Bool
  | [], _, _ => false
  | s :: rest, cur, w =>
      match s with
      | .andAlloc _ _ =>
          if w = cur then progUntouched w (cur + 1) rest
          else isFinalAndTarget rest (cur + 1) w
      | _ => isFinalAndTarget rest (s.nextCur cur) w
private theorem rawPebble_eq_evalBool_of_isFinalAndTarget :
    ∀ (p : List DecStep) (cur : ℕ) (st : ℕ → Bool) (w : ℕ),
      isFinalAndTarget p cur w = true → rawPebble p cur st w = evalBool p cur st w
  | [], _, _, _, h => by simp [isFinalAndTarget] at h
  | .allocZero :: rest, _, _, w, h => rawPebble_eq_evalBool_of_isFinalAndTarget rest _ _ w h
  | .x _ :: rest, _, _, w, h => rawPebble_eq_evalBool_of_isFinalAndTarget rest _ _ w h
  | .cnot _ _ :: rest, _, _, w, h => rawPebble_eq_evalBool_of_isFinalAndTarget rest _ _ w h
  | .andAlloc _ _ :: rest, cur, st, w, h => by
      dsimp only [isFinalAndTarget, rawPebble, evalBool, DecStep.nextCur] at h ⊢
      by_cases hw : w = cur
      · subst hw
        simp only [↓reduceIte] at h ⊢
        rw [evalBool_untouched rest (w + 1) _ w h]
        simp [DecStep.stepBool]
      · simp only [hw, ↓reduceIte] at h ⊢
        exact rawPebble_eq_evalBool_of_isFinalAndTarget rest (cur + 1) _ w h
/-- Decoder wire index of the `j`-th output-mux AND pebble in `progOutMux_68` (`0 ≤ j < 8`). -/
def qMux8Nat : ℕ → ℕ
  | 0 => 156
  | 1 => 157
  | 2 => 158
  | 3 => 160
  | 4 => 161
  | 5 => 162
  | 6 => 163
  | _ => 164
/-- The `10` final `.andAlloc` pebble indices in `progLoadInternal68`:
`67` (`!c0 ∧ c1`), `68` (`!c0 ∧ !c1 ∧ (u8 < 218)`), and `qMux8Nat 0..7` (mux AND terms). -/
def qPeb10 : Fin 10 → ℕ
  | ⟨0, _⟩ => 67
  | ⟨1, _⟩ => 68
  | ⟨k + 2, _⟩ => qMux8Nat k
theorem qPeb10_bounds (i : Fin 10) : 67 ≤ qPeb10 i ∧ qPeb10 i < 165 := by
  revert i; decide
theorem qPeb10_inj : Function.Injective qPeb10 := by
  intro i j h; revert i j h; decide
theorem rawPebble_progLoadInternal68_spec (st₀ : ℕ → Bool)
    (hcl₀ : ∀ q, 61 ≤ q → st₀ q = false) :
    let en := Bool.xor (rawPebble progLoadInternal68 61 st₀ 67)
                       (rawPebble progLoadInternal68 61 st₀ 68)
    (en = false → coinBarrelIdxFastPure st₀ = 0) ∧
    (en = true → ∀ j : Fin 8,
      Bool.xor (st₀ (17 + j.val)) (rawPebble progLoadInternal68 61 st₀ (qMux8Nat j.val)) =
        (coinBarrelIdxFastPure st₀).testBit j.val) := by
  have hFinalMux : ∀ j : Fin 8, isFinalAndTarget progLoadInternal68 61 (qMux8Nat j.val) = true := by
    intro j
    revert j
    decide
  have hUntMux : ∀ j : Fin 8, progUntouched (qMux8Nat j.val) 165 progEnFromOrtho_68 = true := by
    intro j
    revert j
    decide
  have hUntU8 : ∀ j : Fin 8, progUntouched (69 + j.val) 165 progEnFromOrtho_68 = true := by
    intro j
    revert j
    decide
  have hMuxOk : (List.range 8).all (fun k ↦
      bexprEquivOn [2, 69 + k, muxSrcWire68 k]
        (symGet (runSymTrie progOutMux_68 155 (mkInitSym 155)) (qMux8Nat k))
        (.and (.var 2) (.xor (.var (69 + k)) (.var (muxSrcWire68 k))))) = true := by
    clear * -
    decide
  obtain ⟨hcl₈, _, _, _, _, hst₈_u8⟩ := evalBool_progPrefix60_spec st₀ hcl₀
  obtain ⟨_, hen0_spec, hen1_spec⟩ := evalBool_progLoadInternal68_spec st₀ hcl₀
  generalize hst₈ : evalBool progPrefix60 61 st₀ = st₈ at hcl₈ hst₈_u8
  generalize hst₉ : evalBool progOutMux_68 155 st₈ = st₉
  generalize hst₁₀ : evalBool progEnFromOrtho_68 165 st₉ = st₁₀
  generalize hstFull : evalBool progLoadInternal68 61 st₀ = stFull at hen0_spec hen1_spec
  have hchain : stFull = st₁₀ := by
    rw [← hstFull, progLoadInternal68, evalBool_append, progPrefix60_stats.2.1, hst₈,
        progLoadSuffix8, evalBool_append, progOutMux_68_end, hst₉, hst₁₀]
  have hcl₉ : ∀ q, 165 ≤ q → st₉ q = false := fun q hq ↦ by
    rw [← hst₉]
    refine evalBool_clean progOutMux_68 155 st₈ progOutMux_68_wf hcl₈ q ?_
    rw [progOutMux_68_end]
    exact hq
  have h165_eq : st₁₀ 165 = Bool.xor (st₉ 67) (st₉ 68) := by
    rw [← hst₁₀]
    exact checkSymWire progEnFromOrtho_68 165 (by decide) progEnFromOrtho_68_wf
      [67, 68] 165 (by decide) (.xor (.var 67) (.var 68))
      (Eq.mp (Bool.and_eq_true _ _) enFromOrtho68Sym_ok).1 st₉ hcl₉
  have hPeb {w : ℕ} (hw : isFinalAndTarget progLoadInternal68 61 w = true) :
      rawPebble progLoadInternal68 61 st₀ w = st₁₀ w := by
    rw [rawPebble_eq_evalBool_of_isFinalAndTarget progLoadInternal68 61 st₀ w hw,
        hstFull, hchain]
  have hf67 : isFinalAndTarget progLoadInternal68 61 67 = true := by
    clear * -
    decide
  have hf68 : isFinalAndTarget progLoadInternal68 61 68 = true := by
    clear * -
    decide
  have hu67 : progUntouched 67 165 progEnFromOrtho_68 = true := by
    clear * -
    decide
  have hu68 : progUntouched 68 165 progEnFromOrtho_68 = true := by
    clear * -
    decide
  have hen_eq : Bool.xor (rawPebble progLoadInternal68 61 st₀ 67)
      (rawPebble progLoadInternal68 61 st₀ 68) = stFull 165 := by
    rw [hPeb hf67, hPeb hf68, hchain, h165_eq, ← hst₁₀,
        evalBool_untouched progEnFromOrtho_68 165 st₉ 67 hu67,
        evalBool_untouched progEnFromOrtho_68 165 st₉ 68 hu68]
  refine ⟨fun h0 ↦ hen0_spec (hen_eq ▸ h0), fun h1 j ↦ ?_⟩
  have hqMux_lt : qMux8Nat j.val < 165 := (qPeb10_bounds ⟨j.val + 2, by omega⟩).2
  have hpMux : rawPebble progLoadInternal68 61 st₀ (qMux8Nat j.val) = st₉ (qMux8Nat j.val) := by
    rw [hPeb (hFinalMux j), ← hst₁₀]
    exact evalBool_untouched progEnFromOrtho_68 165 st₉ (qMux8Nat j.val) (hUntMux j)
  have hMux_ev : st₉ (qMux8Nat j.val) =
      (st₈ 2 && Bool.xor (st₈ (69 + j.val)) (st₈ (muxSrcWire68 j.val))) := by
    rw [← hst₉]
    exact checkSymWire progOutMux_68 155 (by decide) progOutMux_68_wf
      [2, 69 + j.val, muxSrcWire68 j.val] (qMux8Nat j.val) (by omega)
      (.and (.var 2) (.xor (.var (69 + j.val)) (.var (muxSrcWire68 j.val))))
      (List.all_eq_true.mp hMuxOk j.val (List.mem_range.mpr j.isLt)) st₈ hcl₈
  have hOut_ev : st₉ (69 + j.val) = Bool.xor (st₈ (69 + j.val))
      (st₈ 2 && Bool.xor (st₈ (69 + j.val)) (st₈ (muxSrcWire68 j.val))) := by
    rw [← hst₉]
    exact checkSymWire progOutMux_68 155 (by decide) progOutMux_68_wf
      [2, 69 + j.val, muxSrcWire68 j.val] (69 + j.val) (by omega)
      (.xor (.var (69 + j.val))
        (.and (.var 2) (.xor (.var (69 + j.val)) (.var (muxSrcWire68 j.val)))))
      (List.all_eq_true.mp outMux68Sym_ok j.val (List.mem_range.mpr j.isLt)) st₈ hcl₈
  have hidx_cp : st₁₀ (69 + j.val) = st₉ (69 + j.val) := by
    rw [← hst₁₀]
    exact evalBool_untouched progEnFromOrtho_68 165 st₉ (69 + j.val) (hUntU8 j)
  rw [hpMux, ← hst₈_u8 j.val j.isLt, hMux_ev, ← hOut_ev, ← hidx_cp, ← hchain]
  exact hen1_spec (hen_eq ▸ h1) j
/-- Selector of the `8`-wire `u8` decoder input (`decWireNum C (17 + j)`) inside
  `fullSysCoreWires mPayload`. -/
def selU8InCore {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    QRegister 8 (fullSysCoreWires mPayload) where
  wires :=
    { toFun := fun j ↦
        ⟨decWireNum (fullSysCoreWires mPayload) (17 + j.val),
          decWireNum_lt_core (core_lo_4034 hmPay) (by have := j.isLt; omega)⟩
      inj' := fun j₁ j₂ h ↦ by
        have hv := congrArg Fin.val h
        dsimp only [decWireNum] at hv
        split_ifs at hv <;> exact Fin.ext (by omega) }
theorem selU8InCore_ge_3924 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (j : Fin 8) :
    3924 ≤ (selU8InCore hmPay j).val := by
  have hC := core_lo_4034 hmPay
  have hj := j.isLt
  change 3924 ≤ decWireNum (fullSysCoreWires mPayload) (17 + j.val)
  dsimp only [decWireNum]
  split_ifs <;> omega
/-- `8`-wire `u8` core subregister `rCore.compose (selU8InCore hmPay)`. -/
def rU8Core8 {n mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) : QRegister 8 n :=
  rCore.compose (selU8InCore hmPay)
/-- Selector of the `10` active `.andAlloc` pebbles `8 + (qPeb10 i - 61)` inside `rWB` (`143 ≤
  mWB`). -/
def selPeb10InWB {mWB : ℕ} (hmWB : 143 ≤ mWB) : QRegister 10 mWB where
  wires :=
    { toFun := fun i ↦
        ⟨8 + (qPeb10 i - 61), by have := qPeb10_bounds i; omega⟩
      inj' := fun i₁ i₂ h ↦ by
        have hv := congrArg Fin.val h
        have hb₁ := qPeb10_bounds i₁
        have hb₂ := qPeb10_bounds i₂
        exact qPeb10_inj (by dsimp at hv; omega) }
/-- `10`-wire active pebble subregister `rWB.compose (selPeb10InWB hmWB)`. -/
def rPeb10 {n mWB : ℕ} (hmWB : 143 ≤ mWB) (rWB : QRegister mWB n) : QRegister 10 n :=
  rWB.compose (selPeb10InWB hmWB)
/-- `9`-wire `(wEn, wIdx[0..8))` subregister `rPeb10[1..10)` inside `rWB`. -/
def rEnIdx9 {n mWB : ℕ} (hmWB : 143 ≤ mWB) (rWB : QRegister mWB n) : QRegister 9 n :=
  (rPeb10 hmWB rWB).slice 1 9 (by decide)
theorem progLoadInternal68_perm_bound {mWB : ℕ} (hmWB : 143 ≤ mWB) :
    8 + (progEndCur 61 progLoadInternal68 - 61) ≤ mWB := by
  rw [progLoadInternal68_stats.2.1]; omega
/-- `permOfProg`-reordered `rWB` register grouping all `68` pebbles of `progLoadInternal68` into
  `[8..76)`. -/
def rWBPerm68 {n mWB : ℕ} (hmWB : 143 ≤ mWB) (rWB : QRegister mWB n) : QRegister mWB n :=
  let e := permOfProg mWB progLoadInternal68 61 8 (progLoadInternal68_perm_bound hmWB)
  rWB.compose ⟨⟨e.symm, e.symm.injective⟩⟩
/-- `75`-wire subregister `(rP[0..8) ++ rP[76..143))` inside an `mWB`-wire register (`143 ≤
  mWB`). -/
def rScr75OfReg {n mWB : ℕ} (hmWB : 143 ≤ mWB) (rP : QRegister mWB n) : QRegister 75 n :=
  (rP.slice 0 8 (by omega)).concat (rP.slice 76 67 (by omega))
    (rP.slice_disjoint_of_le 0 8 76 67 (by omega) (by omega) (by omega))
/-- `75`-wire clean scratch subregister `(rWBPerm68[0..8) ++ rWBPerm68[76..143))` inside `rWB`
  (`143 ≤ mWB`). -/
def rScr75 {n mWB : ℕ} (hmWB : 143 ≤ mWB) (rWB : QRegister mWB n) : QRegister 75 n :=
  rScr75OfReg hmWB (rWBPerm68 hmWB rWB)
theorem rScr75_apply_perm {n mWB : ℕ} (hmWB : 143 ≤ mWB) (rWB : QRegister mWB n) (k : Fin 75)
    : ∃ u : Fin mWB, (u.val < 8 ∨ 76 ≤ u.val) ∧ rScr75 hmWB rWB k = rWB ((permOfProg mWB
    progLoadInternal68 61 8 (progLoadInternal68_perm_bound hmWB)).symm u) := by
  suffices h : ∀ rP : QRegister mWB n,
      ∃ u : Fin mWB, (u.val < 8 ∨ 76 ≤ u.val) ∧ rScr75OfReg hmWB rP k = rP u from
    h (rWBPerm68 hmWB rWB)
  intro rP
  dsimp only [rScr75OfReg]
  change Fin (8 + 67) at k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · refine ⟨⟨i.val, by
      have := i.isLt
      omega⟩, Or.inl i.isLt, ?_⟩
    rw [QRegister.concat_apply_left]
    exact congrArg rP (Fin.ext (by simp))
  · refine ⟨⟨76 + j.val, by
      have := j.isLt
      omega⟩, Or.inr (by
      dsimp
      omega), ?_⟩
    rw [QRegister.concat_apply_right]
    exact congrArg rP (Fin.ext (by simp))
theorem disj_rScr75_right {n kA mWB : ℕ} {rA : QRegister kA n} {rWB : QRegister mWB n}
    (hmWB : 143 ≤ mWB) (hAW : rA.DisjointWires rWB) : rA.DisjointWires (rScr75 hmWB rWB) := by
  rw [QRegister.disjoint_iff]
  intro a k hak
  obtain ⟨u, _, hsk⟩ := rScr75_apply_perm hmWB rWB k
  rw [hsk] at hak
  exact hAW.ne a _ hak
theorem rPeb10_disj_rScr75 {n mWB : ℕ} (hmWB : 143 ≤ mWB) (rWB : QRegister mWB n) :
    (rPeb10 hmWB rWB).DisjointWires (rScr75 hmWB rWB) := by
  rw [QRegister.disjoint_iff]
  intro i k hik
  obtain ⟨u, hu_range, hsk⟩ := rScr75_apply_perm hmWB rWB k
  have hspec := permOfProg_spec mWB progLoadInternal68 61 8 (progLoadInternal68_perm_bound hmWB)
  rw [hsk] at hik
  have he_eq : permOfProg mWB progLoadInternal68 61 8 (progLoadInternal68_perm_bound hmWB)
      (selPeb10InWB hmWB i) = u :=
    (congrArg _ (rWB.wires.injective hik)).trans
      ((permOfProg mWB progLoadInternal68 61 8
        (progLoadInternal68_perm_bound hmWB)).apply_symm_apply u)
  have hb := qPeb10_bounds i
  have hmid := (hspec (selPeb10InWB hmWB i)).2.2
    ⟨by
     dsimp [selPeb10InWB]; omega,
     by rw [progLoadInternal68_stats.2.1]; dsimp [selPeb10InWB]; omega⟩
  have hAt : isAndTarget progLoadInternal68 61 (qPeb10 i) = true := by
    clear * -
    revert i
    decide
  rw [show 61 + ((selPeb10InWB hmWB i).val - 8) = qPeb10 i by
    dsimp [selPeb10InWB]; omega,
    hAt, ite_eq_left rfl, progLoadInternal68_stats.2.2, he_eq] at hmid
  rcases hu_range with hlt | hge <;> omega
theorem pebBitFnGen_rScr75_zero {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (β : BitAssignment n) (hWB0 : ∀ w : Fin mWB, β (rWB w) = 0)
    (k : Fin 75) : pebBitFnGen hmPay progLoadInternal68 (by omega : 114 ≤ mWB) rCore rWB β
    (rScr75 hmWB rWB k) = 0 := by
  obtain ⟨u, hu_range, hsk⟩ := rScr75_apply_perm hmWB rWB k
  have hspec := permOfProg_spec mWB progLoadInternal68 61 8 (progLoadInternal68_perm_bound hmWB)
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin mWB,
      (permOfProg mWB progLoadInternal68 61 8 (progLoadInternal68_perm_bound hmWB)).symm u = idx :=
    ⟨_, rfl⟩
  have he_idx :
    (permOfProg mWB progLoadInternal68 61 8 (progLoadInternal68_perm_bound hmWB) idx).val =
      u.val := by
    rw [← hidx, Equiv.apply_symm_apply]
  rw [hsk, hidx]
  change pebBitFnGen hmPay progLoadInternal68 (by omega) rCore rWB β (rWB idx) = 0
  let rCln := rWB.slice 8 106 (by omega)
  dsimp only [pebBitFnGen]
  by_cases hIn : 8 ≤ idx.val ∧ idx.val < 8 + 106
  · let m : Fin 106 := ⟨idx.val - 8, by omega⟩
    have hrm : rWB idx = rCln m :=
      congrArg rWB (Fin.ext (by dsimp [m, rCln, QRegister.slice]; omega))
    rw [hrm, CoinDispatchedBarrel288.Internal.writeRegProg_apply_reg]
    have hnot_tar : isAndTarget progLoadInternal68 61 (61 + m.val) = false := by
      dsimp only [m]
      by_cases hlt113 : idx.val < 8 + (progEndCur 61 progLoadInternal68 - 61)
      · have hm_in := (hspec idx).2.2 ⟨hIn.1, hlt113⟩
        rcases Bool.eq_false_or_eq_true (isAndTarget progLoadInternal68 61 (61 + (idx.val - 8)))
          with ht | ht
        · rw [ht, ite_eq_left rfl, progLoadInternal68_stats.2.2, he_idx] at hm_in
          rcases hu_range with h1 | h2 <;> omega
        · exact ht
      · exact isAndTarget_ge progLoadInternal68 61 (61 + (idx.val - 8))
          (by rw [progLoadInternal68_stats.2.1] at hlt113 ⊢; omega)
    rw [rawPebble_of_not_andTarget _ _ _ _ hnot_tar]
    simp
  · have hnc : rWB idx ∉ Set.range rCln.wires := by
      rintro ⟨m, hm⟩
      have hv := congrArg Fin.val (rWB.wires.injective hm)
      have hmLt := m.isLt
      dsimp [rCln, QRegister.slice] at hv
      omega
    rw [CoinDispatchedBarrel288.Internal.writeRegProg_apply_of_not_mem
      _ _ _ _ hnc]
    exact hWB0 idx
/-- `93`-wire combined register `rU8Core8[0..8) ++ rPeb10[0..10) ++ rScr75[0..75)` for
  `ctxFast64x4WG`. -/
def rComb93 {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) : QRegister 93 n := ((rU8Core8 hmPay rCore).concat (rPeb10
    hmWB rWB) ((hCW.compose_left _).compose_right _)).concat (rScr75 hmWB rWB)
    (qreg_disjoint_concat_left (disj_rScr75_right hmWB (hCW.compose_left _))
    (rPeb10_disj_rScr75 hmWB rWB))
theorem rComb93_u8 {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (j : Fin 8) :
    rComb93 hmPay hmWB rCore rWB hCW ⟨j.val, by omega⟩ = rU8Core8 hmPay rCore j := by
  have heq : (⟨j.val, by omega⟩ : Fin 93) = Fin.castAdd 75 (Fin.castAdd 10 j) := Fin.ext rfl
  rw [heq]; dsimp only [rComb93]
  rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
theorem rComb93_peb10 {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (i : Fin 10) :
    rComb93 hmPay hmWB rCore rWB hCW ⟨8 + i.val, by omega⟩ = rPeb10 hmWB rWB i := by
  have heq : (⟨8 + i.val, by omega⟩ : Fin 93) = Fin.castAdd 75 (Fin.natAdd 8 i) := Fin.ext rfl
  rw [heq]; dsimp only [rComb93]
  rw [QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem rComb93_enIdx9 {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (i : Fin 9) :
    rComb93 hmPay hmWB rCore rWB hCW ⟨9 + i.val, by omega⟩ = rEnIdx9 hmWB rWB i := by
  have h1 : (⟨9 + i.val, by omega⟩ : Fin 93) = ⟨8 + (⟨1 + i.val, by omega⟩ : Fin 10).val,
    by omega⟩ :=
    Fin.ext (by dsimp; omega)
  rw [h1, rComb93_peb10]
  rfl
theorem rComb93_scr75 {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (k : Fin 75) :
    rComb93 hmPay hmWB rCore rWB hCW ⟨18 + k.val, by omega⟩ = rScr75 hmWB rWB k := by
  have heq : (⟨18 + k.val, by omega⟩ : Fin 93) = Fin.natAdd 18 k := Fin.ext rfl
  rw [heq]; dsimp only [rComb93]
  rw [QRegister.concat_apply_right]
/-- Decodes a `9`-bit `(wEn, wIdx[0..8))` tuple into a `Fin 218` electron slot with zero
  fallback. -/
def gatedIdx9 (ei : BitAssignment 9) : Fin 218 :=
  let raw := if ei 0 = 1 then bitsVal (fun j : Fin 8 ↦ ei ⟨1 + j.val, by omega⟩) else 0
  if h : raw < 218 then ⟨raw, h⟩ else 0
theorem gatedIdx9_val_zero (ei : BitAssignment 9) (h0 : ei 0 = 0) :
    (gatedIdx9 ei).val = 0 := by
  have hne : ei 0 ≠ 1 := by rw [h0]; decide
  dsimp only [gatedIdx9]
  rw [ite_eq_right hne, dite_eq_left (by decide : 0 < 218)]
theorem gatedIdx9_val_one (ei : BitAssignment 9) (h1 : ei 0 = 1)
    (hlt : bitsVal (fun j : Fin 8 ↦ ei ⟨1 + j.val, by omega⟩) < 218) :
    (gatedIdx9 ei).val = bitsVal (fun j : Fin 8 ↦ ei ⟨1 + j.val, by omega⟩) := by
  dsimp only [gatedIdx9]
  rw [ite_eq_left h1, dite_eq_left hlt]
/-- Prefix selector `Fin C → Fin (C + 9)` for `rDataEI := rCore.concat rEnIdx9`. -/
def selCoreInEI (C : ℕ) : QRegister C (C + 9) where
  wires := ⟨Fin.castAdd 9, Fin.castAdd_injective C 9⟩
/-- `posCoreWires` selector inside `fullSysCoreWires mPayload + 9`. -/
def selCoreEI {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    QRegister posCoreWires (fullSysCoreWires mPayload + 9) :=
  (selCoreInEI (fullSysCoreWires mPayload)).compose (selPosInFullSys hmPay)
/-- `218`-slot selector reading `rEnIdx9` (`Fin.natAdd C`) on `fullSysCoreWires mPayload + 9`. -/
def sFnEI (C : ℕ) (δ : BitAssignment (C + 9)) : Fin 218 :=
  gatedIdx9 (fun i ↦ δ (Fin.natAdd C i))
/-- Active `18`-wire electron slot subregister inside `fullSysCoreWires mPayload + 9` for
  `sFnEI`. -/
def fastEISlotReg {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (d : Fin (2 ^ (fullSysCoreWires mPayload + 9))) : QRegister 18
    (fullSysCoreWires mPayload + 9) := (selCoreInEI (fullSysCoreWires mPayload)).compose
    (rFullSysElecSlot hmPay (sFnEI (fullSysCoreWires mPayload) (basisBits (fullSysCoreWires
    mPayload + 9) d)))
theorem fastEISlotReg_replaceIndex {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (d : Fin (2 ^ (fullSysCoreWires mPayload + 9))) (v : Fin (2 ^ 18)) :
    fastEISlotReg hmPay ((fastEISlotReg hmPay d).replaceIndex d v) = fastEISlotReg hmPay d := by
  let C := fullSysCoreWires mPayload
  dsimp only [fastEISlotReg]
  refine congrArg (fun e ↦ (selCoreInEI C).compose (rFullSysElecSlot hmPay e)) ?_
  dsimp only [sFnEI]
  refine congrArg gatedIdx9 (funext fun i ↦ ?_)
  refine QRegister.basisBits_replaceIndex_of_not_mem _ d v (Fin.natAdd C i) ?_
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp [selCoreInEI] at hv
  omega
/-- `Slot18Lens (fullSysCoreWires mPayload + 9)` selecting `rElec[sFnEI]` for the inner `.hole`
  circuits. -/
noncomputable def fastEILens {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Slot18Lens (fullSysCoreWires mPayload + 9) :=
  mkSlot18LensOfSlotReg (fastEISlotReg hmPay) (fastEISlotReg_replaceIndex hmPay)
private theorem natAdd_not_mem_selHad_selCoreEI {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (i : Fin 9) : selDataInAct (fullSysCoreWires mPayload + 9)
    (Fin.natAdd (fullSysCoreWires mPayload) i) ∉ Set.range
    (selHadOfPosCore (selCoreEI hmPay)).wires := by
  rintro ⟨k, hk⟩
  change Fin (3924 + 18) at k
  revert hk
  refine Fin.addCases (fun idx hk ↦ ?_) (fun m hk ↦ ?_) k
  · dsimp only [selHadOfPosCore] at hk
    rw [QRegister.concat_apply_left] at hk
    have hv := congrArg Fin.val ((selDataInAct _).wires.injective hk)
    simp [selCoreEI, selCoreInEI] at hv
    omega
  · dsimp only [selHadOfPosCore] at hk
    rw [QRegister.concat_apply_right] at hk
    exact (selDataInAct_disj_selMeasInAct _).ne _ m hk.symm
theorem hsFnEI_had {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload + 9)) (h : ∀ u : Wire
    (fullSysCoreWires mPayload + 9), selDataInAct (fullSysCoreWires mPayload + 9) u ∉
    Set.range (selHadOfPosCore (selCoreEI hmPay)).wires → γ₁ u = γ₂ u) : sFnEI
    (fullSysCoreWires mPayload) γ₁ = sFnEI (fullSysCoreWires mPayload) γ₂ := congrArg
    gatedIdx9 (funext fun i ↦ h (Fin.natAdd _ i) (natAdd_not_mem_selHad_selCoreEI hmPay i))
theorem hTblBit_fastEILens {n mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rEI : QRegister 9 n) (hCEI : rCore.DisjointWires rEI)
    (g : Fin (2 ^ n)) (j : Fin 18) :
    let rDataEI := rCore.concat rEI hCEI
    basisBits 18 ((fastEILens hmPay).tbl (rDataEI.extractIndex g)) j =
      basisBits n g (rElecSlot (rDataEI.compose (selCoreEI hmPay))
        (sFnEI (fullSysCoreWires mPayload) (fun u ↦ basisBits n g (rDataEI u))) j) := by
  intro rDataEI
  let C := fullSysCoreWires mPayload
  have hSub : basisBits (fullSysCoreWires mPayload + 9) (rDataEI.extractIndex g) =
      (fun u ↦ basisBits n g (rDataEI u)) :=
    funext fun u ↦ QRegister.basisBits_extractIndex rDataEI g u
  change basisBits 18 ((fastEISlotReg hmPay (rDataEI.extractIndex g)).extractIndex
      (rDataEI.extractIndex g)) j = _
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  dsimp only [fastEISlotReg]
  rw [hSub]
  refine congrArg (basisBits n g) ?_
  change rDataEI (selCoreInEI C (selPosInFullSys hmPay (rElecSlot (QRegExt.ofFin
    posCoreWires) _ j))) = rElecSlot (rDataEI.compose (selCoreEI hmPay)) _ j
  exact (rElecSlot_apply_ofFin (rDataEI.compose (selCoreEI hmPay)) _ j).symm
theorem hWriteEq_fastEILens {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    uWriteSub (selHadOfPosCore (selCoreEI hmPay)) (uLensLoad (fastEILens hmPay)) =
      uLensWrite (fastEILens hmPay) := by
  let C := fullSysCoreWires mPayload
  refine uWriteSub_uLensLoad_eq_uLensWrite_of_slotReg (selHadOfPosCore (selCoreEI hmPay))
    (fastEILens hmPay) (fastEISlotReg hmPay) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun d j ↦ rDataElec_mem_selHadOfPosCore (selCoreEI hmPay) _ j)
    (selMeasInAct_mem_selHadOfPosCore (selCoreEI hmPay)) (fun g₀ z hSame ↦ congrArg (fun e ↦
    (selCoreInEI C).compose (rFullSysElecSlot hmPay e)) ?_)
  dsimp only [sFnEI]
  refine congrArg gatedIdx9 (funext fun i ↦ ?_)
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact hSame _ (natAdd_not_mem_selHad_selCoreEI hmPay i)
-- Disjointness witness for the `64`-leaf gated W-state router inside `DiagCtxWG 93`.
theorem fast64_hdLo :
    DisjWCohGate1 (M := 93) ⟨9, by decide⟩ (fun d : Fin 6 ↦ ⟨10 + d.val, by omega⟩)
      (fun l : Fin 64 ↦ ⟨18 + l.val, by omega⟩) ⟨92, by decide⟩ :=
  ⟨fun _ ↦ Fin.ne_of_val_ne (by dsimp; omega),
   Fin.ne_of_val_ne (by decide),
   fun _ _ ↦ Fin.ne_of_val_ne (by dsimp; omega),
   fun _ ↦ Fin.ne_of_val_ne (by dsimp; omega),
   fun _ _ h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega),
   fun _ ↦ Fin.ne_of_val_ne (by dsimp; omega)⟩
-- Disjointness witness for the `4`-leaf gated W-state router inside `DiagCtxWG 93`.
theorem fast64_hdHi :
    DisjWCohGate1 (M := 93) ⟨9, by decide⟩ (fun d : Fin 2 ↦ ⟨16 + d.val, by omega⟩)
      (fun h : Fin 4 ↦ ⟨82 + h.val, by omega⟩) ⟨92, by decide⟩ :=
  ⟨fun _ ↦ Fin.ne_of_val_ne (by dsimp; omega),
   Fin.ne_of_val_ne (by decide),
   fun _ _ ↦ Fin.ne_of_val_ne (by dsimp; omega),
   fun _ ↦ Fin.ne_of_val_ne (by dsimp; omega),
   fun _ _ h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega),
   fun _ ↦ Fin.ne_of_val_ne (by dsimp; omega)⟩
end BoothOpt_FastAnchorOuterAndStageBShave
end SharedScope
end SlimStageBOuterDepsD

noncomputable section SlimStageBOuterDeps

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
section SharedScope
local instance (priority := 1000000) instNeZeroK9 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority :=
  1000000) instGroupUnitaryFast_SlimStageBOuterDeps (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_SlimStageBOuterDeps (D : ℕ) : Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
namespace BoothOpt_FastAnchorOuterAndStageBShave
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open MeasureBranchHadamardSem (ket bit_cases matrix_ext_ket)
open CoinDispatchedBarrel288.Internal (CliffProg)
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open AnchorSwap0Split133 MultiBankWStateRouter ParticleOneHotWState
open BoothOpt_02_Cached64x4TrueSwapEngine (CliffWritesAbove)
section Part3_OuterFastEngine
open HoistBorrow42ProjBridge (RealizesOnProj)
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_concat_left)
open InterWalkRSum42Hoist (kFull80 rCoreFull)
open CoinDispatchedBarrel288 FastCoinBarrelDecoder279 Pass1BarrelIdxLoad273
open Pass1BarrelIdxPebbled273
  (progLoadInternal68 progLoadInternal68_stats progLoadInternal68_end_le rawPebble cliffOfProgGen
  progFwdCircuit progToDynWrap count_progToDynWrap_toff count_progToDynWrap_t progToDynWrap_realizes
  HasCleanTailFrom rCombPeb rCombPeb_cln106 hasCleanTailFrom_rWB_proj0 singleton_rWB_mul_proj0
  stHighCore pebBitFnGen vPeb_ket_of_scr0_gen ket_basisOutcomeProjector_zero
  cliffProg_onRegister_eval_inv)
open PosSlots24Barrel3Pass (permUnitary_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensLoadPerm lensWritePerm lensSwapPerm)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply selDataInAct_disj_selMeasInAct
  concat_compose_selDataInAct concat_compose_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure
  (extractPair liftPairIdx lensLoadEquiv lensWriteEquiv lensSwapEquiv uLensLoad uLensWrite uLensSwap
  uLensWrite_mul_uLensLoad_projZero_eq_uLensSwap)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 P_slot0_eq_diagonal)
open BoothOpt_02_Cached64x4TrueSwapEngine
open BoothOpt_03_CoinBarrelIdxFastTrueSwap
  (rFullSysElecSlot rFullSysElecSlot_val coinBarrelIdxFast_val_lt_218 coinBarrelFastSlotReg
  coinBarrelFastSlot18Lens coinBarrelFastOnDataLens)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (selLiftAct concat_compose_selLiftAct uLensLoad_liftSlot18Lens uLensWrite_liftSlot18Lens
  uLensSwap_liftSlot18Lens P_slot0_liftSlot18Lens P_slot0_conjTranspose P_slot0_mul_E_anchorLoc
  L_anchor P_anc0 E_anchorLoc E_anchor uAnchorLensSwap realizesOnProj_mul_right
  realizesOnProj_congr_unitary selDataInAct_embedMatrix_comm_P_anc0)
open StageBFastInnerPartnerShift
  (dPreHole218 dPreHole218_count_toff dPreHole218_count_t dPostHole218)
def cZeroFallback93 : CliffProg 93 :=
  .seq (.x ⟨18, by decide⟩)
  (.seq (.cnot ⟨9, by decide⟩ ⟨18, by decide⟩ (by decide))
  (.seq (.x ⟨82, by decide⟩)
        (.cnot ⟨9, by decide⟩ ⟨82, by decide⟩ (by decide))))
/-- Inner `148 T` `64 × 4` coherent zero-gated W-state router context (`base = 18`). -/
def ctxFastTrees93 : DiagCtxWG 93 :=
  .wStateTreeCohGate1 5 ⟨9, by decide⟩ (fun d ↦ ⟨10 + d.val, by omega⟩)
    (fun l ↦ ⟨18 + l.val, by omega⟩) ⟨92, by decide⟩ fast64_hdLo
  (.wStateTreeCohGate1 1 ⟨9, by decide⟩ (fun d ↦ ⟨16 + d.val, by omega⟩)
    (fun h ↦ ⟨82 + h.val, by omega⟩) ⟨92, by decide⟩ fast64_hdHi
  (.cliffConj cZeroFallback93 .hole))
/-- `93`-wire pre-linearization Clifford setting `wEn := q68 ⊕ q67` and `wIdx_j := qMux_j ⊕
  u8_j`. -/
def cPreLin93 : CliffProg 93 :=
  .seq (.cnot ⟨8, by decide⟩ ⟨9, by decide⟩ (by decide))
  (.seq (.cnot ⟨0, by decide⟩ ⟨10, by decide⟩ (by decide))
  (.seq (.cnot ⟨1, by decide⟩ ⟨11, by decide⟩ (by decide))
  (.seq (.cnot ⟨2, by decide⟩ ⟨12, by decide⟩ (by decide))
  (.seq (.cnot ⟨3, by decide⟩ ⟨13, by decide⟩ (by decide))
  (.seq (.cnot ⟨4, by decide⟩ ⟨14, by decide⟩ (by decide))
  (.seq (.cnot ⟨5, by decide⟩ ⟨15, by decide⟩ (by decide))
  (.seq (.cnot ⟨6, by decide⟩ ⟨16, by decide⟩ (by decide))
        (.cnot ⟨7, by decide⟩ ⟨17, by decide⟩ (by decide)))))))))
/-- Full `148 T` `DiagCtxWG 93` wrapper (`cPreLin93` + `ctxFastTrees93`). -/
def ctxFast64x4WG : DiagCtxWG 93 := .cliffConj cPreLin93 ctxFastTrees93
theorem countT_ctxFast64x4WG : ctxFast64x4WG.countT = 148 := rfl
theorem ctxFastTrees93_writesAbove18 : DiagCtxWGWritesAbove 18 ctxFastTrees93 :=
  ⟨fun _ ↦ by
   dsimp; omega,
   fun _ ↦ by dsimp; omega,
   ⟨by
    dsimp [CliffWritesAbove]; omega,
    by dsimp [CliffWritesAbove]; omega,
    by dsimp [CliffWritesAbove]; omega,
    by dsimp [CliffWritesAbove]; omega⟩,
   trivial⟩
/-- Entry invariant on `BitAssignment 93` for `ctxFastTrees93`. -/
def invTreesIn93 (γ : BitAssignment 93) : Prop :=
  (γ ⟨9, by decide⟩ = 1 → bitsVal (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) < 218) ∧
  (∀ idx : Wire 93, 18 ≤ idx.val → γ idx = 0)
/-- `.hole` invariant on `BitAssignment 93` produced by `ctxFastTrees93`. -/
def invHole93 (γ : BitAssignment 93) : Prop :=
  let s₀ := gatedIdx9 (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩)
  (∀ l : Fin 64, γ ⟨18 + l.val, by omega⟩ = if l.val = s₀.val % 64 then 1 else 0) ∧
  (∀ h : Fin 4, γ ⟨82 + h.val, by omega⟩ = if h.val = s₀.val / 64 then 1 else 0) ∧
  γ ⟨87, by decide⟩ = 0 ∧
  (∀ r : Fin 4, γ ⟨88 + r.val, by omega⟩ = 0) ∧
  γ ⟨92, by decide⟩ = 0
theorem cZeroFallback93_eval (δ : BitAssignment 93) (w : Wire 93) : cZeroFallback93.eval δ w =
    if w = ⟨18, by decide⟩ then δ ⟨18, by decide⟩ + 1 + δ ⟨9, by decide⟩
    else if w = ⟨82, by decide⟩ then δ ⟨82, by decide⟩ + 1 + δ ⟨9, by decide⟩ else δ w := by
  have h18_ne_82 : (⟨18, by decide⟩ : Wire 93) ≠ ⟨82, by decide⟩ := Fin.ne_of_val_ne (by decide)
  have h82_ne_18 : (⟨82, by decide⟩ : Wire 93) ≠ ⟨18, by decide⟩ := Fin.ne_of_val_ne (by decide)
  have h9_ne_18 : (⟨9, by decide⟩ : Wire 93) ≠ ⟨18, by decide⟩ := Fin.ne_of_val_ne (by decide)
  have h9_ne_82 : (⟨9, by decide⟩ : Wire 93) ≠ ⟨82, by decide⟩ := Fin.ne_of_val_ne (by decide)
  dsimp only [cZeroFallback93, CliffProg.eval]
  by_cases hw18 : w = ⟨18, by decide⟩
  · subst hw18
    rw [ite_eq_left rfl, Function.update_of_ne h18_ne_82, Function.update_of_ne h18_ne_82,
        Function.update_self, Function.update_self, Function.update_of_ne h9_ne_18]
  · rw [ite_eq_right hw18]
    by_cases hw82 : w = ⟨82, by decide⟩
    · subst hw82
      rw [ite_eq_left rfl, Function.update_self, Function.update_self,
          Function.update_of_ne h9_ne_82, Function.update_of_ne h82_ne_18,
          Function.update_of_ne h82_ne_18, Function.update_of_ne h9_ne_18,
          Function.update_of_ne h9_ne_18]
    · rw [ite_eq_right hw82, Function.update_of_ne hw82, Function.update_of_ne hw82,
          Function.update_of_ne hw18, Function.update_of_ne hw18]
theorem validAtWith_ctxFastTrees93 (γ : BitAssignment 93) (hIn : invTreesIn93 γ) :
    ctxFastTrees93.ValidAtWith invHole93 γ := by
  let body1 : DiagCtxWG 93 :=
    .wStateTreeCohGate1 1 ⟨9, by decide⟩ (fun d ↦ ⟨16 + d.val, by omega⟩)
      (fun h ↦ ⟨82 + h.val, by omega⟩) ⟨92, by decide⟩ fast64_hdHi
      (.cliffConj cZeroFallback93 .hole)
  obtain ⟨γ₁, hfwd1, hval1, hout1, hpres1⟩ := DiagCtxWG.wStateTreeCohGate1_step 5
    ⟨9, by decide⟩ (fun d ↦ ⟨10 + d.val, by omega⟩)
    (fun l ↦ ⟨18 + l.val, by omega⟩) ⟨92, by decide⟩ fast64_hdLo body1 γ
    (fun l ↦ hIn.2 _ (by dsimp; omega)) (hIn.2 _ (by decide))
  have hγ₁_outHi : ∀ h : Fin 4, γ₁ ⟨82 + h.val, by omega⟩ = 0 := fun h ↦
    (hpres1 _ fun l ↦ Fin.ne_of_val_ne (by dsimp; omega)).trans (hIn.2 _ (by dsimp; omega))
  have hγ₁_92 : γ₁ ⟨92, by decide⟩ = 0 :=
    (hpres1 _ fun l ↦ Fin.ne_of_val_ne (by dsimp; omega)).trans (hIn.2 _ (by decide))
  obtain ⟨γ₂, hfwd2, hval2, hout2, hpres2⟩ := DiagCtxWG.wStateTreeCohGate1_step 1
    ⟨9, by decide⟩ (fun d ↦ ⟨16 + d.val, by omega⟩)
    (fun h ↦ ⟨82 + h.val, by omega⟩) ⟨92, by decide⟩ fast64_hdHi
    (.cliffConj cZeroFallback93 .hole) γ₁ hγ₁_outHi hγ₁_92
  have hValid : ctxFastTrees93.ValidAt γ := hval1 (hval2 trivial)
  refine DiagCtxWG.validAtWith_of_validAt ctxFastTrees93 hValid ?_
  have hfwd_eq : ctxFastTrees93.fwdBits γ = cZeroFallback93.eval γ₂ := hfwd1.trans hfwd2
  rw [hfwd_eq]
  have hγ₂_low : ∀ (w : Wire 93), w.val < 18 → γ₂ w = γ w := fun w hw ↦
    (hpres2 w fun h ↦ Fin.ne_of_val_ne (by dsimp; omega)).trans
      (hpres1 w fun l ↦ Fin.ne_of_val_ne (by dsimp; omega))
  have hγ₃_ei : (fun i : Fin 9 ↦ cZeroFallback93.eval γ₂ ⟨9 + i.val, by omega⟩) =
      (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩) := funext fun i ↦ by
    rw [cZeroFallback93_eval,
        ite_eq_right (Fin.ne_of_val_ne (by dsimp; omega)),
        ite_eq_right (Fin.ne_of_val_ne (by dsimp; omega))]
    exact hγ₂_low _ (by dsimp; omega)
  have hγ₂_9 : γ₂ ⟨9, by decide⟩ = γ ⟨9, by decide⟩ := hγ₂_low _ (by decide)
  have hγ₁_9 : γ₁ ⟨9, by decide⟩ = γ ⟨9, by decide⟩ :=
    hpres1 _ fun l ↦ Fin.ne_of_val_ne (by dsimp; omega)
  have hγ₁_hi2 : (fun d : Fin 2 ↦ γ₁ ⟨16 + d.val, by omega⟩) =
      (fun d : Fin 2 ↦ γ ⟨16 + d.val, by omega⟩) :=
    funext fun d ↦ hpres1 _ fun l ↦ Fin.ne_of_val_ne (by dsimp; omega)
  have hγ₂_lo64 : ∀ l : Fin 64, γ₂ ⟨18 + l.val, by omega⟩ = γ₁ ⟨18 + l.val, by omega⟩ :=
    fun l ↦ hpres2 _ fun h ↦ Fin.ne_of_val_ne (by dsimp; omega)
  have hγ₂_hi_clean : ∀ (w : Wire 93), 86 ≤ w.val → cZeroFallback93.eval γ₂ w = 0 := fun w hw ↦ by
    rw [cZeroFallback93_eval,
        ite_eq_right (Fin.ne_of_val_ne (by dsimp; omega)),
        ite_eq_right (Fin.ne_of_val_ne (by dsimp; omega))]
    exact (hpres2 w fun h ↦ Fin.ne_of_val_ne (by dsimp; omega)).trans
      ((hpres1 w fun l ↦ Fin.ne_of_val_ne (by dsimp; omega)).trans (hIn.2 w (by omega)))
  dsimp only [invHole93]
  rw [hγ₃_ei]
  have hsplit := bitsVal_split_6_2 (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩)
  have hlo_lt : bitsVal (fun d : Fin 6 ↦ γ ⟨10 + d.val, by omega⟩) < 64 := by
    have h := idxValD_lt_two_pow (fun d : Fin 6 ↦ (⟨10 + d.val, by omega⟩ : Wire 93)) γ
    rw [idxValD_eq_bitsVal] at h
    omega
  have hlo_fn : (fun d : Fin 6 ↦ (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) ⟨d.val, by omega⟩) =
      (fun d : Fin 6 ↦ γ ⟨10 + d.val, by omega⟩) := rfl
  have hhi_fn : (fun d : Fin 2 ↦ (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) ⟨6 + d.val, by omega⟩) =
      (fun d : Fin 2 ↦ γ ⟨16 + d.val, by omega⟩) :=
    funext fun d ↦ congrArg γ (Fin.ext (by dsimp; omega))
  have hsub8 : (fun j : Fin 8 ↦ (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩) ⟨1 + j.val, by omega⟩) =
      (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) :=
    funext fun j ↦ congrArg γ (Fin.ext (by dsimp; omega))
  rw [hlo_fn, hhi_fn] at hsplit
  refine ⟨?_, ?_, hγ₂_hi_clean _ (by decide), fun r ↦ hγ₂_hi_clean _ (by dsimp; omega),
          hγ₂_hi_clean _ (by decide)⟩
  · intro l
    rw [cZeroFallback93_eval]
    have hne82 : (⟨18 + l.val, by omega⟩ : Wire 93) ≠ ⟨82, by decide⟩ :=
      Fin.ne_of_val_ne (by dsimp; omega)
    rcases bit_cases (γ ⟨9, by decide⟩) with h9 | h9
    · have hs0 : (gatedIdx9 (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩)).val = 0 :=
        gatedIdx9_val_zero _ h9
      rw [hs0]; simp only [Nat.zero_mod]
      by_cases hl0 : l.val = 0
      · have heq18 : (⟨18 + l.val, by omega⟩ : Wire 93) = ⟨18, by decide⟩ :=
          Fin.ext (by dsimp; omega)
        rw [ite_eq_left heq18, ite_eq_left hl0, hγ₂_9, h9]
        have hz2 : γ₂ ⟨18, by decide⟩ = 0 :=
          (hγ₂_lo64 ⟨0, by decide⟩).trans ((hout1 ⟨0, by decide⟩).trans (by rw [h9, ite_self]))
        rw [hz2]; rfl
      · have hne18 : (⟨18 + l.val, by omega⟩ : Wire 93) ≠ ⟨18, by decide⟩ :=
          Fin.ne_of_val_ne (by dsimp; omega)
        rw [ite_eq_right hne18, ite_eq_right hne82, ite_eq_right hl0, hγ₂_lo64 l, hout1 l, h9]
        split_ifs <;> rfl
    · have hlt218 : bitsVal (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) < 218 := hIn.1 h9
      have hs1 : (gatedIdx9 (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩)).val =
          bitsVal (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) :=
        (gatedIdx9_val_one _ h9 (hsub8 ▸ hlt218)).trans (congrArg bitsVal hsub8)
      have hmod : (gatedIdx9 (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩)).val % 64 =
          bitsVal (fun d : Fin 6 ↦ γ ⟨10 + d.val, by omega⟩) := by
        rw [hs1, hsplit]; omega
      rw [hmod]
      by_cases hl0 : l.val = 0
      · have heq18 : (⟨18 + l.val, by omega⟩ : Wire 93) = ⟨18, by decide⟩ :=
          Fin.ext (by dsimp; omega)
        rw [ite_eq_left heq18, hγ₂_9, h9]
        have h11 : γ₂ ⟨18, by decide⟩ + 1 + 1 = γ₂ ⟨18, by decide⟩ := by
          rw [add_assoc]; change γ₂ ⟨18, by decide⟩ + 0 = _; exact add_zero _
        rw [h11, ← heq18, hγ₂_lo64 l, hout1 l, h9]
      · have hne18 : (⟨18 + l.val, by omega⟩ : Wire 93) ≠ ⟨18, by decide⟩ :=
          Fin.ne_of_val_ne (by dsimp; omega)
        rw [ite_eq_right hne18, ite_eq_right hne82, hγ₂_lo64 l, hout1 l, h9]
  · intro h
    rw [cZeroFallback93_eval]
    have hne18 : (⟨82 + h.val, by omega⟩ : Wire 93) ≠ ⟨18, by decide⟩ :=
      Fin.ne_of_val_ne (by dsimp; omega)
    rw [ite_eq_right hne18]
    rcases bit_cases (γ ⟨9, by decide⟩) with h9 | h9
    · have hs0 : (gatedIdx9 (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩)).val = 0 :=
        gatedIdx9_val_zero _ h9
      rw [hs0]; simp only [Nat.zero_div]
      by_cases hh0 : h.val = 0
      · have heq82 : (⟨82 + h.val, by omega⟩ : Wire 93) = ⟨82, by decide⟩ :=
          Fin.ext (by dsimp; omega)
        rw [ite_eq_left heq82, ite_eq_left hh0, hγ₂_9, h9]
        have hz2 : γ₂ ⟨82, by decide⟩ = 0 :=
          (hout2 ⟨0, by decide⟩).trans (by rw [hγ₁_9, h9, ite_self])
        rw [hz2]; rfl
      · have hne82 : (⟨82 + h.val, by omega⟩ : Wire 93) ≠ ⟨82, by decide⟩ :=
          Fin.ne_of_val_ne (by dsimp; omega)
        rw [ite_eq_right hne82, ite_eq_right hh0, hout2 h, hγ₁_9, h9]
        split_ifs <;> rfl
    · have hlt218 : bitsVal (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) < 218 := hIn.1 h9
      have hs1 : (gatedIdx9 (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩)).val =
          bitsVal (fun j : Fin 8 ↦ γ ⟨10 + j.val, by omega⟩) :=
        (gatedIdx9_val_one _ h9 (hsub8 ▸ hlt218)).trans (congrArg bitsVal hsub8)
      have hdiv : (gatedIdx9 (fun i : Fin 9 ↦ γ ⟨9 + i.val, by omega⟩)).val / 64 =
          bitsVal (fun d : Fin 2 ↦ γ ⟨16 + d.val, by omega⟩) := by
        rw [hs1, hsplit]; omega
      rw [hdiv]
      by_cases hh0 : h.val = 0
      · have heq82 : (⟨82 + h.val, by omega⟩ : Wire 93) = ⟨82, by decide⟩ :=
          Fin.ext (by dsimp; omega)
        rw [ite_eq_left heq82, hγ₂_9, h9]
        have h11 : γ₂ ⟨82, by decide⟩ + 1 + 1 = γ₂ ⟨82, by decide⟩ := by
          rw [add_assoc]; change γ₂ ⟨82, by decide⟩ + 0 = _; exact add_zero _
        rw [h11, ← heq82, hout2 h, hγ₁_hi2, hγ₁_9, h9]
      · have hne82 : (⟨82 + h.val, by omega⟩ : Wire 93) ≠ ⟨82, by decide⟩ :=
          Fin.ne_of_val_ne (by dsimp; omega)
        rw [ite_eq_right hne82, hout2 h, hγ₁_hi2, hγ₁_9, h9]
theorem invHole93_iff_invHoleSlot218 {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (β : BitAssignment n) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    invHole93 (fun idx ↦ β (rComb93 hmPay hmWB rCore rWB hCW idx)) ↔
      invHoleSlot218 (le_refl 75) rDataEI (sFnEI (fullSysCoreWires mPayload))
        (rScr75 hmWB rWB) β := by
  intro hCEI rDataEI
  have hsEq : gatedIdx9 (fun i : Fin 9 ↦
    β (rComb93 hmPay hmWB rCore rWB hCW ⟨9 + i.val, by omega⟩)) =
      sFnEI (fullSysCoreWires mPayload) (fun u ↦ β (rDataEI u)) := by
    dsimp only [sFnEI]
    refine congrArg gatedIdx9 (funext fun i ↦ congrArg β ?_)
    rw [rComb93_enIdx9]
    exact (QRegister.concat_apply_right rCore (rEnIdx9 hmWB rWB) hCEI i).symm
  have hLo : ∀ l : Fin 64,
      β (rComb93 hmPay hmWB rCore rWB hCW ⟨18 + l.val, by omega⟩) =
        β (rScr75 hmWB rWB ⟨l.val, by omega⟩) :=
    fun l ↦ congrArg β (rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨l.val, by omega⟩)
  have hHi : ∀ h : Fin 4,
      β (rComb93 hmPay hmWB rCore rWB hCW ⟨82 + h.val, by omega⟩) =
        β (rScr75 hmWB rWB ⟨64 + h.val, by omega⟩) := fun h ↦ by
    have heq : (⟨82 + h.val, by omega⟩ : Fin 93) = ⟨18 + (⟨64 + h.val, by omega⟩ : Fin 75).val,
      by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [heq]; exact congrArg β (rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨64 + h.val, by omega⟩)
  have h87 : β (rComb93 hmPay hmWB rCore rWB hCW ⟨87, by decide⟩) =
      β (rScr75 hmWB rWB ⟨69, by decide⟩) :=
    congrArg β (rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨69, by decide⟩)
  have hRow : ∀ r : Fin 4,
      β (rComb93 hmPay hmWB rCore rWB hCW ⟨88 + r.val, by omega⟩) =
        β (p2dSubReg (rScr75 hmWB rWB) 70 4 (by omega) r) := fun r ↦ by
    have heq : (⟨88 + r.val, by omega⟩ : Fin 93) = ⟨18 + (⟨70 + r.val, by omega⟩ : Fin 75).val,
      by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [heq]; exact congrArg β (rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨70 + r.val, by omega⟩)
  have h92 : β (rComb93 hmPay hmWB rCore rWB hCW ⟨92, by decide⟩) =
      β (rScr75 hmWB rWB ⟨74, by decide⟩) :=
    congrArg β (rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨74, by decide⟩)
  dsimp only [invHole93, invHoleSlot218]
  simp only [hsEq, hLo, hHi, h87, hRow, h92]
theorem rComb93_above18_not_mem_actEI {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB)
    (idx : Wire 93) (hidx : 18 ≤ idx.val) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    rComb93 hmPay hmWB rCore rWB hCW idx ∉ Set.range rActEI.wires := by
  intro hCEI hDA_EI rActEI
  let k : Fin 75 := ⟨idx.val - 18, by omega⟩
  have hik : idx = ⟨18 + k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
  rw [hik, rComb93_scr75]
  have hDS_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires (rScr75 hmWB rWB) :=
    qreg_disjoint_concat_left (disj_rScr75_right hmWB hCW)
      ((rPeb10_disj_rScr75 hmWB rWB).compose_left _)
  have hActScr : rActEI.DisjointWires (rScr75 hmWB rWB) :=
    disjointWires_concat_left hDA_EI hDS_EI (disj_rScr75_right hmWB hAW)
  rintro ⟨u, hu⟩
  exact hActScr.ne u k hu
theorem hCombPres_fastEILens_perm {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB)
    (e : Equiv.Perm (Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18))))
    (heCore : ∀ (w : Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18)))
      (i : Fin (fullSysCoreWires mPayload)), 3924 ≤ i.val →
      basisBits ((fullSysCoreWires mPayload + 9) + 18) (e w)
        (Fin.castAdd 18 (Fin.castAdd 9 i)) =
      basisBits ((fullSysCoreWires mPayload + 9) + 18) w
        (Fin.castAdd 18 (Fin.castAdd 9 i)))
    (heEI : ∀ (w : Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18))) (i : Fin 9),
      basisBits ((fullSysCoreWires mPayload + 9) + 18) (e w)
        (Fin.castAdd 18 (Fin.natAdd (fullSysCoreWires mPayload) i)) =
      basisBits ((fullSysCoreWires mPayload + 9) + 18) w
        (Fin.castAdd 18 (Fin.natAdd (fullSysCoreWires mPayload) i))) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    ∀ (idx : Wire 93) (g : Fin (2 ^ n))
      (y : Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18))),
      (Operator.permutationUnitary e).1 y (rActEI.extractIndex g) ≠ 0 →
      basisBits n (rActEI.replaceIndex g y) (rComb93 hmPay hmWB rCore rWB hCW idx) =
        basisBits n g (rComb93 hmPay hmWB rCore rWB hCW idx) := by
  intro hCEI hDA_EI rActEI idx g y hnz
  rw [permUnitary_apply] at hnz
  have hy : y = e (rActEI.extractIndex g) := by
    by_contra hne; rw [ite_eq_right hne] at hnz; exact hnz rfl
  subst hy
  by_cases hlt8 : idx.val < 8
  · let j : Fin 8 := ⟨idx.val, hlt8⟩
    have hij : idx = ⟨j.val, by omega⟩ := Fin.ext rfl
    have hr : rComb93 hmPay hmWB rCore rWB hCW idx =
        rActEI (Fin.castAdd 18 (Fin.castAdd 9 (selU8InCore hmPay j))) := by
      rw [hij, rComb93_u8]
      dsimp only [rActEI, rU8Core8]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      rfl
    rw [hr, QRegister.basisBits_replaceIndex_apply,
        heCore _ (selU8InCore hmPay j) (selU8InCore_ge_3924 hmPay j),
        QRegister.basisBits_extractIndex]
  · by_cases h8 : idx.val = 8
    · have hij : idx = ⟨8 + (0 : Fin 10).val, by omega⟩ := Fin.ext h8
      rw [hij, rComb93_peb10]
      refine QRegister.basisBits_replaceIndex_of_not_mem rActEI g _ _ ?_
      rintro ⟨u, hu⟩
      revert hu
      refine Fin.addCases (fun d hu ↦ ?_) (fun m hu ↦ ?_) u
      · dsimp only [rActEI] at hu
        rw [QRegister.concat_apply_left] at hu
        revert hu
        refine Fin.addCases (fun c hu ↦ ?_) (fun i hu ↦ ?_) d
        · rw [QRegister.concat_apply_left] at hu
          exact (hCW.compose_right _).ne c 0 hu
        · rw [QRegister.concat_apply_right] at hu
          have hinj := (rPeb10 hmWB rWB).wires.injective hu
          have hv := congrArg Fin.val hinj
          dsimp [QRegister.slice_apply] at hv; omega
      · dsimp only [rActEI] at hu
        rw [QRegister.concat_apply_right] at hu
        exact (hAW.compose_right _).ne m 0 hu
    · by_cases hlt18 : idx.val < 18
      · let i : Fin 9 := ⟨idx.val - 9, by omega⟩
        have hij : idx = ⟨9 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
        have hr : rComb93 hmPay hmWB rCore rWB hCW idx =
            rActEI (Fin.castAdd 18 (Fin.natAdd (fullSysCoreWires mPayload) i)) := by
          rw [hij, rComb93_enIdx9]
          dsimp only [rActEI]
          rw [QRegister.concat_apply_left, QRegister.concat_apply_right]
        rw [hr, QRegister.basisBits_replaceIndex_apply, heEI _ i,
            QRegister.basisBits_extractIndex]
      · exact QRegister.basisBits_replaceIndex_of_not_mem rActEI g _ _
          (rComb93_above18_not_mem_actEI hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW idx (by omega))
theorem highCore_not_mem_fastEISlotReg {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (d : Fin (2 ^ (fullSysCoreWires mPayload + 9))) (i : Fin (fullSysCoreWires mPayload))
    (hi : 3924 ≤ i.val) : Fin.castAdd 9 i ∉ Set.range (fastEISlotReg hmPay d).wires := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  dsimp only [fastEISlotReg, selCoreInEI] at hv
  simp only [QRegister.compose_apply, Function.Embedding.coeFn_mk, Fin.val_castAdd,
    rFullSysElecSlot_val] at hv
  have hs := (sFnEI (fullSysCoreWires mPayload) (basisBits _ d)).isLt
  have := j.isLt
  omega
theorem natAdd_not_mem_fastEISlotReg {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (d : Fin (2 ^ (fullSysCoreWires mPayload + 9))) (i : Fin 9) :
    Fin.natAdd (fullSysCoreWires mPayload) i ∉ Set.range (fastEISlotReg hmPay d).wires := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp [fastEISlotReg, selCoreInEI] at hv
  omega
theorem hCombPres_fastEILens_load {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    ∀ (idx : Wire 93) (g : Fin (2 ^ n))
      (y : Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18))),
      (uLensLoad (fastEILens hmPay)).1 y (rActEI.extractIndex g) ≠ 0 →
      basisBits n (rActEI.replaceIndex g y) (rComb93 hmPay hmWB rCore rWB hCW idx) =
        basisBits n g (rComb93 hmPay hmWB rCore rWB hCW idx) := by
  let C := fullSysCoreWires mPayload
  refine hCombPres_fastEILens_perm hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW
    (lensLoadEquiv (fastEILens hmPay)) (fun w i _ ↦ ?_) (fun w i ↦ ?_)
  · change basisBits ((C + 9) + 18) (liftPairIdx (lensLoadPerm (fastEILens hmPay)) w) _ = _
    dsimp only [liftPairIdx, extractPair, lensLoadPerm]
    rw [QRegister.replaceIndex_extractIndex]
    refine QRegister.basisBits_replaceIndex_of_not_mem (selMeasInAct (C + 9)) w _ _ ?_
    rintro ⟨m, hm⟩; rw [selMeasInAct_apply] at hm; have hv :=
      congrArg Fin.val hm; dsimp at hv; have := i.isLt; omega
  · change basisBits ((C + 9) + 18) (liftPairIdx (lensLoadPerm (fastEILens hmPay)) w) _ = _
    dsimp only [liftPairIdx, extractPair, lensLoadPerm]
    rw [QRegister.replaceIndex_extractIndex]
    refine QRegister.basisBits_replaceIndex_of_not_mem (selMeasInAct (C + 9)) w _ _ ?_
    rintro ⟨m, hm⟩; rw [selMeasInAct_apply] at hm; have hv :=
      congrArg Fin.val hm; dsimp at hv; have := i.isLt; omega
theorem hCombPres_fastEILens_write {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    ∀ (idx : Wire 93) (g : Fin (2 ^ n))
      (y : Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18))),
      (uLensWrite (fastEILens hmPay)).1 y (rActEI.extractIndex g) ≠ 0 →
      basisBits n (rActEI.replaceIndex g y) (rComb93 hmPay hmWB rCore rWB hCW idx) =
        basisBits n g (rComb93 hmPay hmWB rCore rWB hCW idx) := by
  let C := fullSysCoreWires mPayload
  refine hCombPres_fastEILens_perm hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW
    (lensWriteEquiv (fastEILens hmPay)) (fun w i hi ↦ ?_) (fun w i ↦ ?_)
  · change basisBits ((C + 9) + 18) (liftPairIdx (lensWritePerm (fastEILens hmPay)) w) _ = _
    dsimp only [liftPairIdx, extractPair, lensWritePerm]
    have hnotM : Fin.castAdd 18 (Fin.castAdd 9 i) ∉ Set.range (selMeasInAct (C + 9)).wires := by
      rintro ⟨m, hm⟩; rw [selMeasInAct_apply] at hm; have hv :=
        congrArg Fin.val hm; dsimp at hv; have := i.isLt; omega
    have hd : Fin.castAdd 18 (Fin.castAdd 9 i) = selDataInAct (C + 9) (Fin.castAdd 9 i) :=
      (selDataInAct_apply _).symm
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM, hd,
        QRegister.basisBits_replaceIndex_apply]
    change basisBits (C + 9) ((fastEISlotReg hmPay _).replaceIndex _ _) (Fin.castAdd 9 i) = _
    rw
      [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _
      (highCore_not_mem_fastEISlotReg hmPay _ i hi),
        QRegister.basisBits_extractIndex]
  · change basisBits ((C + 9) + 18) (liftPairIdx (lensWritePerm (fastEILens hmPay)) w) _ = _
    dsimp only [liftPairIdx, extractPair, lensWritePerm]
    have hnotM : Fin.castAdd 18 (Fin.natAdd C i) ∉ Set.range (selMeasInAct (C + 9)).wires := by
      rintro ⟨m, hm⟩; rw [selMeasInAct_apply] at hm; have hv :=
        congrArg Fin.val hm; dsimp at hv; have := i.isLt; omega
    have hd : Fin.castAdd 18 (Fin.natAdd C i) = selDataInAct (C + 9) (Fin.natAdd C i) :=
      (selDataInAct_apply _).symm
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM, hd,
        QRegister.basisBits_replaceIndex_apply]
    change basisBits (C + 9) ((fastEISlotReg hmPay _).replaceIndex _ _) (Fin.natAdd C i) = _
    rw
      [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (natAdd_not_mem_fastEISlotReg hmPay _ i),
        QRegister.basisBits_extractIndex]
theorem hCombPres_fastEILens_swap {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    ∀ (idx : Wire 93) (g : Fin (2 ^ n))
      (y : Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18))),
      (uLensSwap (fastEILens hmPay)).1 y (rActEI.extractIndex g) ≠ 0 →
      basisBits n (rActEI.replaceIndex g y) (rComb93 hmPay hmWB rCore rWB hCW idx) =
        basisBits n g (rComb93 hmPay hmWB rCore rWB hCW idx) := by
  let C := fullSysCoreWires mPayload
  refine hCombPres_fastEILens_perm hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW
    (lensSwapEquiv (fastEILens hmPay)) (fun w i hi ↦ ?_) (fun w i ↦ ?_)
  · change basisBits ((C + 9) + 18) (liftPairIdx (lensSwapPerm (fastEILens hmPay)) w) _ = _
    dsimp only [liftPairIdx, extractPair, lensSwapPerm]
    have hnotM : Fin.castAdd 18 (Fin.castAdd 9 i) ∉ Set.range (selMeasInAct (C + 9)).wires := by
      rintro ⟨m, hm⟩; rw [selMeasInAct_apply] at hm; have hv :=
        congrArg Fin.val hm; dsimp at hv; have := i.isLt; omega
    have hd : Fin.castAdd 18 (Fin.castAdd 9 i) = selDataInAct (C + 9) (Fin.castAdd 9 i) :=
      (selDataInAct_apply _).symm
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM, hd,
        QRegister.basisBits_replaceIndex_apply]
    change basisBits (C + 9) ((fastEISlotReg hmPay _).replaceIndex _ _) (Fin.castAdd 9 i) = _
    rw
      [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _
      (highCore_not_mem_fastEISlotReg hmPay _ i hi),
        QRegister.basisBits_extractIndex]
  · change basisBits ((C + 9) + 18) (liftPairIdx (lensSwapPerm (fastEILens hmPay)) w) _ = _
    dsimp only [liftPairIdx, extractPair, lensSwapPerm]
    have hnotM : Fin.castAdd 18 (Fin.natAdd C i) ∉ Set.range (selMeasInAct (C + 9)).wires := by
      rintro ⟨m, hm⟩; rw [selMeasInAct_apply] at hm; have hv :=
        congrArg Fin.val hm; dsimp at hv; have := i.isLt; omega
    have hd : Fin.castAdd 18 (Fin.natAdd C i) = selDataInAct (C + 9) (Fin.natAdd C i) :=
      (selDataInAct_apply _).symm
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM, hd,
        QRegister.basisBits_replaceIndex_apply]
    change basisBits (C + 9) ((fastEISlotReg hmPay _).replaceIndex _ _) (Fin.natAdd C i) = _
    rw
      [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (natAdd_not_mem_fastEISlotReg hmPay _ i),
        QRegister.basisBits_extractIndex]
theorem hCombPres_mul {M n kAct : ℕ} (rAct : QRegister kAct n) (rComb : QRegister M n)
    {V₁ V₂ : Unitary (2 ^ kAct)} (h₁ : ∀ (idx : Wire M) (g : Fin (2 ^ n)) (y : Fin (2 ^
    kAct)), V₁.1 y (rAct.extractIndex g) ≠ 0 → basisBits n (rAct.replaceIndex g y) (rComb idx)
    = basisBits n g (rComb idx)) (h₂ : ∀ (idx : Wire M) (g : Fin (2 ^ n)) (y : Fin (2 ^
    kAct)), V₂.1 y (rAct.extractIndex g) ≠ 0 → basisBits n (rAct.replaceIndex g y) (rComb idx)
    = basisBits n g (rComb idx)) : ∀ (idx : Wire M) (g : Fin (2 ^ n)) (y : Fin (2 ^ kAct)),
    (V₁ * V₂).1 y (rAct.extractIndex g) ≠ 0 → basisBits n (rAct.replaceIndex g y) (rComb idx)
    = basisBits n g (rComb idx) := by
  intro idx g y hnz
  change (V₁.1 * V₂.1) y (rAct.extractIndex g) ≠ 0 at hnz
  rw [Matrix.mul_apply] at hnz
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  let g₁ := rAct.replaceIndex g z
  have hrep : rAct.replaceIndex g₁ y = rAct.replaceIndex g y := by
    apply eq_of_basisBits_eq; intro w
    by_cases hw : w ∈ Set.range rAct.wires
    · obtain ⟨u, rfl⟩ := hw
      rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
  have hex : rAct.extractIndex g₁ = z := QRegister.extractIndex_replaceIndex rAct g z
  rw [← hrep]
  exact (h₁ idx g₁ y (hex ▸ left_ne_zero_of_mul hz)).trans (h₂ idx g z (right_ne_zero_of_mul hz))
open Classical in
theorem p2d_ketPredProj_congr_fast {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    (h : ∀ β, S₁ β ↔ S₂ β) : p2d_ketPredProj S₁ = p2d_ketPredProj S₂ := by
  apply matrix_ext_ket; intro β
  rw [p2d_ketPredProj_mul_ket, p2d_ketPredProj_mul_ket]
  by_cases h1 : S₁ β
  · rw [ite_eq_left h1, ite_eq_left ((h β).mp h1)]
  · rw [ite_eq_right h1, ite_eq_right (mt (h β).mpr h1)]
theorem dPreTreesFast_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    let hDA_EI : rDataEI.DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := rDataEI.concat rAnchor18 hDA_EI
    let hDS_EI : rDataEI.DisjointWires (rScr75 hmWB rWB) := qreg_disjoint_concat_left
        (disj_rScr75_right hmWB hCW) ((rPeb10_disj_rScr75 hmWB rWB).compose_left _)
    let hCS_EI := hDS_EI.compose_left (selCoreEI hmPay)
    let hAS_75 := disj_rScr75_right hmWB hAW
    let L_ei := fastEILens hmPay
    let dHole := dPreHole218 (le_refl 75) v rDataEI (selCoreEI hmPay)
      rAnchor18 (rScr75 hmWB rWB) hDA_EI hCS_EI hAS_75
    let P_trees := p2d_ketPredProj (fun β ↦
      invTreesIn93 (fun idx ↦ β (rComb93 hmPay hmWB rCore rWB hCW idx)))
    p2d_RealizesConstCleanUnitary P_trees
      (toDynWG v (rComb93 hmPay hmWB rCore rWB hCW) dHole ctxFastTrees93)
      (rActEI.embedUnitary (uLensWrite L_ei * uLensLoad L_ei)) := by
  intro hCEI rDataEI hDA_EI rActEI hDS_EI hCS_EI hAS_75 L_ei dHole P_trees
  have hHole0 := dPreHole218_slot_realizes (le_refl 75) v rDataEI (selCoreEI hmPay)
      (sFnEI (fullSysCoreWires mPayload)) L_ei rAnchor18 (rScr75 hmWB rWB) hDA_EI hDS_EI
      hAS_75 (hsFnEI_had hmPay) (hTblBit_fastEILens hmPay rCore (rEnIdx9 hmWB rWB) hCEI)
      (hWriteEq_fastEILens hmPay) (fun _ ↦ True) (fun _ _ _ ↦ Iff.rfl)
  have hProjEq : p2d_ketPredProj (fun β ↦ True ∧ invHole93 (fun idx ↦ β (rComb93 hmPay hmWB
      rCore rWB hCW idx))) = p2d_ketPredProj (fun β ↦ True ∧ invHoleSlot218 (le_refl 75)
      rDataEI (sFnEI (fullSysCoreWires mPayload)) (rScr75 hmWB rWB) β) :=
      p2d_ketPredProj_congr_fast fun β ↦ and_congr Iff.rfl
      (invHole93_iff_invHoleSlot218 hmPay hmWB rCore rWB hCW β)
  have hHole : p2d_RealizesConstCleanUnitary (p2d_ketPredProj fun β ↦ True ∧ invHole93 (fun
      idx ↦ β (rComb93 hmPay hmWB rCore rWB hCW idx))) dHole
      (rActEI.embedUnitary (uLensWrite L_ei * uLensLoad L_ei)) := by
    rw [hProjEq]; exact hHole0
  have hComm : DiagCtxWGCommutesWith (rComb93 hmPay hmWB rCore rWB hCW)
      (rActEI.embedUnitary (uLensWrite L_ei * uLensLoad L_ei)) ctxFastTrees93 :=
      diagCtxWGWritesAbove_to_commutesWith rActEI (uLensWrite L_ei * uLensLoad L_ei)
      (rComb93 hmPay hmWB rCore rWB hCW) 18 (rComb93_above18_not_mem_actEI hmPay hmWB rCore
      rAnchor18 rWB hCA hCW hAW) (hCombPres_mul rActEI (rComb93 hmPay hmWB rCore rWB hCW)
      (hCombPres_fastEILens_write hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW)
      (hCombPres_fastEILens_load hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW))
      ctxFastTrees93_writesAbove18
  have hTrees := realizes_toDynWG_commutes_above 18 v (rComb93 hmPay hmWB rCore rWB hCW)
    (fun _ ↦ True) (fun _ _ _ ↦ Iff.rfl) invHole93 dHole
    (rActEI.embedUnitary (uLensWrite L_ei * uLensLoad L_ei)) hHole
    ctxFastTrees93 invTreesIn93 ctxFastTrees93_writesAbove18 hComm validAtWith_ctxFastTrees93
  have hTrue : P_trees = p2d_ketPredProj (fun β ↦ True ∧
      invTreesIn93 (fun idx ↦ β (rComb93 hmPay hmWB rCore rWB hCW idx))) :=
    p2d_ketPredProj_congr_fast fun _ ↦ ⟨fun h ↦ ⟨trivial, h⟩, And.right⟩
  rwa [← hTrue] at hTrees
open ElecHadConjLoadAndTrueSwapComp (xor18)
theorem peb_realizesOnProj_of_p2d {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (_hP : Pᴴ = P)
    (h : p2d_RealizesConstCleanUnitary P d U) :
    Pass1BarrelIdxPebbled273.RealizesOnProj P U.1 d := fun M ↦ by
  obtain ⟨M', hwp⟩ := h.1 M
  refine ⟨M', hwp, ?_⟩
  have hEq := h.2 M default
  rwa [congrFun hwp default] at hEq
theorem hoist_realizesOnProj_of_peb {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hP : Pᴴ = P)
    (h : Pass1BarrelIdxPebbled273.RealizesOnProj P U.1 d) :
    RealizesOnProj P U d := fun M ↦ by
  obtain ⟨M', hwp, hproj⟩ := h M
  refine ⟨M', hwp, ?_⟩
  simpa only [hP] using hproj
theorem cliffProg_inv_eval_eq_inv {M n : ℕ} [NeZero (2 ^ n)]
    (r : QRegister M n) (c : CliffProg M) :
    ((c.inv.onRegister r).toCircuit).eval = (((c.onRegister r).toCircuit).eval)⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  apply Subtype.ext; apply matrix_ext_ket; intro β
  have hcPre : ∀ α : BitAssignment n, ((c.onRegister r).toCircuit).eval.1.mulVec (ket α) = ket
      (writeRegProg α r (c.eval (fun idx ↦ α (r idx)))) :=
    fun α ↦ (eval_onRegister_prog_ket r (.cliff c) α).trans
      (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
  have hcPost : ∀ α : BitAssignment n, ((c.inv.onRegister r).toCircuit).eval.1.mulVec (ket α)
      = ket (writeRegProg α r (c.inv.eval (fun idx ↦ α (r idx)))) :=
    fun α ↦ (eval_onRegister_prog_ket r (.cliff c.inv) α).trans
      (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
  have hRead : ∀ (α : BitAssignment n) (f : BitAssignment M),
      (fun idx ↦ writeRegProg α r f (r idx)) = f := fun α f ↦
    funext fun idx ↦ writeRegProg_apply_reg α r f idx
  rw [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      hcPre, hcPost, hRead, CliffProg.inv_eval]
  apply congrArg ket; funext w
  by_cases hm : w ∈ Set.range r.wires
  · obtain ⟨idx, rfl⟩ := hm
    exact writeRegProg_apply_reg _ _ _ _
  · rw[writeRegProg_apply_of_not_mem _ _ _ _ hm, writeRegProg_apply_of_not_mem _ _ _ _ hm]
/-- Generic `420 T` (`68 × 4 + 148`) `0`-Toffoli wrapper combining `progLoadInternal68` (`272 T`)
with `ctxFast64x4WG` (`148 T`) on `(rCore, rWB)` (`80 ≤ mPayload`, `143 ≤ mWB`). -/
noncomputable def dWrapFast68 {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) (dHole : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  let hWB114 : 114 ≤ mWB := by omega
  let rComb := rCombPeb rCore rWB hWB114 hCW
  let cPebCliff := cliffOfProgGen hmPay 8 106 progLoadInternal68 61
    progLoadInternal68_end_le progLoadInternal68_stats.1
  let cRestore : Circuit n := (cPebCliff.inv.onRegister rComb).toCircuit
  let cReapply : Circuit n := (cPebCliff.onRegister rComb).toCircuit
  let dWG := toDynWG v (rComb93 hmPay hmWB rCore rWB hCW) dHole ctxFast64x4WG
  progToDynWrap v hmPay rComb progLoadInternal68 61 le_rfl
    progLoadInternal68_end_le progLoadInternal68_stats.1
    (.seq (.circuit cRestore) (.seq dWG (.circuit cReapply)))
theorem count_dWrapFast68_toff {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) (dHole : DynamicCircuit Var n) :
    (dWrapFast68 hmPay hmWB v rCore rWB hCW dHole).count TOFF = dHole.count TOFF := by
  unfold dWrapFast68
  simp only [count_progToDynWrap_toff, DynamicCircuit.count,
    Internal.CliffProg.toCircuit_count_toff, toDynWG_count_toff, add_zero, zero_add]
theorem count_dWrapFast68_t {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) (dHole : DynamicCircuit Var n) :
    (dWrapFast68 hmPay hmWB v rCore rWB hCW dHole).count T = 420 + dHole.count T := by
  unfold dWrapFast68
  simp only [count_progToDynWrap_t, progLoadInternal68_stats.2.2, DynamicCircuit.count,
    Internal.CliffProg.toCircuit_count_t, toDynWG_count_t, countT_ctxFast64x4WG]
  omega
/-- Composite pebble-plus-linearization forward unitary `L_93 * (C_inv * U_68)` on `2 ^ n`. -/
noncomputable def vLinUnitary {n mPayload mWB : ℕ} [NeZero (2 ^ n)] (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) : Unitary (2 ^ n) :=
  let hWB114 : 114 ≤ mWB := by omega
  let rComb := rCombPeb rCore rWB hWB114 hCW
  let cPebCliff := cliffOfProgGen hmPay 8 106 progLoadInternal68 61
    progLoadInternal68_end_le progLoadInternal68_stats.1
  let U_68 := (progFwdCircuit hmPay rComb progLoadInternal68 61 le_rfl
    progLoadInternal68_end_le progLoadInternal68_stats.1).eval
  let C_inv := ((cPebCliff.inv.onRegister rComb).toCircuit).eval
  let L_93 := ((cPreLin93.onRegister (rComb93 hmPay hmWB rCore rWB hCW)).toCircuit).eval
  L_93 * (C_inv * U_68)
theorem dWrapFast68_realizes_gen {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWB : ℕ} [NeZero (2 ^ n)] (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) {P_out P_trees : Operator (2 ^ n)}
    {U_out U_ei : Unitary (2 ^ n)} {dHole : DynamicCircuit Var n} (hP_out : P_outᴴ = P_out)
    (hP_trees : P_treesᴴ = P_trees) (hTailP : HasCleanTailFrom (rCombPeb rCore rWB (by omega)
    hCW) (fullSysCoreWires mPayload + 8) P_out) (hTailU : HasCleanTailFrom (rCombPeb rCore
    rWB (by omega) hCW) (fullSysCoreWires mPayload + 8) (U_out.1 * P_out)) (hTrees :
    Pass1BarrelIdxPebbled273.RealizesOnProj P_trees U_ei.1 (toDynWG v (rComb93 hmPay hmWB
    rCore rWB hCW) dHole ctxFastTrees93)) (hSub : P_trees * ((vLinUnitary hmPay hmWB rCore rWB
    hCW).1 * P_out) = (vLinUnitary hmPay hmWB rCore rWB hCW).1 * P_out) (hInt : U_ei.1 *
    ((vLinUnitary hmPay hmWB rCore rWB hCW).1 * P_out) = (vLinUnitary hmPay hmWB rCore rWB
    hCW).1 * (U_out.1 * P_out)) : Pass1BarrelIdxPebbled273.RealizesOnProj P_out U_out.1
    (dWrapFast68 hmPay hmWB v rCore rWB hCW dHole) := by
  let hWB114 : 114 ≤ mWB := by omega
  let rComb := rCombPeb rCore rWB hWB114 hCW
  let cPebCliff := cliffOfProgGen hmPay 8 106 progLoadInternal68 61
    progLoadInternal68_end_le progLoadInternal68_stats.1
  let rC93 := rComb93 hmPay hmWB rCore rWB hCW
  let V_lin := vLinUnitary hmPay hmWB rCore rWB hCW
  unfold dWrapFast68
  refine progToDynWrap_realizes v hmPay rComb progLoadInternal68 61 le_rfl
    progLoadInternal68_end_le progLoadInternal68_stats.1 hP_out hTailP hTailU ?_
  refine Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit _ _
    (cliffProg_onRegister_eval_inv rComb cPebCliff) ?_
  dsimp only [ctxFast64x4WG, toDynWG]
  refine Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit _ _
    (cliffProg_inv_eval_eq_inv rC93 cPreLin93) ?_
  let U_68 := (progFwdCircuit hmPay rComb progLoadInternal68 61 le_rfl
    progLoadInternal68_end_le progLoadInternal68_stats.1).eval
  let C_inv := ((cPebCliff.inv.onRegister rComb).toCircuit).eval
  let L_93 := ((cPreLin93.onRegister rC93).toCircuit).eval
  have hV_val : V_lin.1 = L_93.1 * (C_inv.1 * U_68.1) := by
    dsimp only [V_lin, vLinUnitary, L_93, C_inv, U_68, rC93, rComb, cPebCliff, hWB114]
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
  have hQ_eq : L_93.1 * (C_inv.1 * (U_68.1 * P_out * U_68.1ᴴ) * C_inv.1ᴴ) * L_93.1ᴴ =
      V_lin.1 * P_out * V_lin.1ᴴ := by
    rw [hV_val]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hW_eq : L_93.1 * (C_inv.1 * (U_68.1 * U_out.1 * U_68.1ᴴ) * C_inv.1ᴴ) * L_93.1ᴴ =
      V_lin.1 * U_out.1 * V_lin.1ᴴ := by
    rw [hV_val]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hQ_eq, hW_eq]
  let Q := V_lin.1 * P_out * V_lin.1ᴴ
  let W := V_lin.1 * U_out.1 * V_lin.1ᴴ
  have hQ_herm : Qᴴ = Q := by
    simp [Q, Matrix.conjTranspose_mul, hP_out, Matrix.mul_assoc]
  have hSubQ : P_trees * Q = Q := by
    calc P_trees * (V_lin.1 * P_out * V_lin.1ᴴ)
        = (P_trees * (V_lin.1 * P_out)) * V_lin.1ᴴ := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [hSub]
  have hV_unit : V_lin.1ᴴ * V_lin.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V_lin
  have hIntQ : U_ei.1 * Q = W * Q := by
    calc U_ei.1 * (V_lin.1 * P_out * V_lin.1ᴴ)
        = (U_ei.1 * (V_lin.1 * P_out)) * V_lin.1ᴴ := by simp only [Matrix.mul_assoc]
      _ = (V_lin.1 * (U_out.1 * P_out)) * V_lin.1ᴴ := by rw [hInt]
      _ = V_lin.1 * U_out.1 * (V_lin.1ᴴ * V_lin.1) * P_out * V_lin.1ᴴ := by
            simp only [hV_unit, Matrix.mul_one, Matrix.mul_assoc]
      _ = W * Q := by simp only [W, Q, Matrix.mul_assoc]
  exact Pass1BarrelIdxPebbled273.RealizesOnProj.congr_op hQ_herm
    (Pass1BarrelIdxPebbled273.RealizesOnProj.mono_proj hP_trees hQ_herm hSubQ hTrees) hIntQ
theorem hasCleanTailFrom_embedMatrix_mul_proj0 {n mPayload mWB kA : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hWB : 114 ≤ mWB) (hCW : rCore.DisjointWires rWB)
    (rA : QRegister kA n) (hAW : rA.DisjointWires rWB) (E : Operator (2 ^ kA)) :
    HasCleanTailFrom (rCombPeb rCore rWB hWB hCW) (fullSysCoreWires mPayload + 8)
      (rA.embedMatrix E * rWB.basisOutcomeProjector 0) := by
  intro q hq
  let k : Fin 106 := ⟨q.val - (fullSysCoreWires mPayload + 8), by have := q.isLt; omega⟩
  have hqk : q = ⟨fullSysCoreWires mPayload + 8 + k.val, by have := q.isLt; omega⟩ :=
    Fin.ext (by dsimp [k]; omega)
  rw [hqk, rCombPeb_cln106]
  have hEqReg : QRegister.singleton (rWB ⟨8 + k.val, by have := k.isLt; omega⟩) =
      rWB.compose (QRegister.singleton ⟨8 + k.val, by have := k.isLt; omega⟩) :=
    QRegister.ext (Function.Embedding.ext fun _ ↦ rfl)
  have hDisj : rA.DisjointWires (QRegister.singleton (rWB ⟨8 + k.val, by have := k.isLt; omega⟩)) :=
    hEqReg ▸ hAW.compose_right _
  rw[← Matrix.mul_assoc,
    ← (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rA) _ hDisj E 0,
      Matrix.mul_assoc, singleton_rWB_mul_proj0]
/-- Classical bit-assignment produced by `vLinUnitary` on a basis ket with clean `rWB`. -/
noncomputable def fastLinState {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (β : BitAssignment n) : BitAssignment n :=
  let βlemHexeb := pebBitFnGen hmPay progLoadInternal68 (by omega) rCore rWB β
  let rC93 := rComb93 hmPay hmWB rCore rWB hCW
  writeRegProg βlemHexeb rC93 (cPreLin93.eval (fun idx ↦ βlemHexeb (rC93 idx)))
theorem vLinUnitary_mulVec_ket {n mPayload mWB : ℕ} [NeZero (2 ^ n)] (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) (β : BitAssignment n)
    (hWB0 : ∀ j : Fin mWB, β (rWB j) = 0) : (vLinUnitary hmPay hmWB rCore rWB hCW).1.mulVec
    (ket β) = ket (fastLinState hmPay hmWB rCore rWB hCW β) := by
  have hscr0 : ∀ s : Fin (mWB - 8), β ((rWB.slice 8 (mWB - 8) (by omega)) s) = 0 :=
    fun s ↦ hWB0 _
  dsimp only [vLinUnitary, fastLinState]
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, Submonoid.coe_mul,
      vPeb_ket_of_scr0_gen hmPay progLoadInternal68
        progLoadInternal68_end_le progLoadInternal68_stats.1 (by omega) rCore rWB hCW β hscr0]
  exact (eval_onRegister_prog_ket
    (rComb93 hmPay hmWB rCore rWB hCW) (.cliff cPreLin93) _).trans
    (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
theorem upd93_ne {f : BitAssignment 93} {a b : Wire 93} (v : ZMod 2) (h : a.val ≠ b.val) :
    Function.update f b v a = f a := Function.update_of_ne (Fin.ne_of_val_ne h) v f
theorem upd93_eq {f : BitAssignment 93} {a b : Wire 93} (v : ZMod 2) (h : a.val = b.val) :
    Function.update f b v a = v := by
  rw [Fin.ext h, Function.update_self]
theorem cPreLin93_eval_outside (δ : BitAssignment 93) (w : Wire 93)
    (hw : w.val < 9 ∨ 18 ≤ w.val) : cPreLin93.eval δ w = δ w := by
  dsimp only [cPreLin93, CliffProg.eval]
  repeat rw [upd93_ne _ (by dsimp; omega)]
theorem cPreLin93_eval_nine (δ : BitAssignment 93) :
    cPreLin93.eval δ ⟨9, by decide⟩ = δ ⟨9, by decide⟩ + δ ⟨8, by decide⟩ := by
  dsimp only [cPreLin93, CliffProg.eval]
  repeat rw [upd93_ne _ (by decide)]
  rw [Function.update_self]
theorem cPreLin93_eval_ten_add (δ : BitAssignment 93) (j : Fin 8) :
    cPreLin93.eval δ ⟨10 + j.val, by omega⟩ =
      δ ⟨10 + j.val, by omega⟩ + δ ⟨j.val, by omega⟩ := by
  fin_cases j <;>
    (dsimp only [cPreLin93, CliffProg.eval]
     repeat (first | rw [upd93_ne _ (by decide)] | rw [upd93_eq _ (by decide)]))
theorem pebBitFnGen_outside_rWB {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (p : List DecStep) (hWB : 114 ≤ mWB) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (β : BitAssignment n) {w : Wire n} (hw : w ∉ Set.range rWB.wires)
    : pebBitFnGen hmPay p hWB rCore rWB β w = β w := by
  have hnc : w ∉ Set.range (rWB.slice 8 106 (by omega)).wires := by
    rintro ⟨m, rfl⟩; exact hw ⟨_, rfl⟩
  exact Internal.writeRegProg_apply_of_not_mem _ _ _ _ hnc
theorem fastLinState_outside_rWB {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) (β : BitAssignment n) {w : Wire n}
    (hw : w ∉ Set.range rWB.wires) : fastLinState hmPay hmWB rCore rWB hCW β w = β w := by
  let rC93 := rComb93 hmPay hmWB rCore rWB hCW
  dsimp only [fastLinState]
  by_cases hm : w ∈ Set.range rC93.wires
  · obtain ⟨idx, rfl⟩ := hm
    rw [writeRegProg_apply_reg]
    have hlt9 : idx.val < 9 := by
      by_contra hge9
      by_cases hlt18 : idx.val < 18
      · let i : Fin 9 := ⟨idx.val - 9, by omega⟩
        have hij : idx = ⟨9 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
        rw [hij, rComb93_enIdx9] at hw
        exact hw ⟨_, rfl⟩
      · let k : Fin 75 := ⟨idx.val - 18, by omega⟩
        have hik : idx = ⟨18 + k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
        obtain ⟨u, _, hsk⟩ := rScr75_apply_perm hmWB rWB k
        rw [hik, rComb93_scr75, hsk] at hw
        exact hw ⟨_, rfl⟩
    rw [cPreLin93_eval_outside _ _ (Or.inl hlt9)]
    exact pebBitFnGen_outside_rWB hmPay progLoadInternal68 (by omega) rCore rWB β hw
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hm]
    exact pebBitFnGen_outside_rWB hmPay progLoadInternal68 (by omega) rCore rWB β hw
theorem fastLinState_congr_highCore {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hmWB : 143 ≤ mWB) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) (β₁ β₂ : BitAssignment n)
    (hWB₁ : ∀ j : Fin mWB, β₁ (rWB j) = 0) (hWB₂ : ∀ j : Fin mWB, β₂ (rWB j) = 0) (hHigh : ∀ i
    : Fin (fullSysCoreWires mPayload), 3924 ≤ i.val → β₁ (rCore i) = β₂ (rCore i))
    {w : Wire n} (hw : w ∈ Set.range rWB.wires) : fastLinState hmPay hmWB rCore rWB hCW β₁ w =
    fastLinState hmPay hmWB rCore rWB hCW β₂ w := by
  let C := fullSysCoreWires mPayload
  have hC := core_lo_4034 hmPay
  have hst : stHighCore hmPay rCore β₁ = stHighCore hmPay rCore β₂ := by
    funext q
    by_cases hq : q < 61
    · let iq : Fin C := ⟨decWireNum C q, decWireNum_lt_core hC hq⟩
      have hiq : 3924 ≤ iq.val := by dsimp [iq, decWireNum]; split_ifs <;> omega
      have hbeq := hHigh iq hiq
      dsimp only [iq, C] at hbeq
      simp [stHighCore, hq, hbeq]
    · simp [stHighCore, hq]
  let p68 := progLoadInternal68
  let βp₁ := pebBitFnGen hmPay p68 (by omega) rCore rWB β₁
  let βp₂ := pebBitFnGen hmPay p68 (by omega) rCore rWB β₂
  have hpeb_wb : ∀ y ∈ Set.range rWB.wires, βp₁ y = βp₂ y := by
    rintro _ ⟨j, rfl⟩
    let rCln := rWB.slice 8 106 (by omega)
    dsimp only [βp₁, βp₂, pebBitFnGen]
    by_cases hj : 8 ≤ j.val ∧ j.val < 8 + 106
    · let m : Fin 106 := ⟨j.val - 8, by omega⟩
      have hrm : rWB j = rCln m :=
        congrArg rWB (Fin.ext (by dsimp [m, rCln, QRegister.slice]; omega))
      rw [hrm, Internal.writeRegProg_apply_reg, Internal.writeRegProg_apply_reg, hst]
    · have hnc : rWB j ∉ Set.range rCln.wires := by
        rintro ⟨m, hm⟩
        have hv := congrArg Fin.val (rWB.wires.injective hm)
        dsimp [rCln, QRegister.slice] at hv; omega
      rw [Internal.writeRegProg_apply_of_not_mem _ _ _ _ hnc,
          Internal.writeRegProg_apply_of_not_mem _ _ _ _ hnc, hWB₁ j, hWB₂ j]
  let rC93 := rComb93 hmPay hmWB rCore rWB hCW
  have h93 : (fun idx ↦ βp₁ (rC93 idx)) = (fun idx ↦ βp₂ (rC93 idx)) := by
    funext idx
    by_cases hlt8 : idx.val < 8
    · let j : Fin 8 := ⟨idx.val, hlt8⟩
      have hij : idx = ⟨j.val, by omega⟩ := Fin.ext rfl
      have hnotW : rU8Core8 hmPay rCore j ∉ Set.range rWB.wires :=
        fun ⟨k, hk⟩ ↦ hCW.ne (selU8InCore hmPay j) k hk.symm
      rw [hij, rComb93_u8]
      dsimp only [βp₁, βp₂]
      rw [pebBitFnGen_outside_rWB hmPay p68 (by omega) rCore rWB β₁ hnotW,
          pebBitFnGen_outside_rWB hmPay p68 (by omega) rCore rWB β₂ hnotW]
      exact hHigh (selU8InCore hmPay j) (selU8InCore_ge_3924 hmPay j)
    · by_cases hlt18 : idx.val < 18
      · let i : Fin 10 := ⟨idx.val - 8, by omega⟩
        have hij : idx = ⟨8 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
        rw [hij, rComb93_peb10]
        exact hpeb_wb _ ⟨_, rfl⟩
      · let k : Fin 75 := ⟨idx.val - 18, by omega⟩
        have hik : idx = ⟨18 + k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
        obtain ⟨u, _, hsk⟩ := rScr75_apply_perm hmWB rWB k
        rw [hik, rComb93_scr75, hsk]
        exact hpeb_wb _ ⟨_, rfl⟩
  dsimp only [fastLinState]
  change writeRegProg βp₁ rC93 (cPreLin93.eval (fun idx ↦ βp₁ (rC93 idx))) w =
    writeRegProg βp₂ rC93 (cPreLin93.eval (fun idx ↦ βp₂ (rC93 idx))) w
  rw [h93]
  by_cases hm : w ∈ Set.range rC93.wires
  · obtain ⟨idx, rfl⟩ := hm
    rw [writeRegProg_apply_reg, writeRegProg_apply_reg]
  · rw[writeRegProg_apply_of_not_mem _ _ _ _ hm, writeRegProg_apply_of_not_mem _ _ _ _ hm]
    exact hpeb_wb w hw
/-- Maps a `Bool` to `ZMod 2` (`true ↦ 1`, `false ↦ 0`). -/
def bToZ2 (b : Bool) : ZMod 2 := if b then 1 else 0
theorem bToZ2_add (b₁ b₂ : Bool) : bToZ2 b₁ + bToZ2 b₂ = bToZ2 (Bool.xor b₁ b₂) := by
  cases b₁ <;> cases b₂ <;> rfl
theorem bToZ2_decide_eq_one (z : ZMod 2) : bToZ2 (decide (z = 1)) = z := by
  rcases bit_cases z with rfl | rfl <;> rfl
theorem bitsVal_testBit_fin256 (v : Fin 256) :
    bitsVal (fun j : Fin 8 ↦ if v.val.testBit j.val then (1 : ZMod 2) else 0) = v.val := by
  revert v; decide
theorem pebBitFnGen_rPeb10 {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (p : List DecStep) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (β : BitAssignment n) (i : Fin 10) : pebBitFnGen hmPay p
    (by omega) rCore rWB β (rPeb10 hmWB rWB i) = bToZ2
    (rawPebble p 61 (stHighCore hmPay rCore β) (qPeb10 i)) := by
  have hb := qPeb10_bounds i
  let m : Fin 106 := ⟨qPeb10 i - 61, by omega⟩
  have hrm : rPeb10 hmWB rWB i = (rWB.slice 8 106 (by omega)) m :=
    congrArg rWB (Fin.ext (by dsimp [rPeb10, selPeb10InWB, m, QRegister.slice]))
  have hqm : 61 + m.val = qPeb10 i := by dsimp [m]; omega
  dsimp only [pebBitFnGen, bToZ2]
  rw [hrm, Internal.writeRegProg_apply_reg, hqm]
theorem fastLinState_invTrees_and_sFnEI {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB)
    (β : BitAssignment n) (hWB0 : ∀ j : Fin mWB, β (rWB j) = 0) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    let β' := fastLinState hmPay hmWB rCore rWB hCW β
    invTreesIn93 (fun idx ↦ β' (rComb93 hmPay hmWB rCore rWB hCW idx)) ∧
      sFnEI (fullSysCoreWires mPayload) (fun u ↦ β' (rDataEI u)) =
        coinBarrelIdxFast hmPay (fun i ↦ β (rCore i)) := by
  intro hCEI rDataEI β'
  let C := fullSysCoreWires mPayload
  let rC93 := rComb93 hmPay hmWB rCore rWB hCW
  let st₀ := stHighCore hmPay rCore β
  have hcl₀ : ∀ q, 61 ≤ q → st₀ q = false := fun q hq ↦ by
    simp [st₀, stHighCore, show ¬ q < 61 by omega]
  have hlow₀ : ∀ (q : ℕ) (hq : q < 61),
      st₀ q = decide (β (rCore ⟨decWireNum C q, decWireNum_lt_core (core_lo_4034 hmPay) hq⟩) = 1) :=
    fun q hq ↦ by dsimp only [st₀, stHighCore]; exact dite_eq_left hq
  have hpure : coinBarrelIdxFastPure st₀ = (coinBarrelIdxFast hmPay (fun i ↦ β (rCore i))).val :=
    coinBarrelIdxFastPure_eq_core hmPay (fun i ↦ β (rCore i)) st₀ hlow₀
  have hlt218 : (coinBarrelIdxFast hmPay (fun i ↦ β (rCore i))).val < 218 :=
    coinBarrelIdxFast_val_lt_218 hmPay _
  obtain ⟨hen0, hen1⟩ := rawPebble_progLoadInternal68_spec st₀ hcl₀
  let p68 := progLoadInternal68
  let βlemHexeb := pebBitFnGen hmPay p68 (by omega) rCore rWB β
  have hβ'_reg : ∀ idx : Wire 93, β' (rC93 idx) = cPreLin93.eval (fun k ↦ βlemHexeb (rC93 k)) idx :=
    fun idx ↦ writeRegProg_apply_reg _ _ _ idx
  have hpeb_8 : βlemHexeb (rC93 ⟨8, by decide⟩) = bToZ2 (rawPebble p68 61 st₀ 67) := by
    have h8 : (⟨8, by decide⟩ : Wire 93) = ⟨8 + (0 : Fin 10).val, by decide⟩ := rfl
    rw [h8, rComb93_peb10]
    exact pebBitFnGen_rPeb10 hmPay hmWB p68 rCore rWB β 0
  have hpeb_9 : βlemHexeb (rC93 ⟨9, by decide⟩) = bToZ2 (rawPebble p68 61 st₀ 68) := by
    have h9 : (⟨9, by decide⟩ : Wire 93) = ⟨8 + (1 : Fin 10).val, by decide⟩ := rfl
    rw [h9, rComb93_peb10]
    exact pebBitFnGen_rPeb10 hmPay hmWB p68 rCore rWB β 1
  have hβ'_9 : β' (rC93 ⟨9, by decide⟩) =
      bToZ2 (Bool.xor (rawPebble p68 61 st₀ 67) (rawPebble p68 61 st₀ 68)) := by
    rw [hβ'_reg, cPreLin93_eval_nine, hpeb_9, hpeb_8, bToZ2_add, Bool.xor_comm]
  have hβ'_10 : ∀ j : Fin 8, β' (rC93 ⟨10 + j.val, by omega⟩) =
      bToZ2 (Bool.xor (st₀ (17 + j.val)) (rawPebble p68 61 st₀ (qMux8Nat j.val))) := by
    intro j
    have hu8 : βlemHexeb (rC93 ⟨j.val, by omega⟩) = bToZ2 (st₀ (17 + j.val)) := by
      have hnotW : rU8Core8 hmPay rCore j ∉ Set.range rWB.wires :=
        fun ⟨k, hk⟩ ↦ hCW.ne (selU8InCore hmPay j) k hk.symm
      rw [rComb93_u8]
      dsimp only [βlemHexeb]
      rw [pebBitFnGen_outside_rWB hmPay p68 (by omega) rCore rWB β hnotW,
          hlow₀ (17 + j.val) (by have := j.isLt; omega)]
      exact (bToZ2_decide_eq_one _).symm
    have hqMux : βlemHexeb (rC93 ⟨10 + j.val, by omega⟩) =
        bToZ2 (rawPebble p68 61 st₀ (qMux8Nat j.val)) := by
      have hj10 : (⟨10 + j.val, by omega⟩ : Wire 93) =
          ⟨8 + (⟨j.val + 2, by omega⟩ : Fin 10).val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hj10, rComb93_peb10]
      exact pebBitFnGen_rPeb10 hmPay hmWB p68 rCore rWB β ⟨j.val + 2, by omega⟩
    rw [hβ'_reg, cPreLin93_eval_ten_add _ j, hqMux, hu8, bToZ2_add, Bool.xor_comm]
  have hβ'_above18 : ∀ idx : Wire 93, 18 ≤ idx.val → β' (rC93 idx) = 0 := by
    intro idx h18
    let k : Fin 75 := ⟨idx.val - 18, by omega⟩
    have hik : idx = ⟨18 + k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
    rw [hβ'_reg, cPreLin93_eval_outside _ _ (Or.inr h18), hik, rComb93_scr75]
    exact pebBitFnGen_rScr75_zero hmPay hmWB rCore rWB β hWB0 k
  have hEI_eq : (fun i : Fin 9 ↦ β' (rDataEI (Fin.natAdd C i))) =
      (fun i : Fin 9 ↦ β' (rC93 ⟨9 + i.val, by omega⟩)) := by
    funext i
    dsimp only [rDataEI, rC93]
    rw [QRegister.concat_apply_right, rComb93_enIdx9]
  let en := Bool.xor (rawPebble p68 61 st₀ 67) (rawPebble p68 61 st₀ 68)
  rcases Bool.eq_false_or_eq_true en with hen | hen
  · have h9_1 : β' (rC93 ⟨9, by decide⟩) = 1 := by
      rw [hβ'_9]; change bToZ2 en = 1; rw [hen]; rfl
    have hbits_eq : (fun j : Fin 8 ↦ β' (rC93 ⟨10 + j.val, by omega⟩)) =
        (fun j : Fin 8 ↦
          if (coinBarrelIdxFast hmPay (fun i ↦ β (rCore i))).val.testBit j.val
          then (1 : ZMod 2) else 0) := by
      funext j
      rw [hβ'_10 j, hen1 hen j, hpure]
      rfl
    have hbval : bitsVal (fun j : Fin 8 ↦ β' (rC93 ⟨10 + j.val, by omega⟩)) =
        (coinBarrelIdxFast hmPay (fun i ↦ β (rCore i))).val := by
      rw [hbits_eq]
      exact bitsVal_testBit_fin256
        ⟨(coinBarrelIdxFast hmPay (fun i ↦ β (rCore i))).val, by omega⟩
    refine ⟨⟨fun _ ↦ hbval ▸ hlt218, hβ'_above18⟩, ?_⟩
    apply Fin.ext
    dsimp only [sFnEI]
    rw [hEI_eq]
    have hsub8 : (fun j : Fin 8 ↦
          (fun i : Fin 9 ↦ β' (rC93 ⟨9 + i.val, by omega⟩)) ⟨1 + j.val, by omega⟩) =
        (fun j : Fin 8 ↦ β' (rC93 ⟨10 + j.val, by omega⟩)) :=
      funext fun j ↦ congrArg (fun idx ↦ β' (rC93 idx)) (Fin.ext (by dsimp; omega))
    have h9_0 : (fun i : Fin 9 ↦ β' (rC93 ⟨9 + i.val, by omega⟩)) 0 = 1 := h9_1
    rw [gatedIdx9_val_one _ h9_0 (by rw [hsub8, hbval]; exact hlt218), hsub8, hbval]
  · have h9_0 : β' (rC93 ⟨9, by decide⟩) = 0 := by
      rw [hβ'_9]; change bToZ2 en = 0; rw [hen]; rfl
    have hc_val0 : (coinBarrelIdxFast hmPay (fun i ↦ β (rCore i))).val = 0 := hpure ▸ hen0 hen
    refine ⟨⟨fun h1 ↦ absurd (h9_0.symm.trans h1) zero_ne_one, hβ'_above18⟩, ?_⟩
    apply Fin.ext
    dsimp only [sFnEI]
    rw [hEI_eq, gatedIdx9_val_zero _ h9_0, hc_val0]
theorem embedUnitary_permUnitary_mulVec_single_fast {m N : ℕ}
    (r : QRegister m N) (e : Equiv.Perm (Fin (2 ^ m))) (g : Fin (2 ^ N)) :
    (r.embedUnitary (Operator.permutationUnitary e)).1.mulVec (Pi.single g 1) =
      Pi.single (r.replaceIndex g (e (r.extractIndex g))) 1 := by
  ext i
  have hCol : ((r.embedUnitary (Operator.permutationUnitary e)).1.mulVec (Pi.single g 1)) i =
      (r.embedMatrix (Operator.permutationUnitary e).1) i g := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, QRegister.embedUnitary_val]
  rw [hCol, QRegister.embedMatrix_apply]
  by_cases henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv g).2
  · rw [ite_eq_left henv, permUnitary_apply]
    by_cases hex : r.extractIndex i = e (r.extractIndex g)
    · have hi : i = r.replaceIndex g (e (r.extractIndex g)) := by
        apply r.basisSplitEquiv.injective
        rw [r.basisSplitEquiv_replaceIndex]
        exact Prod.ext (by simpa [QRegister.basisSplitEquiv_apply_fst] using hex) henv
      subst hi; simp
    · have hne : i ≠ r.replaceIndex g (e (r.extractIndex g)) := by
        intro h; subst h; exact hex (r.extractIndex_replaceIndex g _)
      simp [hex, hne]
  · have hne : i ≠ r.replaceIndex g (e (r.extractIndex g)) := by
      intro h; subst h
      rw [r.basisSplitEquiv_replaceIndex] at henv
      exact henv rfl
    simp [henv, hne]
theorem concat_replaceIndex_liftPairIdx_fast {n k : ℕ}
    (rD : QRegister k n) (rM : QRegister 18 n) (hDM : rD.DisjointWires rM)
    (F : Fin (2 ^ k) × Fin (2 ^ 18) → Fin (2 ^ k) × Fin (2 ^ 18))
    (g : Fin (2 ^ n)) :
    let p := F (rD.extractIndex g, rM.extractIndex g)
    (rD.concat rM hDM).replaceIndex g (liftPairIdx F ((rD.concat rM hDM).extractIndex g)) =
      rM.replaceIndex (rD.replaceIndex g p.1) p.2 := by
  intro p
  let rDM := rD.concat rM hDM
  have hex : extractPair (rDM.extractIndex g) = (rD.extractIndex g, rM.extractIndex g) := by
    dsimp only [extractPair]
    rw [← QRegister.extractIndex_compose, concat_compose_selDataInAct,
        ← QRegister.extractIndex_compose, concat_compose_selMeasInAct]
  dsimp only [liftPairIdx]
  rw [hex]
  change rDM.replaceIndex g ((selMeasInAct k).replaceIndex ((selDataInAct k).replaceIndex
    (rDM.extractIndex g) p.1) p.2) = rM.replaceIndex (rD.replaceIndex g p.1) p.2
  apply eq_of_basisBits_eq; intro w
  by_cases hwDM : w ∈ Set.range rDM.wires
  · obtain ⟨u, rfl⟩ := hwDM
    rw [QRegister.basisBits_replaceIndex_apply]
    refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) u
    · have hd : Fin.castAdd 18 i = selDataInAct k i := (selDataInAct_apply i).symm
      have hnotM_loc : selDataInAct k i ∉ Set.range (selMeasInAct k).wires :=
        fun ⟨m', hm'⟩ ↦ (selDataInAct_disj_selMeasInAct k).ne i m' hm'.symm
      have hrD : rDM (Fin.castAdd 18 i) = rD i := QRegister.concat_apply_left rD rM hDM i
      have hnotM : rD i ∉ Set.range rM.wires := fun ⟨m', hm'⟩ ↦ hDM.ne i m' hm'.symm
      rw [hrD, hd, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM_loc,
          QRegister.basisBits_replaceIndex_apply,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM,
          QRegister.basisBits_replaceIndex_apply]
    · have hm : Fin.natAdd k m = selMeasInAct k m := (selMeasInAct_apply m).symm
      have hrM : rDM (Fin.natAdd k m) = rM m := QRegister.concat_apply_right rD rM hDM m
      rw [hrM, hm, QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
  · have hnotM : w ∉ Set.range rM.wires := fun ⟨m, hm⟩ ↦
      hwDM ⟨Fin.natAdd k m, (QRegister.concat_apply_right rD rM hDM m).trans hm⟩
    have hnotD : w ∉ Set.range rD.wires := fun ⟨i, hi⟩ ↦
      hwDM ⟨Fin.castAdd 18 i, (QRegister.concat_apply_left rD rM hDM i).trans hi⟩
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwDM,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotM,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotD]
theorem compose_replaceIndex_eq_fast {n k₁ k₂ : ℕ} (outer : QRegister k₂ n)
    (inner : QRegister k₁ k₂) (g : Fin (2 ^ n)) (v : Fin (2 ^ k₁)) :
    (outer.compose inner).replaceIndex g v = outer.replaceIndex g
    (inner.replaceIndex (outer.extractIndex g) v) := by
  apply eq_of_basisBits_eq; intro w
  by_cases hwO : w ∈ Set.range outer.wires
  · obtain ⟨u, rfl⟩ := hwO
    rw [QRegister.basisBits_replaceIndex_apply]
    by_cases huI : u ∈ Set.range inner.wires
    · obtain ⟨i, rfl⟩ := huI
      rw [QRegister.basisBits_replaceIndex_apply]
      exact QRegister.basisBits_replaceIndex_apply (outer.compose inner) g v i
    · have hnot : outer u ∉ Set.range (outer.compose inner).wires :=
        fun ⟨i, hi⟩ ↦ huI ⟨i, outer.wires.injective hi⟩
      rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ huI,
          QRegister.basisBits_extractIndex]
  · have hnot : w ∉ Set.range (outer.compose inner).wires := fun ⟨i, hi⟩ ↦ hwO ⟨inner i, hi⟩
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwO]
theorem embedMatrix_diagonal_eq_fast {m N : ℕ} (r : QRegister m N) (f : Fin (2 ^ m) → ℂ) :
    r.embedMatrix (Matrix.diagonal f) = Matrix.diagonal (fun z ↦ f (r.extractIndex z)) := by
  ext z₁ z₂
  rw [QRegister.embedMatrix_apply]
  by_cases hz : z₁ = z₂
  · subst hz; simp [Matrix.diagonal]
  · simp only [Matrix.diagonal_apply_ne _ hz]
    by_cases henv : (r.basisSplitEquiv z₁).2 = (r.basisSplitEquiv z₂).2
    · have hex : r.extractIndex z₁ ≠ r.extractIndex z₂ := fun heq ↦ hz (r.basisSplitEquiv.injective
        (Prod.ext (by simpa [QRegister.basisSplitEquiv_apply_fst] using heq) henv))
      simp [henv, Matrix.diagonal, hex]
    · simp [henv]
open Classical in
theorem embedMatrix_p_slot0_mulVec_ket {n kData : ℕ} (rData : QRegister kData n)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) (L : Slot18Lens kData)
    (β : BitAssignment n) : ((rData.concat rMeas hDM).embedMatrix (P_slot0 L)).mulVec (ket β)
    = if S_slot0Lens rData L β then ket β else 0 := by
  have hDiag : (rData.concat rMeas hDM).embedMatrix (P_slot0 L) =
      Matrix.diagonal (fun z ↦ if L.tbl (rData.extractIndex z) = 0 then (1 : ℂ) else 0) := by
    rw [P_slot0_eq_diagonal L, embedMatrix_diagonal_eq_fast]
    apply congrArg Matrix.diagonal; funext z
    rw [← QRegister.extractIndex_compose, concat_compose_selDataInAct]
  rw [hDiag]
  let g := (basisBitsEquiv n).symm β
  have hket : ket β = Pi.single g 1 := rfl
  by_cases hS : S_slot0Lens rData L β
  · rw [ite_eq_left hS, hket]
    have ht : L.tbl (rData.extractIndex g) = 0 := hS
    ext y; rw [Matrix.mulVec_diagonal]
    by_cases hy : y = g
    · subst hy; simp [ht]
    · simp [hy]
  · rw [ite_eq_right hS, hket]
    have ht : L.tbl (rData.extractIndex g) ≠ 0 := hS
    ext y; rw [Matrix.mulVec_diagonal]
    by_cases hy : y = g
    · subst hy; simp [ht]
    · simp [hy]
theorem concat_compose_selCoreInEI {n C : ℕ} (rCore : QRegister C n) (rE : QRegister 9 n)
    (hCE : rCore.DisjointWires rE) : (rCore.concat rE hCE).compose (selCoreInEI C) = rCore :=
    QRegister.ext (Function.Embedding.ext fun i ↦ QRegister.concat_apply_left rCore rE hCE i)
theorem fastLinState_extract_and_tbl {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB)
    (β : BitAssignment n) (hWB0 : ∀ j : Fin mWB, β (rWB j) = 0) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    let g₀ := (basisBitsEquiv n).symm β
    let g_lin := (basisBitsEquiv n).symm (fastLinState hmPay hmWB rCore rWB hCW β)
    rCore.extractIndex g_lin = rCore.extractIndex g₀ ∧
    rAnchor18.extractIndex g_lin = rAnchor18.extractIndex g₀ ∧
    fastEISlotReg hmPay (rDataEI.extractIndex g_lin) =
      (selCoreInEI (fullSysCoreWires mPayload)).compose
        (coinBarrelFastSlotReg hmPay (rCore.extractIndex g₀)) ∧
    (fastEILens hmPay).tbl (rDataEI.extractIndex g_lin) =
      (coinBarrelFastSlot18Lens hmPay).tbl (rCore.extractIndex g₀) := by
  intro hCEI rDataEI g₀ g_lin
  let C := fullSysCoreWires mPayload
  let β_lin := fastLinState hmPay hmWB rCore rWB hCW β
  have hbg₀ : basisBits n g₀ = β := (basisBitsEquiv n).apply_symm_apply β
  have hbg_lin : basisBits n g_lin = β_lin := (basisBitsEquiv n).apply_symm_apply β_lin
  have hCoreEx : rCore.extractIndex g_lin = rCore.extractIndex g₀ := by
    apply eq_of_basisBits_eq; intro i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hbg_lin, hbg₀]
    exact fastLinState_outside_rWB hmPay hmWB rCore rWB hCW β fun ⟨k, hk⟩ ↦ hCW.ne i k hk.symm
  have hAncEx : rAnchor18.extractIndex g_lin = rAnchor18.extractIndex g₀ := by
    apply eq_of_basisBits_eq; intro j
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hbg_lin, hbg₀]
    exact fastLinState_outside_rWB hmPay hmWB rCore rWB hCW β fun ⟨k, hk⟩ ↦ hAW.ne j k hk.symm
  obtain ⟨_, hsFn⟩ := fastLinState_invTrees_and_sFnEI hmPay hmWB rCore rWB hCW β hWB0
  have hSlotEq : fastEISlotReg hmPay (rDataEI.extractIndex g_lin) =
      (selCoreInEI C).compose (coinBarrelFastSlotReg hmPay (rCore.extractIndex g₀)) := by
    dsimp only [fastEISlotReg, coinBarrelFastSlotReg]
    refine congrArg (fun e ↦ (selCoreInEI C).compose (rFullSysElecSlot hmPay e)) ?_
    have hD_bits : basisBits (C + 9) (rDataEI.extractIndex g_lin) = fun u ↦ β_lin (rDataEI u) := by
      funext u; rw [QRegister.basisBits_extractIndex, hbg_lin]
    have hC_bits : basisBits C (rCore.extractIndex g₀) = fun i ↦ β (rCore i) := by
      funext i; rw [QRegister.basisBits_extractIndex, hbg₀]
    rw [hD_bits, hC_bits]
    exact hsFn
  refine ⟨hCoreEx, hAncEx, hSlotEq, ?_⟩
  change (fastEISlotReg hmPay (rDataEI.extractIndex g_lin)).extractIndex
    (rDataEI.extractIndex g_lin) =
    (coinBarrelFastSlotReg hmPay (rCore.extractIndex g₀)).extractIndex (rCore.extractIndex g₀)
  rw [hSlotEq, ← QRegister.extractIndex_compose, ← QRegister.compose_assoc,
      concat_compose_selCoreInEI, QRegister.extractIndex_compose, hCoreEx]
theorem slotUpdate_intertwines_fastLinState {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB)
    (updFlag : Bool)
    (valFn measFn : Fin (2 ^ 18) → Fin (2 ^ 18) → Fin (2 ^ 18))
    (β : BitAssignment n) (hWB0 : ∀ j : Fin mWB, β (rWB j) = 0) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    let g₀ := (basisBitsEquiv n).symm β
    let g_lin := (basisBitsEquiv n).symm (fastLinState hmPay hmWB rCore rWB hCW β)
    let x := rCore.extractIndex g₀
    let m := rAnchor18.extractIndex g₀
    let t := (coinBarrelFastSlot18Lens hmPay).tbl x
    let dx := rDataEI.extractIndex g_lin
    let dEI' := if updFlag then (fastEILens hmPay).updSlot dx (valFn t m) else dx
    let x' := if updFlag then (coinBarrelFastSlot18Lens hmPay).updSlot x (valFn t m) else x
    let g_lhs := rAnchor18.replaceIndex (rDataEI.replaceIndex g_lin dEI') (measFn t m)
    let g_core := rAnchor18.replaceIndex (rCore.replaceIndex g₀ x') (measFn t m)
    (∀ j : Fin mWB, basisBits n g_core (rWB j) = 0) ∧
    basisBits n g_lhs = fastLinState hmPay hmWB rCore rWB hCW (basisBits n g_core) := by
  intro hCEI rDataEI g₀ g_lin x m t dx dEI' x' g_lhs g_core
  let C := fullSysCoreWires mPayload
  let β_lin := fastLinState hmPay hmWB rCore rWB hCW β
  have hbg₀ : basisBits n g₀ = β := (basisBitsEquiv n).apply_symm_apply β
  have hbg_lin : basisBits n g_lin = β_lin := (basisBitsEquiv n).apply_symm_apply β_lin
  obtain ⟨hCoreEx, _, hSlotEq, _⟩ :=
    fastLinState_extract_and_tbl hmPay hmWB rCore rAnchor18 rWB hCW hAW β hWB0
  have hdEI_upd : rDataEI.replaceIndex g_lin dEI' = rCore.replaceIndex g_lin x' := by
    dsimp only [dEI', x']
    by_cases huf : updFlag
    · rw [ite_eq_left huf, ite_eq_left huf]
      change rDataEI.replaceIndex g_lin ((fastEISlotReg hmPay dx).replaceIndex dx (valFn t m)) =
        rCore.replaceIndex g_lin ((coinBarrelFastSlotReg hmPay x).replaceIndex x (valFn t m))
      rw [hSlotEq,
          ← compose_replaceIndex_eq_fast rDataEI
              ((selCoreInEI C).compose (coinBarrelFastSlotReg hmPay x)) g_lin,
          ← QRegister.compose_assoc, concat_compose_selCoreInEI,
          compose_replaceIndex_eq_fast rCore (coinBarrelFastSlotReg hmPay x) g_lin, hCoreEx]
    · rw [ite_eq_right huf, ite_eq_right huf]
      dsimp only [dx, x]
      rw [← hCoreEx, QRegister.replaceIndex_extractIndex, QRegister.replaceIndex_extractIndex]
  have hg_lhs : g_lhs = rAnchor18.replaceIndex (rCore.replaceIndex g_lin x') (measFn t m) := by
    dsimp only [g_lhs]; rw [hdEI_upd]
  have hWB_core : ∀ j : Fin mWB, basisBits n g_core (rWB j) = 0 := by
    intro j
    have hnA : rWB j ∉ Set.range rAnchor18.wires := fun ⟨a, ha⟩ ↦ hAW.ne a j ha
    have hnC : rWB j ∉ Set.range rCore.wires := fun ⟨c, hc⟩ ↦ hCW.ne c j hc
    dsimp only [g_core]
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnA,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnC, hbg₀]
    exact hWB0 j
  have hHigh_core : ∀ i : Fin C, 3924 ≤ i.val →
      basisBits n g_core (rCore i) = β (rCore i) := by
    intro i hi
    have hnA : rCore i ∉ Set.range rAnchor18.wires := fun ⟨a, ha⟩ ↦ hCA.ne i a ha.symm
    dsimp only [g_core]
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnA,
        QRegister.basisBits_replaceIndex_apply]
    dsimp only [x']
    by_cases huf : updFlag
    · rw [ite_eq_left huf]
      change basisBits C ((coinBarrelFastSlotReg hmPay x).replaceIndex x (valFn t m)) i =
        β (rCore i)
      have hnS : i ∉ Set.range (coinBarrelFastSlotReg hmPay x).wires := by
        rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        dsimp only [coinBarrelFastSlotReg] at hv
        rw [rFullSysElecSlot_val] at hv
        have := (coinBarrelIdxFast hmPay (basisBits C x)).isLt
        have := j.isLt
        omega
      rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnS,
          QRegister.basisBits_extractIndex, hbg₀]
    · rw [ite_eq_right huf, QRegister.basisBits_extractIndex, hbg₀]
  refine ⟨hWB_core, funext fun w ↦ ?_⟩
  by_cases hw : w ∈ Set.range rWB.wires
  · obtain ⟨j, rfl⟩ := hw
    have hnA : rWB j ∉ Set.range rAnchor18.wires := fun ⟨a, ha⟩ ↦ hAW.ne a j ha
    have hnC : rWB j ∉ Set.range rCore.wires := fun ⟨c, hc⟩ ↦ hCW.ne c j hc
    rw [hg_lhs, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnA,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnC, hbg_lin]
    exact fastLinState_congr_highCore hmPay hmWB rCore rWB hCW β (basisBits n g_core)
      hWB0 hWB_core (fun i hi ↦ (hHigh_core i hi).symm) ⟨j, rfl⟩
  · rw [fastLinState_outside_rWB hmPay hmWB rCore rWB hCW (basisBits n g_core) hw, hg_lhs]
    dsimp only [g_core]
    by_cases hwA : w ∈ Set.range rAnchor18.wires
    · obtain ⟨a, rfl⟩ := hwA
      rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwA,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwA]
      by_cases hwC : w ∈ Set.range rCore.wires
      · obtain ⟨c, rfl⟩ := hwC
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
      · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwC,
            QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwC, hbg_lin, hbg₀]
        exact fastLinState_outside_rWB hmPay hmWB rCore rWB hCW β hw
theorem ket_eq_pi_single {n : ℕ} (β : BitAssignment n) :
    ket β = Pi.single ((basisBitsEquiv n).symm β) 1 := rfl
theorem pi_single_eq_ket {n : ℕ} (g : Fin (2 ^ n)) :
    (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) = ket (basisBits n g) :=
  congrArg (fun idx ↦ Pi.single idx (1 : ℂ)) ((basisBitsEquiv n).symm_apply_apply g).symm
theorem vLinUnitary_intertwines_load {n mPayload mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    let rCoreAnchor := rCore.concat rAnchor18 hCA
    let V_lin := vLinUnitary hmPay hmWB rCore rWB hCW
    let P_wb := rWB.basisOutcomeProjector 0
    (rActEI.embedUnitary (uLensLoad (fastEILens hmPay))).1 * (V_lin.1 * P_wb) =
      V_lin.1 *
        ((rCoreAnchor.embedUnitary (uLensLoad (coinBarrelFastSlot18Lens hmPay))).1 * P_wb) := by
  intro hCEI hDA_EI rActEI rCoreAnchor V_lin P_wb
  apply matrix_ext_ket; intro β
  dsimp only [V_lin, P_wb]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec,
      ket_basisOutcomeProjector_zero]
  by_cases hWB0 : ∀ j : Fin mWB, β (rWB j) = 0
  · rw [ite_eq_left hWB0, vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW β hWB0]
    obtain ⟨_, hAncEx, _, hTblEq⟩ :=
      fastLinState_extract_and_tbl hmPay hmWB rCore rAnchor18 rWB hCW hAW β hWB0
    obtain ⟨hWB_core, hEq⟩ := slotUpdate_intertwines_fastLinState hmPay hmWB rCore rAnchor18 rWB
      hCA hCW hAW false (fun t _ ↦ t) (fun t m ↦ xor18 m t) β hWB0
    simp only [Bool.false_eq_true, ↓reduceIte] at hWB_core hEq
    rw [ket_eq_pi_single (fastLinState hmPay hmWB rCore rWB hCW β), ket_eq_pi_single β]
    dsimp only [uLensLoad]
    rw [embedUnitary_permUnitary_mulVec_single_fast, embedUnitary_permUnitary_mulVec_single_fast]
    dsimp only [rActEI, rCoreAnchor, lensLoadEquiv]
    simp only [Equiv.ofBijective_apply]
    rw [concat_replaceIndex_liftPairIdx_fast (rCore.concat (rEnIdx9 hmWB rWB) hCEI) rAnchor18 hDA_EI
          (lensLoadPerm (fastEILens hmPay)),
        concat_replaceIndex_liftPairIdx_fast rCore rAnchor18 hCA
          (lensLoadPerm (coinBarrelFastSlot18Lens hmPay))]
    dsimp only [lensLoadPerm]
    rw [hAncEx, hTblEq, pi_single_eq_ket, pi_single_eq_ket,
        vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW _ hWB_core]
    exact congrArg ket hEq
  · rw [ite_eq_right hWB0, Matrix.mulVec_zero, Matrix.mulVec_zero,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem vLinUnitary_intertwines_write {n mPayload mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    let rCoreAnchor := rCore.concat rAnchor18 hCA
    let V_lin := vLinUnitary hmPay hmWB rCore rWB hCW
    let P_wb := rWB.basisOutcomeProjector 0
    (rActEI.embedUnitary (uLensWrite (fastEILens hmPay))).1 * (V_lin.1 * P_wb) =
      V_lin.1 *
        ((rCoreAnchor.embedUnitary (uLensWrite (coinBarrelFastSlot18Lens hmPay))).1 * P_wb) := by
  intro hCEI hDA_EI rActEI rCoreAnchor V_lin P_wb
  apply matrix_ext_ket; intro β
  dsimp only [V_lin, P_wb]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec,
      ket_basisOutcomeProjector_zero]
  by_cases hWB0 : ∀ j : Fin mWB, β (rWB j) = 0
  · rw [ite_eq_left hWB0, vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW β hWB0]
    obtain ⟨_, hAncEx, _, hTblEq⟩ :=
      fastLinState_extract_and_tbl hmPay hmWB rCore rAnchor18 rWB hCW hAW β hWB0
    obtain ⟨hWB_core, hEq⟩ := slotUpdate_intertwines_fastLinState hmPay hmWB rCore rAnchor18 rWB
      hCA hCW hAW true (fun t m ↦ xor18 t m) (fun _ m ↦ m) β hWB0
    simp only [↓reduceIte] at hWB_core hEq
    rw [ket_eq_pi_single (fastLinState hmPay hmWB rCore rWB hCW β), ket_eq_pi_single β]
    dsimp only [uLensWrite]
    rw [embedUnitary_permUnitary_mulVec_single_fast, embedUnitary_permUnitary_mulVec_single_fast]
    dsimp only [rActEI, rCoreAnchor, lensWriteEquiv]
    simp only [Equiv.ofBijective_apply]
    rw [concat_replaceIndex_liftPairIdx_fast (rCore.concat (rEnIdx9 hmWB rWB) hCEI) rAnchor18 hDA_EI
          (lensWritePerm (fastEILens hmPay)),
        concat_replaceIndex_liftPairIdx_fast rCore rAnchor18 hCA
          (lensWritePerm (coinBarrelFastSlot18Lens hmPay))]
    dsimp only [lensWritePerm]
    rw [hAncEx, hTblEq, pi_single_eq_ket, pi_single_eq_ket,
        vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW _ hWB_core]
    exact congrArg ket hEq
  · rw [ite_eq_right hWB0, Matrix.mulVec_zero, Matrix.mulVec_zero,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem vLinUnitary_intertwines_swap {n mPayload mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    let rCoreAnchor := rCore.concat rAnchor18 hCA
    let V_lin := vLinUnitary hmPay hmWB rCore rWB hCW
    let P_wb := rWB.basisOutcomeProjector 0
    (rActEI.embedUnitary (uLensSwap (fastEILens hmPay))).1 * (V_lin.1 * P_wb) =
      V_lin.1 *
        ((rCoreAnchor.embedUnitary (uLensSwap (coinBarrelFastSlot18Lens hmPay))).1 * P_wb) := by
  intro hCEI hDA_EI rActEI rCoreAnchor V_lin P_wb
  apply matrix_ext_ket; intro β
  dsimp only [V_lin, P_wb]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec,
      ket_basisOutcomeProjector_zero]
  by_cases hWB0 : ∀ j : Fin mWB, β (rWB j) = 0
  · rw [ite_eq_left hWB0, vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW β hWB0]
    obtain ⟨_, hAncEx, _, hTblEq⟩ :=
      fastLinState_extract_and_tbl hmPay hmWB rCore rAnchor18 rWB hCW hAW β hWB0
    obtain ⟨hWB_core, hEq⟩ := slotUpdate_intertwines_fastLinState hmPay hmWB rCore rAnchor18 rWB
      hCA hCW hAW true (fun _ m ↦ m) (fun t _ ↦ t) β hWB0
    simp only [↓reduceIte] at hWB_core hEq
    rw [ket_eq_pi_single (fastLinState hmPay hmWB rCore rWB hCW β), ket_eq_pi_single β]
    dsimp only [uLensSwap]
    rw [embedUnitary_permUnitary_mulVec_single_fast, embedUnitary_permUnitary_mulVec_single_fast]
    dsimp only [rActEI, rCoreAnchor, lensSwapEquiv]
    simp only [Equiv.ofBijective_apply]
    rw [concat_replaceIndex_liftPairIdx_fast (rCore.concat (rEnIdx9 hmWB rWB) hCEI) rAnchor18 hDA_EI
          (lensSwapPerm (fastEILens hmPay)),
        concat_replaceIndex_liftPairIdx_fast rCore rAnchor18 hCA
          (lensSwapPerm (coinBarrelFastSlot18Lens hmPay))]
    dsimp only [lensSwapPerm]
    rw [hAncEx, hTblEq, pi_single_eq_ket, pi_single_eq_ket,
        vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW _ hWB_core]
    exact congrArg ket hEq
  · rw [ite_eq_right hWB0, Matrix.mulVec_zero, Matrix.mulVec_zero,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
/-- Core `420 T`-wrapped `64 × 4` gated W-state pre-pass (`16,404 T`, `TOFF = 0`)
on `rCore.concat rAnchor18` (`80 ≤ mPayload`, `143 ≤ mWB`). -/
noncomputable def dPreCoreAnchor64x4Fast {Var : Type} {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rAnchor18 : QRegister 18 n)
    (rWB : QRegister mWB n) (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) : DynamicCircuit Var n
    :=
  let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
  let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
  let hDA_EI : rDataEI.DisjointWires rAnchor18 :=
    qreg_disjoint_concat_left hCA
      (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
  let hDS_EI : rDataEI.DisjointWires (rScr75 hmWB rWB) := qreg_disjoint_concat_left
      (disj_rScr75_right hmWB hCW) ((rPeb10_disj_rScr75 hmWB rWB).compose_left _)
  dWrapFast68 hmPay hmWB v rCore rWB hCW
    (dPreHole218 (le_refl 75) v rDataEI (selCoreEI hmPay)
      rAnchor18 (rScr75 hmWB rWB) hDA_EI (hDS_EI.compose_left (selCoreEI hmPay))
      (disj_rScr75_right hmWB hAW))
theorem dPreCoreAnchor64x4Fast_count_toff {Var : Type} {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rAnchor18 : QRegister 18 n)
    (rWB : QRegister mWB n) (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    (dPreCoreAnchor64x4Fast hmPay hmWB v rCore rAnchor18 rWB hCA hCW hAW).count TOFF = 0 := by
  dsimp only [dPreCoreAnchor64x4Fast]
  rw [count_dWrapFast68_toff, dPreHole218_count_toff]
theorem dPreCoreAnchor64x4Fast_count_t {Var : Type} {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n) (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    (dPreCoreAnchor64x4Fast hmPay hmWB v rCore rAnchor18 rWB hCA hCW hAW).count T = 16404 := by
  dsimp only [dPreCoreAnchor64x4Fast]
  rw [count_dWrapFast68_t, dPreHole218_count_t]
theorem dPreCoreAnchor64x4Fast_count_t_le {Var : Type} {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rAnchor18 : QRegister 18 n)
    (rWB : QRegister mWB n) (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    (dPreCoreAnchor64x4Fast hmPay hmWB v rCore rAnchor18 rWB hCA hCW hAW).count T ≤ 16404 :=
    le_of_eq (dPreCoreAnchor64x4Fast_count_t hmPay hmWB v rCore rAnchor18 rWB hCA hCW hAW)
open Classical in
theorem dPreCoreAnchor64x4Fast_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18)
    (hCW : rCore.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let L_core := coinBarrelFastSlot18Lens hmPay
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rAnchor18 hCA) rWB (uLensWrite L_core * uLensLoad L_core)
      (dPreCoreAnchor64x4Fast hmPay hmWB v rCore rAnchor18 rWB hCA hCW hAW) := by
  intro L_core
  apply Pass1BarrelIdxPebbled273.RealizesOnProj.to_cleanWorkspace
  let rCoreAnchor := rCore.concat rAnchor18 hCA
  have hCAW : rCoreAnchor.DisjointWires rWB := qreg_disjoint_concat_left hCW hAW
  let P_wb := rWB.basisOutcomeProjector 0
  let P_trees := p2d_ketPredProj (fun β ↦
    invTreesIn93 (fun idx ↦ β (rComb93 hmPay hmWB rCore rWB hCW idx)))
  have hTrees := peb_realizesOnProj_of_p2d (p2d_ketPredProj_conjTranspose _)
    (dPreTreesFast_realizes hmPay hmWB v rCore rAnchor18 rWB hCA hCW hAW)
  refine dWrapFast68_realizes_gen hmPay hmWB v rCore rWB hCW
    (QRegister.basisOutcomeProjector_conjTranspose _ 0) (p2d_ketPredProj_conjTranspose _)
    (hasCleanTailFrom_rWB_proj0 rCore rWB (by omega) hCW)
    (hasCleanTailFrom_embedMatrix_mul_proj0 rCore rWB (by omega) hCW rCoreAnchor hCAW _)
    hTrees ?_ ?_
  · apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_basisOutcomeProjector_zero]
    by_cases hWB0 : ∀ j : Fin mWB, β (rWB j) = 0
    · rw [ite_eq_left hWB0, vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW β hWB0,
          p2d_ketPredProj_mul_ket,
          ite_eq_left (fastLinState_invTrees_and_sFnEI hmPay hmWB rCore rWB hCW β hWB0).1]
    · rw [ite_eq_right hWB0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) := (hCW.compose_right _).compose_right _
    let hDA_EI : (rCore.concat (rEnIdx9 hmWB rWB) hCEI).DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA
        (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right _))
    let rActEI := (rCore.concat (rEnIdx9 hmWB rWB) hCEI).concat rAnchor18 hDA_EI
    let L_ei := fastEILens hmPay
    let V := (vLinUnitary hmPay hmWB rCore rWB hCW).1
    let U_W_ei := (rActEI.embedUnitary (uLensWrite L_ei)).1
    let U_L_ei := (rActEI.embedUnitary (uLensLoad L_ei)).1
    let U_W_c := (rCoreAnchor.embedUnitary (uLensWrite L_core)).1
    let U_L_c := (rCoreAnchor.embedUnitary (uLensLoad L_core)).1
    have hIntLoad : U_L_ei * (V * P_wb) = V * (U_L_c * P_wb) :=
      vLinUnitary_intertwines_load hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW
    have hIntWrite : U_W_ei * (V * P_wb) = V * (U_W_c * P_wb) :=
      vLinUnitary_intertwines_write hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW
    have hCommLoad : U_L_c * P_wb = P_wb * U_L_c :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) rWB hCAW _ 0
    rw [rActEI.embedUnitary_mul, rCoreAnchor.embedUnitary_mul,
        Submonoid.coe_mul, Submonoid.coe_mul]
    change (U_W_ei * U_L_ei) * (V * P_wb) = V * ((U_W_c * U_L_c) * P_wb)
    calc (U_W_ei * U_L_ei) * (V * P_wb)
        = U_W_ei * (U_L_ei * (V * P_wb)) := by simp only [Matrix.mul_assoc]
      _ = U_W_ei * (V * (U_L_c * P_wb)) := by rw [hIntLoad]
      _ = U_W_ei * (V * (P_wb * U_L_c)) := by rw [hCommLoad]
      _ = (U_W_ei * (V * P_wb)) * U_L_c := by simp only [Matrix.mul_assoc]
      _ = (V * (U_W_c * P_wb)) * U_L_c := by rw [hIntWrite]
      _ = V * (U_W_c * (P_wb * U_L_c)) := by simp only [Matrix.mul_assoc]
      _ = V * (U_W_c * (U_L_c * P_wb)) := by rw [← hCommLoad]
      _ = V * ((U_W_c * U_L_c) * P_wb) := by simp only [Matrix.mul_assoc]
/-- Data-lifted `420 T`-wrapped `64 × 4` gated W-state pre-pass (`16,404 T`, `TOFF = 0`)
for `coinBarrelFastOnDataLens hmPay selCore` on `rData.concat rAnchor18` (`143 ≤ mWB`). -/
noncomputable def dPreAnchor64x4Fast {Var : Type} {n mPayload kData mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var) (rData : QRegister kData n)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) (rAnchor18 : QRegister 18 n)
    (rWB : QRegister mWB n) (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) : DynamicCircuit Var n
    := dPreCoreAnchor64x4Fast hmPay hmWB v (rData.compose selCore) rAnchor18 rWB
    (hDA.compose_left selCore) (hDW.compose_left selCore) hAW
theorem dPreAnchor64x4Fast_count_toff {Var : Type} {n mPayload kData mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var) (rData : QRegister kData n)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) (rAnchor18 : QRegister 18 n)
    (rWB : QRegister mWB n) (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) : (dPreAnchor64x4Fast
    hmPay hmWB v rData selCore rAnchor18 rWB hDA hDW hAW).count TOFF = 0 :=
    dPreCoreAnchor64x4Fast_count_toff hmPay hmWB v _ rAnchor18 rWB _ _ hAW
theorem dPreAnchor64x4Fast_count_t_le {Var : Type} {n mPayload kData mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var) (rData : QRegister kData n)
    (selCore : QRegister (fullSysCoreWires mPayload) kData) (rAnchor18 : QRegister 18 n)
    (rWB : QRegister mWB n) (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) : (dPreAnchor64x4Fast
    hmPay hmWB v rData selCore rAnchor18 rWB hDA hDW hAW).count T ≤ 16404 :=
    dPreCoreAnchor64x4Fast_count_t_le hmPay hmWB v _ rAnchor18 rWB _ _ hAW
theorem dPreAnchor64x4Fast_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload kData mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (rAnchor18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWB) (hAW : rAnchor18.DisjointWires rWB) :
    let L := coinBarrelFastOnDataLens hmPay selCore
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.concat rAnchor18 hDA) rWB (uLensWrite L * uLensLoad L)
      (dPreAnchor64x4Fast hmPay hmWB v rData selCore rAnchor18 rWB hDA hDW hAW) := by
  intro L
  have hCore := dPreCoreAnchor64x4Fast_realizes hmPay hmWB v (rData.compose selCore) rAnchor18 rWB
    (hDA.compose_left selCore) (hDW.compose_left selCore) hAW
  have hU : (rData.concat rAnchor18 hDA).embedUnitary (uLensWrite L * uLensLoad L) =
      ((rData.compose selCore).concat rAnchor18 (hDA.compose_left selCore)).embedUnitary
        (uLensWrite (coinBarrelFastSlot18Lens hmPay) *
          uLensLoad (coinBarrelFastSlot18Lens hmPay)) := by
    dsimp only [L, coinBarrelFastOnDataLens]
    rw [← uLensWrite_liftSlot18Lens, ← uLensLoad_liftSlot18Lens,
        ← (selLiftAct selCore).embedUnitary_mul, ← QRegister.embedUnitary_compose,
        concat_compose_selLiftAct]
  change Pass1BarrelIdxPebbled273.RealizesOnProj _
    ((rData.concat rAnchor18 hDA).embedUnitary (uLensWrite L * uLensLoad L)).1 _
  rw [hU]
  exact hCore
theorem embed_intertwine_op_fast {k m n : ℕ} {rA : QRegister k n} {rW : QRegister m n}
    (hDisj : rA.DisjointWires rW) {U : Unitary (2 ^ k)} {E F V : Operator (2 ^ k)}
    (hLoc : U.1 * E = F * V) : (rA.embedUnitary U).1 *
    (rA.embedMatrix E * rW.basisOutcomeProjector 0) =
    (rA.embedMatrix F * rW.basisOutcomeProjector 0) * rA.embedMatrix V := by
  rw [QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← rA.embedMatrix_mul, hLoc,
      rA.embedMatrix_mul, Matrix.mul_assoc,
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rA) rW hDisj V 0,
        ← Matrix.mul_assoc]
end Part3_OuterFastEngine
section Part4_FastAnchorPolyAndBundles
open HoistBorrow42ProjBridge (RealizesOnProj)
open HeldMsbInc7Sandwich288 (basisOutcomeProjector_zero_concat_eq_mul)
open InterWalkRSum42Hoist (kFull80 qreg_ext)
open HeldStreamFoldedPass123Bridge (pRawCtrl3ExtOn pRawHoistExtOn)
open BarrelPass2AndHeld3PassSelectStitch (uSingleBarrelFolded6Full uSingleBarrelFolded6Seg)
open SingleBarrel8StepClean
  (FoldedPass123Bundle179_11 uSingleBarrelFolded6Seg_mul_catState48_eq_Mod4OfB
  uSingleBarrelFolded6Seg_mul_pCoinSlack010Seg)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (StageAAnchorInput179_11 StageBAnchorInput179_11
    uSingleBarrelFolded6Full_intertwines_rawStream_and_ext11)
section NoSizeOfFolded
/-- Symbolic-dimension core for `{mWork}`-polymorphic `FoldedPass123` circuit realizations. -/
structure FoldedPass123CircuitSpecCore_mWork (kAct mWork : ℕ)
    (pRawCtrl pRawCat : ∀ {n : ℕ}, QRegister kAct n → QRegister mWork n → Operator (2 ^ n))
    (uFoldedCtrlFull uFoldedCatFull : Fin 10 → Configuration → Unitary (2 ^ kAct))
    (tFoldCtrl tFoldCat : Fin 10 → ℕ) where
  dFoldedCtrl : Fin 10 → Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rAct : QRegister kAct n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  dFoldedCat : Fin 10 → Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rAct : QRegister kAct n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  hToffCtrl : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCtrl j c v rAct rWork hD).count TOFF = 0
  hToffCat : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCat j c v rAct rWork hD).count TOFF = 0
  hTCtrl : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCtrl j c v rAct rWork hD).count T ≤ tFoldCtrl j
  hTCat : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCat j c v rAct rWork hD).count T ≤ tFoldCat j
  hRealRawCtrl : ∀ j c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    RealizesOnProj (pRawCtrl rAct rWork)
      (rAct.embedUnitary (uFoldedCtrlFull j c))
      (dFoldedCtrl j c v rAct rWork hD)
  hRealRawCat : ∀ j c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    RealizesOnProj (pRawCat rAct rWork)
      (rAct.embedUnitary (uFoldedCatFull j c))
      (dFoldedCat j c v rAct rWork hD)
/-- `{mWork}`-polymorphic `FoldedPass123` circuit specification (`k_idle = 11`). -/
abbrev FoldedPass123CircuitSpec_mWork (mWork : ℕ) (uFoldedCtrlFull uFoldedCatFull : Fin 10 →
    Configuration → Unitary (2 ^ kFull80)) (tFoldCtrl tFoldCat : Fin 10 → ℕ) : Type 1 :=
    FoldedPass123CircuitSpecCore_mWork kFull80 mWork
    (fun rA rW ↦ pRawCtrl3ExtOn 11 (by decide) rA rW)
    (fun rA rW ↦ pRawHoistExtOn 11 (by decide) rA rW) uFoldedCtrlFull uFoldedCatFull tFoldCtrl
    tFoldCat
end NoSizeOfFolded
/-- Anchor `18`-qubit slice `[0..18)` inside `rWork : QRegister mWork n` (`18 ≤ mWork`). -/
def rAnchor18OfMWork {mWork n : ℕ} (hm18 : 18 ≤
    mWork) (rWork : QRegister mWork n) : QRegister 18 n :=
  rWork.compose (QRegister.block 0 18 (by omega))
/-- Remaining `(mWork - 18)`-qubit scratch slice `[18..mWork)` inside `rWork : QRegister mWork
  n`. -/
def rWorkRemOfMWork {mWork n : ℕ} (hm18 : 18 ≤
    mWork) (rWork : QRegister mWork n) : QRegister (mWork - 18) n :=
  rWork.compose (QRegister.block 18 (mWork - 18) (by omega))
theorem rAnchor18OfMWork_disj_rWorkRemOfMWork {mWork n : ℕ} (hm18 : 18 ≤
    mWork) (rWork : QRegister mWork n) :
    (rAnchor18OfMWork hm18 rWork).DisjointWires (rWorkRemOfMWork hm18 rWork) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val (rWork.wires.injective hij)
  simp [QRegister.block] at hv
  omega
private theorem compose_block_zero_proj0_mWork {m' mWork n : ℕ}
    (hEq : m' = mWork) (hle : 0 + m' ≤ mWork) (rWork : QRegister mWork n) :
    (rWork.compose (QRegister.block 0 m' hle)).basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 := by
  subst hEq
  have hId : rWork.compose (QRegister.block 0 m' hle) = rWork := by
    apply InterWalkRSum42Hoist.qreg_ext; intro i
    dsimp only [QRegister.compose_apply]
    exact congrArg rWork.wires (Fin.ext (by simp [QRegister.block, Fin.natAddEmb]))
  rw [hId]
theorem rAnchor18OfMWork_proj0_mul_rWorkRemOfMWork_proj0 {mWork n : ℕ} (hm18 : 18 ≤ mWork)
    (rWork : QRegister mWork n) : (rAnchor18OfMWork hm18 rWork).basisOutcomeProjector 0 *
    (rWorkRemOfMWork hm18 rWork).basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 := by
  rw [← basisOutcomeProjector_zero_concat_eq_mul
    (rAnchor18OfMWork hm18 rWork) (rWorkRemOfMWork hm18 rWork)
    (rAnchor18OfMWork_disj_rWorkRemOfMWork hm18 rWork)]
  have hle : 0 + (18 + (mWork - 18)) ≤ mWork := by omega
  have hSub : (rAnchor18OfMWork hm18 rWork).concat (rWorkRemOfMWork hm18 rWork)
      (rAnchor18OfMWork_disj_rWorkRemOfMWork hm18 rWork) =
      rWork.compose (QRegister.block 0 (18 + (mWork - 18)) hle) := by
    apply InterWalkRSum42Hoist.qreg_ext; intro i
    by_cases hi : i.val < 18
    · have h1 :=
        QRegister.concat_apply_left (rAnchor18OfMWork hm18 rWork) (rWorkRemOfMWork hm18 rWork)
        (rAnchor18OfMWork_disj_rWorkRemOfMWork hm18 rWork) ⟨i.val, hi⟩
      have hidx1 : Fin.castAdd (mWork - 18) (⟨i.val, hi⟩ : Fin 18) = i := Fin.ext rfl
      rw [hidx1] at h1
      rw [h1]
      dsimp only [rAnchor18OfMWork, QRegister.compose_apply]
      exact congrArg rWork.wires (Fin.ext (by simp [QRegister.block, Fin.natAddEmb]))
    · have hge : 18 ≤ i.val := Nat.le_of_not_lt hi
      have h2 :=
        QRegister.concat_apply_right (rAnchor18OfMWork hm18 rWork) (rWorkRemOfMWork hm18 rWork)
        (rAnchor18OfMWork_disj_rWorkRemOfMWork hm18 rWork) ⟨i.val - 18, by omega⟩
      have hidx : Fin.natAdd 18 (⟨i.val - 18, by omega⟩ : Fin (mWork - 18)) = i :=
        Fin.ext (by simp; omega)
      rw [hidx] at h2
      rw [h2]
      dsimp only [rWorkRemOfMWork, QRegister.compose_apply]
      exact congrArg rWork.wires (Fin.ext (by
        simp [QRegister.block, Fin.natAddEmb,
        Nat.add_sub_of_le hge]))
  rw [hSub]
  exact compose_block_zero_proj0_mWork (by omega) hle rWork
/-- Standalone Fast-Outer constructor for `FoldedPass123Bundle179_11`
(`25,252 + 724 + tA + tB` `T`, `0-TOFF`) from `StageAAnchorInput179_11`,
`StageBAnchorInput179_11`, and `StageABGhostInput288`. -/
noncomputable def mkFoldedPass123Bundle179_11_FastAnchorStandalone
    {B : Fin 10 → ℕ} {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    {tACtrl tACat tBCtrl tBCat : Fin 10 → ℕ}
    (stA : BoothOpt_Anchor218CachedTrueSwapOuter.StageAAnchorInput179_11 tACtrl tACat)
    (stB : BoothOpt_Anchor218CachedTrueSwapOuter.StageBAnchorInput179_11 B hB6 hB27 tBCtrl tBCat) :
    FoldedPass123Bundle179_11 B hB6 hB27
      (fun j ↦ 25252 + 724 + tACtrl j + tBCtrl j)
      (fun j ↦ 25252 + 724 + tACat j + tBCat j) where
  uFoldedCtrlFull j _ := uSingleBarrelFolded6Full (stA.uStageACtrlFull j) (stB.uStageBCtrlFull j)
  uFoldedCatFull j _ := uSingleBarrelFolded6Full (stA.uStageACatFull j) (stB.uStageBCatFull j)
  uFoldedSeg j _ := uSingleBarrelFolded6Seg (stA.uStageASeg j) (stB.uStageBSeg j)
  hInterRawCtrl j _ :=
    (uSingleBarrelFolded6Full_intertwines_rawStream_and_ext11
      (stA.uStageACtrlFull j) (stB.uStageBCtrlFull j) (stA.uStageASeg j) (stB.uStageBSeg j)
      (stA.hACtrlRaw j) (stB.hBCtrlRaw j) (stA.hACtrl3 j) (stB.hBCtrl3 j)
      (stA.hAIdle11 j) (stB.hBIdle11 j)).2.2.2.1
  hInterRawCat j _ :=
    (uSingleBarrelFolded6Full_intertwines_rawStream_and_ext11
      (stA.uStageACatFull j) (stB.uStageBCatFull j) (stA.uStageASeg j) (stB.uStageBSeg j)
      (stA.hACatRaw j) (stB.hBCatRaw j) (stA.hACtrl3 j) (stB.hBCtrl3 j)
      (stA.hAIdle11 j) (stB.hBIdle11 j)).2.2.2.2
  hCtrl3Seg j _ :=
    (uSingleBarrelFolded6Full_intertwines_rawStream_and_ext11
      (stA.uStageACtrlFull j) (stB.uStageBCtrlFull j) (stA.uStageASeg j) (stB.uStageBSeg j)
      (stA.hACtrlRaw j) (stB.hBCtrlRaw j) (stA.hACtrl3 j) (stB.hBCtrl3 j)
      (stA.hAIdle11 j) (stB.hBIdle11 j)).2.1
  hIdle11Seg j _ :=
    (uSingleBarrelFolded6Full_intertwines_rawStream_and_ext11
      (stA.uStageACtrlFull j) (stB.uStageBCtrlFull j) (stA.uStageASeg j) (stB.uStageBSeg j)
      (stA.hACtrlRaw j) (stB.hBCtrlRaw j) (stA.hACtrl3 j) (stB.hBCtrl3 j)
      (stA.hAIdle11 j) (stB.hBIdle11 j)).2.2.1
  hSlackSeg j _ :=
    uSingleBarrelFolded6Seg_mul_pCoinSlack010Seg (stA.uStageASeg j) (stB.uStageBSeg j)
      (stA.hASlack010 j) (stB.hBSlack010 j)
  hCat48 selOra j _ :=
    uSingleBarrelFolded6Seg_mul_catState48_eq_Mod4OfB selOra (B j) (hB6 j) (hB27 j)
      (stA.uStageASeg j) (stB.uStageBSeg j) (stA.hACat48 j) (stB.hBCat48 j)
end Part4_FastAnchorPolyAndBundles
end BoothOpt_FastAnchorOuterAndStageBShave
namespace SlimStageBOuterDeps
export SingleBarrel8StepClean (FoldedPass123Bundle179_11)
export BoothOpt_Anchor218CachedTrueSwapOuter (StageAAnchorInput179_11 StageBAnchorInput179_11)
export BoothOpt_FastAnchorOuterAndStageBShave
  (DiagCtxWG dPreCoreAnchor64x4Fast dPreAnchor64x4Fast FoldedPass123CircuitSpecCore_mWork
  FoldedPass123CircuitSpec_mWork rAnchor18OfMWork rWorkRemOfMWork
  rAnchor18OfMWork_disj_rWorkRemOfMWork mkFoldedPass123Bundle179_11_FastAnchorStandalone)
end SlimStageBOuterDeps
end SharedScope
end
end SlimStageBOuterDeps

noncomputable section InnerSwapAnchorOfStr

section
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
section SharedScope
local instance (priority := 1000000) instNeZeroK8 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
local instance (priority :=
  1000000) instGroupUnitaryFast03b0l (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast03b0l (D : ℕ) : Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open StageADeconstrCore
  (selDataInAct selMeasInAct concat_compose_selDataInAct concat_compose_selMeasInAct
  selDataInAct_disj_selMeasInAct)
namespace StageADeconstrAndQftShare
open LocalClassicalPerm SpecsAux
open SpecsAux.SpecMirror OctahedralOrbit PosSlots24BranchConcrete
open PosSlots24CompactHead123 PosHeadRev18CacheAux
open StageAConjHAndStreamBridge
open BoothOpt_Anchor218CachedTrueSwapOuter
open scoped ComplexOrder MatrixOrder Circuit.Notation
section Part4_AnchorStageA48062
open CanonRank7Circuit
open HoistBorrow42ProjBridge (RealizesOnProj)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_concat_left disjointWires_compose_of_disjoint)
open NuclearTwistRealizes (slot2AxisSum)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSum0 qreg_ext qreg_block_apply)
open HeldMsbInc7Sandwich288 (basisOutcomeProjector_zero_concat_eq_mul)
open PosPostPrep80MergedVep (cSwapCore3967 uSwapCore3967 uSwapCore3967_mul_self)
open Leaf4Ext48TopStitch (rCoreFull_disj_rSum0 rPGIdle hSum0_disj_PGIdle pPGIdleZero)
open DoubleDutyFoldedRealizesBridge
  (selPosCoreInCore80 rPG7Full hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full)
open GridGuard654ReflAux
  (symWrapDynList symWrapDynList_count_TOFF symWrapDynList_count_T ValidSymStepList symStepFwdList
  symStepFwdList_cons symStepFwdList_append)
open ZeroHypSlot0CommAndHMidClosure (basisOutcomeProjector_zero_mul_self)
open ForestQft117BundleNoTopBridge (pStream218Core)
open MeasureBranchHadamardSem (ket_projZeroAll projZeroAll_eq_basisOutcomeProjector_zero)
theorem basisOutcomeProjector_comm_part4 {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n)
    (r₂ : QRegister k₂ n) (a : Fin (2 ^ k₁)) (b : Fin (2 ^ k₂)) : r₁.basisOutcomeProjector a *
    r₂.basisOutcomeProjector b = r₂.basisOutcomeProjector b * r₁.basisOutcomeProjector a := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
  exact diagonal_comm_op_assoc _ _
theorem realizesOnProj_seq_part4 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {E₁ E₂ V : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)}
    {d₁ d₂ : DynamicCircuit Var n} (hTrans : U₁.1 * E₁ = E₂ * V)
    (h₁ : RealizesOnProj E₁ U₁ d₁) (h₂ : RealizesOnProj E₂ U₂ d₂) : RealizesOnProj E₁
    (U₂ * U₁) (.seq d₁ d₂) := h₁.seq_intertwine hTrans h₂
theorem realizesOnProj_of_clean_proj0 {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)] {rA : QRegister k n} {rW : QRegister m n}
    (hAW : rA.DisjointWires rW) {U : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (h : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rA rW U d) :
    RealizesOnProj (rW.basisOutcomeProjector 0) (rA.embedUnitary U) d := by
  have h1 := RealizesOnProj.of_clean_embed hAW (1 : Operator (2 ^ k)) h
  rwa [QRegister.embedMatrix_one, Matrix.one_mul] at h1
theorem E_anchor_mul_right {mWorkSub18 n : ℕ} (E₀ K : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) : E_anchor (E₀ * K) rAct rAnchor18 rWork hAA =
    E_anchor E₀ rAct rAnchor18 rWork hAA * rAct.embedMatrix K := by
  let rAA := rAct.concat rAnchor18 hAA
  have hAAW : rAA.DisjointWires rWork := disjointWires_concat_left hAA hAW hAnW
  have hLoc : E_anchorLoc (E₀ * K) =
      E_anchorLoc E₀ * (selDataInAct kFull80).embedMatrix K := by
    unfold E_anchorLoc
    rw [(selDataInAct kFull80).embedMatrix_mul, Matrix.mul_assoc _ _ P_anc0,
        selDataInAct_embedMatrix_comm_P_anc0 K]
    simp only [Matrix.mul_assoc]
  have hDataK : rAA.embedMatrix ((selDataInAct kFull80).embedMatrix K) = rAct.embedMatrix K := by
    rw [← QRegister.embedMatrix_compose, concat_compose_selDataInAct]
  unfold E_anchor
  change rAA.embedMatrix (E_anchorLoc (E₀ * K)) * rWork.basisOutcomeProjector 0 =
    (rAA.embedMatrix (E_anchorLoc E₀) * rWork.basisOutcomeProjector 0) * rAct.embedMatrix K
  calc rAA.embedMatrix (E_anchorLoc (E₀ * K)) * rWork.basisOutcomeProjector 0
      = rAA.embedMatrix (E_anchorLoc E₀) *
          (rAA.embedMatrix ((selDataInAct kFull80).embedMatrix K) *
            rWork.basisOutcomeProjector 0) := by
          rw [hLoc, rAA.embedMatrix_mul, Matrix.mul_assoc]
    _ = rAA.embedMatrix (E_anchorLoc E₀) * (rWork.basisOutcomeProjector 0 * rAct.embedMatrix K) :=
      by
          rw [(QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAA) rWork hAAW
                ((selDataInAct kFull80).embedMatrix K) 0, hDataK]
    _ = (rAA.embedMatrix (E_anchorLoc E₀) * rWork.basisOutcomeProjector 0) * rAct.embedMatrix K :=
      by
          rw [← Matrix.mul_assoc]
-- Pebbled `RealizesOnProj` bridge (`Pass1BarrelIdxPebbled273`) & `symWrapDynList` combinator
abbrev PebRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (P U : Operator (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  Pass1BarrelIdxPebbled273.RealizesOnProj P U d
theorem pebRealizes_iff_realizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {P : Operator (2 ^ n)} (hP : Pᴴ = P) (U : Unitary (2 ^ n))
    (d : DynamicCircuit Var n) : PebRealizes P U.1 d ↔ RealizesOnProj P U d := by
  simp only [PebRealizes, Pass1BarrelIdxPebbled273.RealizesOnProj,
    RealizesOnProj, hP]
theorem unitary_eq_involutivePermUnitary_of_mulVec {n : ℕ} {V : Unitary (2 ^ n)}
    {f : BitAssignment n → BitAssignment n} (hf : Function.Involutive f) (hV : ∀ β :
    BitAssignment n, V.1.mulVec (basisKet β) = basisKet (f β)) : V = involutivePermUnitary f
    hf := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [ket_involutivePermUnitary, ket_eq_basisKet, ket_eq_basisKet, hV]
theorem involutivePermUnitary_conjTranspose {m : ℕ}
    (f : BitAssignment m → BitAssignment m) (hf : Function.Involutive f) :
    (involutivePermUnitary f hf).1ᴴ = (involutivePermUnitary f hf).1 := by
  have hinv : (involutivePermUnitary f hf)⁻¹ = involutivePermUnitary f hf :=
    mul_eq_one_iff_inv_eq.mp (involutivePermUnitary_mul_self f hf)
  rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, hinv]
theorem uStepAnd_involutive {n : ℕ} (s : SymTempAndStep n) :
    Function.Involutive (fun β : BitAssignment n ↦
      Function.update β s.anc (β s.anc + β s.c₁ * β s.c₂)) := by
  intro β; funext w
  by_cases hw : w = s.anc
  · subst hw
    simp [Function.update_self, Function.update_of_ne s.h₁a, Function.update_of_ne s.h₂a]
  · simp [Function.update_of_ne hw]
noncomputable def uStepAnd {n : ℕ} (s : SymTempAndStep n) : Unitary (2 ^ n) :=
    involutivePermUnitary (fun β ↦ Function.update β s.anc (β s.anc + β s.c₁ * β s.c₂))
    (uStepAnd_involutive s)
theorem uStepAnd_conjTranspose {n : ℕ} (s : SymTempAndStep n) : (uStepAnd s).1ᴴ =
    (uStepAnd s).1 := involutivePermUnitary_conjTranspose _ _
theorem ket_uStepAnd {n : ℕ} (s : SymTempAndStep n) (β : BitAssignment n) :
    (uStepAnd s).1.mulVec (ket β) = ket (Function.update β s.anc (β s.anc + β s.c₁ * β s.c₂))
    := ket_involutivePermUnitary _ _ β
noncomputable def uSymStepFwd {n : ℕ} (s : SymTempAndStep n) : Unitary (2 ^ n) :=
  s.midPre.eval * (uStepAnd s * s.pre.eval)
theorem ket_uSymStepFwd {n : ℕ} (s : SymTempAndStep n) (β : BitAssignment n) :
    (uSymStepFwd s).1.mulVec (ket β) = ket (s.stepFwd β) := by
  dsimp only [uSymStepFwd, SymTempAndStep.stepFwd]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  have hpre : s.pre.eval.1.mulVec (ket β) = ket (s.f_pre β) := by
    simpa only [ket_eq_basisKet] using s.local_pre.perm β
  have hmid : ∀ γ, s.midPre.eval.1.mulVec (ket γ) = ket (s.f_midPre γ) := fun γ ↦ by
    simpa only [ket_eq_basisKet] using s.local_midPre.perm γ
  rw [hpre, ket_uStepAnd, hmid]
noncomputable def uSymStepFwdList {n : ℕ} : List (SymTempAndStep n) → Unitary (2 ^ n)
  | [] => 1
  | s :: rest => uSymStepFwdList rest * uSymStepFwd s
theorem ket_uSymStepFwdList {n : ℕ} (L : List (SymTempAndStep n)) (β : BitAssignment n) :
    (uSymStepFwdList L).1.mulVec (ket β) = ket (symStepFwdList L β) := by
  induction L generalizing β with
  | nil => simp [uSymStepFwdList]
  | cons s rest ih =>
      simp only [uSymStepFwdList, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ket_uSymStepFwd, ih, symStepFwdList_cons]
theorem eval_eq_inv_of_classicalPerm_id {n : ℕ} {c₁ c₂ : Circuit n}
    {f₁ f₂ : BitAssignment n → BitAssignment n} (h₁ : ClassicalPerm c₁ f₁)
    (h₂ : ClassicalPerm c₂ f₂) (hid : ∀ β, f₂ (f₁ β) = β) : c₂.eval = c₁.eval⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Subtype.ext (matrix_ext_ket fun β ↦ ?_))
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [ket_eq_basisKet, h₁ β, h₂ (f₁ β), hid β]
theorem singleton_proj0_mul_reg_proj0 {m n : ℕ} (r : QRegister m n) (q : Fin m) :
    (QRegister.singleton (r q)).basisOutcomeProjector 0 * r.basisOutcomeProjector 0 =
      r.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      diagonal_mul_diagonal_op_assoc]
  apply congrArg Matrix.diagonal; funext x
  by_cases h : r.extractIndex x = 0
  · have hq : (QRegister.singleton (r q)).extractIndex x = 0 := by
      apply eq_of_basisBits_eq; intro i; fin_cases i
      rw [basisBits_extractIndex_assoc]
      change basisBits n x (r q) = basisBits 1 0 0
      rw [← basisBits_extractIndex_assoc r x q, h]
      simp [-Nat.reducePow, basisBits_eq_div_mod]
    simp [h, hq]
  · simp [h]
private theorem conj_herm_part4 {D : ℕ} {P : Operator D} (U : Operator D) (hP : Pᴴ = P) :
    (U * P * Uᴴ)ᴴ = U * P * Uᴴ := by
  simp [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
private theorem conj_unitary_mul_part4 {D : ℕ} (U : Unitary D) (A B : Operator D) :
    (U.1 * A * U.1ᴴ) * (U.1 * B * U.1ᴴ) = U.1 * (A * B) * U.1ᴴ := by
  calc (U.1 * A * U.1ᴴ) * (U.1 * B * U.1ᴴ)
      = U.1 * A * (U.1ᴴ * U.1) * B * U.1ᴴ := by simp only [Matrix.mul_assoc]
    _ = U.1 * (A * B) * U.1ᴴ := by
          rw [← Matrix.star_eq_conjTranspose U.1, Matrix.mem_unitaryGroup_iff'.mp U.2,
              Matrix.mul_one, Matrix.mul_assoc U.1 A B]
theorem realizesOnProj_symWrapDynList {Var : Type} [Fintype Var] [DecidableEq Var]
    {m_anc n : ℕ} [NeZero (2 ^ n)] (v : Var) (rAnc : QRegister m_anc n) :
    ∀ (offset : ℕ) (L : List (SymTempAndStep n)) {P U : Operator (2 ^ n)}
      {d : DynamicCircuit Var n}, ValidSymStepList (∅ : Finset (Wire n)) rAnc offset L →
      Pᴴ = P → Pass1BarrelIdxPebbled273.HasCleanTailFrom rAnc offset P →
      Pass1BarrelIdxPebbled273.HasCleanTailFrom rAnc offset (U * P) →
      PebRealizes ((uSymStepFwdList L).1 * P * (uSymStepFwdList L).1ᴴ)
        ((uSymStepFwdList L).1 * U * (uSymStepFwdList L).1ᴴ) d →
      PebRealizes P U (symWrapDynList v L d)
  | _, [], _, _, _, _, _, _, _, hd => by
      simpa [uSymStepFwdList, symWrapDynList, TempAndStep.wrapDynamicList] using hd
  | offset, s :: rest, P, U, d, hvalid, hP, hP_tail, hU_tail, hd => by
      rcases hvalid with ⟨hlt, hanc, _, hlat, hvalid_rest⟩
      have hpost_inv :=
        eval_eq_inv_of_classicalPerm_id s.local_pre.perm s.local_post.perm s.post_pre_id
      have hmid_inv :=
        eval_eq_inv_of_classicalPerm_id s.local_midPre.perm s.local_midPost.perm s.midPost_midPre_id
      let P₁ := s.pre.eval.1 * P * s.pre.eval.1ᴴ
      let U₁ := s.pre.eval.1 * U * s.pre.eval.1ᴴ
      have hP₁_herm : P₁ᴴ = P₁ := conj_herm_part4 s.pre.eval.1 hP
      have hUP₁ : U₁ * P₁ = s.pre.eval.1 * (U * P) * s.pre.eval.1ᴴ :=
        conj_unitary_mul_part4 s.pre.eval U P
      let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
      have hPreDisj : Disjoint s.pre.support (QRegister.singleton s.anc).image := by
        rw [Finset.disjoint_right]; intro w hw
        obtain ⟨i, rfl⟩ := (QRegister.mem_image _ w).mp hw; fin_cases i; exact s.anc_not_mem_pre
      have hPreComm : P₀ * s.pre.eval.1 = s.pre.eval.1 * P₀ :=
        ((CircuitExt.eval_comm_basisOutcomeProjector_of_disjoint_support s.pre)
          (QRegister.singleton s.anc) hPreDisj 0).symm
      have hP₀_P : P₀ * P = P := by dsimp only [P₀]; rw [hanc]; exact hP_tail ⟨offset, hlt⟩ le_rfl
      have hP₀_UP : P₀ * (U * P) = U * P := by
        dsimp only [P₀]; rw [hanc]; exact hU_tail ⟨offset, hlt⟩ le_rfl
      have hP₁₀ : P₀ * P₁ = P₁ := by
        dsimp only [P₁]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPreComm, Matrix.mul_assoc s.pre.eval.1 P₀ P,
          hP₀_P]
      have hU₁₀ : P₀ * (U₁ * P₁) = U₁ * P₁ := by
        rw [hUP₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPreComm,
            Matrix.mul_assoc s.pre.eval.1 P₀ (U * P), hP₀_UP]
      let P₃ := (uSymStepFwd s).1 * P * (uSymStepFwd s).1ᴴ
      let U₃ := (uSymStepFwd s).1 * U * (uSymStepFwd s).1ᴴ
      have hP₃_herm : P₃ᴴ = P₃ := conj_herm_part4 (uSymStepFwd s).1 hP
      have hUP₃ : U₃ * P₃ = (uSymStepFwd s).1 * (U * P) * (uSymStepFwd s).1ᴴ :=
        conj_unitary_mul_part4 (uSymStepFwd s) U P
      have hfix : ∀ (β : BitAssignment n) (q : Fin m_anc), offset + 1 ≤ q.val →
          s.stepFwd β (rAnc q) = β (rAnc q) := fun β q hq ↦ s.stepFwd_outside β (hlat q (by omega))
      have hP₃_tail :=
        Pass1BarrelIdxPebbled273.HasCleanTailFrom.conj_perm
          (uSymStepFwd s) s.stepFwd (ket_uSymStepFwd s) hfix (Nat.le_succ offset) hP_tail
      have hU₃_tail : Pass1BarrelIdxPebbled273.HasCleanTailFrom rAnc
          (offset + 1) (U₃ * P₃) := by
        rw [hUP₃]
        exact Pass1BarrelIdxPebbled273.HasCleanTailFrom.conj_perm
          (uSymStepFwd s) s.stepFwd (ket_uSymStepFwd s) hfix (Nat.le_succ offset) hU_tail
      have hd_rest : PebRealizes ((uSymStepFwdList rest).1 * P₃ * (uSymStepFwdList rest).1ᴴ)
          ((uSymStepFwdList rest).1 * U₃ * (uSymStepFwdList rest).1ᴴ) d := by
        have hP_eq : (uSymStepFwdList rest).1 * P₃ * (uSymStepFwdList rest).1ᴴ =
            (uSymStepFwdList (s :: rest)).1 * P * (uSymStepFwdList (s :: rest)).1ᴴ := by
          dsimp only [uSymStepFwdList, P₃]
          simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        have hU_eq : (uSymStepFwdList rest).1 * U₃ * (uSymStepFwdList rest).1ᴴ =
            (uSymStepFwdList (s :: rest)).1 * U * (uSymStepFwdList (s :: rest)).1ᴴ := by
          dsimp only [uSymStepFwdList, U₃]
          simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rwa [hP_eq, hU_eq]
      have hRest := realizesOnProj_symWrapDynList v rAnc (offset + 1) rest
        hvalid_rest hP₃_herm hP₃_tail hU₃_tail hd_rest
      have hMidWrap : PebRealizes ((uStepAnd s).1 * P₁ * (uStepAnd s).1)
          ((uStepAnd s).1 * U₁ * (uStepAnd s).1) (.seq (.circuit s.midPre) (.seq
          (symWrapDynList v rest d) (.circuit s.midPost))) := by
        have hP₃_unf : s.midPre.eval.1 * ((uStepAnd s).1 * P₁ * (uStepAnd s).1) * s.midPre.eval.1ᴴ =
          P₃ := by
          dsimp only [P₃, P₁, uSymStepFwd]
          simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, uStepAnd_conjTranspose,
            Matrix.mul_assoc]
        have hU₃_unf : s.midPre.eval.1 * ((uStepAnd s).1 * U₁ * (uStepAnd s).1) * s.midPre.eval.1ᴴ =
          U₃ := by
          dsimp only [U₃, U₁, uSymStepFwd]
          simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, uStepAnd_conjTranspose,
            Matrix.mul_assoc]
        refine Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit
          s.midPre s.midPost hmid_inv ?_
        rwa [hP₃_unf, hU₃_unf]
      have hAndEval : (StageADeconstrCore.toffCirc s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a
          s.h₂a).eval.1 = (uStepAnd s).1 := congrArg Subtype.val
          (unitary_eq_involutivePermUnitary_of_mulVec (uStepAnd_involutive s)
          (evolve_TOFF_basisKet s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a))
      have hTemp : PebRealizes P₁ U₁ (.seq (DynamicCircuit.andCompute s.c₁ s.c₂ s.anc s.h₁a
          s.h₂a) (.seq (.seq (.circuit s.midPre) (.seq (symWrapDynList v rest d) (.circuit
          s.midPost))) (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂))) := by
        refine Pass1BarrelIdxPebbled273.RealizesOnProj.withTempAnd
          v s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a hP₁_herm hP₁₀ hU₁₀ ?_
        change PebRealizes _ _ _; rw [hAndEval]; exact hMidWrap
      exact Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit
        s.pre s.post hpost_inv hTemp
-- Carry bits of `zTargetSteps36` & `uXorCarry18` single-sum diagonal decomposition
theorem zTargetSteps36_eval_carry {n : ℕ} (rCore : QRegister posCoreWires n)
    (rHold36 : QRegister 36 n) (hCW : rCore.DisjointWires rHold36) (β : BitAssignment n)
    (hClean : ∀ idx : Fin 36, β (rHold36 idx) = 0) (k : Fin 18) :
    (symStepFwdList (zTargetSteps36 (le_refl 36) rCore rHold36 hCW) β)
      (rHold36 ⟨k.val, by have := k.isLt; omega⟩) =
      carryBit18Pos (fun i ↦ β (rCore i)) k := by
  have hCM : Disjoint rCore.image (∅ : Finset (Wire n)) := Finset.disjoint_empty_right _
  have hWM : Disjoint rHold36.image (∅ : Finset (Wire n)) := Finset.disjoint_empty_right _
  obtain ⟨_, heC0⟩ :=
    zTargetAxisCarrySteps_valid_and_eval (le_refl 36) rCore rHold36 hCW 0 ∅ hCM hWM
  obtain ⟨_, heC1⟩ :=
    zTargetAxisCarrySteps_valid_and_eval (le_refl 36) rCore rHold36 hCW 1 ∅ hCM hWM
  obtain ⟨_, heC2⟩ :=
    zTargetAxisCarrySteps_valid_and_eval (le_refl 36) rCore rHold36 hCW 2 ∅ hCM hWM
  obtain ⟨_, heM0⟩ := zTargetAxisMuxSteps_valid_and_eval (le_refl 36) rCore rHold36 hCW 0 ∅ hCM hWM
  obtain ⟨_, heM1⟩ := zTargetAxisMuxSteps_valid_and_eval (le_refl 36) rCore rHold36 hCW 1 ∅ hCM hWM
  obtain ⟨_, heM2⟩ := zTargetAxisMuxSteps_valid_and_eval (le_refl 36) rCore rHold36 hCW 2 ∅ hCM hWM
  let b1 := symStepFwdList (zTargetAxisCarrySteps (le_refl 36) rCore rHold36 hCW 0) β
  let b2 := symStepFwdList (zTargetAxisCarrySteps (le_refl 36) rCore rHold36 hCW 1) b1
  let b3 := symStepFwdList (zTargetAxisCarrySteps (le_refl 36) rCore rHold36 hCW 2) b2
  let b4 := symStepFwdList (zTargetAxisMuxSteps (le_refl 36) rCore rHold36 hCW 0) b3
  let b5 := symStepFwdList (zTargetAxisMuxSteps (le_refl 36) rCore rHold36 hCW 1) b4
  let b6 := symStepFwdList (zTargetAxisMuxSteps (le_refl 36) rCore rHold36 hCW 2) b5
  have hSeq : symStepFwdList (zTargetSteps36 (le_refl 36) rCore rHold36 hCW) β = b6 := by
    dsimp only [zTargetSteps36, b6, b5, b4, b3, b2, b1]; simp only [symStepFwdList_append]
  rw [hSeq]
  have hw_ne (a b : ℕ) (ha : a < 36) (hb : b < 36) (hab : a ≠ b) :
      rHold36 ⟨a, ha⟩ ≠ rHold36 ⟨b, hb⟩ :=
    fun h ↦ hab (congrArg Fin.val (rHold36.wires.injective h))
  have latCore {z : Wire n} (hz : z ∈ rCore.image) (idx : Fin 36) : z ≠ rHold36 idx := fun heq ↦ by
    obtain ⟨i, hi⟩ := (QRegister.mem_image rCore _).mp hz; exact hCW.ne i idx (hi.trans heq)
  obtain ⟨hc0, ho0⟩ :=
    heC0 β (fun j ↦ hClean ⟨6 * (0 : Fin 3).val + j.val, by have := j.isLt; omega⟩)
  obtain ⟨hc1, ho1⟩ := heC1 b1 (fun j ↦ (ho0 _ fun i ↦ hw_ne _ _ _ _
    (by have := j.isLt; have := i.isLt; omega)).trans
      (hClean ⟨6 + j.val, by have := j.isLt; omega⟩))
  have hb2_out (z : Wire n) (hz : ∀ a (ha : a < 12), z ≠ rHold36 ⟨a, by omega⟩) : b2 z = β z :=
    (ho1 z fun i ↦ hz _ (by have := i.isLt; omega)).trans
      (ho0 z fun i ↦ hz _ (by have := i.isLt; omega))
  obtain ⟨hc2, ho2⟩ := heC2 b2 (fun j ↦ (hb2_out _ fun a ha ↦ hw_ne _ _ _ _
    (by have := j.isLt; omega)).trans (hClean ⟨12 + j.val, by have := j.isLt; omega⟩))
  have hb3_out (z : Wire n) (hz : ∀ a (ha : a < 18), z ≠ rHold36 ⟨a, by omega⟩) : b3 z = β z :=
    (ho2 z fun i ↦ hz _ (by have := i.isLt; omega)).trans (hb2_out z fun a ha ↦ hz a (by omega))
  obtain ⟨_, hoM0⟩ := heM0 b3 (fun u ↦ (hb3_out _ fun a ha ↦ hw_ne _ _ _ _
    (by have := u.isLt; omega)).trans (hClean ⟨18 + u.val, by have := u.isLt; omega⟩))
  have hb4_out (z : Wire n) (hz : ∀ a (ha : 18 ≤ a ∧ a < 24), z ≠ rHold36 ⟨a, by omega⟩) :
      b4 z = b3 z :=
    hoM0 z fun i ↦ hz _ ⟨by omega, by have := i.isLt; omega⟩
  obtain ⟨_, hoM1⟩ := heM1 b4 (fun u ↦ (hb4_out _ fun a ha ↦ hw_ne _ _ _ _ (by omega)).trans
    ((hb3_out _ fun a ha ↦ hw_ne _ _ _ _ (by omega)).trans
      (hClean ⟨24 + u.val, by have := u.isLt; omega⟩)))
  obtain ⟨_, hoM2⟩ := heM2 b5 (fun u ↦ (hoM1 _ fun i ↦ hw_ne _ _ _ _
    (by have := u.isLt; have := i.isLt; omega)).trans ((hb4_out _ fun a ha ↦ hw_ne _ _ _ _
      (by omega)).trans ((hb3_out _ fun a ha ↦ hw_ne _ _ _ _ (by omega)).trans
      (hClean ⟨30 + u.val, by have := u.isLt; omega⟩))))
  have hb6_b3 : b6 (rHold36 ⟨k.val, by have := k.isLt; omega⟩) =
      b3 (rHold36 ⟨k.val, by have := k.isLt; omega⟩) :=
    (hoM2 _ fun u ↦ hw_ne _ _ _ _ (by have := k.isLt; have := u.isLt; omega)).trans
      ((hoM1 _ fun u ↦ hw_ne _ _ _ _ (by have := k.isLt; have := u.isLt; omega)).trans
        (hb4_out _ fun a ha ↦ hw_ne _ _ _ _ (by have := k.isLt; omega)))
  rw [hb6_b3]
  let w : Fin 3 := ⟨k.val / 6, by have := k.isLt; omega⟩
  let j : Fin 6 := ⟨k.val % 6, by omega⟩
  have hk_idx : (⟨k.val, by have := k.isLt; omega⟩ : Fin 36) =
      ⟨6 * w.val + j.val, by have := w.isLt; have := j.isLt; omega⟩ :=
    Fin.ext (by dsimp only [w, j]; omega)
  rw [hk_idx]
  unfold carryBit18Pos
  let dSeq (b : BitAssignment n) (w₀ : Fin 3) : Fin 6 → ZMod 2 := fun i ↦
    b (rHeadFine21 rCore ⟨7 * w₀.val + i.val + 1, by have := w₀.isLt; have := i.isLt; omega⟩)
  let cIn (b : BitAssignment n) (w₀ : Fin 3) : ZMod 2 :=
    1 + (b (rCosetB0 rCore w₀) + 1) * b (rHeadFine21 rCore ⟨7 * w₀.val, by have := w₀.isLt; omega⟩)
  change b3 (rHold36 ⟨6 * w.val + j.val, _⟩) =
    carrySeq6 (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) w i)) (dSeq β w) (cIn β w) j.val
  have hCarryCore (w₀ : Fin 3) (b : BitAssignment n)
      (hCore : ∀ {z}, z ∈ rCore.image → b z = β z) :
      carrySeq6 (fun i ↦ b (axisBitRev6 (rElecSlot rCore 0) w₀ i)) (dSeq b w₀) (cIn b w₀) j.val =
      carrySeq6 (fun i ↦ β (axisBitRev6 (rElecSlot rCore 0) w₀ i)) (dSeq β w₀) (cIn β w₀)
        j.val := by
    dsimp only [dSeq, cIn]
    rw [show (fun i : Fin 6 ↦ b (axisBitRev6 (rElecSlot rCore 0) w₀ i)) = _ from
          funext fun i ↦ hCore (phcHead_y0_mem_core rCore w₀ i),
        show (fun i : Fin 6 ↦ b (rHeadFine21 rCore ⟨7 * w₀.val + i.val + 1, _⟩)) = _ from
          funext fun i ↦ hCore (phcHead_dBit_mem_core rCore _),
        hCore (phcHead_b0_mem_core rCore w₀), hCore (phcHead_dBit_mem_core rCore _)]
  have hw3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hw3 w with hw | hw | hw
  · simp only [hw]
    exact (ho2 _ fun i ↦ hw_ne _ _ _ _ (by dsimp; have := j.isLt; have := i.isLt; omega)).trans
      ((ho1 _ fun i ↦ hw_ne _ _ _ _ (by dsimp; have := j.isLt; have := i.isLt; omega)).trans
        (hc0 j))
  · simp only [hw]
    exact (ho2 _ fun i ↦ hw_ne _ _ _ _ (by dsimp; have := j.isLt; have := i.isLt; omega)).trans
      ((hc1 j).trans (hCarryCore 1 b1 fun hz ↦ ho0 _ fun _ ↦ latCore hz _))
  · simp only [hw]
    exact (hc2 j).trans (hCarryCore 2 b2 fun hz ↦ hb2_out _ fun _ _ ↦ latCore hz _)
def xorCarryLocalBits (γ : BitAssignment (posCoreWires + 18)) :
    BitAssignment (posCoreWires + 18) :=
  let γCore : BitAssignment posCoreWires := fun i ↦ γ ⟨i.val, by have := i.isLt; omega⟩
  fun idx ↦
    if h : idx.val < posCoreWires then γ idx
    else γ idx + carryBit18Pos γCore ⟨idx.val - posCoreWires, by have := idx.isLt; omega⟩
theorem xorCarryLocalBits_involutive : Function.Involutive xorCarryLocalBits := by
  intro γ; funext idx
  have hCoreEq : (fun i : Fin posCoreWires ↦
    xorCarryLocalBits γ ⟨i.val, by have := i.isLt; omega⟩) =
      fun i : Fin posCoreWires ↦ γ ⟨i.val, by have := i.isLt; omega⟩ := by
    funext i; simp [xorCarryLocalBits, i.isLt]
  conv_lhs => rw [xorCarryLocalBits]
  rw [hCoreEq]
  by_cases h : idx.val < posCoreWires
  · simp [h, xorCarryLocalBits]
  · simp [h, xorCarryLocalBits, add_assoc, CharTwo.add_self_eq_zero]
noncomputable def uXorCarry18 : Unitary (2 ^ (posCoreWires + 18)) :=
  involutivePermUnitary xorCarryLocalBits xorCarryLocalBits_involutive
theorem uXorCarry18_mul_self : uXorCarry18 * uXorCarry18 = 1 :=
  involutivePermUnitary_mul_self xorCarryLocalBits xorCarryLocalBits_involutive
theorem ket_embedUnitary_uXorCarry18 {n : ℕ} (rCore : QRegister posCoreWires n)
    (rCarry : QRegister 18 n) (hCC : rCore.DisjointWires rCarry) (β : BitAssignment n) :
    ((rCore.concat rCarry hCC).embedUnitary uXorCarry18).1.mulVec (ket β) = ket (writeReg β
    rCarry fun k ↦ β (rCarry k) + carryBit18Pos (fun i ↦ β (rCore i)) k) := by
  let rCC := rCore.concat rCarry hCC
  rw [uXorCarry18, ket_embedUnitary_involutivePermUnitary]
  refine congrArg ket (funext fun z ↦ ?_)
  have hCoreLoc : (fun i : Fin posCoreWires ↦ β (rCC ⟨i.val, by have := i.isLt; omega⟩)) =
      fun i : Fin posCoreWires ↦ β (rCore i) := by
    funext i
    exact congrArg β (QRegister.concat_apply_left rCore rCarry hCC i)
  by_cases hT : ∃ k : Fin 18, rCarry k = z
  · obtain ⟨k, rfl⟩ := hT
    have hkCC : rCC ⟨posCoreWires + k.val, by have := k.isLt; omega⟩ = rCarry k :=
      QRegister.concat_apply_right rCore rCarry hCC k
    rw [← hkCC, writeReg_apply_reg, hkCC, writeReg_apply_reg]
    dsimp only [xorCarryLocalBits]
    have hnot : ¬ (posCoreWires + k.val < posCoreWires) := by omega
    rw [dite_eq_right hnot, hkCC, hCoreLoc]
    have hsub : (⟨posCoreWires + k.val - posCoreWires, by have := k.isLt; omega⟩ : Fin 18) = k :=
      Fin.ext (by dsimp only; omega)
    rw [hsub]
  · have hT' : z ∉ Set.range rCarry.wires := hT
    rw [writeReg_apply_of_not_mem _ _ _ _ hT']
    by_cases hC : ∃ i : Fin posCoreWires, rCore i = z
    · obtain ⟨i, rfl⟩ := hC
      have hiCC : rCC ⟨i.val, by have := i.isLt; omega⟩ = rCore i :=
        QRegister.concat_apply_left rCore rCarry hCC i
      rw [← hiCC, writeReg_apply_reg]
      dsimp only [xorCarryLocalBits]
      rw [dite_eq_left i.isLt]
    · have hCC' : z ∉ Set.range rCC.wires := by
        rintro ⟨idx, hidx⟩
        dsimp only [rCC] at hidx
        refine Fin.addCases
          (motive := fun idx ↦ (rCore.concat rCarry hCC) idx = z → False)
          (fun i hEq ↦ hC ⟨i, by rwa [QRegister.concat_apply_left] at hEq⟩)
          (fun k hEq ↦ hT ⟨k, by rwa [QRegister.concat_apply_right] at hEq⟩)
          idx hidx
      exact writeReg_apply_of_not_mem _ _ _ _ hCC'
noncomputable def uXorConstGen {m : ℕ} (u : Fin (2 ^ m)) : Unitary (2 ^ m) :=
  involutivePermUnitary (fun γ k ↦ γ k + basisBits m u k)
    (fun γ ↦ funext fun k ↦ by dsimp only; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])
noncomputable abbrev uXorConst18 (u : Fin (2 ^ 18)) : Unitary (2 ^ 18) := uXorConstGen u
theorem embedUnitary_uXorGen_eq_sum_diag {m kCore kAAZ n : ℕ}
    (fBit : BitAssignment kCore → BitAssignment m) (uXorFull : Unitary (2 ^ (kCore + m)))
    (hFull : ∀ (rC : QRegister kCore n) (rT : QRegister m n) (hCT : rC.DisjointWires rT) (β :
    BitAssignment n), ((rC.concat rT hCT).embedUnitary uXorFull).1.mulVec (ket β) = ket
    (writeReg β rT fun k ↦ β (rT k) + fBit (fun i ↦ β (rC i)) k))
    (idxAAZ : Fin (2 ^ kAAZ) → Fin (2 ^ m)) (D_diag : Fin (2 ^ m) → Operator (2 ^ kAAZ)) (hD :
    ∀ u : Fin (2 ^ m), D_diag u = Matrix.diagonal (fun x ↦ if idxAAZ x = u then (1 : ℂ) else
    0)) (rAAZ : QRegister kAAZ n) (rC : QRegister kCore n) (rT : QRegister m n)
    (hCT : rC.DisjointWires rT) (hIdx : ∀ (β : BitAssignment n) (u : Fin (2 ^ m)), idxAAZ
    (rAAZ.extractIndex ((basisBitsEquiv n).symm (writeReg β rT fun k ↦ β (rT k) + basisBits m
    u k))) = (basisBitsEquiv m).symm (fBit (fun i ↦ β (rC i)))) :
    ((rC.concat rT hCT).embedUnitary uXorFull).1 = ∑ u : Fin (2 ^ m), rAAZ.embedMatrix
    (D_diag u) * (rT.embedUnitary (uXorConstGen u)).1 := by
  apply matrix_ext_ket; intro β
  rw [hFull rC rT hCT β, Matrix.sum_mulVec]
  let u₀ : Fin (2 ^ m) := (basisBitsEquiv m).symm (fBit (fun i ↦ β (rC i)))
  have hTerm : ∀ u : Fin (2 ^ m), (rAAZ.embedMatrix (D_diag u) * (rT.embedUnitary
      (uXorConstGen u)).1).mulVec (ket β) = if u₀ = u then ket
      (writeReg β rT fun k ↦ β (rT k) + basisBits m u k) else 0 := by
    intro u
    let γ := writeReg β rT fun k ↦ β (rT k) + basisBits m u k
    have hX : (rT.embedUnitary (uXorConstGen u)).1.mulVec (ket β) = ket γ := by
      rw [uXorConstGen, ket_embedUnitary_involutivePermUnitary]
    rw [← Matrix.mulVec_mulVec, hX, hD u, embedMatrix_diagonal_local, diagonal_mulVec_ket_assoc,
      hIdx β u]
    change (if u₀ = u then (1 : ℂ) else 0) • ket γ = if u₀ = u then ket γ else 0
    by_cases hu : u₀ = u
    · rw [ite_eq_left hu, ite_eq_left hu, one_smul]
    · rw [ite_eq_right hu, ite_eq_right hu, zero_smul]
  simp only [hTerm, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hu₀ : basisBits m u₀ = fBit (fun i ↦ β (rC i)) := basisBits_basisBitsEquiv_symm _
  simp only [hu₀]
theorem sum_mul_comm_part4 {ι : Type*} [Fintype ι] {D : ℕ}
    (F : ι → Operator D) (K : Operator D) (h : ∀ u, F u * K = K * F u) :
    (∑ u : ι, F u) * K = K * (∑ u : ι, F u) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ ↦ h u
theorem mul_sum_mul_part4 {ι : Type*} [Fintype ι] {D : ℕ} (U : Operator D) (F : ι → Operator D)
    (K : Operator D) (h : ∀ u, U * (F u * K) = F u * (U * K)) : U * ((∑ u : ι, F u) * K) =
    (∑ u : ι, F u) * (U * K) := by
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ ↦ h u
theorem embedUnitary_uXorCarry18_eq_sum_D_carry {n : ℕ}
    (rAAZ : QRegister ((kFull80 + 18) + 18) n) (rSubstPos : QRegister posCoreWires n)
    (rCarry18 : QRegister 18 n) (hSubPCarry : rSubstPos.DisjointWires rCarry18) (hCompSubPos :
    rAAZ.compose (selAAZ_Subst.compose rPosCoreInFull) = rSubstPos) :
    ((rSubstPos.concat rCarry18 hSubPCarry).embedUnitary uXorCarry18).1 = ∑ u : Fin (2 ^ 18),
    rAAZ.embedMatrix (D_carry_AAZ u) * (rCarry18.embedUnitary (uXorConst18 u)).1 := by
  refine embedUnitary_uXorGen_eq_sum_diag carryBit18Pos uXorCarry18
    (fun rC rT hCT β ↦ ket_embedUnitary_uXorCarry18 rC rT hCT β)
    carryIdx18_AAZ D_carry_AAZ (fun _ ↦ rfl) rAAZ rSubstPos rCarry18 hSubPCarry (fun β u ↦ ?_)
  unfold carryIdx18_AAZ
  apply congrArg (basisBitsEquiv 18).symm
  apply congrArg carryBit18Pos
  funext i
  rw [basisBits_extractIndex_assoc, ← QRegister.compose_apply rAAZ, hCompSubPos,
      basisBits_basisBitsEquiv_symm]
  exact writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦ hSubPCarry.ne i k hk.symm)
/-- `36`-wire pebbled target/carry slice `rWork[0..36)`. -/
abbrev rHold36OfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) : QRegister 36 n := rWork.slice 0 36 (by omega)
/-- `18`-wire carry slice `rWork[0..18)`. -/
abbrev rCarry18OfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) : QRegister 18 n := rWork.slice 0 18 (by omega)
/-- `18`-wire target slice `rWork[18..36)`. -/
abbrev rZ18OfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) : QRegister 18 n := rWork.slice 18 18 (by omega)
/-- `(mWorkSub18 - 36)`-wire tail workspace slice `rWork[36..mWorkSub18)`. -/
abbrev rWRestOfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) : QRegister (mWorkSub18 - 36) n :=
  rWork.slice 36 (mWorkSub18 - 36) (by omega)
theorem rCarry18OfSub18_disj_rZ18OfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) :
    (rCarry18OfSub18 hm36 rWork).DisjointWires (rZ18OfSub18 hm36 rWork) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val (rWork.wires.injective hij)
  simp at hv; omega
theorem rZ18OfSub18_disj_rWRestOfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) :
    (rZ18OfSub18 hm36 rWork).DisjointWires (rWRestOfSub18 hm36 rWork) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val (rWork.wires.injective hij)
  simp at hv; omega
theorem rCarry18OfSub18_disj_rWRestOfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) :
    (rCarry18OfSub18 hm36 rWork).DisjointWires (rWRestOfSub18 hm36 rWork) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val (rWork.wires.injective hij)
  simp at hv; omega
theorem rCarry18OfSub18_concat_rZ18OfSub18 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) :
    (rCarry18OfSub18 hm36 rWork).concat (rZ18OfSub18 hm36 rWork)
      (rCarry18OfSub18_disj_rZ18OfSub18 hm36 rWork) = rHold36OfSub18 hm36 rWork := by
  apply qreg_ext; intro idx
  change Fin (18 + 18) at idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.concat_apply_left]
    exact congrArg rWork (Fin.ext (by simp))
  · rw [QRegister.concat_apply_right]
    exact congrArg rWork (Fin.ext (by simp; omega))
theorem rCarry18OfSub18_proj0_mul_rZ18OfSub18_proj0 {mWorkSub18 n : ℕ} (hm36 : 36 ≤ mWorkSub18)
    (rWork : QRegister mWorkSub18 n) : (rCarry18OfSub18 hm36 rWork).basisOutcomeProjector 0 *
    (rZ18OfSub18 hm36 rWork).basisOutcomeProjector 0 =
    (rHold36OfSub18 hm36 rWork).basisOutcomeProjector 0 := by
  rw [← basisOutcomeProjector_zero_concat_eq_mul _ _ (rCarry18OfSub18_disj_rZ18OfSub18 hm36 rWork),
      rCarry18OfSub18_concat_rZ18OfSub18]
theorem rHold36OfSub18_proj0_mul_rWRestOfSub18_proj0 {mWorkSub18 n : ℕ}
    (hm36 : 36 ≤ mWorkSub18) (rWork : QRegister mWorkSub18 n) :
    (rHold36OfSub18 hm36 rWork).basisOutcomeProjector 0 *
    (rWRestOfSub18 hm36 rWork).basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 :=
    (GidneyTwoAngleGuardWrap220.basisOutcomeProjector_zero_slice_split rWork hm36).symm
abbrev StrCallback (Var : Type) (mWorkSub18 n : ℕ) :=
    (rCore : QRegister (fullSysCoreWires 80) n) → (rSum42 : QRegister 42 n) →
    (rW : QRegister ((mWorkSub18 - 36) + 11) n) → rCore.DisjointWires rSum42 →
    rCore.DisjointWires rW → rSum42.DisjointWires rW → DynamicCircuit Var n
/-- Width- and stream-parametric swap-wrapped pebbled inner anchor Stage-A dynamic circuit
(`155 ≤ mWorkSub18`, `16,260 + tStrPair` T-gates, `0` TOFF). -/
noncomputable def dInnerSwapAnchor_ofStr {Var : Type} {mWorkSub18 n : ℕ}
    (hm155 : 155 ≤ mWorkSub18) (v : Var) (dStrAdd dStrInv : StrCallback Var mWorkSub18 n)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) : DynamicCircuit Var n :=
  have hm36 : 36 ≤ mWorkSub18 := by omega
  let rSubst := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  let rHold36 := rHold36OfSub18 hm36 rWork
  let rZ18 := rZ18OfSub18 hm36 rWork
  let rWRest := rWRestOfSub18 hm36 rWork
  let rIdle11 := rAct.compose (rPGIdle 11 (by decide))
  let hWRestIdle : rWRest.DisjointWires rIdle11 :=
    (QRegExt.disjointWires_symm ((hAW.compose_left (rPGIdle 11 (by decide))).compose_right _))
  let rW136 : QRegister ((mWorkSub18 - 36) + 11) n := rWRest.concat rIdle11 hWRestIdle
  let rCore := rAct.compose rCoreFull
  let rSum42 := rAct.compose rSum0
  let rPG7 := rAct.compose rPG7Full
  let hCSum42 := disjointWires_compose_of_disjoint rAct rCoreFull_disj_rSum0
  let hCPG := disjointWires_compose_of_disjoint rAct hCoreFull_disj_rPG7Full
  let hSPG := disjointWires_compose_of_disjoint rAct rSum0_disj_rPG7Full
  let hCW136 : rCore.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rCoreFull).compose_right _)
      (disjointWires_compose_of_disjoint rAct rCoreFull_disj_rPGIdle11)
  let hSW136 : rSum42.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rSum0).compose_right _)
      (disjointWires_compose_of_disjoint rAct (hSum0_disj_PGIdle 11 (by decide)))
  let hPGW136 : rPG7.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rPG7Full).compose_right _)
      (disjointWires_compose_of_disjoint rAct rPG7Full_disj_rPGIdle11)
  let hZW136 : rZ18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (rZ18OfSub18_disj_rWRestOfSub18 hm36 rWork)
      (QRegExt.disjointWires_symm ((hAW.compose_left (rPGIdle 11 (by decide))).compose_right _))
  let hCZ : rCore.DisjointWires rZ18 := (hAW.compose_left rCoreFull).compose_right _
  let hSZ : rSum42.DisjointWires rZ18 := (hAW.compose_left rSum0).compose_right _
  let hPGZ : rPG7.DisjointWires rZ18 := (hAW.compose_left rPG7Full).compose_right _
  let rCS := rCore.concat rSum42 hCSum42
  let hCS_Z := disjointWires_concat_left hCSum42 hCZ hSZ
  let hCS_PG := disjointWires_concat_left hCSum42 hCPG hSPG
  let rHeldAct := (rCS.concat rZ18 hCS_Z).concat rPG7
    (disjointWires_concat_left hCS_Z hCS_PG (QRegExt.disjointWires_symm hPGZ))
  let hCS_W136 := disjointWires_concat_left hCSum42 hCW136 hSW136
  let hHeldW136 : rHeldAct.DisjointWires rW136 :=
    disjointWires_concat_left _ (disjointWires_concat_left hCS_Z hCS_W136 hZW136) hPGW136
  let rSubstPos := rSubst.compose rPosCoreInFull
  let hSubPHold : rSubstPos.DisjointWires rHold36 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hSubPZ : rSubstPos.DisjointWires rZ18 := (hSubW.compose_left rPosCoreInFull).compose_right _
  let hQDisj : (phcHead_rQRev18 rSubstPos).DisjointWires rZ18 :=
    QRegister.disjoint_iff.mpr fun k j heq ↦ by
      obtain ⟨i, hi⟩ := (QRegister.mem_image rSubstPos _).mp (phcHead_rQRev18_mem_core rSubstPos k)
      exact hSubPZ.ne i j (hi.trans heq)
  let rCorePos := rAct.compose rPosCoreInFull
  let rScr178 : QRegister (((mWorkSub18 - 36) + 11) + 42) n :=
    rW136.concat rSum42 (QRegExt.disjointWires_symm hSW136)
  let hCPSum : rCorePos.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rAct (rCoreFull_disj_rSum0.compose_left selPosCoreInCore80)
  let hCPScr : rCorePos.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136)
      (hCW136.compose_left selPosCoreInCore80) hCPSum
  let hAnW136 : rAnchor18.DisjointWires rW136 := disj_concat_right_part4 hWRestIdle
      (hAnW.compose_right _)
        (QRegExt.disjointWires_symm (hAA.compose_left (rPGIdle 11 (by decide))))
  let hAnScr : rAnchor18.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136) hAnW136
      (QRegExt.disjointWires_symm (hAA.compose_left rSum0))
  let cXorQ : Circuit n := copyXorRegCircuit (phcHead_rQRev18 rSubstPos) rZ18 hQDisj
  let dSw : DynamicCircuit Var n := .circuit (cSwapCore3967.onRegister rCore)
  let dPhiF :=
    dPhiOnHeldZ18AnchorFwd128 (by omega : 128 ≤ (mWorkSub18 - 36) + 11) v rHeldAct rW136 hHeldW136
  let dPhiI :=
    dPhiOnHeldZ18AnchorInv128 (by omega : 128 ≤ (mWorkSub18 - 36) + 11) v rHeldAct rW136 hHeldW136
  let dStrI := dStrInv rCore rSum42 rW136 hCSum42 hCW136 hSW136
  let dHead := dHeadAnchorConjH172 (by omega : 172 ≤ ((mWorkSub18 - 36) + 11) + 42) v
    rCorePos rAnchor18 rScr178 (hAA.compose_left rPosCoreInFull) hCPScr hAnScr
  let dStrA := dStrAdd rCore rSum42 rW136 hCSum42 hCW136 hSW136
  let dMid5 : DynamicCircuit Var n := .seq dPhiF (.seq dStrI (.seq dHead (.seq dStrA dPhiI)))
  let dPeb : DynamicCircuit Var n :=
    symWrapDynList v (zTargetSteps36 (le_refl 36) rSubstPos rHold36 hSubPHold)
      (.seq (.circuit cXorQ) (.seq dMid5 (.circuit cXorQ)))
  .seq dSw (.seq dPeb dSw)
@[simp] theorem count_dInnerSwapAnchor_ofStr_toff {Var : Type} {mWorkSub18 n : ℕ}
    (hm155 : 155 ≤ mWorkSub18) (v : Var) (dStrAdd dStrInv : StrCallback Var mWorkSub18 n)
    (hToff : ∀ rC rS rW hCS hCW hSW, (dStrAdd rC rS rW hCS hCW hSW).count TOFF = 0 ∧ (dStrInv
    rC rS rW hCS hCW hSW).count TOFF = 0) (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) : (dInnerSwapAnchor_ofStr hm155 v dStrAdd dStrInv
    rAct rAnchor18 rWork hAA hAW hAnW).count TOFF = 0 := by
  have hAdd := fun rC rS rW hCS hCW hSW ↦ (hToff rC rS rW hCS hCW hSW).1
  have hInv := fun rC rS rW hCS hCW hSW ↦ (hToff rC rS rW hCS hCW hSW).2
  dsimp only [dInnerSwapAnchor_ofStr]
  simp [symWrapDynList_count_TOFF, cSwapCore3967_counts.1, hAdd, hInv]
theorem count_dInnerSwapAnchor_ofStr_t_le {Var : Type} {mWorkSub18 n tStrPair : ℕ}
    (hm155 : 155 ≤ mWorkSub18) (v : Var) (dStrAdd dStrInv : StrCallback Var mWorkSub18 n) (hT
    : ∀ rC rS rW hCS hCW hSW, (dStrAdd rC rS rW hCS hCW hSW).count T + (dStrInv rC rS rW hCS
    hCW hSW).count T ≤ tStrPair) (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dInnerSwapAnchor_ofStr hm155 v dStrAdd dStrInv rAct rAnchor18 rWork hAA hAW hAnW).count T
    ≤ 16260 + tStrPair := by
  have hm36 : 36 ≤ mWorkSub18 := by omega
  let rWRest := rWRestOfSub18 hm36 rWork
  let rIdle11 := rAct.compose (rPGIdle 11 (by decide))
  let hWRestIdle : rWRest.DisjointWires rIdle11 :=
    (QRegExt.disjointWires_symm ((hAW.compose_left (rPGIdle 11 (by decide))).compose_right _))
  let rW136 : QRegister ((mWorkSub18 - 36) + 11) n := rWRest.concat rIdle11 hWRestIdle
  have hStr := hT (rAct.compose rCoreFull) (rAct.compose rSum0) rW136
    (disjointWires_compose_of_disjoint rAct rCoreFull_disj_rSum0)
    (disj_concat_right_part4 hWRestIdle ((hAW.compose_left rCoreFull).compose_right _)
      (disjointWires_compose_of_disjoint rAct rCoreFull_disj_rPGIdle11))
    (disj_concat_right_part4 hWRestIdle ((hAW.compose_left rSum0).compose_right _)
      (disjointWires_compose_of_disjoint rAct (hSum0_disj_PGIdle 11 (by decide))))
  dsimp only [dInnerSwapAnchor_ofStr]
  dsimp only [rW136, rWRest, rIdle11] at hStr
  simp only [DynamicCircuit.count, symWrapDynList_count_T, length_zTargetSteps36]
  have hXorT : ∀ {k : ℕ} {a b : QRegister k n} (h : a.DisjointWires b),
      (copyXorRegCircuit a b h).count T = 0 := fun _ ↦ by simp
  rw [Circuit.count_onRegister, cSwapCore3967_counts.2, hXorT,
      count_dPhiOnHeldZ18AnchorFwd128_t, count_dPhiOnHeldZ18AnchorInv128_t,
      count_dHeadAnchorConjH172_t]
  omega
private theorem unitary_herm_of_sq_one {D : ℕ} {U : Unitary D} (h : U.1 * U.1 = 1) : U.1ᴴ = U.1 :=
  by
  have hinv : U⁻¹ = U := mul_eq_one_iff_inv_eq.mp (Subtype.ext h)
  rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, hinv]
private theorem mul3_comm_of_comm {D : ℕ} {A B C P : Operator D} (hA : A * P = P * A)
    (hB : B * P = P * B) (hC : C * P = P * C) : (A * (B * C)) * P = P * (A * (B * C)) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hC, ← Matrix.mul_assoc B P C, hB,
      Matrix.mul_assoc P B C, ← Matrix.mul_assoc A P, hA, Matrix.mul_assoc]
private theorem herm_mul_of_comm_part4 {D : ℕ} {A B : Operator D}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (hc : A * B = B * A) : (A * B)ᴴ = A * B := by
  rw [Matrix.conjTranspose_mul, hB, hA, hc.symm]
private theorem idem_mul_of_comm_part4 {D : ℕ} {A B : Operator D}
    (hA : A * A = A) (hB : B * B = B) (hc : A * B = B * A) : (A * B) * (A * B) = A * B := by
  calc (A * B) * (A * B) = A * (B * A) * B := by simp only [Matrix.mul_assoc]
    _ = (A * A) * (B * B) := by rw [← hc]; simp only [Matrix.mul_assoc]
    _ = A * B := by rw [hA, hB]
private theorem conj_invol_mid_part4 {D : ℕ} (C X M : Operator D) (hX : X * X = 1) :
    (C * X) * (X * M * X) * (X * Cᴴ) = C * M * Cᴴ := by
  calc (C * X) * (X * M * X) * (X * Cᴴ)
      = C * (X * X) * M * (X * X) * Cᴴ := by simp only [Matrix.mul_assoc]
    _ = C * M * Cᴴ := by rw [hX, Matrix.mul_one, Matrix.mul_one]
private theorem conj_eq_of_mul_eq_part4 {D : ℕ} {V W P : Operator D}
    (hP : Pᴴ = P) (h : V * P = W * P) : V * P * Vᴴ = W * P * Wᴴ := by
  have hadj : P * Vᴴ = P * Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP] using congrArg (·ᴴ) h
  rw [h, Matrix.mul_assoc W P Vᴴ, hadj, ← Matrix.mul_assoc]
private theorem conj_unitary_eq_on_proj_part4 {D : ℕ} (V W : Unitary D) {U P : Operator D}
    (hP : Pᴴ = P) (hVP : V.1 * P = W.1 * P) (hVUP : V.1 * (U * P) = W.1 * (U * P)) :
    (W.1 * U * W.1ᴴ) * (V.1 * P * V.1ᴴ) = (V.1 * U * V.1ᴴ) * (V.1 * P * V.1ᴴ) := by
  have hadj : P * V.1ᴴ = P * W.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP] using congrArg (·ᴴ) hVP
  symm
  calc (V.1 * U * V.1ᴴ) * (V.1 * P * V.1ᴴ)
      = V.1 * (U * P) * V.1ᴴ := conj_unitary_mul_part4 V U P
    _ = W.1 * U * (P * V.1ᴴ) := by rw [hVUP]; simp only [Matrix.mul_assoc]
    _ = W.1 * (U * P) * W.1ᴴ := by rw [hadj]; simp only [Matrix.mul_assoc]
    _ = (W.1 * U * W.1ᴴ) * (W.1 * P * W.1ᴴ) := (conj_unitary_mul_part4 W U P).symm
    _ = (W.1 * U * W.1ᴴ) * (V.1 * P * V.1ᴴ) := by rw [conj_eq_of_mul_eq_part4 hP hVP]
theorem dInnerSwapAnchor_ofStr_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWorkSub18 n : ℕ} [NeZero (2 ^ n)]
    (hm155 : 155 ≤ mWorkSub18) (v : Var)
    (dStrAdd dStrInv : StrCallback Var mWorkSub18 n)
    (hReal : ∀ rC rS rW (hCS : rC.DisjointWires rS) hCW hSW,
      let rCS := rC.concat rS hCS
      RealizesOnProj (rCS.embedMatrix pSum42CoreZero * rW.basisOutcomeProjector 0)
        (rCS.embedUnitary uStr218_3Axis) (dStrAdd rC rS rW hCS hCW hSW) ∧
      RealizesOnProj (rCS.embedMatrix eStream218Core * rW.basisOutcomeProjector 0)
        (rCS.embedUnitary uStr218_3Axis⁻¹) (dStrInv rC rS rW hCS hCW hSW))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    RealizesOnProj
      (E_anchor (E_raw217 * pPGIdleZero 11 (by decide)) rAct rAnchor18 rWork hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame uInnerSwapFull))
      (dInnerSwapAnchor_ofStr hm155 v dStrAdd dStrInv rAct rAnchor18 rWork hAA hAW hAnW) := by
  have hm36 : 36 ≤ mWorkSub18 := by omega
  let rAA := rAct.concat rAnchor18 hAA
  let rSubst := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  let rHold36 := rHold36OfSub18 hm36 rWork
  let rCarry18 := rCarry18OfSub18 hm36 rWork
  let rZ18 := rZ18OfSub18 hm36 rWork
  let rWRest := rWRestOfSub18 hm36 rWork
  let rIdle11 := rAct.compose (rPGIdle 11 (by decide))
  let hWRestIdle : rWRest.DisjointWires rIdle11 :=
    (QRegExt.disjointWires_symm ((hAW.compose_left (rPGIdle 11 (by decide))).compose_right _))
  let rW136 : QRegister ((mWorkSub18 - 36) + 11) n := rWRest.concat rIdle11 hWRestIdle
  let hAA_Z : rAA.DisjointWires rZ18 :=
    disjointWires_concat_left hAA (hAW.compose_right _) (hAnW.compose_right _)
  let rAAZ : QRegister ((kFull80 + 18) + 18) n := rAA.concat rZ18 hAA_Z
  let hAAZ_Carry : rAAZ.DisjointWires rCarry18 := disjointWires_concat_left hAA_Z
      (disjointWires_concat_left hAA (hAW.compose_right _) (hAnW.compose_right _))
      (QRegExt.disjointWires_symm (rCarry18OfSub18_disj_rZ18OfSub18 hm36 rWork))
  let hAAZ_WRest : rAAZ.DisjointWires rWRest := disjointWires_concat_left hAA_Z
      (disjointWires_concat_left hAA (hAW.compose_right _) (hAnW.compose_right _))
      (rZ18OfSub18_disj_rWRestOfSub18 hm36 rWork)
  let hCarryW136 : rCarry18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (rCarry18OfSub18_disj_rWRestOfSub18 hm36 rWork)
      (QRegExt.disjointWires_symm ((hAW.compose_left (rPGIdle 11 (by decide))).compose_right _))
  let rCore := rAct.compose rCoreFull
  let rSum42 := rAct.compose rSum0
  let rPG7 := rAct.compose rPG7Full
  let hCSum42 := disjointWires_compose_of_disjoint rAct rCoreFull_disj_rSum0
  let hCPG := disjointWires_compose_of_disjoint rAct hCoreFull_disj_rPG7Full
  let hSPG := disjointWires_compose_of_disjoint rAct rSum0_disj_rPG7Full
  let hCW136 : rCore.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rCoreFull).compose_right _)
      (disjointWires_compose_of_disjoint rAct rCoreFull_disj_rPGIdle11)
  let hSW136 : rSum42.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rSum0).compose_right _)
      (disjointWires_compose_of_disjoint rAct (hSum0_disj_PGIdle 11 (by decide)))
  let hPGW136 : rPG7.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rPG7Full).compose_right _)
      (disjointWires_compose_of_disjoint rAct rPG7Full_disj_rPGIdle11)
  let hZW136 : rZ18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (rZ18OfSub18_disj_rWRestOfSub18 hm36 rWork)
      (QRegExt.disjointWires_symm ((hAW.compose_left (rPGIdle 11 (by decide))).compose_right _))
  let hCZ : rCore.DisjointWires rZ18 := (hAW.compose_left rCoreFull).compose_right _
  let hSZ : rSum42.DisjointWires rZ18 := (hAW.compose_left rSum0).compose_right _
  let hPGZ : rPG7.DisjointWires rZ18 := (hAW.compose_left rPG7Full).compose_right _
  let rCS := rCore.concat rSum42 hCSum42
  let hCS_Z := disjointWires_concat_left hCSum42 hCZ hSZ
  let hCS_PG := disjointWires_concat_left hCSum42 hCPG hSPG
  let rHeldAct := (rCS.concat rZ18 hCS_Z).concat rPG7
    (disjointWires_concat_left hCS_Z hCS_PG (QRegExt.disjointWires_symm hPGZ))
  let hCS_W136 := disjointWires_concat_left hCSum42 hCW136 hSW136
  let hHeldW136 : rHeldAct.DisjointWires rW136 :=
    disjointWires_concat_left _ (disjointWires_concat_left hCS_Z hCS_W136 hZW136) hPGW136
  let rSubstPos := rSubst.compose rPosCoreInFull
  let hSubPHold : rSubstPos.DisjointWires rHold36 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hSubPCarry : rSubstPos.DisjointWires rCarry18 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hSubPZ : rSubstPos.DisjointWires rZ18 := (hSubW.compose_left rPosCoreInFull).compose_right _
  let hQDisj : (phcHead_rQRev18 rSubstPos).DisjointWires rZ18 :=
    QRegister.disjoint_iff.mpr fun k j heq ↦ by
      obtain ⟨i, hi⟩ := (QRegister.mem_image rSubstPos _).mp (phcHead_rQRev18_mem_core rSubstPos k)
      exact hSubPZ.ne i j (hi.trans heq)
  let rCorePos := rAct.compose rPosCoreInFull
  let rScr178 : QRegister (((mWorkSub18 - 36) + 11) + 42) n :=
    rW136.concat rSum42 (QRegExt.disjointWires_symm hSW136)
  let hCPSum : rCorePos.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rAct (rCoreFull_disj_rSum0.compose_left selPosCoreInCore80)
  let hCPScr : rCorePos.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136)
      (hCW136.compose_left selPosCoreInCore80) hCPSum
  let hAnW136 : rAnchor18.DisjointWires rW136 := disj_concat_right_part4 hWRestIdle
      (hAnW.compose_right _)
        (QRegExt.disjointWires_symm (hAA.compose_left (rPGIdle 11 (by decide))))
  let hAnScr : rAnchor18.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136) hAnW136
      (QRegExt.disjointWires_symm (hAA.compose_left rSum0))
  let rHeadAct := rCorePos.concat rAnchor18 (hAA.compose_left rPosCoreInFull)
  have hHeadDisjScr : rHeadAct.DisjointWires rScr178 :=
    disjointWires_concat_left (hAA.compose_left rPosCoreInFull) hCPScr hAnScr
  have hHeadDisjW136 : rHeadAct.DisjointWires rW136 := disjointWires_concat_left
      (hAA.compose_left rPosCoreInFull) (hCW136.compose_left selPosCoreInCore80) hAnW136
  -- Register composition identities with `rAAZ`
  have hAAZ_AA : rAAZ.compose selAAZ_AA = rAA := concat_compose_selDataInAct rAA rZ18 hAA_Z
  have hAAZ_Z : rAAZ.compose selAAZ_Z = rZ18 := concat_compose_selMeasInAct rAA rZ18 hAA_Z
  have hAAZ_Data : rAAZ.compose selAAZ_Data = rAct := by
    rw [← QRegister.compose_assoc, hAAZ_AA]; exact concat_compose_selDataInAct rAct rAnchor18 hAA
  have hAAZ_Subst : rAAZ.compose selAAZ_Subst = rSubst := by
    dsimp only [selAAZ_Subst, rSubst, rActAnchorSubst]
    rw [← QRegister.compose_assoc, hAAZ_AA]
    exact concat_compose_selSubstSlot0 rSlot0InFull rAct rAnchor18 hAA
  have hCompCore : rAAZ.compose (selAAZ_Data.compose rCoreFull) = rCore := by
    rw [← QRegister.compose_assoc, hAAZ_Data]
  have hCompCS : rAAZ.compose (selAAZ_Data.compose rCSFull80) = rCS := by
    rw [← QRegister.compose_assoc, hAAZ_Data]
    apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp [rCS, rCore, rCSFull80, QRegister.concat_apply_left]
    · simp [rCS, rSum42, rCSFull80, QRegister.concat_apply_right]
  have hCompSubPos : rAAZ.compose (selAAZ_Subst.compose rPosCoreInFull) = rSubstPos := by
    rw [← QRegister.compose_assoc, hAAZ_Subst]
  have hCompSubstPZ : rAAZ.compose ((selAAZ_Subst.compose rPosCoreInFull).concat selAAZ_Z
      (selAAZ_Subst_disj_Z.compose_left rPosCoreInFull)) = rSubstPos.concat rZ18 hSubPZ := by
    apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
          ← QRegister.compose_apply rAAZ, hCompSubPos]
    · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
          ← QRegister.compose_apply rAAZ, hAAZ_Z]
  have hCompHeld : rAAZ.compose selAAZ_HeldAct = rHeldAct := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun iCZ ↦ ?_) (fun mPG ↦ ?_) idx
    · refine Fin.addCases (fun iCS ↦ ?_) (fun jZ ↦ ?_) iCZ
      · dsimp only [selAAZ_HeldAct, rHeldAct]
        rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
            QRegister.concat_apply_left, QRegister.concat_apply_left,
            ← QRegister.compose_apply rAAZ, hCompCS]
      · dsimp only [selAAZ_HeldAct, rHeldAct]
        rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_right,
            QRegister.concat_apply_left, QRegister.concat_apply_right,
            ← QRegister.compose_apply rAAZ, hAAZ_Z]
    · dsimp only [selAAZ_HeldAct, rHeldAct, rPG7]
      rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
          ← QRegister.compose_apply rAAZ, ← QRegister.compose_assoc, hAAZ_Data]
  have hCompHead : rAAZ.compose (selAAZ_AA.compose (selLiftAct rPosCoreInFull)) = rHeadAct := by
    apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
    · dsimp only [selLiftAct, rHeadAct, rCorePos]
      rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.concat_apply_left,
          QRegister.concat_apply_left, ← QRegister.compose_apply rAAZ selAAZ_AA, hAAZ_AA,
          QRegister.compose_apply, ← QRegister.compose_apply rAA (selDataInAct kFull80),
          concat_compose_selDataInAct, ← QRegister.compose_apply rAct rPosCoreInFull]
    · dsimp only [selLiftAct, rHeadAct]
      rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.concat_apply_right,
          QRegister.concat_apply_right, ← QRegister.compose_apply rAAZ selAAZ_AA, hAAZ_AA,
          ← QRegister.compose_apply rAA (selMeasInAct kFull80), concat_compose_selMeasInAct]
  -- Step 1: `RealizesOnProj` for `dMid5` on `P218_n * PW136`
  let PW136 := rW136.basisOutcomeProjector 0
  let P218_n := rAAZ.embedMatrix P218_AAZ
  have hP218_CS : P218_n = rCS.embedMatrix (pStream218Core 80) := by
    dsimp only [P218_n]; rw [P218_AAZ_def, ← QRegister.embedMatrix_compose, hCompCS]
  have hP218_comm_W136 : P218_n * PW136 = PW136 * P218_n := by
    rw [hP218_CS]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0
  have hPhiFUnitEq : rHeldAct.embedUnitary uPhiHeldZ18AnchorCat = rAAZ.embedUnitary uPhiAnc_AAZ :=
    by
    rw [← hCompHeld, QRegister.embedUnitary_compose, ← uPhiAnc_AAZ_def]
  have hPhiIUnitEq : rHeldAct.embedUnitary uPhiHeldZ18AnchorCat⁻¹ =
    rAAZ.embedUnitary uPhiAnc_AAZ⁻¹ := by
    rw [QRegister.embedUnitary_inv, QRegister.embedUnitary_inv, hPhiFUnitEq]
  have hPhiIProj := realizesOnProj_of_clean_proj0 hHeldW136
    (dPhiOnHeldZ18AnchorInv128_realizes (by
      omega : 128 ≤ (mWorkSub18 - 36) +
      11) v rHeldAct rW136 hHeldW136)
  rw [hPhiIUnitEq] at hPhiIProj
  have hPhiFRaw := realizesOnProj_of_clean_proj0 hHeldW136
    (dPhiOnHeldZ18AnchorFwd128_realizes (by
      omega : 128 ≤ (mWorkSub18 - 36) +
      11) v rHeldAct rW136 hHeldW136)
  rw [hPhiFUnitEq] at hPhiFRaw
  have hPhiFProj := realizesOnProj_mul_right P218_n hPhiFRaw
  rw [← hP218_comm_W136] at hPhiFProj
  have hStrPair := hReal rCore rSum42 rW136 hCSum42 hCW136 hSW136
  have hHeadRaw := realizesOnProj_of_clean_proj0 hHeadDisjScr
    (dHeadAnchorConjH172_realizes (by omega : 172 ≤ ((mWorkSub18 - 36) + 11) + 42) v
      rCorePos rAnchor18 rScr178 (hAA.compose_left rPosCoreInFull) hCPScr hAnScr)
  have hScrProjEq : rScr178.basisOutcomeProjector 0 =
      rCS.embedMatrix pSum42CoreZero * PW136 := by
    have hSumProj : rCS.embedMatrix pSum42CoreZero = rSum42.basisOutcomeProjector 0 := by
      rw [pSum42CoreZero, embedMatrix_basisOutcomeProjector_zero_assoc]
      apply congrArg (fun r : QRegister 42 n ↦ r.basisOutcomeProjector 0)
      apply qreg_ext; intro j
      have hj : rZLoc (fullSysCoreWires 80) 42 j = Fin.natAdd (fullSysCoreWires 80) j :=
        Fin.ext (by simp [rZLoc])
      rw [QRegister.compose_apply, hj]; dsimp only [rCS]; rw [QRegister.concat_apply_right]
    rw [basisOutcomeProjector_zero_concat_eq_mul rW136 rSum42 (QRegExt.disjointWires_symm hSW136),
      hSumProj]
    exact basisOutcomeProjector_comm_part4 rW136 rSum42 0 0
  have hHeadUnitEq : rHeadAct.embedUnitary uHeadAnchorConjH = rAAZ.embedUnitary uHeadAnc_AAZ := by
    rw [← hCompHead, QRegister.embedUnitary_compose, ← uHeadAnc_AAZ_def]
  rw [hScrProjEq, hHeadUnitEq] at hHeadRaw
  have hStrAUnitEq : rCS.embedUnitary uStr218_3Axis = rAAZ.embedUnitary uStr218_AAZ := by
    rw [← hCompCS, QRegister.embedUnitary_compose, ← uStr218_AAZ_def]
  have hStrIUnitEq : rCS.embedUnitary uStr218_3Axis⁻¹ = rAAZ.embedUnitary uStr218_AAZ⁻¹ := by
    rw [QRegister.embedUnitary_inv, QRegister.embedUnitary_inv, hStrAUnitEq]
  have hStrIProj := hStrPair.2; rw [hStrIUnitEq] at hStrIProj
  have hStrAProj := hStrPair.1; rw [hStrAUnitEq] at hStrAProj
  have hTransStrI : (rAAZ.embedUnitary uStr218_AAZ⁻¹).1 * (rCS.embedMatrix eStream218Core * PW136) =
      (rCS.embedMatrix pSum42CoreZero * PW136) * 1 := by
    rw [← hStrIUnitEq, Matrix.mul_one, ← Matrix.mul_assoc, QRegister.embedUnitary_val,
        ← rCS.embedMatrix_mul, inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero]
  have hTransHead : (rAAZ.embedUnitary uHeadAnc_AAZ).1 * (rCS.embedMatrix pSum42CoreZero * PW136) =
      (rCS.embedMatrix pSum42CoreZero * PW136) * (rAAZ.embedUnitary uHeadAnc_AAZ).1 := by
    rw [← hScrProjEq, ← hHeadUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeadAct) rScr178 hHeadDisjScr
      _ 0
  have hHeadStrA := realizesOnProj_seq_part4 hTransHead hHeadRaw hStrAProj
  have hMidE := realizesOnProj_seq_part4 hTransStrI hStrIProj hHeadStrA
  have hP218MulEq : (rCS.embedMatrix eStream218Core * PW136) * rCS.embedMatrix eStream218Coreᴴ =
      P218_n * PW136 := by
    have hCommW : PW136 * rCS.embedMatrix eStream218Coreᴴ =
        rCS.embedMatrix eStream218Coreᴴ * PW136 :=
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0).symm
    rw [Matrix.mul_assoc, hCommW, ← Matrix.mul_assoc, ← rCS.embedMatrix_mul,
        eStream218Core_mul_conjTranspose, ← hP218_CS]
  have hMidP218 := realizesOnProj_mul_right (rCS.embedMatrix eStream218Coreᴴ) hMidE
  rw [hP218MulEq, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
      _root_.mul_assoc uStr218_AAZ uHeadAnc_AAZ] at hMidP218
  have hPhiFCommW136 : (rAAZ.embedUnitary uPhiAnc_AAZ).1 * PW136 =
      PW136 * (rAAZ.embedUnitary uPhiAnc_AAZ).1 := by
    rw [← hPhiFUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeldAct) rW136 hHeldW136 _ 0
  have hPhiICommW136 : (rAAZ.embedUnitary uPhiAnc_AAZ⁻¹).1 * PW136 =
      PW136 * (rAAZ.embedUnitary uPhiAnc_AAZ⁻¹).1 := by
    rw [← hPhiIUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeldAct) rW136 hHeldW136 _ 0
  have hMid3CommW136 :
      (rAAZ.embedUnitary (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))).1 * PW136 =
        PW136 * (rAAZ.embedUnitary (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))).1 := by
    have h1 : (rAAZ.embedUnitary uStr218_AAZ).1 * PW136 =
        PW136 * (rAAZ.embedUnitary uStr218_AAZ).1 := by
      rw [← hStrAUnitEq]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0
    have h2 : (rAAZ.embedUnitary uStr218_AAZ⁻¹).1 * PW136 =
        PW136 * (rAAZ.embedUnitary uStr218_AAZ⁻¹).1 := by
      rw [← hStrIUnitEq]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0
    have h3 : (rAAZ.embedUnitary uHeadAnc_AAZ).1 * PW136 =
        PW136 * (rAAZ.embedUnitary uHeadAnc_AAZ).1 := by
      rw [← hHeadUnitEq]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeadAct) rW136
        hHeadDisjW136 _ 0
    simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    exact mul3_comm_of_comm h1 h3 h2
  obtain ⟨_, _, _, hPhiAnc218, _, hXorS218⟩ := uCSDiag_comm_AAZ (stream42DiagFn slot2AxisSum)
  rw [P218_AAZ_eq_diag] at hPhiAnc218 hXorS218
  have hPhiFCommP218 : (rAAZ.embedUnitary uPhiAnc_AAZ).1 * (P218_n * PW136) =
      (P218_n * PW136) * (rAAZ.embedUnitary uPhiAnc_AAZ).1 := by
    dsimp only [P218_n]
    rw [← Matrix.mul_assoc, QRegister.embedUnitary_val, ← rAAZ.embedMatrix_mul, hPhiAnc218,
        rAAZ.embedMatrix_mul, Matrix.mul_assoc, ← QRegister.embedUnitary_val,
        hPhiFCommW136, ← Matrix.mul_assoc]
  have hMid3TransW :
      (rAAZ.embedUnitary (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))).1 * (P218_n * PW136) =
        PW136 * ((rAAZ.embedUnitary (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))).1 * P218_n) :=
          by
    rw [hP218_comm_W136, ← Matrix.mul_assoc, hMid3CommW136, Matrix.mul_assoc]
  have hMid4Proj := realizesOnProj_seq_part4 hMid3TransW hMidP218 hPhiIProj
  have hMid5Proj := realizesOnProj_seq_part4 hPhiFCommP218 hPhiFProj hMid4Proj
  let uMid5_AAZ := (uPhiAnc_AAZ⁻¹ * (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) * uPhiAnc_AAZ
  let U_mid5 := rAAZ.embedUnitary uMid5_AAZ
  have hMid5UnitEq : (rAAZ.embedUnitary uPhiAnc_AAZ⁻¹ * rAAZ.embedUnitary (uStr218_AAZ *
      (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) * rAAZ.embedUnitary uPhiAnc_AAZ = U_mid5 := by
    dsimp only [U_mid5, uMid5_AAZ]; simp only [QRegister.embedUnitary_mul]
  rw [hMid5UnitEq] at hMid5Proj
  have hMid5CommW136 : U_mid5.1 * PW136 = PW136 * U_mid5.1 := by
    rw [← hMid5UnitEq]
    simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc _ _ (rAAZ.embedUnitary uPhiAnc_AAZ).1]
    exact mul3_comm_of_comm hPhiICommW136 hMid3CommW136 hPhiFCommW136
  -- Step 2: Single-sum commutation of `C_18` with `U_mid5` on `P218_n * PW136`
  let C_18 : Unitary (2 ^ n) := (rSubstPos.concat rCarry18 hSubPCarry).embedUnitary uXorCarry18
  have hC18_sq : C_18.1 * C_18.1 = 1 := by
    dsimp only [C_18]
    rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uXorCarry18_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  have hC18_herm : C_18.1ᴴ = C_18.1 := unitary_herm_of_sq_one hC18_sq
  have hP218W_herm : (P218_n * PW136)ᴴ = P218_n * PW136 :=
    herm_mul_of_comm_part4 (by
      rw [hP218_CS, ← QRegister.embedMatrix_conjTranspose]
      exact congrArg rCS.embedMatrix (by
        rw [← eStream218Core_mul_conjTranspose, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]))
      (QRegister.basisOutcomeProjector_conjTranspose rW136 0) hP218_comm_W136
  have hC18_sum :=
    embedUnitary_uXorCarry18_eq_sum_D_carry rAAZ rSubstPos rCarry18 hSubPCarry hCompSubPos
  have hD_comm_W136 : ∀ u : Fin (2 ^ 18),
      rAAZ.embedMatrix (D_carry_AAZ u) * PW136 = PW136 * rAAZ.embedMatrix (D_carry_AAZ u) := fun u ↦
        by
    unfold D_carry_AAZ PW136
    rw [embedMatrix_diagonal_local, QRegister.basisOutcomeProjector_eq_diagonal]
    exact diagonal_comm_op_assoc _ _
  have hC18_comm_P218W : C_18.1 * (P218_n * PW136) = (P218_n * PW136) * C_18.1 := by
    dsimp only [C_18]
    rw [hC18_sum]
    refine sum_mul_comm_part4 _ _ fun u ↦ ?_
    let X_u := (rCarry18.embedUnitary (uXorConst18 u)).1
    have hX_P218 : X_u * P218_n = P218_n * X_u :=
      (rAAZ.embedMatrix_comm_of_disjoint rCarry18 hAAZ_Carry P218_AAZ (uXorConst18 u).1).symm
    have hX_W136 : X_u * PW136 = PW136 * X_u :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCarry18) rW136 hCarryW136 _ 0
    have hD_P218 : rAAZ.embedMatrix (D_carry_AAZ u) * P218_n =
        P218_n * rAAZ.embedMatrix (D_carry_AAZ u) := by
      dsimp only [P218_n]
      rw [← rAAZ.embedMatrix_mul, D_carry_AAZ_comm_P218 u, rAAZ.embedMatrix_mul]
    calc (rAAZ.embedMatrix (D_carry_AAZ u) * X_u) * (P218_n * PW136)
        = rAAZ.embedMatrix (D_carry_AAZ u) * ((X_u * P218_n) * PW136) := by
          simp only [Matrix.mul_assoc]
      _ = (rAAZ.embedMatrix (D_carry_AAZ u) * P218_n) * (PW136 * X_u) := by
            rw [hX_P218, Matrix.mul_assoc P218_n X_u PW136, hX_W136]; simp only [Matrix.mul_assoc]
      _ = (P218_n * PW136) * (rAAZ.embedMatrix (D_carry_AAZ u) * X_u) := by
            rw [hD_P218, Matrix.mul_assoc P218_n, ← Matrix.mul_assoc _ PW136, hD_comm_W136 u]
            simp only [Matrix.mul_assoc]
  have hC18_conj_Umid5 :
      (C_18.1 * U_mid5.1 * C_18.1ᴴ) * (P218_n * PW136) = U_mid5.1 * (P218_n * PW136) := by
    have hInter : U_mid5.1 * (C_18.1 * (P218_n * PW136)) =
        C_18.1 * (U_mid5.1 * (P218_n * PW136)) := by
      change U_mid5.1 *
        (((rSubstPos.concat rCarry18 hSubPCarry).embedUnitary uXorCarry18).1 * (P218_n * PW136)) =
        ((rSubstPos.concat rCarry18 hSubPCarry).embedUnitary uXorCarry18).1 *
          (U_mid5.1 * (P218_n * PW136))
      rw [hC18_sum]
      refine mul_sum_mul_part4 _ _ _ fun u ↦ ?_
      let X_u := (rCarry18.embedUnitary (uXorConst18 u)).1
      have hU_X : U_mid5.1 * X_u = X_u * U_mid5.1 :=
        rAAZ.embedMatrix_comm_of_disjoint rCarry18 hAAZ_Carry uMid5_AAZ.1 (uXorConst18 u).1
      have hD_X : rAAZ.embedMatrix (D_carry_AAZ u) * X_u = X_u * rAAZ.embedMatrix (D_carry_AAZ u) :=
        rAAZ.embedMatrix_comm_of_disjoint rCarry18 hAAZ_Carry (D_carry_AAZ u) (uXorConst18 u).1
      have hX_P218 : X_u * P218_n = P218_n * X_u :=
        (rAAZ.embedMatrix_comm_of_disjoint rCarry18 hAAZ_Carry P218_AAZ (uXorConst18 u).1).symm
      have hX_W136 : X_u * PW136 = PW136 * X_u :=
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCarry18) rW136 hCarryW136 _ 0
      have hUMidD : U_mid5.1 * (rAAZ.embedMatrix (D_carry_AAZ u) * P218_n) =
          rAAZ.embedMatrix (D_carry_AAZ u) * (U_mid5.1 * P218_n) := by
        dsimp only [U_mid5, P218_n]
        rw [QRegister.embedUnitary_val, ← rAAZ.embedMatrix_mul, ← rAAZ.embedMatrix_mul,
            uMid5_AAZ_comm_D_carry_on_P218 u, rAAZ.embedMatrix_mul, rAAZ.embedMatrix_mul]
      calc U_mid5.1 * ((rAAZ.embedMatrix (D_carry_AAZ u) * X_u) * (P218_n * PW136))
          = (U_mid5.1 * X_u) * ((rAAZ.embedMatrix (D_carry_AAZ u) * P218_n) * PW136) := by
              rw [hD_X]; simp only [Matrix.mul_assoc]
        _ = X_u * ((U_mid5.1 * (rAAZ.embedMatrix (D_carry_AAZ u) * P218_n)) * PW136) := by
              rw [hU_X]; simp only [Matrix.mul_assoc]
        _ = (X_u * rAAZ.embedMatrix (D_carry_AAZ u)) * (U_mid5.1 * (P218_n * PW136)) := by
              rw [hUMidD]; simp only [Matrix.mul_assoc]
        _ = (rAAZ.embedMatrix (D_carry_AAZ u) * X_u) * (U_mid5.1 * (P218_n * PW136)) := by
              rw [← hD_X]
    rw [hC18_herm]
    calc (C_18.1 * U_mid5.1 * C_18.1) * (P218_n * PW136)
        = C_18.1 * (U_mid5.1 * (C_18.1 * (P218_n * PW136))) := by simp only [Matrix.mul_assoc]
      _ = (C_18.1 * C_18.1) * (U_mid5.1 * (P218_n * PW136)) := by rw [hInter, ← Matrix.mul_assoc]
      _ = U_mid5.1 * (P218_n * PW136) := by rw [hC18_sq, Matrix.one_mul]
  have hMid5Peb₀ := (pebRealizes_iff_realizesOnProj hP218W_herm U_mid5 _).mpr
    (show RealizesOnProj (P218_n * PW136) U_mid5
      (.seq (dPhiOnHeldZ18AnchorFwd128
          (by omega : 128 ≤ (mWorkSub18 - 36) + 11) v rHeldAct rW136 hHeldW136)
        (.seq (dStrInv rCore rSum42 rW136 hCSum42 hCW136 hSW136)
          (.seq (dHeadAnchorConjH172 (by omega : 172 ≤ ((mWorkSub18 - 36) + 11) + 42) v
            rCorePos rAnchor18 rScr178 (hAA.compose_left rPosCoreInFull) hCPScr hAnScr)
            (.seq (dStrAdd rCore rSum42 rW136 hCSum42 hCW136 hSW136)
              (dPhiOnHeldZ18AnchorInv128
                (by omega : 128 ≤ (mWorkSub18 - 36) + 11) v rHeldAct rW136 hHeldW136))))) from
      fun M ↦ let ⟨M', hwp, heq⟩ := hMid5Proj M
        ⟨M', by simpa only [DynamicCircuit.compile_seq, wp_qSeq] using hwp, heq⟩)
  have hMid5PebC18 := hMid5Peb₀.congr_op hP218W_herm hC18_conj_Umid5.symm
  -- Step 3: Forward pebbled unitary `V_tot` on `PHold36_0` agrees with `C_18 * U_xorZ`
  let L := zTargetSteps36 (le_refl 36) rSubstPos rHold36 hSubPHold
  let cXorQ : Circuit n := copyXorRegCircuit (phcHead_rQRev18 rSubstPos) rZ18 hQDisj
  let V_tot : Unitary (2 ^ n) := cXorQ.eval * uSymStepFwdList L
  let U_xorZ : Unitary (2 ^ n) := rAAZ.embedUnitary uXorSubst_AAZ
  have hUxorZ_eq : U_xorZ = (rSubstPos.concat rZ18 hSubPZ).embedUnitary uXorZTarget18 := by
    dsimp only [U_xorZ]; rw [uXorSubst_AAZ_def, ← QRegister.embedUnitary_compose, hCompSubstPZ]
  have hUxorZ_sq : U_xorZ.1 * U_xorZ.1 = 1 := by
    rw [hUxorZ_eq, ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uXorZTarget18_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  have hUxorZ_herm : U_xorZ.1ᴴ = U_xorZ.1 := unitary_herm_of_sq_one hUxorZ_sq
  let PHold36_0 := rHold36.basisOutcomeProjector 0
  let PCarry18_0 := rCarry18.basisOutcomeProjector 0
  let PZ18_0 := rZ18.basisOutcomeProjector 0
  have hVtot_PHold : V_tot.1 * PHold36_0 = (C_18 * U_xorZ).1 * PHold36_0 := by
    apply matrix_ext_ket; intro β
    have hket : ∀ γ : BitAssignment n, ket γ = MeasureBranchHadamardSem.ket γ := fun _ ↦ rfl
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [PHold36_0]
    rw [← projZeroAll_eq_basisOutcomeProjector_zero]
    by_cases hClean : ∀ idx : Fin 36, β (rHold36 idx) = 0
    · rw [hket β, ket_projZeroAll, ite_eq_left hClean, ← hket β]
      dsimp only [V_tot]
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ket_uSymStepFwdList]
      have hcXorQKet : ∀ γ : BitAssignment n, cXorQ.eval.1.mulVec (ket γ) = ket (writeReg γ
          rZ18 fun k ↦ γ (rZ18 k) + γ (phcHead_rQRev18 rSubstPos k)) :=
        fun γ ↦ by simpa only [ket_eq_basisKet] using
          copyXorRegCircuit_classicalPerm (phcHead_rQRev18 rSubstPos) rZ18 hQDisj γ
      rw [hcXorQKet, hUxorZ_eq, ket_embedUnitary_uXorZTarget18, ket_embedUnitary_uXorCarry18]
      obtain ⟨_, heL⟩ := zTargetSteps36_valid_and_eval (le_refl 36) rSubstPos rHold36 hSubPHold
        ∅ (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
      obtain ⟨hMuxVal, hOutL⟩ := heL β hClean
      let β' := writeReg β rZ18 fun k ↦
        β (rZ18 k) + basisBits 18 (headTargetPoint18 (fun i ↦ β (rSubstPos i))) k
      have hSubPos_β' : (fun i ↦ β' (rSubstPos i)) = fun i ↦ β (rSubstPos i) :=
        funext fun i ↦ writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦ hSubPZ.ne i k hk.symm)
      refine congrArg ket (funext fun z ↦ ?_)
      by_cases hCz : ∃ k : Fin 18, rCarry18 k = z
      · obtain ⟨k, rfl⟩ := hCz
        have hNotZ : rCarry18 k ∉ Set.range rZ18.wires :=
          fun ⟨j, hj⟩ ↦ (rCarry18OfSub18_disj_rZ18OfSub18 hm36 rWork).ne k j hj.symm
        rw [writeReg_apply_of_not_mem _ _ _ _ hNotZ, writeReg_apply_reg,
            writeReg_apply_of_not_mem _ _ _ _ hNotZ, hSubPos_β']
        have hCarryIdx : rCarry18 k = rHold36 ⟨k.val, by have := k.isLt; omega⟩ := by
          simp only [rCarry18, rHold36, rCarry18OfSub18, rHold36OfSub18, QRegister.slice_apply]
        rw [hCarryIdx, hClean _, zero_add]
        exact zTargetSteps36_eval_carry rSubstPos rHold36 hSubPHold β hClean k
      · rw [writeReg_apply_of_not_mem _ _ _ _ hCz]
        by_cases hZz : ∃ k : Fin 18, rZ18 k = z
        · obtain ⟨k, rfl⟩ := hZz
          rw [writeReg_apply_reg, writeReg_apply_reg]
          have hZIdx : rZ18 k = rHold36 ⟨18 + k.val, by have := k.isLt; omega⟩ := by
            dsimp only [rZ18, rHold36, rZ18OfSub18, rHold36OfSub18]
            rw [QRegister.slice_apply, QRegister.slice_apply]
            exact congrArg rWork (Fin.ext (by dsimp only; omega))
          rw [hZIdx, hClean _, zero_add]
          have hQ_L : symStepFwdList L β (phcHead_rQRev18 rSubstPos k) =
            β (phcHead_rQRev18 rSubstPos k) :=
            hOutL _ fun idx heq ↦ by
              obtain ⟨i, hi⟩ :=
                (QRegister.mem_image rSubstPos _).mp (phcHead_rQRev18_mem_core rSubstPos k)
              exact hSubPHold.ne i idx (hi.trans heq)
          rw [hQ_L]
          let w : Fin 3 := ⟨k.val / 6, by have := k.isLt; omega⟩
          let j : Fin 6 := ⟨5 - k.val % 6, by omega⟩
          have hk_eq : k = ⟨6 * w.val + (5 - j.val), by have := w.isLt; have := j.isLt; omega⟩ :=
            Fin.ext (by dsimp only [w, j]; have := k.isLt; omega)
          have hHoldIdx : (⟨18 + k.val, by have := k.isLt; omega⟩ : Fin 36) =
              ⟨18 + 6 * w.val + (5 - j.val), by have := w.isLt; have := j.isLt; omega⟩ :=
            Fin.ext (by dsimp only [w, j]; have := k.isLt; omega)
          have hQIdx : phcHead_rQRev18 rSubstPos k =
              rHeadFine21 rSubstPos ⟨7 * w.val + j.val + 1, by
                have := w.isLt; have :=
                j.isLt; omega⟩ :=
            congrArg (rHeadFine21 rSubstPos).wires (Fin.ext (by dsimp [phcHead_rQRev18, w, j]))
          have hBit := headTargetPoint18_bit_eq_mux_xor_q rSubstPos β w j
          rw [← hk_eq] at hBit
          rw [hHoldIdx, hMuxVal w j, hQIdx, hBit]
        · rw [writeReg_apply_of_not_mem _ _ _ _ hZz, writeReg_apply_of_not_mem _ _ _ _ hZz]
          exact hOutL z fun idx heq ↦ by
            by_cases hlt18 : idx.val < 18
            · exact hCz ⟨⟨idx.val, hlt18⟩, by
                rw [heq]
                simp only [rCarry18, rHold36, rCarry18OfSub18, rHold36OfSub18,
                  QRegister.slice_apply]⟩
            · exact hZz ⟨⟨idx.val - 18, by have := idx.isLt; omega⟩, by
                rw [heq]
                dsimp only [rZ18, rHold36, rZ18OfSub18, rHold36OfSub18]
                rw [QRegister.slice_apply, QRegister.slice_apply]
                exact congrArg rWork (Fin.ext (by dsimp only; omega))⟩
    · rw [hket β, ket_projZeroAll, ite_eq_right hClean, Matrix.mulVec_zero, Matrix.mulVec_zero]
  -- Step 4: Projectors `P_init_n`, `P_sw_n`, `P_mid` & wrapping `dMid5` -> `dPeb` ->
  -- `dInnerSwapAnchor_ofStr`
  let P_init_AAZ := E_init_AAZ * E_init_AAZᴴ
  let P_sw_AAZ := uSw_AAZ.1 * P_init_AAZ * uSw_AAZ.1ᴴ
  have hPinitAAZ_herm : P_init_AAZᴴ = P_init_AAZ := by
    simp [P_init_AAZ, Matrix.conjTranspose_mul]
  have hPswAAZ_herm : P_sw_AAZᴴ = P_sw_AAZ := conj_herm_part4 uSw_AAZ.1 hPinitAAZ_herm
  have hSwSq_AAZ : uSw_AAZ * uSw_AAZ = 1 := by
    rw [uSw_AAZ_def, ← QRegister.embedUnitary_mul, uSwapCore3967_mul_self,
      QRegister.embedUnitary_one]
  have hSwHerm_AAZ : uSw_AAZ.1ᴴ = uSw_AAZ.1 :=
    unitary_herm_of_sq_one (unitary_val_mul_self_eq_one_assoc hSwSq_AAZ)
  have hPW136_split : PW136 = rWRest.basisOutcomeProjector 0 * rIdle11.basisOutcomeProjector 0 :=
    basisOutcomeProjector_zero_concat_eq_mul rWRest rIdle11 hWRestIdle
  have hIdleProj_AAZ : rIdle11.basisOutcomeProjector 0 =
      rAAZ.embedMatrix ((selAAZ_Data.compose (rPGIdle 11 (by decide))).basisOutcomeProjector 0) :=
        by
    rw [embedMatrix_basisOutcomeProjector_gen_part4, ← QRegister.compose_assoc, hAAZ_Data]
  have hAAZ_comm_W136 {M : Operator (2 ^ ((kFull80 + 18) + 18))}
      (hIdle : M * (selAAZ_Data.compose (rPGIdle 11 (by decide))).basisOutcomeProjector 0 =
        (selAAZ_Data.compose (rPGIdle 11 (by decide))).basisOutcomeProjector 0 * M) :
      rAAZ.embedMatrix M * PW136 = PW136 * rAAZ.embedMatrix M := by
    have h1 : rAAZ.embedMatrix M * rWRest.basisOutcomeProjector 0 =
        rWRest.basisOutcomeProjector 0 * rAAZ.embedMatrix M :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZ) rWRest hAAZ_WRest _ 0
    have h2 : rAAZ.embedMatrix M * rIdle11.basisOutcomeProjector 0 =
        rIdle11.basisOutcomeProjector 0 * rAAZ.embedMatrix M := by
      rw [hIdleProj_AAZ, ← rAAZ.embedMatrix_mul, hIdle, rAAZ.embedMatrix_mul]
    rw [hPW136_split, ← Matrix.mul_assoc, h1,
      Matrix.mul_assoc _ _ (rIdle11.basisOutcomeProjector 0),
        h2, ← Matrix.mul_assoc]
  have hEinit_comm_W136 := hAAZ_comm_W136 E_init_AAZ_comm_pPGIdle11.1
  have hPinit_comm_W136 := hAAZ_comm_W136 E_init_AAZ_comm_pPGIdle11.2
  have hSw_comm_W136 : (rAAZ.embedUnitary uSw_AAZ).1 * PW136 = PW136 *
    (rAAZ.embedUnitary uSw_AAZ).1 := by
    have hSwCore : rAAZ.embedUnitary uSw_AAZ = rCore.embedUnitary uSwapCore3967 := by
      rw [uSw_AAZ_def, ← QRegister.embedUnitary_compose, hCompCore]
    rw [hSwCore]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCore) rW136 hCW136 _ 0
  have hPsw_comm_W136 : rAAZ.embedMatrix P_sw_AAZ * PW136 = PW136 * rAAZ.embedMatrix P_sw_AAZ := by
    have hexp : rAAZ.embedMatrix P_sw_AAZ =
        (rAAZ.embedUnitary uSw_AAZ).1 * rAAZ.embedMatrix P_init_AAZ *
          (rAAZ.embedUnitary uSw_AAZ).1 := by
      dsimp only [P_sw_AAZ]
      rw [hSwHerm_AAZ, QRegister.embedUnitary_val, rAAZ.embedMatrix_mul, rAAZ.embedMatrix_mul]
    rw [hexp, Matrix.mul_assoc _ _ (rAAZ.embedUnitary uSw_AAZ).1]
    exact mul3_comm_of_comm hSw_comm_W136 hPinit_comm_W136 hSw_comm_W136
  let P_CW := PCarry18_0 * PW136
  have hPCW_herm : P_CWᴴ = P_CW :=
    herm_mul_of_comm_part4 (QRegister.basisOutcomeProjector_conjTranspose rCarry18 0)
      (QRegister.basisOutcomeProjector_conjTranspose rW136 0)
      (basisOutcomeProjector_comm_part4 rCarry18 rW136 0 0)
  let P_init_n := rAAZ.embedMatrix P_init_AAZ * P_CW
  let P_sw_n := rAAZ.embedMatrix P_sw_AAZ * P_CW
  have hAAZ_comm_PCW {M : Operator (2 ^ ((kFull80 + 18) + 18))}
      (hW : rAAZ.embedMatrix M * PW136 = PW136 * rAAZ.embedMatrix M) :
      rAAZ.embedMatrix M * P_CW = P_CW * rAAZ.embedMatrix M := by
    dsimp only [P_CW]
    rw [← Matrix.mul_assoc,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZ) rCarry18 hAAZ_Carry _ 0,
        Matrix.mul_assoc, hW, ← Matrix.mul_assoc]
  have hPinit_comm_PCW := hAAZ_comm_PCW hPinit_comm_W136
  have hPsw_comm_PCW := hAAZ_comm_PCW hPsw_comm_W136
  have hPinit_n_herm : P_init_nᴴ = P_init_n :=
    herm_mul_of_comm_part4 (by rw [← QRegister.embedMatrix_conjTranspose, hPinitAAZ_herm])
      hPCW_herm hPinit_comm_PCW
  have hPsw_n_herm : P_sw_nᴴ = P_sw_n :=
    herm_mul_of_comm_part4 (by rw [← QRegister.embedMatrix_conjTranspose, hPswAAZ_herm])
      hPCW_herm hPsw_comm_PCW
  let uC7_AAZ := uXorSubst_AAZ * uMid5_AAZ * uXorSubst_AAZ
  let U_peb := rAAZ.embedUnitary uC7_AAZ
  let U_C9 := rAAZ.embedUnitary uC9_AAZ
  have huC9_eq_sw_uC7 : uC9_AAZ = uSw_AAZ * uC7_AAZ * uSw_AAZ := by
    rw [uC9_AAZ_def]; dsimp only [uC7_AAZ, uMid5_AAZ]; simp only [_root_.mul_assoc]
  have hSwZ : selAAZ_Z.basisOutcomeProjector 0 * uSw_AAZ.1 =
      uSw_AAZ.1 * selAAZ_Z.basisOutcomeProjector 0 := by
    rw [uSw_AAZ_def, QRegister.embedUnitary_val]
    exact
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZ_Data.compose rCoreFull))
      selAAZ_Z (selAAZ_Data_disj_Z.compose_left rCoreFull) _ 0).symm
  have hPZ_PswAAZ : selAAZ_Z.basisOutcomeProjector 0 * P_sw_AAZ = P_sw_AAZ := by
    dsimp only [P_sw_AAZ, P_init_AAZ]
    calc selAAZ_Z.basisOutcomeProjector 0 * (uSw_AAZ.1 * (E_init_AAZ * E_init_AAZᴴ) * uSw_AAZ.1ᴴ)
        = (selAAZ_Z.basisOutcomeProjector 0 * uSw_AAZ.1) * E_init_AAZ * E_init_AAZᴴ * uSw_AAZ.1ᴴ :=
          by
            simp only [Matrix.mul_assoc]
      _ = uSw_AAZ.1 * (selAAZ_Z.basisOutcomeProjector 0 * E_init_AAZ) * E_init_AAZᴴ * uSw_AAZ.1ᴴ :=
        by
            rw [hSwZ]
            simp only [Matrix.mul_assoc]
      _ = uSw_AAZ.1 * (E_init_AAZ * E_init_AAZᴴ) * uSw_AAZ.1ᴴ := by
            rw [selAAZ_Z_proj0_mul_E_init_AAZ]
            simp only [Matrix.mul_assoc]
  have hPZ_UpebPswAAZ : selAAZ_Z.basisOutcomeProjector 0 * (uC7_AAZ.1 * P_sw_AAZ) =
      uC7_AAZ.1 * P_sw_AAZ := by
    have hAA_Z_comm : selAAZ_Z.basisOutcomeProjector 0 *
        (selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 =
        (selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 *
          selAAZ_Z.basisOutcomeProjector 0 :=
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_AA) selAAZ_Z
        (selDataInAct_disj_selMeasInAct (kFull80 + 18)) _ 0).symm
    have hC7Sw : uC7_AAZ.1 * uSw_AAZ.1 * E_init_AAZ =
        uSw_AAZ.1 * ((selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 * E_init_AAZ) := by
      have hSwSqM : uSw_AAZ.1 * uSw_AAZ.1 = 1 := unitary_val_mul_self_eq_one_assoc hSwSq_AAZ
      have hC9M : (uSw_AAZ.1 * uC7_AAZ.1 * uSw_AAZ.1) * E_init_AAZ =
          (selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 * E_init_AAZ := by
        have h := uC9_AAZ_eq_on_E_init
        rw [huC9_eq_sw_uC7] at h
        simpa only [Submonoid.coe_mul, Matrix.mul_assoc] using h
      calc uC7_AAZ.1 * uSw_AAZ.1 * E_init_AAZ
          = (uSw_AAZ.1 * uSw_AAZ.1) * uC7_AAZ.1 * uSw_AAZ.1 * E_init_AAZ := by
              rw [hSwSqM, Matrix.one_mul]
        _ = uSw_AAZ.1 * ((uSw_AAZ.1 * uC7_AAZ.1 * uSw_AAZ.1) * E_init_AAZ) := by
              simp only [Matrix.mul_assoc]
        _ = uSw_AAZ.1 * ((selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 * E_init_AAZ) :=
          by
              rw [hC9M]
    dsimp only [P_sw_AAZ, P_init_AAZ]
    let UAf := (selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1
    calc selAAZ_Z.basisOutcomeProjector 0 *
      (uC7_AAZ.1 * (uSw_AAZ.1 * (E_init_AAZ * E_init_AAZᴴ) * uSw_AAZ.1ᴴ))
        = selAAZ_Z.basisOutcomeProjector 0 *
          ((uC7_AAZ.1 * uSw_AAZ.1 * E_init_AAZ) * (E_init_AAZᴴ * uSw_AAZ.1ᴴ)) := by
            simp only [Matrix.mul_assoc]
      _ = (selAAZ_Z.basisOutcomeProjector 0 * uSw_AAZ.1) * (UAf * E_init_AAZ) *
        (E_init_AAZᴴ * uSw_AAZ.1ᴴ) := by
            rw [hC7Sw]; dsimp only [UAf]; simp only [Matrix.mul_assoc]
      _ = uSw_AAZ.1 * (selAAZ_Z.basisOutcomeProjector 0 * UAf) * E_init_AAZ *
        (E_init_AAZᴴ * uSw_AAZ.1ᴴ) := by
            rw [hSwZ]; simp only [Matrix.mul_assoc]
      _ = uSw_AAZ.1 * UAf * (selAAZ_Z.basisOutcomeProjector 0 * E_init_AAZ) *
        (E_init_AAZᴴ * uSw_AAZ.1ᴴ) := by
            dsimp only [UAf]; rw [hAA_Z_comm]; simp only [Matrix.mul_assoc]
      _ = uSw_AAZ.1 * (UAf * E_init_AAZ) * (E_init_AAZᴴ * uSw_AAZ.1ᴴ) := by
            rw [selAAZ_Z_proj0_mul_E_init_AAZ]; simp only [Matrix.mul_assoc]
      _ = uC7_AAZ.1 * (uSw_AAZ.1 * (E_init_AAZ * E_init_AAZᴴ) * uSw_AAZ.1ᴴ) := by
            dsimp only [UAf]; rw [← hC7Sw]; simp only [Matrix.mul_assoc]
  have hPHold_split : PHold36_0 = PZ18_0 * PCarry18_0 := by
    dsimp only [PHold36_0, PZ18_0, PCarry18_0]
    rw [← rCarry18OfSub18_proj0_mul_rZ18OfSub18_proj0 hm36 rWork]
    exact basisOutcomeProjector_comm_part4 rCarry18 rZ18 0 0
  have hPZ_eq_AAZ : PZ18_0 = rAAZ.embedMatrix (selAAZ_Z.basisOutcomeProjector 0) := by
    dsimp only [PZ18_0]; rw [embedMatrix_basisOutcomeProjector_gen_part4, hAAZ_Z]
  have hPHold_of_PZ {M : Operator (2 ^ ((kFull80 + 18) + 18))}
      (hZ : selAAZ_Z.basisOutcomeProjector 0 * M = M) :
      PHold36_0 * (rAAZ.embedMatrix M * P_CW) = rAAZ.embedMatrix M * P_CW := by
    dsimp only [P_CW]
    rw [hPHold_split, hPZ_eq_AAZ]
    calc (rAAZ.embedMatrix (selAAZ_Z.basisOutcomeProjector 0) * PCarry18_0) *
            (rAAZ.embedMatrix M * (PCarry18_0 * PW136))
        = (rAAZ.embedMatrix (selAAZ_Z.basisOutcomeProjector 0) * rAAZ.embedMatrix M) *
            (PCarry18_0 * PCarry18_0) * PW136 := by
            rw [Matrix.mul_assoc (rAAZ.embedMatrix (selAAZ_Z.basisOutcomeProjector 0)),
                ← Matrix.mul_assoc PCarry18_0,
                ← (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZ) rCarry18
                  hAAZ_Carry M 0]
            dsimp only [PCarry18_0]
            simp only [Matrix.mul_assoc]
      _ = rAAZ.embedMatrix M * (PCarry18_0 * PW136) := by
            dsimp only [PCarry18_0]
            rw [← rAAZ.embedMatrix_mul, hZ, basisOutcomeProjector_zero_mul_self, Matrix.mul_assoc]
  have hPHold_Psw : PHold36_0 * P_sw_n = P_sw_n := hPHold_of_PZ hPZ_PswAAZ
  have hPHold_UpebPsw : PHold36_0 * (U_peb.1 * P_sw_n) = U_peb.1 * P_sw_n := by
    dsimp only [P_sw_n, U_peb]
    rw [QRegister.embedUnitary_val, ← Matrix.mul_assoc (rAAZ.embedMatrix _),
        ← rAAZ.embedMatrix_mul]
    exact hPHold_of_PZ hPZ_UpebPswAAZ
  let P_mid := V_tot.1 * P_sw_n * V_tot.1ᴴ
  have hPmid_herm : P_midᴴ = P_mid := conj_herm_part4 V_tot.1 hPsw_n_herm
  have hVtot_Psw : V_tot.1 * P_sw_n = (C_18 * U_xorZ).1 * P_sw_n := by
    rw [← hPHold_Psw, ← Matrix.mul_assoc, hVtot_PHold, Matrix.mul_assoc]
  have hPmid_eq : P_mid = (C_18 * U_xorZ).1 * P_sw_n * (C_18 * U_xorZ).1ᴴ :=
    conj_eq_of_mul_eq_part4 hPsw_n_herm hVtot_Psw
  have hUxorZ_comm_P218W : U_xorZ.1 * (P218_n * PW136) = (P218_n * PW136) * U_xorZ.1 := by
    have hSubIdle : rSubst.compose (rPGIdle 11 (by decide)) = rIdle11 := by
      apply qreg_ext; intro j
      dsimp only [rSubst, rActAnchorSubst, rIdle11]
      rw [QRegister.compose_apply, QRegister.compose_apply,
          rDataSubstSlot0_apply_of_not_mem _ _ _ _ (fun ⟨q, hq⟩ ↦
            rSlot0InFull_disj_rPGIdle11.ne q j hq)]
    have hSubPosIdle : rSubstPos.DisjointWires rIdle11 := by
      rw [← hSubIdle]
      exact disjointWires_compose_of_disjoint rSubst
        (rCoreFull_disj_rPGIdle11.compose_left selPosCoreInCore80)
    have hSubPZ_W136 : (rSubstPos.concat rZ18 hSubPZ).DisjointWires rW136 :=
        disjointWires_concat_left hSubPZ (disj_concat_right_part4 hWRestIdle
        ((hSubW.compose_left rPosCoreInFull).compose_right _) hSubPosIdle) hZW136
    have hUW : U_xorZ.1 * PW136 = PW136 * U_xorZ.1 := by
      rw [hUxorZ_eq]
      exact
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rSubstPos.concat rZ18 hSubPZ))
        rW136 hSubPZ_W136 _ 0
    dsimp only [U_xorZ, P218_n]
    rw [← Matrix.mul_assoc, QRegister.embedUnitary_val, ← rAAZ.embedMatrix_mul, hXorS218,
        rAAZ.embedMatrix_mul, Matrix.mul_assoc, ← QRegister.embedUnitary_val, hUW,
          ← Matrix.mul_assoc]
  have hP218W_sub_Pmid : (P218_n * PW136) * P_mid = P_mid := by
    have hP218Init : P218_AAZ * E_init_AAZ = E_init_AAZ := by
      rw [P218_AAZ_def, E_init_AAZ_def]
      dsimp only [selAAZ_Data]
      rw [QRegister.compose_assoc, QRegister.embedMatrix_compose, ← Matrix.mul_assoc,
          ← selAAZ_AA.embedMatrix_mul, pStream218_mul_E_anchorLoc_E_raw217]
    have hP218_PswAAZ : P218_AAZ * P_sw_AAZ = P_sw_AAZ := by
      dsimp only [P_sw_AAZ, P_init_AAZ]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← uSw_AAZ_comm_Pc2_and_streams.2.1,
          Matrix.mul_assoc uSw_AAZ.1 P218_AAZ, ← Matrix.mul_assoc P218_AAZ E_init_AAZ, hP218Init]
    have hP218W_Psw : (P218_n * PW136) * P_sw_n = P_sw_n := by
      dsimp only [P_sw_n, P_CW, P218_n]
      calc (rAAZ.embedMatrix P218_AAZ * PW136) * (rAAZ.embedMatrix P_sw_AAZ * (PCarry18_0 * PW136))
          = (rAAZ.embedMatrix P218_AAZ * rAAZ.embedMatrix P_sw_AAZ) *
              (PCarry18_0 * (PW136 * PW136)) := by
              rw [Matrix.mul_assoc (rAAZ.embedMatrix P218_AAZ),
                  ← Matrix.mul_assoc PW136 (rAAZ.embedMatrix P_sw_AAZ), hPsw_comm_W136.symm,
                  Matrix.mul_assoc (rAAZ.embedMatrix P_sw_AAZ) PW136,
                  ← Matrix.mul_assoc PW136 PCarry18_0 PW136,
                  (basisOutcomeProjector_comm_part4 rCarry18 rW136 0 0).symm]
              dsimp only [PCarry18_0, PW136]; simp only [Matrix.mul_assoc]
        _ = rAAZ.embedMatrix P_sw_AAZ * (PCarry18_0 * PW136) := by
              dsimp only [PCarry18_0, PW136]
              rw [← rAAZ.embedMatrix_mul, hP218_PswAAZ, basisOutcomeProjector_zero_mul_self]
    have hCU_comm : (P218_n * PW136) * (C_18 * U_xorZ).1 = (C_18 * U_xorZ).1 * (P218_n * PW136) :=
      by
      rw [Submonoid.coe_mul, ← Matrix.mul_assoc, hC18_comm_P218W.symm,
          Matrix.mul_assoc C_18.1, hUxorZ_comm_P218W.symm, ← Matrix.mul_assoc]
    rw [hPmid_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCU_comm,
        Matrix.mul_assoc (C_18 * U_xorZ).1 _ P_sw_n, hP218W_Psw]
  have hOpOnPmid : (C_18.1 * U_mid5.1 * C_18.1ᴴ) * P_mid =
      (V_tot.1 * U_peb.1 * V_tot.1ᴴ) * P_mid := by
    have hVtot_UpebPsw : V_tot.1 * (U_peb.1 * P_sw_n) =
        (C_18 * U_xorZ).1 * (U_peb.1 * P_sw_n) := by
      rw [← hPHold_UpebPsw, ← Matrix.mul_assoc, hVtot_PHold, Matrix.mul_assoc]
    have hUpeb_unf : U_peb.1 = U_xorZ.1 * U_mid5.1 * U_xorZ.1 := by
      dsimp only [U_peb, uC7_AAZ, U_xorZ, U_mid5]
      simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    have hConjC7 : (C_18 * U_xorZ).1 * U_peb.1 * (C_18 * U_xorZ).1ᴴ =
        C_18.1 * U_mid5.1 * C_18.1ᴴ := by
      rw [Submonoid.coe_mul, Matrix.conjTranspose_mul, hUxorZ_herm, hUpeb_unf]
      exact conj_invol_mid_part4 C_18.1 U_xorZ.1 U_mid5.1 hUxorZ_sq
    rw [← hConjC7]
    exact conj_unitary_eq_on_proj_part4 V_tot (C_18 * U_xorZ) hPsw_n_herm hVtot_Psw hVtot_UpebPsw
  have hMid5PebMid :=
    (Pass1BarrelIdxPebbled273.RealizesOnProj.mono_proj
      hP218W_herm hPmid_herm hP218W_sub_Pmid hMid5PebC18).congr_op hPmid_herm hOpOnPmid
  have hcXorQ_inv : cXorQ.eval = cXorQ.eval⁻¹ :=
    eval_eq_inv_of_classicalPerm_id
      (copyXorRegCircuit_classicalPerm (phcHead_rQRev18 rSubstPos) rZ18 hQDisj)
      (copyXorRegCircuit_classicalPerm (phcHead_rQRev18 rSubstPos) rZ18 hQDisj)
      (fun β ↦ by
        funext z
        by_cases hz : ∃ k : Fin 18, rZ18 k = z
        · obtain ⟨k, rfl⟩ := hz
          have hQNotZ : phcHead_rQRev18 rSubstPos k ∉ Set.range rZ18.wires :=
            fun ⟨j, hj⟩ ↦ hQDisj.ne k j hj.symm
          rw [writeReg_apply_reg, writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ hQNotZ,
              add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · rw [writeReg_apply_of_not_mem _ _ _ _ hz, writeReg_apply_of_not_mem _ _ _ _ hz])
  have hBodyPeb :=
    Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit
      (P := (uSymStepFwdList L).1 * P_sw_n * (uSymStepFwdList L).1ᴴ)
      (U := (uSymStepFwdList L).1 * U_peb.1 * (uSymStepFwdList L).1ᴴ)
      cXorQ cXorQ hcXorQ_inv (by
      have hP_assoc : cXorQ.eval.1 * ((uSymStepFwdList L).1 * P_sw_n * (uSymStepFwdList L).1ᴴ) *
          cXorQ.eval.1ᴴ = P_mid := by
        dsimp only [P_mid, V_tot]
        simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have hU_assoc : cXorQ.eval.1 * ((uSymStepFwdList L).1 * U_peb.1 * (uSymStepFwdList L).1ᴴ) *
          cXorQ.eval.1ᴴ = V_tot.1 * U_peb.1 * V_tot.1ᴴ := by
        dsimp only [V_tot]
        simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rwa [hP_assoc, hU_assoc])
  have hvL := (zTargetSteps36_valid_and_eval (le_refl 36) rSubstPos rHold36 hSubPHold
    ∅ (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)).1
  have hTailPsw : Pass1BarrelIdxPebbled273.HasCleanTailFrom rHold36 0 P_sw_n :=
    fun q _ ↦ by
      rw [← hPHold_Psw, ← Matrix.mul_assoc, singleton_proj0_mul_reg_proj0 rHold36 q, hPHold_Psw]
  have hTailUpeb : Pass1BarrelIdxPebbled273.HasCleanTailFrom rHold36 0 (U_peb.1 * P_sw_n) :=
    fun q _ ↦ by
      rw [← hPHold_UpebPsw, ← Matrix.mul_assoc, singleton_proj0_mul_reg_proj0 rHold36 q,
        hPHold_UpebPsw]
  have hPebWrap :=
    realizesOnProj_symWrapDynList v rHold36 0 L hvL hPsw_n_herm hTailPsw hTailUpeb hBodyPeb
  let cSw := cSwapCore3967.onRegister rCore
  have hcSw_eval : cSw.eval = rAAZ.embedUnitary uSw_AAZ := by
    dsimp only [cSw]
    rw [Circuit.eval_onRegister, ← uSwapCore3967_eq_eval, uSw_AAZ_def,
        ← QRegister.embedUnitary_compose, hCompCore]
  have hcSw_sq : cSw.eval * cSw.eval = 1 := by
    rw [hcSw_eval, ← QRegister.embedUnitary_mul, hSwSq_AAZ, QRegister.embedUnitary_one]
  have hcSw_inv : cSw.eval = cSw.eval⁻¹ := eq_inv_of_mul_eq_one_left hcSw_sq
  have hcSw_herm : cSw.eval.1ᴴ = cSw.eval.1 :=
    unitary_herm_of_sq_one (congrArg Subtype.val hcSw_sq)
  have hcSw_comm_PCW : cSw.eval.1 * P_CW = P_CW * cSw.eval.1 := by
    rw [hcSw_eval]; dsimp only [P_CW, PCarry18_0]
    rw [← Matrix.mul_assoc, QRegister.embedUnitary_val,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZ) rCarry18 hAAZ_Carry _ 0,
        ← QRegister.embedUnitary_val, Matrix.mul_assoc, hSw_comm_W136, ← Matrix.mul_assoc]
  have hInnerPeb : PebRealizes P_init_n U_C9.1
      (dInnerSwapAnchor_ofStr hm155 v dStrAdd dStrInv rAct rAnchor18 rWork hAA hAW hAnW) := by
    unfold dInnerSwapAnchor_ofStr
    refine Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit
      cSw cSw hcSw_inv ?_
    have hP_eq : cSw.eval.1 * P_init_n * cSw.eval.1ᴴ = P_sw_n := by
      dsimp only [P_init_n, P_sw_n, P_sw_AAZ]
      rw [hcSw_herm, hSwHerm_AAZ]
      calc cSw.eval.1 * (rAAZ.embedMatrix P_init_AAZ * P_CW) * cSw.eval.1
          = cSw.eval.1 * rAAZ.embedMatrix P_init_AAZ * (P_CW * cSw.eval.1) := by
              simp only [Matrix.mul_assoc]
        _ = (cSw.eval.1 * rAAZ.embedMatrix P_init_AAZ * cSw.eval.1) * P_CW := by
              rw [← hcSw_comm_PCW]; simp only [Matrix.mul_assoc]
        _ = rAAZ.embedMatrix (uSw_AAZ.1 * P_init_AAZ * uSw_AAZ.1) * P_CW := by
              rw [hcSw_eval, QRegister.embedUnitary_val, ← rAAZ.embedMatrix_mul,
                ← rAAZ.embedMatrix_mul]
    have hU_eq : cSw.eval.1 * U_C9.1 * cSw.eval.1ᴴ = U_peb.1 := by
      dsimp only [U_C9, U_peb]
      rw [hcSw_herm, hcSw_eval, huC9_eq_sw_uC7, ← Submonoid.coe_mul, ← Submonoid.coe_mul,
          ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
      apply congrArg Subtype.val; apply congrArg rAAZ.embedUnitary
      calc uSw_AAZ * (uSw_AAZ * uC7_AAZ * uSw_AAZ) * uSw_AAZ
          = (uSw_AAZ * uSw_AAZ) * uC7_AAZ * (uSw_AAZ * uSw_AAZ) := by simp only [_root_.mul_assoc]
        _ = uC7_AAZ := by rw [hSwSq_AAZ, one_mul, mul_one]
    rwa [hP_eq, hU_eq]
  -- Step 5: Convert `PebRealizes P_init_n` to `RealizesOnProj (E_anchor (E_raw217 * pPGIdleZero
  -- 11))`
  have hInnerProj := (pebRealizes_iff_realizesOnProj hPinit_n_herm U_C9 _).mp hInnerPeb
  have hEinit_comm_PCW := hAAZ_comm_PCW hEinit_comm_W136
  have hEAnchorEq : E_anchor (E_raw217 * pPGIdleZero 11 (by decide)) rAct rAnchor18 rWork hAA =
      rAAZ.embedMatrix E_init_AAZ * P_CW := by
    rw [E_anchor_mul_right E_raw217 (pPGIdleZero 11 (by decide)) rAct rAnchor18 rWork hAA hAW hAnW]
    have hIdleEmbed : rAct.embedMatrix (pPGIdleZero 11 (by decide)) =
        rIdle11.basisOutcomeProjector 0 := by
      unfold pPGIdleZero
      exact embedMatrix_basisOutcomeProjector_zero_assoc rAct (rPGIdle 11 (by decide))
    unfold E_anchor
    rw [hIdleEmbed, ← rHold36OfSub18_proj0_mul_rWRestOfSub18_proj0 hm36 rWork,
        ← rCarry18OfSub18_proj0_mul_rZ18OfSub18_proj0 hm36 rWork,
        basisOutcomeProjector_comm_part4 rCarry18 rZ18 0 0,
        E_init_AAZ_def, rAAZ.embedMatrix_mul, ← QRegister.embedMatrix_compose, hAAZ_AA,
        embedMatrix_basisOutcomeProjector_zero_assoc, hAAZ_Z]
    dsimp only [P_CW, PCarry18_0]
    rw [hPW136_split]
    dsimp only [rAA, rWRest, rCarry18, rZ18]
    simp only [Matrix.mul_assoc]
  have hAbsorbInit : P_init_n * (rAAZ.embedMatrix E_init_AAZ * P_CW) =
      E_anchor (E_raw217 * pPGIdleZero 11 (by decide)) rAct rAnchor18 rWork hAA := by
    have hPCW_idem : P_CW * P_CW = P_CW :=
      idem_mul_of_comm_part4 (basisOutcomeProjector_zero_mul_self rCarry18)
        (basisOutcomeProjector_zero_mul_self rW136)
        (basisOutcomeProjector_comm_part4 rCarry18 rW136 0 0)
    rw [hEAnchorEq]
    dsimp only [P_init_n, P_init_AAZ]
    calc (rAAZ.embedMatrix (E_init_AAZ * E_init_AAZᴴ) * P_CW) *
            (rAAZ.embedMatrix E_init_AAZ * P_CW)
        = (rAAZ.embedMatrix (E_init_AAZ * E_init_AAZᴴ) * rAAZ.embedMatrix E_init_AAZ) *
            (P_CW * P_CW) := by
            rw [Matrix.mul_assoc _ P_CW, ← Matrix.mul_assoc P_CW, hEinit_comm_PCW.symm]
            simp only [Matrix.mul_assoc]
      _ = rAAZ.embedMatrix E_init_AAZ * P_CW := by
            rw [← rAAZ.embedMatrix_mul, E_init_AAZ_mul_conjTranspose_mul_self, hPCW_idem]
  have hOnInit := realizesOnProj_mul_right (rAAZ.embedMatrix E_init_AAZ * P_CW) hInnerProj
  rw [hAbsorbInit] at hOnInit
  refine realizesOnProj_congr_unitary ?_ hOnInit
  have hTargetUnit : rAA.embedUnitary (uAnchorFrame uInnerSwapFull) =
      rAAZ.embedUnitary (selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)) := by
    rw [← QRegister.embedUnitary_compose, hAAZ_AA]
  dsimp only [U_C9]
  rw[hEAnchorEq, hTargetUnit, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← Matrix.mul_assoc _ _ P_CW, ← Matrix.mul_assoc _ _ P_CW, ← rAAZ.embedMatrix_mul,
      ← rAAZ.embedMatrix_mul, uC9_AAZ_eq_on_E_init]
attribute [irreducible] dInnerSwapAnchor_ofStr
end Part4_AnchorStageA48062
end StageADeconstrAndQftShare
end SharedScope
end
end InnerSwapAnchorOfStr

noncomputable section Slot3MidKickWStateMultiBank
set_option maxRecDepth 8192

section
namespace Slot3MidKickWStateMultiBank
local instance (priority := 1000000) instNeZeroTwoPowK16 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (wire_ne_of_lt wire_ne_of_gt cleanRem mul_mulVec_prog writeRegProg writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem)
open MeasureBranchHadamardSem (bit_cases ket matrix_ext_ket ket_CNOT ket_X RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open FastMidKick275Aux
open Prod57BoothHoist
  (p57DiagProj ket_p57DiagProj p57DiagProj_conjTranspose RealizesCleanUnitary_congr_unitary)
open Slot3Exact216Oracle80
open Leaf3PrepAndMidKickSpecs
open MultiBankWStateRouter
open Slot3MidKickOpt
section Part1_WStateSplitEngine
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency false
theorem eval_seq_mulVec {n : ℕ} (c₁ c₂ : Circuit n) (v : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec v = c₂.eval.1.mulVec (c₁.eval.1.mulVec v) := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, mul_mulVec_prog]
/-- Store-locality on variable `v`: `wp d.compile` preserves `v`-independence and only inspects
postconditions along `Function.update σ v _`. -/
def LocalOnVar {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (d : DynamicCircuit Var n) : Prop := (∀ (Ψ : CQAssertionCompat Var (2 ^ n)), (∀ σ val, Ψ
    (Function.update σ v val) = Ψ σ) → ∀ σ val, wp d.compile Ψ (Function.update σ v val) = wp
    d.compile Ψ σ) ∧ (∀ (Θ Φ : CQAssertionCompat Var (2 ^ n)) (σ : Store Var), (∀ val, Θ
    (Function.update σ v val) = Φ (Function.update σ v val)) → wp d.compile Θ σ = wp d.compile
    Φ σ)
theorem LocalOnVar.identity {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) :
    LocalOnVar (n := n) v .identity := by
  refine ⟨fun Ψ hΨ σ val ↦ hΨ σ val, fun Θ Φ σ h ↦ ?_⟩
  simpa only [DynamicCircuit.compile_identity, wp_qSeq, wp_qIf, wp_skip, wp_abort,
    wp_assign_eq_compat, wp_qAssign_eq_compat, wp_qMeasure_eq_compat,
    Function.update_eq_self] using h (σ v)
theorem LocalOnVar.circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (c : Circuit n) : LocalOnVar v (.circuit c) := by
  refine ⟨fun Ψ hΨ σ val ↦ ?_, fun Θ Φ σ h ↦ ?_⟩
  · simp only [DynamicCircuit.compile_circuit, wp_circuit_compile_compat, wpQAssignCompat]
    exact congrArg (qAssignObsMap c.eval) (hΨ σ val)
  · simp only [DynamicCircuit.compile_circuit, wp_circuit_compile_compat, wpQAssignCompat]
    exact congrArg (qAssignObsMap c.eval) (by simpa only [Function.update_eq_self] using h (σ v))
theorem LocalOnVar.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : LocalOnVar v d₁) (h₂ : LocalOnVar v d₂) : LocalOnVar v (.seq d₁ d₂) := by
  refine ⟨fun Ψ hΨ σ val ↦ ?_, fun Θ Φ σ h ↦ ?_⟩
  · simp only [DynamicCircuit.compile_seq, wp_qSeq]
    exact h₁.1 (wp d₂.compile Ψ) (h₂.1 Ψ hΨ) σ val
  · simp only [DynamicCircuit.compile_seq, wp_qSeq]
    refine h₁.2 (wp d₂.compile Θ) (wp d₂.compile Φ) σ fun val ↦ ?_
    refine h₂.2 Θ Φ (Function.update σ v val) fun val' ↦ ?_
    simpa only [Function.update_idem] using h val'
theorem LocalOnVar.measIf {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : QRegister 1 n) (c : Circuit n) :
    LocalOnVar v (.seq (.measure v r) (dynQIfVar v (.circuit c) .identity)) := by
  refine ⟨fun Ψ _ σ val ↦ ?_, fun Θ Φ σ h ↦ ?_⟩
  · simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_measure,
      DynamicCircuit.compile_qIf, DynamicCircuit.compile_circuit,
      QProg.measureRegister, wp_qSeq, wp_qIf, wp_qMeasure_apply,
      CQAssertionCompat.subst_apply, Store.subst, Function.update_idem]
    rfl
  · simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_measure,
      DynamicCircuit.compile_qIf, DynamicCircuit.compile_circuit,
      QProg.measureRegister, wp_qSeq, wp_qIf, wp_qMeasure_apply,
      CQAssertionCompat.subst_apply, Store.subst, wp_circuit_compile_compat, wpQAssignCompat]
    congr 1; funext o
    split_ifs <;> rw [h]
theorem localOnVar_remeasureIf {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (w : Wire n) (c : Circuit n) : LocalOnVar v (remeasureIf_dqmu v w c) :=
  LocalOnVar.measIf v (QRegister.singleton w) c
theorem localOnVar_zResetFixup {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (cFix : Circuit n) : LocalOnVar v (zResetFixupDyn v q cFix) :=
  LocalOnVar.measIf v (QRegister.singleton q) (Circuit.X q ;;ᶜ cFix)
theorem localOnVar_xUnload {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (pairs : List (WirePair n)) {rest : DynamicCircuit Var n}
    (hRest : LocalOnVar v rest) : LocalOnVar v (xUnloadCzPairsSeqDyn v q pairs rest) :=
  (LocalOnVar.circuit v _).seq ((localOnVar_remeasureIf v q _).seq hRest)
theorem localOnVar_wShiftDummyLevel {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k) :
    LocalOnVar v (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd) :=
    (LocalOnVar.circuit v _).seq ((localOnVar_zResetFixup v qEnc _).seq (localOnVar_xUnload v
    wDum _ (LocalOnVar.circuit v _)))
theorem localOnVar_wShiftDummyLevels {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) :
    ∀ (m : ℕ) (hm : m ≤ k), LocalOnVar v (wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj m hm)
  | 0, _ => LocalOnVar.circuit v _
  | d + 1, hd =>
      (localOnVar_wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj d (Nat.le_of_succ_le hd)).seq
        (localOnVar_wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd)
theorem localOnVar_wOptExpandDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) :
    LocalOnVar v (wOptExpandDyn v R k uLo w rDum wDum qEnc hInj) :=
  (LocalOnVar.circuit v _).seq
    (localOnVar_wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj k le_rfl)
/-- Bridge from `LocalOnVar` + `SubspaceStep P (U.1 * P) d` to `RealizesCleanUnitary` +
  `PreservesStoreConst`. -/
theorem LocalOnVar.toRealizesAndPreserves {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d : DynamicCircuit Var n} {U : Unitary (2 ^ n)}
    (hd : LocalOnVar v d) (hP : Pᴴ = P) (hs : SubspaceStep (Var := Var) P (U.1 * P) d) :
    RealizesCleanUnitary v P d U ∧ PreservesStoreConst d := by
  have hc := hs.toConstCleanUnitary hP
  refine ⟨⟨hd.1, fun Θ hΘ σ ↦ ?_⟩, hc.1⟩
  have hConst : wp d.compile Θ σ = wp d.compile (fun _ ↦ Θ σ) σ :=
    hd.2 Θ (fun _ ↦ Θ σ) σ (fun val ↦ hΘ σ val)
  rw [hConst]
  ext1
  simp only [conj_apply_mat, hP, wpQAssignCompat, qAssign_obs_map_val,
    Matrix.conjTranspose_conjTranspose]
  exact hc.2 (Θ σ) σ
/-- Predicate-gated computational-basis state operator: maps `ket δ` (when `InvBit δ` holds) to
  `ket (st δ)`. -/
def predOp {n : ℕ} (InvBit : BitAssignment n → Prop) [DecidablePred InvBit]
    (st : BitAssignment n → BitAssignment n) : Operator (2 ^ n) :=
  mkVecOp fun δ ↦ if InvBit δ then ket (st δ) else 0
theorem predOp_mulVec_ket {n : ℕ} (InvBit : BitAssignment n → Prop) [DecidablePred InvBit]
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : (predOp InvBit st).mulVec
    (ket δ) = if InvBit δ then ket (st δ) else 0 := mkVecOp_mulVec_ket _ δ
theorem subspaceStep_predOp_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (InvBit : BitAssignment n → Prop) [DecidablePred InvBit]
    (st₁ st₂ : BitAssignment n → BitAssignment n) (c : Circuit n)
    (hAct : ∀ δ, InvBit δ → c.eval.1.mulVec (ket (st₁ δ)) = ket (st₂ δ)) :
    SubspaceStep (Var := Var) (predOp InvBit st₁) (predOp InvBit st₂) (.circuit c) := by
  refine subspaceStep_congr_out (subspaceStep_of_circuit (predOp InvBit st₁) c) ?_
  apply matrix_ext_ket; intro δ
  rw [mul_mulVec_prog, predOp_mulVec_ket, predOp_mulVec_ket]
  split_ifs with hc
  · exact hAct δ hc
  · rw [Matrix.mulVec_zero]
/-- `0-T` CNOT XOR accumulation of `M` wires `src 0, ..., src (M - 1)` into `dst`. -/
def cnotSumTo {n : ℕ} : (M : ℕ) → (src : Fin M → Wire n) → (dst : Wire n) →
    (∀ i, src i ≠ dst) → Circuit n
  | 0, _, _, _ => .identity
  | M + 1, src, dst, hne =>
      Circuit.CNOT (src 0) dst (hne 0) ;;ᶜ
        cnotSumTo M (fun i ↦ src i.succ) dst (fun i ↦ hne i.succ)
theorem count_cnotSumTo {n : ℕ} :
    ∀ (M : ℕ) (src : Fin M → Wire n) (dst : Wire n) (hne : ∀ i, src i ≠ dst),
      (cnotSumTo M src dst hne).count .T = 0 ∧ (cnotSumTo M src dst hne).count .TOFF = 0
  | 0, _, _, _ => ⟨rfl, rfl⟩
  | M + 1, src, dst, hne => by
      obtain ⟨ht, hf⟩ := count_cnotSumTo M (fun i ↦ src i.succ) dst (fun i ↦ hne i.succ)
      simp [cnotSumTo, Circuit.count_seq, Circuit.CNOT, ht, hf]
theorem cnotSumTo_mulVec_ket {n : ℕ} :
    ∀ (M : ℕ) (src : Fin M → Wire n) (dst : Wire n) (hne : ∀ i, src i ≠ dst) (δ : BitAssignment n),
      (cnotSumTo M src dst hne).eval.1.mulVec (ket δ) =
        ket (Function.update δ dst (δ dst + ∑ i : Fin M, δ (src i)))
  | 0, _, dst, _, δ => by simp [cnotSumTo, Function.update_eq_self]
  | M + 1, src, dst, hne, δ => by
      rw [cnotSumTo, eval_seq_mulVec, ket_CNOT,
        cnotSumTo_mulVec_ket M (fun i ↦ src i.succ) dst (fun i ↦ hne i.succ)]
      congr 1; funext w
      by_cases hw : w = dst
      · subst hw
        simp only [Function.update_self, Fin.sum_univ_succ]
        have hsum : (∑ i : Fin M, Function.update δ w (δ w + δ (src 0)) (src i.succ)) =
            ∑ i : Fin M, δ (src i.succ) :=
          Finset.sum_congr rfl fun i _ ↦ Function.update_of_ne (hne i.succ) _ _
        rw [hsum, add_assoc]
      · simp [Function.update_of_ne hw]
theorem sum_subOneHot {n M : ℕ} (src : Fin M → Wire n) (hinj : Function.Injective src)
    (base : BitAssignment n) (h0 : ∀ i, base (src i) = 0)
    (act : Bool) (iStar : Fin M) :
    let δ := if act then Function.update base (src iStar) 1 else base
    (∑ i : Fin M, δ (src i)) = if act then 1 else 0 := by
  intro δ
  cases act
  · simp [δ, h0]
  · simp only [δ, ↓reduceIte]
    rw [Finset.sum_eq_single iStar]
    · simp
    · intro j _ hj; rw [Function.update_of_ne (hinj.ne hj), h0 j]
    · intro habs; exact (habs (Finset.mem_univ _)).elim
/-- Clean-dummy wrapper around `wOptExpandDyn` (`2 * R * (2^k - 1) + 2 * k` `T`s):
`(rDum, wDum, qEnc)` start at `0` and end at `0`! -/
def wOptExpandClean {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) : DynamicCircuit Var n :=
  let p0 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  let flat : Fin (R * 2 ^ k) → Wire n := fun idx ↦
    w ⟨idx.val / 2 ^ k, Nat.div_lt_of_lt_mul (by have := idx.isLt; linarith)⟩
      ⟨idx.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  let cPre : Circuit n :=
    Circuit.X rDum ;;ᶜ cnotSumTo R (fun b ↦ w b p0) rDum (fun b ↦ hInj.w_ne_rDum b p0)
  let cPost : Circuit n :=
    cnotSumTo (R * 2 ^ k) flat rDum (fun _ ↦ hInj.w_ne_rDum _ _) ;;ᶜ Circuit.X rDum
  .seq (.circuit cPre) (.seq (wOptExpandDyn v R k uLo w rDum wDum qEnc hInj) (.circuit cPost))
theorem count_wOptExpandClean {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) :
    (wOptExpandClean v R k uLo w rDum wDum qEnc hInj).count .T = 2 * R * (2 ^ k - 1) + 2 * k ∧
    (wOptExpandClean v R k uLo w rDum wDum qEnc hInj).count .TOFF = 0 := by
  have hXT : (Circuit.X rDum).count .T = 0 := rfl
  have hXF : (Circuit.X rDum).count .TOFF = 0 := rfl
  dsimp only [wOptExpandClean, DynamicCircuit.count]
  simp only [Circuit.count_seq, (count_cnotSumTo _ _ _ _).1, (count_cnotSumTo _ _ _ _).2,
    (count_wOptExpandDyn v R k uLo w rDum wDum qEnc hInj).1,
    (count_wOptExpandDyn v R k uLo w rDum wDum qEnc hInj).2, hXT, hXF]
  exact ⟨by omega, trivial⟩
theorem localOnVar_wOptExpandClean {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) : LocalOnVar v
    (wOptExpandClean v R k uLo w rDum wDum qEnc hInj) := (LocalOnVar.circuit v _).seq
    ((localOnVar_wOptExpandDyn v R k uLo w rDum wDum qEnc hInj).seq (LocalOnVar.circuit v _))
theorem subspaceStep_wOptExpandClean_predOp {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (InvBit : BitAssignment n → Prop) [DecidablePred InvBit]
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (baseSt : BitAssignment n → BitAssignment n)
    (actFn : BitAssignment n → Bool)
    (bStarFn : BitAssignment n → Fin R)
    (hClean : ∀ δ, InvBit δ →
      (∀ b p, baseSt δ (w b p) = 0) ∧ baseSt δ rDum = 0 ∧ baseSt δ wDum = 0 ∧ baseSt δ qEnc = 0)
    (_hActIndep : ∀ δ b p, actFn (Function.update δ (w b p) 1) = actFn δ)
    (hActRDum : ∀ δ a, actFn (Function.update δ rDum a) = actFn δ)
    (hBStarRDum : ∀ δ a, bStarFn (Function.update δ rDum a) = bStarFn δ) :
    let p0 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
    let stIn : BitAssignment n → BitAssignment n := fun δ ↦
      if actFn (baseSt δ) then Function.update (baseSt δ) (w (bStarFn (baseSt δ)) p0) 1 else
        baseSt δ
    let stOut : BitAssignment n → BitAssignment n := fun δ ↦ if actFn (baseSt δ) then
        Function.update (baseSt δ) (w (bStarFn (baseSt δ)) ⟨idxValD uLo (baseSt δ),
        idxValD_lt_two_pow uLo _⟩) 1 else baseSt δ
    SubspaceStep (Var := Var) (predOp InvBit stIn) (predOp InvBit stOut)
      (wOptExpandClean v R k uLo w rDum wDum qEnc hInj) := by
  intro p0 stIn stOut
  let baseDum : BitAssignment n → BitAssignment n := fun δ ↦
    Function.update (baseSt δ) rDum (if actFn (baseSt δ) then 0 else 1)
  let stMidIn : BitAssignment n → BitAssignment n := fun δ ↦
    Function.update (stIn δ) rDum (if actFn (baseSt δ) then 0 else 1)
  let stMidOut : BitAssignment n → BitAssignment n := fun δ ↦
    Function.update (stOut δ) rDum (if actFn (baseSt δ) then 0 else 1)
  have hPre : SubspaceStep (Var := Var) (predOp InvBit stIn) (predOp InvBit stMidIn)
      (.circuit (Circuit.X rDum ;;ᶜ cnotSumTo R (fun b ↦ w b p0) rDum (fun b ↦
        hInj.w_ne_rDum b p0))) := by
    refine subspaceStep_predOp_circuit InvBit stIn stMidIn _ fun δ hc ↦ ?_
    obtain ⟨hw0, hr0, _, _⟩ := hClean δ hc
    rw [eval_seq_mulVec, ket_X, cnotSumTo_mulVec_ket]
    have hwinj0 : Function.Injective (fun b : Fin R ↦ w b p0) :=
      fun b₁ b₂ e ↦ (hInj.w_inj b₁ p0 b₂ p0 e).1
    have hsum : (∑ i : Fin R, Function.update (stIn δ) rDum (stIn δ rDum + 1) (w i p0)) =
        if actFn (baseSt δ) then 1 else 0 := by
      have heq : (∑ i : Fin R, Function.update (stIn δ) rDum (stIn δ rDum + 1) (w i p0)) =
          ∑ i : Fin R, stIn δ (w i p0) :=
        Finset.sum_congr rfl fun i _ ↦ Function.update_of_ne (hInj.w_ne_rDum i p0) _ _
      rw [heq]
      exact sum_subOneHot (fun b ↦ w b p0) hwinj0 (baseSt δ) (fun b ↦
        hw0 b p0) (actFn (baseSt δ)) (bStarFn (baseSt δ))
    have hrd_in : stIn δ rDum = 0 := by
      dsimp only [stIn]; split_ifs
      · rw [Function.update_of_ne (hInj.w_ne_rDum _ _).symm, hr0]
      · exact hr0
    rw [Function.update_self, hsum, Function.update_idem, hrd_in, zero_add]
    congr 1; dsimp only [stMidIn]
    by_cases hA : actFn (baseSt δ) = true <;> simp [hA]
  let P_pred : BitAssignment n → Prop := fun γ ↦ γ rDum = (if actFn γ then 0 else 1)
  let _ : DecidablePred P_pred := fun _ ↦ Classical.propDecidable _
  let activePred : BitAssignment n → Prop := fun γ ↦ actFn γ = true
  let _ : DecidablePred activePred := fun _ ↦ inferInstance
  have hMidCore := subspaceStep_mul_right (predOp InvBit baseDum)
    (subspaceStep_wOptExpandDyn (Var := Var) v P_pred activePred bStarFn uLo w rDum wDum qEnc hInj
      (fun _ hP ↦ by dsimp [P_pred, activePred] at hP ⊢; exact hP))
  have hEqMid (m : ℕ) (hm : m ≤ k) (pT : BitAssignment n → Fin (2 ^ k))
      (hpT : ∀ δ, (⟨idxValPrefix uLo (baseDum δ) m hm, Nat.lt_of_lt_of_le
        (idxValPrefix_lt_two_pow uLo (baseDum δ) m hm)
        (Nat.pow_le_pow_right (by omega) hm)⟩ : Fin (2 ^ k)) = pT δ) :
      oneHotOptPreOp (OptBasePred P_pred wDum qEnc) activePred bStarFn uLo w m hm *
        predOp InvBit baseDum =
      predOp InvBit (fun δ ↦ Function.update
        (if actFn (baseSt δ) then Function.update (baseSt δ) (w (bStarFn (baseSt δ)) (pT δ)) 1
         else baseSt δ) rDum (if actFn (baseSt δ) then 0 else 1)) := by
    apply matrix_ext_ket
    intro δ
    rw [mul_mulVec_prog, predOp_mulVec_ket, predOp_mulVec_ket]
    by_cases hc : InvBit δ
    · rw [ite_eq_left hc, ite_eq_left hc]
      obtain ⟨hw0, _, hwd0, hq0⟩ := hClean δ hc
      dsimp only [oneHotOptPreOp]
      rw [mkVecOp_mulVec_ket]
      dsimp only [oneHotOptPreVec]
      have hbd_w : ∀ b p, baseDum δ (w b p) = 0 := fun b p ↦
        (Function.update_of_ne (hInj.w_ne_rDum b p) _ _).trans (hw0 b p)
      have hbd_P : OptBasePred P_pred wDum qEnc (baseDum δ) := by
        refine ⟨?_, (Function.update_of_ne hInj.rDum_ne_wDum.symm _ _).trans hwd0,
          (Function.update_of_ne hInj.rDum_ne_qEnc.symm _ _).trans hq0⟩
        dsimp [P_pred, baseDum]
        rw [Function.update_self, hActRDum]
      rw [ite_eq_left ⟨hbd_P, hbd_w⟩]
      have hAct_bd : activePred (baseDum δ) ↔ actFn (baseSt δ) = true := by
        dsimp [activePred, baseDum]
        rw [hActRDum]
      by_cases hA : actFn (baseSt δ) = true
      · rw [ite_eq_left (hAct_bd.mpr hA), hpT δ, hBStarRDum _ _]
        dsimp only [baseDum]
        simp only [hA, ↓reduceIte]
        exact congrArg ket (Function.update_comm (hInj.w_ne_rDum _ _).symm _ _ _)
      · rw [ite_eq_right (mt hAct_bd.mp hA)]
        dsimp only [baseDum]
        simp only [hA, Bool.false_eq_true, ↓reduceIte]
    · rw [ite_eq_right hc, ite_eq_right hc, Matrix.mulVec_zero]
  have hEqMidIn : oneHotOptPreOp (OptBasePred P_pred wDum qEnc) activePred bStarFn uLo w 0
      (Nat.zero_le k) * predOp InvBit baseDum = predOp InvBit stMidIn :=
    hEqMid 0 (Nat.zero_le k) (fun _ ↦ p0) (fun _ ↦ Fin.ext rfl)
  have hEqMidOut : oneHotOptPreOp (OptBasePred P_pred wDum qEnc) activePred bStarFn uLo w k
      le_rfl * predOp InvBit baseDum = predOp InvBit stMidOut :=
    hEqMid k le_rfl (fun δ ↦ ⟨idxValD uLo (baseSt δ), idxValD_lt_two_pow uLo _⟩)
      (fun δ ↦ Fin.ext (idxValD_congr uLo fun d ↦ Function.update_of_ne (hInj.uLo_ne_rDum d) _ _))
  have hMid : SubspaceStep (Var := Var) (predOp InvBit stMidIn) (predOp InvBit stMidOut)
      (wOptExpandDyn v R k uLo w rDum wDum qEnc hInj) := by
    rw [← hEqMidIn, ← hEqMidOut]; exact hMidCore
  let flat : Fin (R * 2 ^ k) → Wire n := fun idx ↦
    w ⟨idx.val / 2 ^ k, Nat.div_lt_of_lt_mul (by have := idx.isLt; linarith)⟩
      ⟨idx.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  have hFlatInj : Function.Injective flat := by
    intro i₁ i₂ e
    obtain ⟨hb, hp⟩ := hInj.w_inj _ _ _ _ e
    have hdiv : i₁.val / 2 ^ k = i₂.val / 2 ^ k := congrArg Fin.val hb
    have hmod : i₁.val % 2 ^ k = i₂.val % 2 ^ k := congrArg Fin.val hp
    have hd₁ := Nat.div_add_mod i₁.val (2 ^ k)
    have hd₂ := Nat.div_add_mod i₂.val (2 ^ k)
    exact Fin.ext (by rw [← hd₁, ← hd₂, hdiv, hmod])
  have hPost : SubspaceStep (Var := Var) (predOp InvBit stMidOut) (predOp InvBit stOut)
      (.circuit (cnotSumTo (R * 2 ^ k) flat rDum (fun _ ↦
        hInj.w_ne_rDum _ _) ;;ᶜ Circuit.X rDum)) := by
    refine subspaceStep_predOp_circuit InvBit stMidOut stOut _ fun δ hc ↦ ?_
    obtain ⟨hw0, hr0, _, _⟩ := hClean δ hc
    rw [eval_seq_mulVec, cnotSumTo_mulVec_ket, ket_X]
    have hsum_eq : (∑ idx : Fin (R * 2 ^ k), stMidOut δ (flat idx)) =
        ∑ idx : Fin (R * 2 ^ k), stOut δ (flat idx) :=
      Finset.sum_congr rfl fun idx _ ↦ Function.update_of_ne (hInj.w_ne_rDum _ _) _ _
    have hsum : (∑ idx : Fin (R * 2 ^ k), stOut δ (flat idx)) = if actFn (baseSt δ) then 1 else 0 :=
      by
      by_cases hA : actFn (baseSt δ) = true
      · let bS := bStarFn (baseSt δ)
        let pS : Fin (2 ^ k) := ⟨idxValD uLo (baseSt δ), idxValD_lt_two_pow uLo _⟩
        let iS : Fin (R * 2 ^ k) := ⟨bS.val * 2 ^ k + pS.val, by
          have hb := bS.isLt; have hp := pS.isLt; nlinarith⟩
        have hflatS : flat iS = w bS pS := by
          dsimp only [flat, iS]
          have hdiv : (bS.val * 2 ^ k + pS.val) / 2 ^ k = bS.val := by
            rw [Nat.mul_comm bS.val (2 ^ k), Nat.mul_add_div (Nat.two_pow_pos k),
              Nat.div_eq_of_lt pS.isLt, add_zero]
          have hmod : (bS.val * 2 ^ k + pS.val) % 2 ^ k = pS.val := by
            rw [Nat.mul_comm bS.val (2 ^ k), Nat.mul_add_mod, Nat.mod_eq_of_lt pS.isLt]
          congr 1
          · exact Fin.ext hdiv
          · exact Fin.ext hmod
        have hstS : stOut δ = Function.update (baseSt δ) (flat iS) 1 := by
          simp only [stOut, hA, ↓reduceIte, hflatS, bS, pS]
        rw [hstS]
        simpa [hA] using sum_subOneHot flat hFlatInj (baseSt δ) (fun _ ↦ hw0 _ _) true iS
      · simp [stOut, hA, flat, hw0]
    rw [hsum_eq, hsum, Function.update_self, Function.update_idem]
    dsimp only [stMidOut]
    rw [Function.update_self, Function.update_idem]
    have hrd_out : stOut δ rDum = 0 := by
      dsimp only [stOut]; split_ifs
      · rw [Function.update_of_ne (hInj.w_ne_rDum _ _).symm, hr0]
      · exact hr0
    congr 1
    have hval : ((if actFn (baseSt δ) = true then (0 : ZMod 2) else 1) +
        (if actFn (baseSt δ) = true then 1 else 0) + 1) = stOut δ rDum := by
      rw [hrd_out]; by_cases hA : actFn (baseSt δ) = true <;> simp [hA]
    rw [hval, Function.update_eq_self]
  exact hPre.seq (hMid.seq hPost)
/-- Pair-of-wires matrix `Fin N → Fin (2 ^ 1) → Wire n` on `r268 : QRegister 268 n`. -/
def wPairBit268 {n N : ℕ} (r268 : QRegister 268 n) (w0 w1 : Fin N → Wire 268) : Fin N → Fin
    (2 ^ 1) → Wire n := fun i p ↦ if p.val = 0 then r268 (w0 i) else r268 (w1 i)
@[simp] theorem wPairBit268_zero {n N : ℕ} (r268 : QRegister 268 n) (w0 w1 : Fin N → Wire 268)
    (i : Fin N) (h0 : 0 < 2 ^ 1) : wPairBit268 r268 w0 w1 i ⟨0, h0⟩ = r268 (w0 i) := rfl
@[simp] theorem wPairBit268_zero_fin2 {n N : ℕ} (r268 : QRegister 268 n)
    (w0 w1 : Fin N → Wire 268) (i : Fin N) : wPairBit268 r268 w0 w1 i 0 = r268 (w0 i) := rfl
@[simp] theorem wPairBit268_one_fin2 {n N : ℕ} (r268 : QRegister 268 n)
    (w0 w1 : Fin N → Wire 268) (i : Fin N) : wPairBit268 r268 w0 w1 i 1 = r268 (w1 i) := rfl
theorem wOptInj_bit268 {n N : ℕ} (r268 : QRegister 268 n) (w0 w1 : Fin N → Wire 268)
    (actB : Wire 268) (hb : actB.val < 174) (hw0 : ∀ i, 174 ≤ (w0 i).val ∧ (w0 i).val < 265)
    (hw1 : ∀ i, 174 ≤ (w1 i).val ∧ (w1 i).val < 265) (h01 : ∀ i j, w0 i ≠ w1 j)
    (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1) :
    WOptInj N 1 ![r268 actB] (wPairBit268 r268 w0 w1)
    (r268 ⟨265, by decide⟩) (r268 ⟨266, by decide⟩) (r268 ⟨267, by decide⟩) := by
  have huNe {c : Wire 268} (hc : 174 ≤ c.val) (d : Fin 1) : ![r268 actB] d ≠ r268 c := by
    fin_cases d
    exact r268.wires.injective.ne (wire_ne_of_lt (by omega))
  have hwNe {c : Wire 268} (hc : 265 ≤ c.val) (b : Fin N) (p : Fin (2 ^ 1)) :
      wPairBit268 r268 w0 w1 b p ≠ r268 c := by
    dsimp only [wPairBit268]
    split_ifs
    · exact r268.wires.injective.ne (wire_ne_of_lt (by have := (hw0 b).2; omega))
    · exact r268.wires.injective.ne (wire_ne_of_lt (by have := (hw1 b).2; omega))
  exact
    { w_inj b₁ p₁ b₂ p₂ e := by
        have hp₁ := p₁.isLt
        have hp₂ := p₂.isLt
        dsimp only [wPairBit268] at e
        split_ifs at e with h1 h2 h2
        · exact ⟨hinj0 (r268.wires.injective e), Fin.ext (by omega)⟩
        · exact (h01 b₁ b₂ (r268.wires.injective e)).elim
        · exact (h01 b₂ b₁ (r268.wires.injective e.symm)).elim
        · exact ⟨hinj1 (r268.wires.injective e), Fin.ext (by omega)⟩
      uLo_ne_w d b p := by
        dsimp only [wPairBit268]
        split_ifs
        · exact huNe (hw0 b).1 d
        · exact huNe (hw1 b).1 d
      uLo_ne_rDum := huNe (by decide)
      uLo_ne_wDum := huNe (by decide)
      uLo_ne_qEnc := huNe (by decide)
      w_ne_rDum := hwNe (by decide)
      w_ne_wDum := hwNe (by decide)
      w_ne_qEnc := hwNe (by decide)
      rDum_ne_wDum := r268.wires.injective.ne (by decide)
      rDum_ne_qEnc := r268.wires.injective.ne (by decide)
      wDum_ne_qEnc := r268.wires.injective.ne (by decide) }
/-- W-State Regime-II dynamic circuit (`2 * N + 2` `T`s, `0 .TOFF`) replacing
`mk94SeqSplit N (fun i ↦ mk94SplitBit (w0 i) (w1 i) actB ...)`. -/
def dSeqSplitBit_wstate {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n) (N : ℕ)
    (w0 w1 : Fin N → Wire 268) (actB : Wire 268) (hb : actB.val < 174)
    (hw0 : ∀ i, 174 ≤ (w0 i).val ∧ (w0 i).val < 265)
    (hw1 : ∀ i, 174 ≤ (w1 i).val ∧ (w1 i).val < 265) (h01 : ∀ i j, w0 i ≠ w1 j)
    (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1) : DynamicCircuit Var n :=
  wOptExpandClean v N 1 ![r268 actB] (wPairBit268 r268 w0 w1)
    (r268 ⟨265, by decide⟩) (r268 ⟨266, by decide⟩) (r268 ⟨267, by decide⟩)
    (wOptInj_bit268 r268 w0 w1 actB hb hw0 hw1 h01 hinj0 hinj1)
theorem dSeqSplitBit_wstate_counts {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n)
    (N : ℕ) (w0 w1 : Fin N → Wire 268) (actB : Wire 268) (hb : actB.val < 174)
    (hw0 : ∀ i, 174 ≤ (w0 i).val ∧ (w0 i).val < 265)
    (hw1 : ∀ i, 174 ≤ (w1 i).val ∧ (w1 i).val < 265) (h01 : ∀ i j, w0 i ≠ w1 j)
    (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1) : (dSeqSplitBit_wstate v
    r268 N w0 w1 actB hb hw0 hw1 h01 hinj0 hinj1).count .T = 2 * N + 2 ∧ (dSeqSplitBit_wstate
    v r268 N w0 w1 actB hb hw0 hw1 h01 hinj0 hinj1).count .TOFF = 0 := by
  obtain ⟨ht, hf⟩ := count_wOptExpandClean v N 1 ![r268 actB] (wPairBit268 r268 w0 w1)
    (r268 ⟨265, by decide⟩) (r268 ⟨266, by decide⟩) (r268 ⟨267, by decide⟩)
    (wOptInj_bit268 r268 w0 w1 actB hb hw0 hw1 h01 hinj0 hinj1)
  exact ⟨ht.trans (by omega), hf⟩
theorem idxValD_singleton {n : ℕ} (w : Wire n) (γ : BitAssignment n) :
    idxValD ![w] γ = (γ w).val := by
  dsimp [idxValD, idxValPrefix]
  rcases bit_cases (γ w) with h | h <;> simp [h, ZMod.val_zero]
theorem dSeqSplitBit_wstate_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r268 : QRegister 268 n)
    (N : ℕ) (w0 w1 : Fin N → Wire 268) (actB : Wire 268)
    (hb : actB.val < 174)
    (hw0 : ∀ i, 174 ≤ (w0 i).val ∧ (w0 i).val < 265)
    (hw1 : ∀ i, 174 ≤ (w1 i).val ∧ (w1 i).val < 265)
    (h01 : ∀ i j, w0 i ≠ w1 j)
    (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1)
    (Inv : BitAssignment 268 → Prop)
    (actFn268 : BitAssignment 268 → Bool)
    (bStarFn268 : BitAssignment 268 → Fin N)
    (hActLt : ∀ {γ₁ γ₂ : BitAssignment 268},
      (∀ q : Wire 268, q.val < 174 → γ₁ q = γ₂ q) →
      actFn268 γ₁ = actFn268 γ₂ ∧ bStarFn268 γ₁ = bStarFn268 γ₂)
    (hInv : ∀ γ : BitAssignment 268, Inv γ →
      (∀ i : Fin N,
        γ (w0 i) = (if actFn268 γ then 1 else 0) * (if i = bStarFn268 γ then 1 else 0)) ∧
      (∀ i : Fin N, γ (w1 i) = 0) ∧
      γ ⟨265, by decide⟩ = 0 ∧ γ ⟨266, by decide⟩ = 0 ∧ γ ⟨267, by decide⟩ = 0) :
    let prog :=
      mk94SeqSplit N (fun i ↦ mk94SplitBit (w0 i) (w1 i) actB hb (hw0 i).1 (hw1 i).1 (h01 i i))
    RealizesCleanUnitary v (p57DiagProj r268 Inv)
      (dSeqSplitBit_wstate v r268 N w0 w1 actB hb hw0 hw1 h01 hinj0 hinj1)
      ((prog.fwdCircuit r268).eval) ∧
    PreservesStoreConst (dSeqSplitBit_wstate v r268 N w0 w1 actB hb hw0 hw1 h01 hinj0 hinj1) := by
  intro prog
  let InvBit (δ : BitAssignment n) : Prop := Inv (fun q ↦ δ (r268 q))
  let _ : DecidablePred InvBit := fun _ ↦ Classical.propDecidable _
  let actFn (δ : BitAssignment n) : Bool := actFn268 (fun q ↦ δ (r268 q))
  let bStarFn (δ : BitAssignment n) : Fin N := bStarFn268 (fun q ↦ δ (r268 q))
  let base268 (γ : BitAssignment 268) : BitAssignment 268 :=
    fun q ↦ if ∃ i : Fin N, q = w0 i then 0 else γ q
  let baseSt (δ : BitAssignment n) : BitAssignment n :=
    writeRegProg δ r268 (base268 (fun q ↦ δ (r268 q)))
  have hBaseW0 (δ : BitAssignment n) (i : Fin N) : baseSt δ (r268 (w0 i)) = 0 := by
    dsimp only [baseSt, base268]
    rw [writeRegProg_apply_reg, ite_eq_left ⟨i, rfl⟩]
  have hBaseNotW0 (δ : BitAssignment n) (x : Wire n) (hx : ∀ i, x ≠ r268 (w0 i)) :
      baseSt δ x = δ x := by
    by_cases hmem : x ∈ Set.range r268.wires
    · obtain ⟨q, rfl⟩ := hmem
      dsimp only [baseSt, base268]
      rw [writeRegProg_apply_reg, ite_eq_right (fun ⟨i, hi⟩ ↦ hx i (congrArg r268 hi))]
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
  have hBaseLt (δ : BitAssignment n) (q : Wire 268) (hq : q.val < 174) :
      baseSt δ (r268 q) = δ (r268 q) :=
    hBaseNotW0 δ _ fun i ↦ r268.wires.injective.ne (wire_ne_of_lt (by have := (hw0 i).1; omega))
  have hActBase : ∀ δ, actFn (baseSt δ) = actFn δ ∧ bStarFn (baseSt δ) = bStarFn δ :=
    fun δ ↦ hActLt (hBaseLt δ)
  have hUpdGe174 : ∀ (δ : BitAssignment n) (u : Wire 268) (hu : 174 ≤ u.val) (a : ZMod 2),
      actFn (Function.update δ (r268 u) a) = actFn δ ∧
      bStarFn (Function.update δ (r268 u) a) = bStarFn δ := fun δ u hu a ↦
    hActLt fun q hq ↦ Function.update_of_ne (r268.wires.injective.ne (wire_ne_of_lt (by omega))) _ _
  have hGe265 (c : Wire 268) (hc : 265 ≤ c.val) (δ : BitAssignment n) :
      baseSt δ (r268 c) = δ (r268 c) :=
    hBaseNotW0 δ _ fun i ↦ r268.wires.injective.ne (wire_ne_of_gt (by have := (hw0 i).2; omega))
  have hClean : ∀ δ, InvBit δ →
      (∀ b p, baseSt δ (wPairBit268 r268 w0 w1 b p) = 0) ∧
      baseSt δ (r268 ⟨265, by decide⟩) = 0 ∧ baseSt δ (r268 ⟨266, by decide⟩) = 0 ∧
      baseSt δ (r268 ⟨267, by decide⟩) = 0 := fun δ hc ↦ by
    obtain ⟨_, hw1_0, h265, h266, h267⟩ := hInv (fun q ↦ δ (r268 q)) hc
    refine ⟨fun b p ↦ ?_, (hGe265 _ (by decide) δ).trans h265,
      (hGe265 _ (by decide) δ).trans h266, (hGe265 _ (by decide) δ).trans h267⟩
    dsimp only [wPairBit268]
    split_ifs
    · exact hBaseW0 δ b
    · exact (hBaseNotW0 δ _ fun i ↦ r268.wires.injective.ne (h01 i b).symm).trans (hw1_0 b)
  have hStep := subspaceStep_wOptExpandClean_predOp (Var := Var) v InvBit
    ![r268 actB] (wPairBit268 r268 w0 w1)
    (r268 ⟨265, by decide⟩) (r268 ⟨266, by decide⟩) (r268 ⟨267, by decide⟩)
    (wOptInj_bit268 r268 w0 w1 actB hb hw0 hw1 h01 hinj0 hinj1)
    baseSt actFn bStarFn hClean
    (fun δ b p ↦ by
      dsimp only [wPairBit268]
      split_ifs
      · exact (hUpdGe174 δ (w0 b) (hw0 b).1 1).1
      · exact (hUpdGe174 δ (w1 b) (hw1 b).1 1).1)
    (fun δ a ↦ (hUpdGe174 δ ⟨265, by decide⟩ (by decide) a).1)
    (fun δ a ↦ (hUpdGe174 δ ⟨265, by decide⟩ (by decide) a).2)
  dsimp only at hStep
  have hInEq : predOp InvBit (fun δ ↦ if actFn (baseSt δ) then Function.update (baseSt δ)
      (wPairBit268 r268 w0 w1 (bStarFn (baseSt δ)) ⟨0, Nat.two_pow_pos 1⟩) 1 else baseSt δ) =
      p57DiagProj r268 Inv := by
    apply matrix_ext_ket
    intro δ
    rw [predOp_mulVec_ket, ket_p57DiagProj]
    by_cases hc : InvBit δ
    · rw [ite_eq_left hc, ite_eq_left hc]
      obtain ⟨hw0_val, _, _, _, _⟩ := hInv (fun q ↦ δ (r268 q)) hc
      rw [(hActBase δ).1, (hActBase δ).2, wPairBit268_zero]
      dsimp only [actFn, bStarFn]
      refine congrArg ket (funext fun x ↦ ?_)
      by_cases hx0 : ∃ i : Fin N, x = r268 (w0 i)
      · obtain ⟨i, rfl⟩ := hx0
        rw [hw0_val i]
        by_cases hA : actFn268 (fun q ↦ δ (r268 q)) = true
        · rw [ite_eq_left hA, ite_eq_left hA, one_mul]
          by_cases hib : i = bStarFn268 (fun q ↦ δ (r268 q))
          · subst hib
            rw [Function.update_self, ite_eq_left rfl]
          · rw [Function.update_of_ne (r268.wires.injective.ne (hinj0.ne hib)),
                ite_eq_right hib, hBaseW0]
        · rw [ite_eq_right hA, ite_eq_right hA, zero_mul, hBaseW0]
      · have hnot0 : ∀ i, x ≠ r268 (w0 i) := fun i e ↦ hx0 ⟨i, e⟩
        split_ifs
        · exact (Function.update_of_ne (hnot0 _) _ _).trans (hBaseNotW0 δ x hnot0)
        · exact hBaseNotW0 δ x hnot0
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hOutEq : predOp InvBit (fun δ ↦ if actFn (baseSt δ) then Function.update (baseSt δ)
      (wPairBit268 r268 w0 w1 (bStarFn (baseSt δ)) ⟨idxValD ![r268 actB] (baseSt δ),
      idxValD_lt_two_pow _ _⟩) 1 else baseSt δ) = ((prog.fwdCircuit r268).eval).1 *
      p57DiagProj r268 Inv := by
    obtain ⟨_, _, hSpec⟩ := mk94SeqSplitBit_spec N w0 w1 actB hb
      (fun i ↦ (hw0 i).1) (fun i ↦ (hw1 i).1) h01 hinj0 hinj1
    apply matrix_ext_ket
    intro δ
    rw [predOp_mulVec_ket, mul_mulVec_prog, ket_p57DiagProj]
    by_cases hc : InvBit δ
    · rw [ite_eq_left hc, ite_eq_left hc]
      obtain ⟨hw0_val, hw1_0, _, _, _⟩ := hInv (fun q ↦ δ (r268 q)) hc
      obtain ⟨hB0, hB1, hBOut⟩ := hSpec (fun q ↦ δ (r268 q)) hw1_0
      rw [prog.fwdCircuit_ket r268 δ, (hActBase δ).1, (hActBase δ).2]
      have hidxB : idxValD ![r268 actB] (baseSt δ) = (δ (r268 actB)).val := by
        rw [idxValD_singleton, hBaseLt δ actB hb]
      dsimp only [actFn, bStarFn]
      refine congrArg ket (funext fun x ↦ ?_)
      have hne_pair_of {z : Wire n} (hz0 : ∀ i, z ≠ r268 (w0 i))
          (hz1 : ∀ i, z ≠ r268 (w1 i)) (p : Fin (2 ^ 1)) :
          z ≠ wPairBit268 r268 w0 w1 (bStarFn268 (fun q ↦ δ (r268 q))) p := by
        dsimp only [wPairBit268]
        split_ifs
        · exact hz0 _
        · exact hz1 _
      by_cases hmem : x ∈ Set.range r268.wires
      · obtain ⟨q, rfl⟩ := hmem
        rw [writeRegProg_apply_reg]
        by_cases hq0 : ∃ i : Fin N, q = w0 i
        · obtain ⟨i, rfl⟩ := hq0
          rw [hB0 i, hw0_val i]
          by_cases hA : actFn268 (fun q ↦ δ (r268 q)) = true
          · rw [ite_eq_left hA, ite_eq_left hA, one_mul]
            rcases fmkBit_cases (δ (r268 actB)) with hb0 | hb1
            · have hp0 : (⟨idxValD ![r268 actB] (baseSt δ),
                idxValD_lt_two_pow _ _⟩ : Fin (2 ^ 1)) = 0 :=
                Fin.ext (by dsimp only; rw [hidxB, hb0]; rfl)
              rw [hp0, hb0, wPairBit268_zero_fin2]
              by_cases hib : i = bStarFn268 (fun q ↦ δ (r268 q))
              · subst hib
                rw [Function.update_self, ite_eq_left rfl]
                ring
              · rw [Function.update_of_ne (r268.wires.injective.ne (hinj0.ne hib)),
                    ite_eq_right hib, hBaseW0]
                ring
            · have hp1 : (⟨idxValD ![r268 actB] (baseSt δ),
                idxValD_lt_two_pow _ _⟩ : Fin (2 ^ 1)) = 1 :=
                Fin.ext (by dsimp only; rw [hidxB, hb1]; rfl)
              rw [hp1, hb1, wPairBit268_one_fin2,
                  Function.update_of_ne (r268.wires.injective.ne (h01 i _)),
                  hBaseW0, (by decide : (1 : ZMod 2) + 1 = 0), mul_zero]
          · rw [ite_eq_right hA, ite_eq_right hA, zero_mul, zero_mul, hBaseW0]
        · by_cases hq1 : ∃ i : Fin N, q = w1 i
          · obtain ⟨i, rfl⟩ := hq1
            have hBase1 : baseSt δ (r268 (w1 i)) = 0 :=
              (hBaseNotW0 δ _ fun j ↦ r268.wires.injective.ne (h01 j i).symm).trans (hw1_0 i)
            rw [hB1 i, hw0_val i]
            by_cases hA : actFn268 (fun q ↦ δ (r268 q)) = true
            · rw [ite_eq_left hA, ite_eq_left hA, one_mul]
              rcases fmkBit_cases (δ (r268 actB)) with hb0 | hb1
              · have hp0 : (⟨idxValD ![r268 actB] (baseSt δ),
                  idxValD_lt_two_pow _ _⟩ : Fin (2 ^ 1)) = 0 :=
                  Fin.ext (by dsimp only; rw [hidxB, hb0]; rfl)
                rw [hp0, hb0, mul_zero, wPairBit268_zero_fin2,
                    Function.update_of_ne (r268.wires.injective.ne (h01 _ i).symm), hBase1]
              · have hp1 : (⟨idxValD ![r268 actB] (baseSt δ),
                  idxValD_lt_two_pow _ _⟩ : Fin (2 ^ 1)) = 1 :=
                  Fin.ext (by dsimp only; rw [hidxB, hb1]; rfl)
                rw [hp1, hb1, mul_one, wPairBit268_one_fin2]
                by_cases hib : i = bStarFn268 (fun q ↦ δ (r268 q))
                · subst hib
                  rw [Function.update_self, ite_eq_left rfl]
                · rw [Function.update_of_ne (r268.wires.injective.ne (hinj1.ne hib)),
                      ite_eq_right hib, hBase1]
            · rw [ite_eq_right hA, ite_eq_right hA, zero_mul, zero_mul, hBase1]
          · rw [hBOut q (fun i e ↦ hq0 ⟨i, e⟩) (fun i e ↦ hq1 ⟨i, e⟩)]
            have hnot0 : ∀ i, r268 q ≠ r268 (w0 i) :=
              fun i ↦ r268.wires.injective.ne fun e ↦ hq0 ⟨i, e⟩
            have hnot1 : ∀ i, r268 q ≠ r268 (w1 i) :=
              fun i ↦ r268.wires.injective.ne fun e ↦ hq1 ⟨i, e⟩
            split_ifs
            · exact (Function.update_of_ne (hne_pair_of hnot0 hnot1 _) _ _).trans
                (hBaseNotW0 δ _ hnot0)
            · exact hBaseNotW0 δ _ hnot0
      · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem]
        have hnot0 : ∀ i, x ≠ r268 (w0 i) := fun _ e ↦ hmem ⟨_, e.symm⟩
        have hnot1 : ∀ i, x ≠ r268 (w1 i) := fun _ e ↦ hmem ⟨_, e.symm⟩
        split_ifs
        · exact (Function.update_of_ne (hne_pair_of hnot0 hnot1 _) _ _).trans
            (hBaseNotW0 δ x hnot0)
        · exact hBaseNotW0 δ x hnot0
    · rw [ite_eq_right hc, ite_eq_right hc, Matrix.mulVec_zero]
  rw [hInEq, hOutEq] at hStep
  exact LocalOnVar.toRealizesAndPreserves (localOnVar_wOptExpandClean v N 1 _ _ _ _ _ _)
    (p57DiagProj_conjTranspose r268 Inv) hStep
/-- W-State Regime-II dynamic circuit (`4 * N + 4` `T`s, `0 .TOFF`) replacing
`mk94SeqSplit N (fun i ↦ mk94SplitTrit (w0 i) (w1 i) (w2 i) actA actC ...)`. -/
def dSeqSplitTrit_wstate {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n) (N : ℕ)
    (w0 w1 w2 : Fin N → Wire 268) (actA actC : Wire 268) (ha : actA.val < 174)
    (hc : actC.val < 174) (hw0 : ∀ i, 174 ≤ (w0 i).val ∧ (w0 i).val < 265)
    (hw1 : ∀ i, 174 ≤ (w1 i).val ∧ (w1 i).val < 265)
    (hw2 : ∀ i, 174 ≤ (w2 i).val ∧ (w2 i).val < 265) (h01 : ∀ i j, w0 i ≠ w1 j)
    (h02 : ∀ i j, w0 i ≠ w2 j) (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1)
    (hinj2 : Function.Injective w2) : DynamicCircuit Var n := .seq
    (dSeqSplitBit_wstate v r268 N w0 w1 actC hc hw0 hw1 h01 hinj0 hinj1)
    (dSeqSplitBit_wstate v r268 N w0 w2 actA ha hw0 hw2 h02 hinj0 hinj2)
theorem dSeqSplitTrit_wstate_counts {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n)
    (N : ℕ) (w0 w1 w2 : Fin N → Wire 268) (actA actC : Wire 268) (ha : actA.val < 174)
    (hc : actC.val < 174) (hw0 : ∀ i, 174 ≤ (w0 i).val ∧ (w0 i).val < 265)
    (hw1 : ∀ i, 174 ≤ (w1 i).val ∧ (w1 i).val < 265)
    (hw2 : ∀ i, 174 ≤ (w2 i).val ∧ (w2 i).val < 265) (h01 : ∀ i j, w0 i ≠ w1 j)
    (h02 : ∀ i j, w0 i ≠ w2 j) (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1)
    (hinj2 : Function.Injective w2) : (dSeqSplitTrit_wstate v r268 N w0 w1 w2 actA actC ha hc
    hw0 hw1 hw2 h01 h02 hinj0 hinj1 hinj2).count .T = 4 * N + 4 ∧ (dSeqSplitTrit_wstate v r268
    N w0 w1 w2 actA actC ha hc hw0 hw1 hw2 h01 h02 hinj0 hinj1 hinj2).count .TOFF = 0 := by
  obtain ⟨t1, f1⟩ := dSeqSplitBit_wstate_counts v r268 N w0 w1 actC hc hw0 hw1 h01 hinj0 hinj1
  obtain ⟨t2, f2⟩ := dSeqSplitBit_wstate_counts v r268 N w0 w2 actA ha hw0 hw2 h02 hinj0 hinj2
  dsimp only [dSeqSplitTrit_wstate, DynamicCircuit.count]
  rw [t1, f1, t2, f2]
  exact ⟨by omega, rfl⟩
theorem dSeqSplitTrit_wstate_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r268 : QRegister 268 n)
    (N : ℕ) (w0 w1 w2 : Fin N → Wire 268) (actA actC : Wire 268)
    (ha : actA.val < 174) (hc : actC.val < 174)
    (hw0 : ∀ i, 174 ≤ (w0 i).val ∧ (w0 i).val < 265)
    (hw1 : ∀ i, 174 ≤ (w1 i).val ∧ (w1 i).val < 265)
    (hw2 : ∀ i, 174 ≤ (w2 i).val ∧ (w2 i).val < 265)
    (h01 : ∀ i j, w0 i ≠ w1 j) (h02 : ∀ i j, w0 i ≠ w2 j) (h12 : ∀ i j, w1 i ≠ w2 j)
    (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1) (hinj2 : Function.Injective w2)
    (Inv : BitAssignment 268 → Prop)
    (actFn268 : BitAssignment 268 → Bool)
    (bStarFn268 : BitAssignment 268 → Fin N)
    (hActLt : ∀ {γ₁ γ₂ : BitAssignment 268},
      (∀ q : Wire 268, q.val < 174 → γ₁ q = γ₂ q) →
      actFn268 γ₁ = actFn268 γ₂ ∧ bStarFn268 γ₁ = bStarFn268 γ₂)
    (hInv : ∀ γ : BitAssignment 268, Inv γ →
      (∀ i : Fin N,
        γ (w0 i) = (if actFn268 γ then 1 else 0) * (if i = bStarFn268 γ then 1 else 0)) ∧
      (∀ i : Fin N, γ (w1 i) = 0) ∧ (∀ i : Fin N, γ (w2 i) = 0) ∧
      γ ⟨265, by decide⟩ = 0 ∧ γ ⟨266, by decide⟩ = 0 ∧ γ ⟨267, by decide⟩ = 0) :
    let prog := mk94SeqSplit N (fun i ↦ mk94SplitTrit (w0 i) (w1 i) (w2 i) actA actC
      ha hc (hw0 i).1 (hw1 i).1 (hw2 i).1 (h01 i i) (h02 i i) (h12 i i))
    RealizesCleanUnitary v (p57DiagProj r268 Inv)
      (dSeqSplitTrit_wstate v r268 N w0 w1 w2 actA actC ha hc hw0 hw1 hw2 h01 h02 hinj0 hinj1 hinj2)
      ((prog.fwdCircuit r268).eval) ∧
    PreservesStoreConst
      (dSeqSplitTrit_wstate v r268 N w0 w1 w2 actA actC ha hc hw0 hw1 hw2 h01 h02 hinj0 hinj1 hinj2)
        := by
  intro prog
  let progC :=
    mk94SeqSplit N (fun i ↦ mk94SplitBit (w0 i) (w1 i) actC hc (hw0 i).1 (hw1 i).1 (h01 i i))
  let progA :=
    mk94SeqSplit N (fun i ↦ mk94SplitBit (w0 i) (w2 i) actA ha (hw0 i).1 (hw2 i).1 (h02 i i))
  obtain ⟨_, _, hSpecC⟩ :=
    mk94SeqSplitBit_spec N w0 w1 actC hc (fun i ↦ (hw0 i).1) (fun i ↦ (hw1 i).1) h01 hinj0 hinj1
  obtain ⟨_, _, hSpecA⟩ :=
    mk94SeqSplitBit_spec N w0 w2 actA ha (fun i ↦ (hw0 i).1) (fun i ↦ (hw2 i).1) h02 hinj0 hinj2
  obtain ⟨_, _, hSpecT⟩ := mk94SeqSplitTrit_spec N w0 w1 w2 actA actC ha hc
    (fun i ↦ (hw0 i).1) (fun i ↦ (hw1 i).1) (fun i ↦ (hw2 i).1) h01 h02 h12 hinj0 hinj1 hinj2
  obtain ⟨hR1, hP1⟩ := dSeqSplitBit_wstate_realizes v r268 N w0 w1 actC hc hw0 hw1 h01 hinj0 hinj1
    Inv actFn268 bStarFn268 hActLt
    (fun γ hγ ↦ let ⟨h0, h1, _, h5, h6, h7⟩ := hInv γ hγ; ⟨h0, h1, h5, h6, h7⟩)
  let InvMid (δ : BitAssignment 268) : Prop := ∃ γ, Inv γ ∧ δ = progC.fwdBits γ
  let actFnMid (δ : BitAssignment 268) : Bool := actFn268 δ && decide (δ actC = 0)
  have hActMidLt : ∀ {γ₁ γ₂ : BitAssignment 268},
      (∀ q : Wire 268, q.val < 174 → γ₁ q = γ₂ q) →
      actFnMid γ₁ = actFnMid γ₂ ∧ bStarFn268 γ₁ = bStarFn268 γ₂ := fun hlt ↦ by
    obtain ⟨h1, h2⟩ := hActLt hlt
    exact ⟨by dsimp [actFnMid]; rw [h1, hlt actC hc], h2⟩
  have hInvMid : ∀ δ : BitAssignment 268, InvMid δ →
      (∀ i : Fin N,
        δ (w0 i) = (if actFnMid δ then 1 else 0) * (if i = bStarFn268 δ then 1 else 0)) ∧
      (∀ i : Fin N, δ (w2 i) = 0) ∧
      δ ⟨265, by decide⟩ = 0 ∧ δ ⟨266, by decide⟩ = 0 ∧ δ ⟨267, by decide⟩ = 0 := by
    rintro δ ⟨γ, hγ, rfl⟩
    obtain ⟨hw0_γ, hw1_γ, hw2_γ, h265, h266, h267⟩ := hInv γ hγ
    obtain ⟨hC0, _, hCOut⟩ := hSpecC γ hw1_γ
    have hlt : ∀ q : Wire 268, q.val < 174 → progC.fwdBits γ q = γ q := fun q hq ↦
      hCOut q (fun i ↦ wire_ne_of_lt (by have := (hw0 i).1; omega))
        (fun i ↦ wire_ne_of_lt (by have := (hw1 i).1; omega))
    obtain ⟨hActEq, hBStarEq⟩ := hActLt hlt
    have hcEq : progC.fwdBits γ actC = γ actC := hlt actC hc
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, ?_, ?_, ?_⟩
    · have hMidB : actFnMid (progC.fwdBits γ) = (actFn268 γ && decide (γ actC = 0)) := by
        dsimp only [actFnMid]; rw [hActEq, hcEq]
      dsimp only [progC] at hMidB hBStarEq hC0 ⊢
      rw [hMidB, hBStarEq, hC0 i, hw0_γ i]
      rcases fmkBit_cases (γ actC) with hc0 | hc0 <;> cases actFn268 γ <;> simp [hc0]
    · rw [hCOut (w2 i) (fun j ↦ (h02 j i).symm) (fun j ↦ (h12 j i).symm), hw2_γ i]
    · rw [hCOut ⟨265, by decide⟩ (fun j ↦ wire_ne_of_gt (by have := (hw0 j).2; dsimp; omega))
        (fun j ↦ wire_ne_of_gt (by have := (hw1 j).2; dsimp; omega)), h265]
    · rw [hCOut ⟨266, by decide⟩ (fun j ↦ wire_ne_of_gt (by have := (hw0 j).2; dsimp; omega))
        (fun j ↦ wire_ne_of_gt (by have := (hw1 j).2; dsimp; omega)), h266]
    · rw [hCOut ⟨267, by decide⟩ (fun j ↦ wire_ne_of_gt (by have := (hw0 j).2; dsimp; omega))
        (fun j ↦ wire_ne_of_gt (by have := (hw1 j).2; dsimp; omega)), h267]
  obtain ⟨hR2, hP2⟩ := dSeqSplitBit_wstate_realizes v r268 N w0 w2 actA ha hw0 hw2 h02 hinj0 hinj2
    InvMid actFnMid bStarFn268 hActMidLt hInvMid
  have hSeq := mk94RealizesCleanUnitary_seq_asym (p57DiagProj_conjTranspose r268 Inv)
      (p57DiagProj_conjTranspose r268 InvMid) hR1 hR2 (mk94DiagProj_seq_clean r268
      progC.fwdBits (fun β _ ↦ progC.fwdCircuit_ket r268 β) (fun γ hγ ↦ ⟨γ, hγ, rfl⟩))
  have hUEq : ((progA.fwdCircuit r268).eval * (progC.fwdCircuit r268).eval).1 *
    p57DiagProj r268 Inv =
      ((prog.fwdCircuit r268).eval).1 * p57DiagProj r268 Inv := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57DiagProj]
    by_cases hβ : Inv (fun q ↦ β (r268 q))
    · rw[ite_eq_left hβ, Submonoid.coe_mul, mul_mulVec_prog, progC.fwdCircuit_ket r268 β,
        progA.fwdCircuit_ket r268, prog.fwdCircuit_ket r268 β]
      have hreg : (fun idx ↦ writeRegProg β r268 (progC.fwdBits (fun q ↦ β (r268 q))) (r268 idx)) =
          progC.fwdBits (fun q ↦ β (r268 q)) :=
        funext fun idx ↦ writeRegProg_apply_reg β r268 _ idx
      rw [hreg, fmkWriteRegProg_idem]
      refine congrArg ket (congrArg (writeRegProg β r268) ?_)
      let γ := fun q ↦ β (r268 q)
      obtain ⟨_, hw1_γ, hw2_γ, _, _, _⟩ := hInv γ hβ
      obtain ⟨hC0, hC1, hCOut⟩ := hSpecC γ hw1_γ
      have hw2_C : ∀ i : Fin N, progC.fwdBits γ (w2 i) = 0 := fun i ↦
        (hCOut (w2 i) (fun j ↦ (h02 j i).symm) (fun j ↦ (h12 j i).symm)).trans (hw2_γ i)
      obtain ⟨hA0, hA2, hAOut⟩ := hSpecA (progC.fwdBits γ) hw2_C
      obtain ⟨hT0, hT1, hT2, hTOut⟩ := hSpecT γ hw1_γ hw2_γ
      have ha_C : progC.fwdBits γ actA = γ actA :=
        hCOut actA (fun i ↦ wire_ne_of_lt (by have := (hw0 i).1; omega))
          (fun i ↦ wire_ne_of_lt (by have := (hw1 i).1; omega))
      funext q
      by_cases hq0 : ∃ i : Fin N, q = w0 i
      · obtain ⟨i, rfl⟩ := hq0
        change progA.fwdBits (progC.fwdBits γ) (w0 i) = prog.fwdBits γ (w0 i)
        rw [hA0 i, hC0 i, ha_C, hT0 i]
        rcases fmkBit_cases (γ actA) with ha0 | ha0 <;>
          rcases fmkBit_cases (γ actC) with hc0 | hc0 <;>
          simp [ha0, hc0, s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
      · by_cases hq1 : ∃ i : Fin N, q = w1 i
        · obtain ⟨i, rfl⟩ := hq1
          change progA.fwdBits (progC.fwdBits γ) (w1 i) = prog.fwdBits γ (w1 i)
          rw [hAOut (w1 i) (fun j ↦ (h01 j i).symm) (fun j ↦ h12 i j), hC1 i, hT1 i]
          rcases fmkBit_cases (γ actA) with ha0 | ha0 <;>
            rcases fmkBit_cases (γ actC) with hc0 | hc0 <;>
            simp [ha0, hc0, s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
        · by_cases hq2 : ∃ i : Fin N, q = w2 i
          · obtain ⟨i, rfl⟩ := hq2
            change progA.fwdBits (progC.fwdBits γ) (w2 i) = prog.fwdBits γ (w2 i)
            rw [hA2 i, hC0 i, ha_C, hT2 i]
            rcases fmkBit_cases (γ actA) with ha0 | ha0 <;>
              rcases fmkBit_cases (γ actC) with hc0 | hc0 <;>
              simp [ha0, hc0, s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
          · change progA.fwdBits (progC.fwdBits γ) q = prog.fwdBits γ q
            rw [hAOut q (fun i e ↦ hq0 ⟨i, e⟩) (fun i e ↦ hq2 ⟨i, e⟩),
              hCOut q (fun i e ↦ hq0 ⟨i, e⟩) (fun i e ↦ hq1 ⟨i, e⟩),
              hTOut q (fun i e ↦ hq0 ⟨i, e⟩) (fun i e ↦ hq1 ⟨i, e⟩) (fun i e ↦ hq2 ⟨i, e⟩)]
    · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact ⟨RealizesCleanUnitary_congr_unitary (p57DiagProj_conjTranspose r268 Inv) hSeq hUEq,
    PreservesStoreConst.seq hP1 hP2⟩
/-- Intermediate invariants for the 5 stages of `mk94SplitU18W11`. -/
def InvU18_s2 (γ : BitAssignment 268) : Prop :=
  (∀ i : Fin 3, γ ⟨174 + i.val, by omega⟩ =
    (if decide (γ mk94AccW = 1) then 1 else 0) *
      (if i = ⟨s3Trit (γ mk94A0W) (γ mk94C0W), s3Trit_lt_three _ _⟩ then 1 else 0)) ∧
  cleanRem 268 (268 - 177) γ
def InvU18_s3 (γ : BitAssignment 268) : Prop :=
  (∀ i : Fin 9, γ ⟨174 + i.val, by omega⟩ =
    (if decide (γ mk94AccW = 1) then 1 else 0) *
      (if i = ⟨s3Trit (γ mk94A0W) (γ mk94C0W) + 3 * s3Trit (γ mk94A1W) (γ mk94C1W), by
        have := s3Trit_lt_three (γ mk94A0W) (γ mk94C0W)
        have := s3Trit_lt_three (γ mk94A1W) (γ mk94C1W); omega⟩ then 1 else 0)) ∧
  cleanRem 268 (268 - 183) γ
def InvU18_s4 (γ : BitAssignment 268) : Prop := cleanRem 268 (268 - 192) γ
def mk94SplitU18_s01 : Mk94SplitProg 268 := .seq mk94SplitU18_s0 mk94SplitU18_s1
theorem mk94SplitU18_s01_spec : mk94SplitU18_s01.FwdClean (cleanRem 268 94) ∧ (∀ γ :
    BitAssignment 268, cleanRem 268 94 γ → InvU18_s2 (mk94SplitU18_s01.fwdBits γ)) := by
  obtain ⟨_, hC1, hB1⟩ := mk94SplitTrit_spec (mk94U18W 0) (mk94U18W 1) (mk94U18W 2)
    mk94A0W mk94C0W (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hStep : ∀ γ : BitAssignment 268, cleanRem 268 94 γ →
      let γ1 := mk94SplitU18_s0.fwdBits γ
      (γ1 (mk94U18W 1) = 0 ∧ γ1 (mk94U18W 2) = 0) ∧
      InvU18_s2 (mk94SplitU18_s01.fwdBits γ) := by
    intro γ hγ γ1
    have h1_0 : γ1 (mk94U18W 0) = γ mk94AccW := by
      simp [γ1, mk94SplitU18_s0, Mk94SplitProg.fwdBits, hγ (mk94U18W 0) (by decide)]
    have h1_out : ∀ q : Wire 268, q ≠ mk94U18W 0 → γ1 q = γ q := fun q hq ↦ by
      simp [γ1, mk94SplitU18_s0, Mk94SplitProg.fwdBits, Function.update_of_ne hq]
    have hz1 : γ1 (mk94U18W 1) = 0 := (h1_out _ (by decide)).trans (hγ _ (by decide))
    have hz2 : γ1 (mk94U18W 2) = 0 := (h1_out _ (by decide)).trans (hγ _ (by decide))
    obtain ⟨h2_0, h2_1, h2_2, h2_out⟩ := hB1 γ1 hz1 hz2
    have hlt : ∀ q : Wire 268, q.val < 174 → (mk94SplitU18_s01.fwdBits γ) q = γ q := fun q hq ↦
      (h2_out q (wire_ne_of_lt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_lt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_lt (by dsimp [mk94U18W]; omega))).trans (h1_out q (wire_ne_of_lt hq))
    have ha0 : γ1 mk94A0W = γ mk94A0W := h1_out _ (by decide)
    have hc0 : γ1 mk94C0W = γ mk94C0W := h1_out _ (by decide)
    refine ⟨⟨hz1, hz2⟩, fun i ↦ ?_, fun w hw ↦ ?_⟩
    · simp only [Fin.ext_iff]
      rw [hlt mk94AccW (by decide), hlt mk94A0W (by decide), hlt mk94C0W (by decide)]
      rcases i with ⟨_ | _ | _ | i, hi⟩
      · have hi0 : (⟨174 + (⟨0, hi⟩ : Fin 3).val, by omega⟩ : Wire 268) = mk94U18W 0 := rfl
        rw [hi0]; dsimp only [mk94SplitU18_s01, mk94SplitU18_s1, Mk94SplitProg.fwdBits]
        rw [h2_0, h1_0, ha0, hc0]
        rcases fmkBit_cases (γ mk94AccW) with h | h <;> simp [h, eq_comm]
      · have hi1 : (⟨174 + (⟨0 + 1, hi⟩ : Fin 3).val, by omega⟩ : Wire 268) = mk94U18W 1 := rfl
        rw [hi1]; dsimp only [mk94SplitU18_s01, mk94SplitU18_s1, Mk94SplitProg.fwdBits]
        rw [h2_1, h1_0, ha0, hc0]
        rcases fmkBit_cases (γ mk94AccW) with h | h <;> simp [h, eq_comm]
      · have hi2 : (⟨174 + (⟨0 + 1 + 1, hi⟩ : Fin 3).val, by omega⟩ : Wire 268) = mk94U18W 2 := rfl
        rw [hi2]; dsimp only [mk94SplitU18_s01, mk94SplitU18_s1, Mk94SplitProg.fwdBits]
        rw [h2_2, h1_0, ha0, hc0]
        rcases fmkBit_cases (γ mk94AccW) with h | h <;> simp [h, eq_comm]
      · omega
    · exact (h2_out w (wire_ne_of_gt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_gt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_gt (by dsimp [mk94U18W]; omega))).trans
        ((h1_out w (wire_ne_of_gt (by dsimp [mk94U18W]; omega))).trans (hγ w (by omega)))
  exact ⟨⟨trivial, hC1 _ fun _ ⟨γ, hγ, h⟩ ↦ by subst h; exact (hStep γ hγ).1⟩,
    fun γ hγ ↦ (hStep γ hγ).2⟩
theorem mk94SplitU18_s2_pres (γ : BitAssignment 268) (hγ : InvU18_s2 γ) :
    InvU18_s3 (mk94SplitU18_s2.fwdBits γ) := by
  obtain ⟨_, _, hB2⟩ := mk94SeqSplitTrit_spec 3
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨177 + i.val, by omega⟩)
    (fun i ↦ ⟨180 + i.val, by omega⟩) mk94A1W mk94C1W (by decide) (by decide)
    (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  obtain ⟨h0, h1, h2, hOut⟩ :=
    hB2 γ (fun i ↦ hγ.2 _ (by dsimp; omega)) (fun i ↦ hγ.2 _ (by dsimp; omega))
  have hlt : ∀ q : Wire 268, q.val < 174 → (mk94SplitU18_s2.fwdBits γ) q = γ q := fun q hq ↦
    hOut q (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
      (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
      (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
  refine ⟨fun i ↦ ?_, fun w hw ↦ ?_⟩
  · simp only [Fin.ext_iff]
    rw [hlt mk94AccW (by decide), hlt mk94A0W (by decide), hlt mk94C0W (by decide),
      hlt mk94A1W (by decide), hlt mk94C1W (by decide)]
    have ht0 := s3Trit_lt_three (γ mk94A0W) (γ mk94C0W)
    have ht1 := s3Trit_lt_three (γ mk94A1W) (γ mk94C1W)
    dsimp only [mk94SplitU18_s2]
    by_cases hi3 : i.val < 3
    · let j : Fin 3 := ⟨i.val, hi3⟩
      have hw : (⟨174 + i.val, by omega⟩ : Wire 268) = ⟨174 + j.val, by omega⟩ := rfl
      rw [hw, h0 j, hγ.1 j]
      simp only [Fin.ext_iff, j]
      (split_ifs <;> try omega); all_goals ring
    · by_cases hi6 : i.val < 6
      · let j : Fin 3 := ⟨i.val - 3, by omega⟩
        have hw : (⟨174 + i.val, by omega⟩ : Wire 268) = ⟨177 + j.val, by omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        rw [hw, h1 j, hγ.1 j]
        simp only [Fin.ext_iff, j]
        (split_ifs <;> try omega); all_goals ring
      · let j : Fin 3 := ⟨i.val - 6, by omega⟩
        have hw : (⟨174 + i.val, by omega⟩ : Wire 268) = ⟨180 + j.val, by omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        rw [hw, h2 j, hγ.1 j]
        simp only [Fin.ext_iff, j]
        (split_ifs <;> try omega); all_goals ring
  · exact (hOut w (fun _ ↦ wire_ne_of_gt (by dsimp; omega))
      (fun _ ↦ wire_ne_of_gt (by dsimp; omega))
      (fun _ ↦ wire_ne_of_gt (by dsimp; omega))).trans (hγ.2 w (by omega))
theorem mk94SplitU18_s3_pres (γ : BitAssignment 268) (hγ : InvU18_s3 γ) :
    InvU18_s4 (mk94SplitU18_s3.fwdBits γ) := by
  obtain ⟨_, _, hB3⟩ := mk94SeqSplitBit_spec 9
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨183 + i.val, by omega⟩) mk94BParW (by decide)
    (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  obtain ⟨_, _, hOut⟩ := hB3 γ (fun i ↦ hγ.2 _ (by dsimp; omega))
  intro w hw
  exact (hOut w (fun _ ↦ wire_ne_of_gt (by dsimp; omega))
    (fun _ ↦ wire_ne_of_gt (by dsimp; omega))).trans (hγ.2 w (by omega))
/-- `48-T` (`0 .TOFF`) W-State replacement for `mk94SplitU18W11.fwdDyn r268` (`72 T`, saving `-24
  T`). -/
def dSplitU18W11_wstate {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n) :
    DynamicCircuit Var n :=
  .seq (mk94SplitU18_s01.fwdDyn r268)
    (.seq
      (dSeqSplitTrit_wstate v r268 3
        (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨177 + i.val, by omega⟩) (fun i ↦
          ⟨180 + i.val, by omega⟩)
        mk94A1W mk94C1W (by decide) (by decide)
        (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
        (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
        (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
        (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
        (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
        (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
        (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
        (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega)))
      (.seq
        (dSeqSplitBit_wstate v r268 9
          (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨183 + i.val, by omega⟩) mk94BParW (by decide)
          (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
          (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
          (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
          (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
          (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega)))
        (mk94SplitU18_s4.fwdDyn r268)))
theorem dSplitU18W11_wstate_counts {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n) :
    (dSplitU18W11_wstate v r268).count .T = 48 ∧
    (dSplitU18W11_wstate v r268).count .TOFF = 0 := by
  obtain ⟨t2, f2⟩ := dSeqSplitTrit_wstate_counts v r268 3
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨177 + i.val, by omega⟩) (fun i ↦
      ⟨180 + i.val, by omega⟩)
    mk94A1W mk94C1W (by decide) (by decide)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  obtain ⟨t3, f3⟩ := dSeqSplitBit_wstate_counts v r268 9
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨183 + i.val, by omega⟩) mk94BParW (by decide)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  dsimp only [dSplitU18W11_wstate]
  repeat rw [mk94DynCount_seq]
  rw [mk94SplitU18_s01.fwdDyn_count_t r268, mk94SplitU18_s01.fwdDyn_count_toff r268,
    mk94SplitU18_s4.fwdDyn_count_t r268, mk94SplitU18_s4.fwdDyn_count_toff r268,
    t2, f2, t3, f3]
  exact ⟨rfl, rfl⟩
theorem dSplitU18W11_wstate_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r268 : QRegister 268 n) : RealizesCleanUnitary v
    (p57DiagProj r268 (cleanRem 268 94)) (dSplitU18W11_wstate v r268)
    ((mk94SplitU18W11.fwdCircuit r268).eval) ∧ PreservesStoreConst
    (dSplitU18W11_wstate v r268) := by
  have h1 := mk94SplitU18_s01.fwdDyn_realizes v r268 (cleanRem 268 94) mk94SplitU18_s01_spec.1
  have hP1 := mk94SplitU18_s01.fwdDyn_preservesStore (Var := Var) r268
  obtain ⟨h2, hP2⟩ := dSeqSplitTrit_wstate_realizes v r268 3
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨177 + i.val, by omega⟩) (fun i ↦
      ⟨180 + i.val, by omega⟩)
    mk94A1W mk94C1W (by decide) (by decide)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    InvU18_s2
    (fun γ ↦ decide (γ mk94AccW = 1))
    (fun γ ↦ ⟨s3Trit (γ mk94A0W) (γ mk94C0W), s3Trit_lt_three _ _⟩)
    (fun hlt ↦ ⟨by
      rw [hlt mk94AccW (by decide)],
      Fin.ext (by dsimp; rw [hlt mk94A0W (by decide), hlt mk94C0W (by decide)])⟩)
    (fun γ hγ ↦ ⟨hγ.1, fun _ ↦ hγ.2 _ (by dsimp; omega), fun _ ↦ hγ.2 _ (by dsimp; omega),
      hγ.2 _ (by decide), hγ.2 _ (by decide), hγ.2 _ (by decide)⟩)
  obtain ⟨h3, hP3⟩ := dSeqSplitBit_wstate_realizes v r268 9
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨183 + i.val, by omega⟩) mk94BParW (by decide)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    InvU18_s3
    (fun γ ↦ decide (γ mk94AccW = 1))
    (fun γ ↦ ⟨s3Trit (γ mk94A0W) (γ mk94C0W) + 3 * s3Trit (γ mk94A1W) (γ mk94C1W), by
      have := s3Trit_lt_three (γ mk94A0W) (γ mk94C0W)
      have := s3Trit_lt_three (γ mk94A1W) (γ mk94C1W); omega⟩)
    (fun hlt ↦ ⟨by
      rw [hlt mk94AccW (by decide)],
      Fin.ext (by
        dsimp; rw [hlt mk94A0W (by decide), hlt mk94C0W (by decide),
        hlt mk94A1W (by decide), hlt mk94C1W (by decide)])⟩)
    (fun γ hγ ↦ ⟨hγ.1, fun _ ↦ hγ.2 _ (by dsimp; omega),
      hγ.2 _ (by decide), hγ.2 _ (by decide), hγ.2 _ (by decide)⟩)
  have h4 := mk94SplitU18_s4.fwdDyn_realizes v r268 InvU18_s4 (fun γ hγ ↦ hγ mk94W11W (by decide))
  have hP4 := mk94SplitU18_s4.fwdDyn_preservesStore (Var := Var) r268
  have h34 := mk94RealizesCleanUnitary_seq_asym (p57DiagProj_conjTranspose r268 InvU18_s3)
      (p57DiagProj_conjTranspose r268 InvU18_s4) h3 h4 (mk94DiagProj_seq_clean r268
      mk94SplitU18_s3.fwdBits (fun β _ ↦ mk94SplitU18_s3.fwdCircuit_ket r268 β)
      mk94SplitU18_s3_pres)
  have h234 := mk94RealizesCleanUnitary_seq_asym (p57DiagProj_conjTranspose r268 InvU18_s2)
      (p57DiagProj_conjTranspose r268 InvU18_s3) h2 h34 (mk94DiagProj_seq_clean r268
      mk94SplitU18_s2.fwdBits (fun β _ ↦ mk94SplitU18_s2.fwdCircuit_ket r268 β)
      mk94SplitU18_s2_pres)
  have h1234 := mk94RealizesCleanUnitary_seq_asym
      (p57DiagProj_conjTranspose r268 (cleanRem 268 94))
      (p57DiagProj_conjTranspose r268 InvU18_s2) h1 h234 (mk94DiagProj_seq_clean r268
      mk94SplitU18_s01.fwdBits (fun β _ ↦ mk94SplitU18_s01.fwdCircuit_ket r268 β)
      mk94SplitU18_s01_spec.2)
  have hUEq : (((mk94SplitU18_s4.fwdCircuit r268).eval * (mk94SplitU18_s3.fwdCircuit
      r268).eval) * (mk94SplitU18_s2.fwdCircuit r268).eval) *
      (mk94SplitU18_s01.fwdCircuit r268).eval = (mk94SplitU18W11.fwdCircuit r268).eval := by
    apply Subtype.ext
    apply matrix_ext_ket; intro β
    rw[Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, mul_mulVec_prog,
        mul_mulVec_prog, mul_mulVec_prog, mk94SplitU18_s01.fwdCircuit_ket r268 β,
        mk94SplitU18_s2.fwdCircuit_ket r268, mk94SplitU18_s3.fwdCircuit_ket r268,
        mk94SplitU18_s4.fwdCircuit_ket r268, mk94SplitU18W11.fwdCircuit_ket r268 β]
    have hreg : ∀ (β' : BitAssignment n) (ξ : BitAssignment 268),
        (fun idx ↦ writeRegProg β' r268 ξ (r268 idx)) = ξ :=
      fun β' ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β' r268 ξ idx
    rw [hreg, fmkWriteRegProg_idem, hreg, fmkWriteRegProg_idem, hreg, fmkWriteRegProg_idem]
    rfl
  refine ⟨?_,
    PreservesStoreConst.seq hP1 (PreservesStoreConst.seq hP2 (PreservesStoreConst.seq hP3 hP4))⟩
  rw [← hUEq]
  exact h1234
private theorem u54_bnd (t : Fin 3) (p : Fin 18) :
    174 ≤ (mk94U54Wire p t).val ∧ (mk94U54Wire p t).val < 265 := by
  revert t p
  decide
private theorem u54_ne {t₁ t₂ : Fin 3} (ht : t₁ ≠ t₂) (i j : Fin 18) :
    mk94U54Wire i t₁ ≠ mk94U54Wire j t₂ := by
  revert i j t₁ t₂ ht
  decide
private theorem u54_inj (t : Fin 3) : Function.Injective (fun p ↦ mk94U54Wire p t) := by
  intro i j h
  revert t i j h
  decide
/-- `18`-trit batch version of `mk94SplitAll36` (`p18 = 0..17`). -/
def mkAll18TritProg : Mk94SplitProg 268 :=
  mk94SeqSplit 18 fun p18 ↦
    mk94SplitTrit (mk94U54Wire p18 0) (mk94U54Wire p18 1) (mk94U54Wire p18 2)
      mk94A2W mk94C2W (by decide) (by decide)
      (by revert p18; decide) (by revert p18; decide) (by revert p18; decide)
      (by revert p18; decide) (by revert p18; decide) (by revert p18; decide)
/-- `76-T` (`0 .TOFF`) W-State replacement for `mk94SplitAll36.fwdDyn r268` (`144 T`, saving `-68
  T`). -/
def dSplitAll36_wstate {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n) :
    DynamicCircuit Var n :=
  dSeqSplitTrit_wstate v r268 18
    (fun p18 ↦ mk94U54Wire p18 0) (fun p18 ↦ mk94U54Wire p18 1) (fun p18 ↦ mk94U54Wire p18 2)
    mk94A2W mk94C2W (by decide) (by decide)
    (by intro p18; decide +revert) (by intro p18; decide +revert) (by intro p18; decide +revert)
    (by intro i j; decide +revert) (by intro i j; decide +revert)
    (by intro i j h; decide +revert) (by intro i j h; decide +revert)
    (by intro i j h; decide +revert)
theorem dSplitAll36_wstate_counts {Var : Type} {n : ℕ} (v : Var) (r268 : QRegister 268 n) :
    (dSplitAll36_wstate v r268).count .T = 76 ∧ (dSplitAll36_wstate v r268).count .TOFF = 0 :=
    dSeqSplitTrit_wstate_counts v r268 18 _ _ _ mk94A2W mk94C2W (by decide) (by decide) _ _ _
    _ _ _ _ _
theorem dSplitAll36_wstate_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r268 : QRegister 268 n) : RealizesCleanUnitary v
    (p57DiagProj r268 mk94InvCleanU18) (dSplitAll36_wstate v r268)
    ((mk94SplitAll36.fwdCircuit r268).eval) ∧ PreservesStoreConst (dSplitAll36_wstate v r268)
    := by
  have h1_zero : ∀ (γ : BitAssignment 268), mk94InvCleanU18 γ →
      (∀ p18 : Fin 18, γ (mk94U54Wire p18 1) = 0) ∧
      (∀ p18 : Fin 18, γ (mk94U54Wire p18 2) = 0) := by
    intro γ ⟨⟨_, _, h93, h94, h95, hcl36⟩, _⟩
    have hGe : ∀ w : Wire 268, ((193 ≤ w.val ∧ w.val < 196) ∨ 232 ≤ w.val) → γ w = 0 := by
      rintro ⟨v, hv⟩ (⟨h1, h2⟩ | h3)
      · interval_cases v <;> assumption
      · exact hcl36 ⟨v, hv⟩ h3
    exact ⟨fun p18 ↦
      hGe _ ((show ∀ p : Fin 18, (193 ≤ (mk94U54Wire p 1).val ∧ (mk94U54Wire p 1).val < 196) ∨
        232 ≤ (mk94U54Wire p 1).val by decide) p18),
      fun p18 ↦
        hGe _ ((show ∀ p : Fin 18, (193 ≤ (mk94U54Wire p 2).val ∧ (mk94U54Wire p 2).val < 196) ∨
        232 ≤ (mk94U54Wire p 2).val by decide) p18)⟩
  obtain ⟨hR, hP⟩ := dSeqSplitTrit_wstate_realizes v r268 18
    (fun p18 ↦ mk94U54Wire p18 0) (fun p18 ↦ mk94U54Wire p18 1) (fun p18 ↦ mk94U54Wire p18 2)
    mk94A2W mk94C2W (by decide) (by decide) (u54_bnd 0) (u54_bnd 1) (u54_bnd 2)
    (u54_ne (by decide)) (u54_ne (by decide)) (u54_ne (by decide))
    (u54_inj 0) (u54_inj 1) (u54_inj 2) mk94InvCleanU18
    (fun γ ↦ decide (γ mk94AccW = 1))
    (fun γ ↦ ⟨mk94ActP18 γ, mk94ActP18_lt γ⟩)
    (fun hlt ↦ ⟨by rw [hlt mk94AccW (by decide)], Fin.ext (mk94ActP18_congr hlt)⟩)
    (fun γ hγ ↦ by
      obtain ⟨h1z, h2z⟩ := h1_zero γ hγ
      refine ⟨fun p18 ↦ ?_, h1z, h2z,
        hγ.1.2.2.2.2.2 _ (by decide), hγ.1.2.2.2.2.2 _ (by decide), hγ.1.2.2.2.2.2 _ (by decide)⟩
      have h0 : mk94U54Wire p18 0 = mk94U18W p18 := rfl
      rw [h0, hγ.1.1 p18]
      rcases fmkBit_cases (γ mk94AccW) with ha | ha <;> simp [ha, Fin.ext_iff])
  obtain ⟨_, _, hSpec18⟩ := mk94SeqSplitTrit_spec 18
    (fun p18 ↦ mk94U54Wire p18 0) (fun p18 ↦ mk94U54Wire p18 1) (fun p18 ↦ mk94U54Wire p18 2)
    mk94A2W mk94C2W (by decide) (by decide)
    (fun p ↦ (u54_bnd 0 p).1) (fun p ↦ (u54_bnd 1 p).1) (fun p ↦ (u54_bnd 2 p).1)
    (u54_ne (by decide)) (u54_ne (by decide)) (u54_ne (by decide))
    (u54_inj 0) (u54_inj 1) (u54_inj 2)
  have hUEq : (mkAll18TritProg.fwdCircuit r268).eval.1 * p57DiagProj r268 mk94InvCleanU18 =
      (mk94SplitAll36.fwdCircuit r268).eval.1 * p57DiagProj r268 mk94InvCleanU18 := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57DiagProj]
    by_cases hβ : mk94InvCleanU18 (fun q ↦ β (r268 q))
    · rw [ite_eq_left hβ, mkAll18TritProg.fwdCircuit_ket r268 β,
        mk94SplitAll36.fwdCircuit_ket r268 β]
      refine congrArg ket (congrArg (writeRegProg β r268) ?_)
      let γ := fun q ↦ β (r268 q)
      obtain ⟨h1z, h2z⟩ := h1_zero γ hβ
      obtain ⟨hT0, hT1, hT2, hTOut⟩ := hSpec18 γ h1z h2z
      obtain ⟨hU54_2, hKeep2⟩ := mk94SplitAll36_spec.2 γ hβ.1
      have hOut : ∀ q : Wire 268,
          (q.val < 174 ∨ q.val = 192 ∨ (196 ≤ q.val ∧ q.val < 232) ∨ 265 ≤ q.val) →
          mkAll18TritProg.fwdBits γ q = γ q := fun q hq ↦
        hTOut q
          (fun p ↦ Fin.ne_of_val_ne (by
            have : (mk94U54Wire p 0).val = 174 + p.val := rfl
            rcases hq with h | h | ⟨h1, h2⟩ | h <;> omega))
          (fun p ↦ Fin.ne_of_val_ne (by
            have :=
              (show ∀ p : Fin 18, (193 ≤ (mk94U54Wire p 1).val ∧ (mk94U54Wire p 1).val < 196) ∨
              (232 ≤ (mk94U54Wire p 1).val ∧ (mk94U54Wire p 1).val < 265) by decide) p
            rcases hq with h | h | ⟨h1, h2⟩ | h <;> rcases this with ⟨_, _⟩ | ⟨_, _⟩ <;> omega))
          (fun p ↦ Fin.ne_of_val_ne (by
            have :=
              (show ∀ p : Fin 18, (193 ≤ (mk94U54Wire p 2).val ∧ (mk94U54Wire p 2).val < 196) ∨
              (232 ≤ (mk94U54Wire p 2).val ∧ (mk94U54Wire p 2).val < 265) by decide) p
            rcases hq with h | h | ⟨h1, h2⟩ | h <;> rcases this with ⟨_, _⟩ | ⟨_, _⟩ <;> omega))
      have hlt : ∀ q : Wire 268, q.val < 174 → mkAll18TritProg.fwdBits γ q = γ q :=
        fun q hq ↦ hOut q (Or.inl hq)
      have hU54_1 : mk94InvU54 (mkAll18TritProg.fwdBits γ) := by
        refine ⟨fun p18 t2 ↦ ?_, ?_, fun w hw ↦
          (hOut w (Or.inr (Or.inr (Or.inr hw)))).trans (hβ.1.2.2.2.2.2 w (by omega))⟩
        · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt,
            hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
          have hp0 : γ (mk94U54Wire p18 0) = γ mk94AccW *
            (if p18.val = mk94ActP18 γ then 1 else 0) :=
            hβ.1.1 p18
          rcases t2 with ⟨_ | _ | _ | v, hv⟩
          · have ht0 : (⟨0, hv⟩ : Fin 3) = 0 := rfl
            rw [ht0]; dsimp only [mkAll18TritProg]
            rw [hT0 p18, hp0]; dsimp only [Fin.val_zero]; (split_ifs <;> try omega); all_goals ring
          · have ht1 : (⟨0 + 1, hv⟩ : Fin 3) = 1 := rfl
            rw [ht1]; dsimp only [mkAll18TritProg]
            rw [hT1 p18, hp0]; dsimp only [Fin.val_one]; (split_ifs <;> try omega); all_goals ring
          · have ht2 : (⟨0 + 1 + 1, hv⟩ : Fin 3) = 2 := rfl
            rw [ht2]; dsimp only [mkAll18TritProg]
            rw [hT2 p18, hp0]; dsimp only [Fin.val_two]; (split_ifs <;> try omega); all_goals ring
          · omega
        · rw [hOut mk94W11W (Or.inr (Or.inl rfl)), hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
          exact hβ.1.2.1
      exact mk94InvU54_ext hU54_1 hU54_2 fun q hq ↦
        (hOut q (hq.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h))))).trans (hKeep2 q hq).symm
    · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact
    ⟨RealizesCleanUnitary_congr_unitary (p57DiagProj_conjTranspose r268 mk94InvCleanU18) hR hUEq,
    hP⟩
end Part1_WStateSplitEngine
section Part2_ParametricWStateMidKick
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency false
/-- `16 - m₀`-trit tail split program (`p18 = 2 + m₀ .. 17`, `0 ≤ m₀ ≤ 15`). -/
def mkTailTritProg (m₀ : ℕ) (hm₀ : m₀ ≤ 15) : Mk94SplitProg 268 :=
  mk94SeqSplit (16 - m₀) fun i ↦
    mk94SplitTrit ⟨176 + m₀ + i.val, by omega⟩
      ⟨233 + 2 * m₀ + 2 * i.val, by omega⟩
      ⟨234 + 2 * m₀ + 2 * i.val, by omega⟩
      mk94A2W mk94C2W (by decide) (by decide)
      (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
      (wire_ne_of_lt (by dsimp; omega))
      (wire_ne_of_lt (by dsimp; omega))
      (wire_ne_of_lt (by dsimp; omega))
/-- Intermediate `268`-wire invariant with `p18 = 0 .. 1 + m₀` intact and `[233 + 2 * m₀ .. 268)`
  clean (`35 - 2 * m₀` wires). -/
def mkInvMidTrit (m₀ : ℕ) (hm₀ : m₀ ≤ 15) (γ : BitAssignment 268) : Prop :=
  (∀ p18 : Fin 18, p18.val < 2 + m₀ → ∀ t2 : Fin 3,
    γ (mk94U54Wire p18 t2) =
      γ mk94AccW *
        (if p18.val = mk94ActP18 γ ∧ t2.val = s3Trit (γ mk94A2W) (γ mk94C2W) then 1 else 0)) ∧
  (∀ i : Fin (16 - m₀),
    γ ⟨176 + m₀ + i.val, by omega⟩ =
      γ mk94AccW * (if 2 + m₀ + i.val = mk94ActP18 γ then 1 else 0)) ∧
  γ mk94W11W = γ mk94B0W * γ mk94B1W ∧
  mkInvMidTail (1 + 2 * m₀) (by omega) γ
theorem mk94U54Wire_lt_bounds (m₀ : ℕ) (hm₀ : m₀ ≤ 15) (p18 : Fin 18) (hp : p18.val < 2 +
    m₀) (t2 : Fin 3) :
    (mk94U54Wire p18 t2).val < 176 + m₀ ∨
    (193 ≤ (mk94U54Wire p18 t2).val ∧ (mk94U54Wire p18 t2).val < 233 + 2 * m₀) := by
  have ht2 := t2.isLt
  dsimp only [mk94U54Wire]
  split_ifs with h0 hp0 ht1 hp1 ht1'
  · exact Or.inl (by dsimp; omega)
  · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩
  · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩
  · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩
  · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩
  · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩
theorem mk94U54Wire_not_cat (p18 : Fin 18) (t2 : Fin 3) :
    ¬(107 ≤ (mk94U54Wire p18 t2).val ∧ (mk94U54Wire p18 t2).val < 149) := by
  revert p18 t2; decide
theorem mkInvMidTrit_congr_cat (m₀ : ℕ) (hm₀ : m₀ ≤ 15) {γ₁ γ₂ : BitAssignment 268}
    (h : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ₁ q = γ₂ q)
    (h₂ : mkInvMidTrit m₀ hm₀ γ₂) : mkInvMidTrit m₀ hm₀ γ₁ := by
  have h107 : ∀ q : Wire 268, q.val < 107 → γ₁ q = γ₂ q := fun q hq ↦ h q (by omega)
  refine ⟨fun p18 hp t2 ↦ ?_, fun i ↦ ?_, ?_, fun w hw ↦ ?_⟩
  · rw [h _ (mk94U54Wire_not_cat p18 t2), h mk94AccW (by decide), mk94ActP18_congr_sel h107,
      h mk94A2W (by decide), h mk94C2W (by decide)]
    exact h₂.1 p18 hp t2
  · rw [h ⟨176 + m₀ + i.val, by omega⟩ (by dsimp; omega), h mk94AccW (by decide),
      mk94ActP18_congr_sel h107]
    exact h₂.2.1 i
  · rw [h mk94W11W (by decide), h mk94B0W (by decide), h mk94B1W (by decide)]
    exact h₂.2.2.1
  · exact (h w (by omega)).trans (h₂.2.2.2 w hw)
theorem mkTailTritProg_spec (m₀ : ℕ) (hm₀ : m₀ ≤ 15) :
    (mkTailTritProg m₀ hm₀).FwdClean (mkInvMidTrit m₀ hm₀) ∧
    (∀ γ : BitAssignment 268, mkInvMidTrit m₀ hm₀ γ →
      let γ' := (mkTailTritProg m₀ hm₀).fwdBits γ
      mk94InvU54 γ' ∧
      ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 233 + 2 * m₀)) → γ' q = γ q) := by
  obtain ⟨_, hCT, hBT⟩ := mk94SeqSplitTrit_spec (16 - m₀)
    (fun i ↦ ⟨176 + m₀ + i.val, by omega⟩)
    (fun i ↦ ⟨233 + 2 * m₀ + 2 * i.val, by omega⟩)
    (fun i ↦ ⟨234 + 2 * m₀ + 2 * i.val, by omega⟩)
    mk94A2W mk94C2W (by decide) (by decide)
    (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j ↦ Fin.ne_of_val_ne (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  refine ⟨hCT _ (fun γ hγ ↦ ⟨fun i ↦ hγ.2.2.2 _ (by dsimp; omega),
      fun i ↦ hγ.2.2.2 _ (by dsimp; omega)⟩),
    fun γ ⟨hLow, hHi, hW11, hCl⟩ ↦ ?_⟩
  obtain ⟨hT0, hT1, hT2, hTOut⟩ := hBT γ
    (fun i ↦ hCl _ (by dsimp; omega)) (fun i ↦ hCl _ (by dsimp; omega))
  have hout : ∀ q : Wire 268,
      (q.val < 176 + m₀ ∨ (192 ≤ q.val ∧ q.val < 233 + 2 * m₀) ∨ 265 ≤ q.val) →
      (mkTailTritProg m₀ hm₀).fwdBits γ q = γ q := fun q hq ↦
    hTOut q
      (fun i ↦ Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega))
      (fun i ↦ Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega))
      (fun i ↦ Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega))
  have hlt : ∀ q : Wire 268, q.val < 174 → (mkTailTritProg m₀ hm₀).fwdBits γ q = γ q :=
    fun q hq ↦ hout q (Or.inl (by omega))
  refine ⟨⟨fun p18 t2 ↦ ?_, ?_, fun w hw ↦ ?_⟩, fun q hq ↦ ?_⟩
  · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt,
      hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
    by_cases hp : p18.val < 2 + m₀
    · have hbnd := mk94U54Wire_lt_bounds m₀ hm₀ p18 hp t2
      rw [hout _ (hbnd.elim Or.inl (fun ⟨h1, h2⟩ ↦ Or.inr (Or.inl ⟨by omega, h2⟩)))]
      exact hLow p18 hp t2
    · let i : Fin (16 - m₀) := ⟨p18.val - (2 + m₀), by omega⟩
      have hp0 : ¬(p18.val = 0) := by omega
      have hp1 : ¬(p18.val = 1) := by omega
      have hp_val : 2 + m₀ + i.val = p18.val := by dsimp [i]; omega
      rcases t2 with ⟨_ | _ | _ | v, hv⟩
      · have hw : mk94U54Wire p18 ⟨0, hv⟩ = ⟨176 + m₀ + i.val, by omega⟩ := by
          apply Fin.ext; simp [mk94U54Wire, i]; omega
        rw [hw]; dsimp only [mkTailTritProg]
        rw [hT0 i, hHi i, hp_val]; (split_ifs <;> try omega); all_goals ring
      · have hw : mk94U54Wire p18 ⟨1, hv⟩ = ⟨233 + 2 * m₀ + 2 * i.val, by omega⟩ := by
          apply Fin.ext; simp [mk94U54Wire, hp0, hp1, i]; omega
        rw [hw]; dsimp only [mkTailTritProg]
        rw [hT1 i, hHi i, hp_val]; (split_ifs <;> try omega); all_goals ring
      · have hw : mk94U54Wire p18 ⟨2, hv⟩ = ⟨234 + 2 * m₀ + 2 * i.val, by omega⟩ := by
          apply Fin.ext; simp [mk94U54Wire, hp0, hp1, i]; omega
        rw [hw]; dsimp only [mkTailTritProg]
        rw [hT2 i, hHi i, hp_val]; (split_ifs <;> try omega); all_goals ring
      · omega
  · rw [hout mk94W11W (Or.inr (Or.inl (by dsimp [mk94W11W]; omega))),
      hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
    exact hW11
  · exact (hout w (Or.inr (Or.inr (by omega)))).trans (hCl w (by omega))
  · rcases hq with hq1 | ⟨hq2, hq3⟩
    · exact hlt q hq1
    · exact hout q (Or.inr (Or.inl ⟨by omega, hq3⟩))
def mkCollapseTrit (m₀ : ℕ) (δ : BitAssignment 268) : BitAssignment 268 := fun w ↦ if 176 + m₀
    ≤ w.val ∧ w.val < 192 then δ mk94AccW * (if w.val - 174 = mk94ActP18 δ then 1 else 0) else
    if 233 + 2 * m₀ ≤ w.val then 0 else δ w
theorem mkTailTritProg_rev_spec (m₀ : ℕ) (hm₀ : m₀ ≤ 15) (δ : BitAssignment 268)
    (hδ : mk94InvU54 δ) : mkInvMidTrit m₀ hm₀ (mkCollapseTrit m₀ δ) ∧ δ =
    (mkTailTritProg m₀ hm₀).fwdBits (mkCollapseTrit m₀ δ) ∧ (mkTailTritProg m₀ hm₀).revBits δ
    = mkCollapseTrit m₀ δ ∧ (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 233 + 2 *
    m₀)) → mkCollapseTrit m₀ δ q = δ q) := by
  have hout : ∀ q : Wire 268, (q.val < 176 + m₀ ∨ (192 ≤ q.val ∧ q.val < 233 + 2 * m₀)) →
      mkCollapseTrit m₀ δ q = δ q := by
    intro q hq
    dsimp only [mkCollapseTrit]
    split_ifs <;> first | rfl | (rcases hq with h | ⟨h1, h2⟩ <;> omega)
  have hlt : ∀ q : Wire 268, q.val < 174 → mkCollapseTrit m₀ δ q = δ q :=
    fun q hq ↦ hout q (Or.inl (by omega))
  have hMid : mkInvMidTrit m₀ hm₀ (mkCollapseTrit m₀ δ) := by
    refine ⟨fun p18 hp t2 ↦ ?_, fun i ↦ ?_, ?_, fun w hw ↦ ?_⟩
    · have hbnd := mk94U54Wire_lt_bounds m₀ hm₀ p18 hp t2
      rw [hout _ (hbnd.elim Or.inl (fun ⟨h1, h2⟩ ↦ Or.inr ⟨by omega, h2⟩)),
        hlt mk94AccW (by decide), mk94ActP18_congr hlt,
        hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
      exact hδ.1 p18 t2
    · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt]
      dsimp only [mkCollapseTrit]
      rw [ite_eq_left ⟨by omega, by omega⟩]
      have hsub : 176 + m₀ + i.val - 174 = 2 + m₀ + i.val := by omega
      rw [hsub]
    · rw [hout mk94W11W (Or.inr ⟨by decide, by dsimp [mk94W11W]; omega⟩),
        hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
      exact hδ.2.1
    · dsimp only [mkCollapseTrit]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  obtain ⟨hU54', hOut'⟩ := (mkTailTritProg_spec m₀ hm₀).2 _ hMid
  have hkeep : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 233 + 2 * m₀)) →
      mkCollapseTrit m₀ δ q = δ q := fun q hq ↦
    hout q (hq.elim (fun h ↦ Or.inl (by omega)) (fun ⟨h1, h2⟩ ↦ Or.inr ⟨by omega, h2⟩))
  have heq : δ = (mkTailTritProg m₀ hm₀).fwdBits (mkCollapseTrit m₀ δ) :=
    mk94InvU54_ext hδ hU54' fun q hq ↦
      ((hOut' q (hq.elim Or.inl (fun ⟨h1, h2⟩ ↦ Or.inr ⟨h1, by omega⟩))).trans
        (hkeep q (hq.elim Or.inl (fun ⟨h1, h2⟩ ↦ Or.inr ⟨h1, by omega⟩)))).symm
  refine ⟨hMid, heq, ?_, hkeep⟩
  conv_lhs => rw [heq]
  exact (mkTailTritProg m₀ hm₀).revBits_fwdBits _
/-- `68 - 4 * m₀`-`T` (`0 .TOFF`) W-State replacement for `(mkTailTritProg m₀ hm₀).fwdDyn r268`. -/
def dSplitTailTrit_wstate (m₀ : ℕ) (hm₀ : m₀ ≤ 15) {Var : Type} {n : ℕ}
    (v : Var) (r268 : QRegister 268 n) : DynamicCircuit Var n :=
  dSeqSplitTrit_wstate v r268 (16 - m₀)
    (fun i ↦ ⟨176 + m₀ + i.val, by omega⟩)
    (fun i ↦ ⟨233 + 2 * m₀ + 2 * i.val, by omega⟩)
    (fun i ↦ ⟨234 + 2 * m₀ + 2 * i.val, by omega⟩)
    mk94A2W mk94C2W (by decide) (by decide)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
theorem dSplitTailTrit_wstate_counts (m₀ : ℕ) (hm₀ : m₀ ≤ 15) {Var : Type} {n : ℕ} (v : Var)
    (r268 : QRegister 268 n) : (dSplitTailTrit_wstate m₀ hm₀ v r268).count .T = 68 - 4 * m₀ ∧
    (dSplitTailTrit_wstate m₀ hm₀ v r268).count .TOFF = 0 := by
  obtain ⟨ht, hf⟩ := dSeqSplitTrit_wstate_counts v r268 (16 - m₀) _ _ _ mk94A2W mk94C2W
    (by decide) (by decide) _ _ _ _ _ _ _ _
  exact ⟨ht.trans (by omega), hf⟩
theorem dSplitTailTrit_wstate_realizes (m₀ : ℕ) (hm₀ : m₀ ≤ 15) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} (v : Var) (r268 : QRegister 268 n) : RealizesCleanUnitary v
    (p57DiagProj r268 (mkInvMidTrit m₀ hm₀)) (dSplitTailTrit_wstate m₀ hm₀ v r268)
    (((mkTailTritProg m₀ hm₀).fwdCircuit r268).eval) ∧ PreservesStoreConst
    (dSplitTailTrit_wstate m₀ hm₀ v r268) := by
  refine dSeqSplitTrit_wstate_realizes v r268 (16 - m₀)
    (fun i ↦ ⟨176 + m₀ + i.val, by omega⟩)
    (fun i ↦ ⟨233 + 2 * m₀ + 2 * i.val, by omega⟩)
    (fun i ↦ ⟨234 + 2 * m₀ + 2 * i.val, by omega⟩)
    mk94A2W mk94C2W (by decide) (by decide)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ Fin.ne_of_val_ne (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (mkInvMidTrit m₀ hm₀)
    (fun γ ↦ decide (γ mk94AccW = 1) && decide (2 + m₀ ≤ mk94ActP18 γ))
    (fun γ ↦ if h : 2 + m₀ ≤ mk94ActP18 γ then
      ⟨mk94ActP18 γ - (2 + m₀), by have := mk94ActP18_lt γ; omega⟩ else ⟨0, by omega⟩)
    (fun {γ₁ γ₂} hlt ↦ by
      have hp := mk94ActP18_congr hlt
      refine ⟨by rw [hlt mk94AccW (by decide), hp], ?_⟩
      by_cases h : 2 + m₀ ≤ mk94ActP18 γ₁
      · have h' : 2 + m₀ ≤ mk94ActP18 γ₂ := hp ▸ h
        rw [dite_eq_left h, dite_eq_left h']; exact Fin.ext (by dsimp; omega)
      · have h' : ¬(2 + m₀ ≤ mk94ActP18 γ₂) := hp ▸ h
        rw [dite_eq_right h, dite_eq_right h'])
    (fun γ hγ ↦ ?_)
  refine ⟨fun i ↦ ?_, fun _ ↦ hγ.2.2.2 _ (by dsimp; omega), fun _ ↦ hγ.2.2.2 _ (by dsimp; omega),
    hγ.2.2.2 _ (by dsimp; omega), hγ.2.2.2 _ (by dsimp; omega), hγ.2.2.2 _ (by dsimp; omega)⟩
  rw [hγ.2.1 i]
  by_cases hge : 2 + m₀ ≤ mk94ActP18 γ
  · rw [dite_eq_left hge]
    rcases fmkBit_cases (γ mk94AccW) with ha | ha
    · simp [ha]
    · simp only [ha, hge, decide_true, Bool.and_self, ↓reduceIte, one_mul, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
  · have hne : ¬(2 + m₀ + i.val = mk94ActP18 γ) := by omega
    simp [hge, hne]
attribute [local semireducible] mk94Pass01BodyBits
end Part2_ParametricWStateMidKick
end
end Slot3MidKickWStateMultiBank
end
end Slot3MidKickWStateMultiBank

noncomputable section SlimStageBDepsA

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
section SharedScope
local instance (priority := 1000000) instNeZeroK13 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority :=
  1000000) instGroupUnitaryFast_SlimStageBDepsA (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_SlimStageBDepsA (D : ℕ) : Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
namespace LocalHeldStreamFoldedPass123Bridge
open HeldStreamFoldedPass123Bridge
section Impl07f
set_option maxRecDepth 131072
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open InterWalkRSum42Hoist (kFull80)
open Leaf4Ext48TopStitch
/-- Raw-stream `dSelectCtrl` `(rAct, rWork)` subspace operator. -/
noncomputable def pRawCtrl3ExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_rawCtrl3Ext k_idle hk) * rWork.basisOutcomeProjector 0
/-- Raw-stream `dSelectCat` `(rAct, rWork)` subspace operator. -/
noncomputable def pRawHoistExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_rawSegExt k_idle hk) * rWork.basisOutcomeProjector 0
end Impl07f
end LocalHeldStreamFoldedPass123Bridge
namespace LocalStageAPointPhase128OnStep
open StageAPointPhase128OnStep
section ConfigK6
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open DyadicQft64 DyadicQft64WalkCircuit DyadicQft64WalkCircuit288
@[simp] theorem activeTwoElecForestFullQftStage128_tCost :
    activeTwoElecForestFullQftStage128.tCost = 221 := rfl
-- ============================================================================
-- Section 2: 5-Cutoff Hybrid `(z_w, rSum14_w)` `CanonStageSpec128` Decomposition (`117 T`) &
--            Concrete `dPointQftPhaseRsum42Fwd128` / `Inv128`
-- ============================================================================
end ConfigK6
end LocalStageAPointPhase128OnStep
namespace LocalHeldStreamEStream42Interface
section ConfigPartnerSwap
set_option maxRecDepth 65536
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open SpecsAux SpecsAux.SpecMirror
open InterWalkRSum42Hoist
  (kActOrig rAct0 E_rawStream42 E_rawStream42_eq_streamProjOp PreservesFeature
  embedAct0_comm_streamOp)
open Leaf4Ext48TopStitch
  (pCtrl3Zero pExt6Zero pExt6Zero_eq_mul pExt6IdleZero pExt6IdleZero_eq_mul pPGIdleZero pSlack3Zero
  rPGIdleOrig rSlack3Orig rUnusedCtrl3Orig)
theorem embedAct0_projZero_comm_E_rawStream42 {m : ℕ} (rOrig : QRegister m kActOrig) :
    (rAct0.compose rOrig).basisOutcomeProjector 0 * E_rawStream42 =
      E_rawStream42 * (rAct0.compose rOrig).basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
    ← QRegister.basisOutcomeProjector, E_rawStream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp ((PreservesFeature.basisOutcomeProjector rOrig 0).id_imp _)
theorem E_rawStream42_comm_pCtrl3Zero : E_rawStream42 * pCtrl3Zero = pCtrl3Zero * E_rawStream42 :=
  (embedAct0_projZero_comm_E_rawStream42 rUnusedCtrl3Orig).symm
theorem E_rawStream42_comm_pSlack3Zero : E_rawStream42 * pSlack3Zero = pSlack3Zero *
    E_rawStream42 :=
  (embedAct0_projZero_comm_E_rawStream42 rSlack3Orig).symm
theorem E_rawStream42_comm_pPGIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_rawStream42 * pPGIdleZero k_idle hk = pPGIdleZero k_idle hk * E_rawStream42 :=
  (embedAct0_projZero_comm_E_rawStream42 (rPGIdleOrig k_idle hk)).symm
theorem E_rawStream42_comm_pExt6Zero : E_rawStream42 * pExt6Zero = pExt6Zero * E_rawStream42 := by
  rw [pExt6Zero_eq_mul, ← Matrix.mul_assoc, E_rawStream42_comm_pCtrl3Zero,
    Matrix.mul_assoc, E_rawStream42_comm_pSlack3Zero, ← Matrix.mul_assoc]
theorem E_rawStream42_comm_pExt6IdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_rawStream42 * pExt6IdleZero k_idle hk = pExt6IdleZero k_idle hk * E_rawStream42 := by
  rw [pExt6IdleZero_eq_mul, ← Matrix.mul_assoc, E_rawStream42_comm_pExt6Zero,
    Matrix.mul_assoc, E_rawStream42_comm_pPGIdleZero k_idle hk, ← Matrix.mul_assoc]
end ConfigPartnerSwap
end LocalHeldStreamEStream42Interface
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
namespace LocalElecHadTrueSwapLocalCompClosure
section ImplElecHad
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24Barrel3Pass
  (rDataElec dataActiveSlot dataActiveSlot_eq_of_anchor_eq rDataAnchor_extract_replace_elec)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
/-- Updating active electron slot `dataActiveSlot selMux idxFn hIdxLt d` inside `d : Fin (2 ^
  kData)`
preserves `dataActiveSlot` because `rDataElec` (`[0 .. 3924)`) is disjoint from `rDataAnchor`
(`[3968 .. 3976)`). -/
theorem dataActiveSlot_replace_active {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) (d : Fin (2 ^ kData))
    (v : Fin (2 ^ 18)) : dataActiveSlot selMux idxFn hIdxLt ((rDataElec selMux (dataActiveSlot
    selMux idxFn hIdxLt d)).replaceIndex d v) = dataActiveSlot selMux idxFn hIdxLt d :=
    dataActiveSlot_eq_of_anchor_eq selMux idxFn hIdxLt (rDataAnchor_extract_replace_elec
    selMux (dataActiveSlot selMux idxFn hIdxLt d) d v)
/-- **Concrete `Slot18Lens kData` for the 218-Electron Anchor Bank (`anchorLens218`)**. -/
noncomputable def anchorLens218 {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) : Slot18Lens kData where
  tbl d := (rDataElec selMux (dataActiveSlot selMux idxFn hIdxLt d)).extractIndex d
  updSlot d v := (rDataElec selMux (dataActiveSlot selMux idxFn hIdxLt d)).replaceIndex d v
  get_put d v := by
    rw [dataActiveSlot_replace_active selMux idxFn hIdxLt d v,
        QRegister.extractIndex_replaceIndex]
  put_get d := QRegister.replaceIndex_extractIndex _ d
  put_put d v₁ v₂ := by
    rw [dataActiveSlot_replace_active selMux idxFn hIdxLt d v₁,
        QRegister.replaceIndex_replaceIndex]
end ImplElecHad
end LocalElecHadTrueSwapLocalCompClosure
namespace LocalZeroHypSlot0CommAndHMidClosure
open ZeroHypSlot0CommAndHMidClosure
section Impl10f
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open StageADeconstrCore (selDataInAct selMeasInAct)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open ElecHadTrueSwapLocalCompClosure (uLensSwap)
/-- **Master Subspace Restriction Identity on `Pm` (`restrictToMeasZero_embed_mul_Pm`)**:
Whenever `V.1 * Pm = Pm * V.1`, `V` acts on `Pm` identically to
`(selDataInAct kData).embedUnitary (restrictToMeasZero V hComm)`! -/
theorem restrictToMeasZero_embed_mul_Pm {kData : ℕ}
    (V : Unitary (2 ^ (kData + 18)))
    (hComm : V.1 * (selMeasInAct kData).basisOutcomeProjector 0 =
      (selMeasInAct kData).basisOutcomeProjector 0 * V.1) :
    let selD := selDataInAct kData
    let selM := selMeasInAct kData
    V.1 * selM.basisOutcomeProjector 0 =
      (selD.embedUnitary (restrictToMeasZero V hComm)).1 * selM.basisOutcomeProjector 0 :=
  op_mul_Pm_eq_embedMatrix_restrictMat V.1 hComm
-- ============================================================================
-- Section 2: Active-Slot Zero Projector `P_slot0 L` & Automatic `hMid` / `hLocalComp`
--            Reduction from `P_slot0 L` Commutation
-- ============================================================================
/-- **Automatic `hMid` Intertwining from `P_slot0 L` Commutation
(`uMid_intertwines_uLensSwap_of_comm_P_slot0`)**:
Whenever `uMid.1 * P_slot0 L = P_slot0 L * uMid.1`,
`(uMid * uLensSwap L).1 * Pm = (uLensSwap L * (selDataInAct kData).embedUnitary (restrictOfCommSlot0
L uMid hCommSlot0)).1 * Pm`! -/
theorem uMid_intertwines_uLensSwap_of_comm_P_slot0 {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18)))
    (hCommSlot0 : uMid.1 * P_slot0 L = P_slot0 L * uMid.1) :
    let selD := selDataInAct kData
    let Pm := (selMeasInAct kData).basisOutcomeProjector 0
    (uMid * uLensSwap L).1 * Pm =
      (uLensSwap L).1 * (selD.embedUnitary (restrictOfCommSlot0 L uMid hCommSlot0)).1 * Pm := by
  intro selD Pm
  have hRes := restrictToMeasZero_embed_mul_Pm (swapConjUnitary L uMid)
    (swapConjUnitary_comm_Pm L uMid hCommSlot0)
  have hMul := congrArg ((uLensSwap L).1 * ·) hRes
  have hLhs : (uLensSwap L).1 * ((swapConjUnitary L uMid).1 * Pm) = (uMid * uLensSwap L).1 * Pm :=
    by
    change (uLensSwap L).1 * (((uLensSwap L).1 * uMid.1 * (uLensSwap L).1) * Pm) =
      (uMid.1 * (uLensSwap L).1) * Pm
    calc
      (uLensSwap L).1 * (((uLensSwap L).1 * uMid.1 * (uLensSwap L).1) * Pm)
        = ((uLensSwap L).1 * (uLensSwap L).1) * (uMid.1 * (uLensSwap L).1) * Pm := by
            simp only [Matrix.mul_assoc]
      _ = (uMid.1 * (uLensSwap L).1) * Pm := by
            rw [uLensSwap_val_mul_self L, Matrix.one_mul]
  rw [hLhs, ← Matrix.mul_assoc] at hMul
  exact hMul
end Impl10f
end LocalZeroHypSlot0CommAndHMidClosure
open ZeroHypStageABToUFoldedPass123SegAndCompac (embedUnitary_list_ofFn_prod)
open InterWalkRSum42Hoist (qreg_ext)
namespace LocalStageBTwoElecQftStream218Inner
open StageBTwoElecQftStream218Inner HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open PosSlots24PartnerMux288 hiding ite_pos ite_neg qreg_ext
open MidKickSub33 (pos24TailMag30MidpointB)
open InterWalkRSum42Hoist (qreg_block_apply)
open QRegExt
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open DyadicQft64WalkCircuit (rAxis654)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix axisProdPrefix)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6 uCoreHadamard18)
open StageAPointPhase128OnStep (hL6_le_654 activeTwoElecForestFullQftStage128)
open Slot0SubAdd14And217Stream (rSum14Slice42)
open StageADeconstrCore (selDataInAct selDataInAct_apply selDataInAct_disj_selMeasInAct)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open ZeroHypSlot0CommAndHMidClosure (P_slot0)
/-- 6-wire sub-block `[6 * w .. 6 * w + 6)` inside an 18-wire electron register. -/
def rAxis6In18 (w : Fin 3) : QRegister 6 18 :=
  QRegister.block (6 * w.val) 6 (by have := w.isLt; omega)
/-- 6-wire input map for axis `w` inside `Fin 18`. -/
def elec18AxisWire (w : Fin 3) (r : Fin 6) : Wire 18 := rAxis6In18 w r
/-- 6-bit momentum value `regVal (rAxis6In18 w) γ` of an 18-wire electron along axis `w`. -/
def elec18AxisVal (w : Fin 3) (γ : BitAssignment 18) : ℕ := regVal (rAxis6In18 w) γ
theorem elec18AxisVal_eq_sum (w : Fin 3) (γ : BitAssignment 18) :
    elec18AxisVal w γ = ∑ r : Fin 6, 2 ^ r.val * (γ (elec18AxisWire w r)).val := by
  unfold elec18AxisVal elec18AxisWire regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
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
theorem compose_selElec18Sum14In42 {n : ℕ} (rElec : QRegister 18 n) (rSum42 : QRegister 42 n)
    (hESum42 : rElec.DisjointWires rSum42) (w : Fin 3) : (rElec.concat rSum42 hESum42).compose
    (selElec18Sum14In42 w) = rElec.concat (rSum42.compose (rSum14Slice42 w))
    (hESum42.compose_right (rSum14Slice42 w)) := by
  apply qreg_ext; intro idx
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
noncomputable def uElec18Sum42Add : Unitary (2 ^ (18 + 42)) := ((selElec18Sum14In42
    2).embedUnitary (uElec18AxisAdd14 2) * (selElec18Sum14In42 1).embedUnitary
    (uElec18AxisAdd14 1)) * (selElec18Sum14In42 0).embedUnitary (uElec18AxisAdd14 0)
/-- General system-register congruence for `catModAddUnitary`: whenever two system registers
`rSys₁ : QRegister k₁ N` and `rSys₂ : QRegister k₂ N` compute the exact same shift on every
ambient bit assignment `β : BitAssignment N`, their embedded `catModAddUnitary` unitaries on a
shared target register `rCat : QRegister B N` are equal. -/
theorem embedUnitary_catModAddUnitary_congr_sys {N k₁ k₂ B : ℕ} (rSys₁ : QRegister k₁ N)
    (rSys₂ : QRegister k₂ N) (rCat : QRegister B N) (h₁ : rSys₁.DisjointWires rCat)
    (h₂ : rSys₂.DisjointWires rCat) (shift₁ : BitAssignment k₁ → ℕ)
    (shift₂ : BitAssignment k₂ → ℕ) (hShift : ∀ β : BitAssignment N, shift₁ (fun i ↦ β (rSys₁
    i)) = shift₂ (fun i ↦ β (rSys₂ i))) : (rSys₁.concat rCat h₁).embedUnitary
    (catModAddUnitary k₁ B shift₁) = (rSys₂.concat rCat h₂).embedUnitary
    (catModAddUnitary k₂ B shift₂) := by
  let rSC₁ := rSys₁.concat rCat h₁
  let rSC₂ := rSys₂.concat rCat h₂
  have hKet : ∀ {k : ℕ} (rSys : QRegister k N) (hSC : rSys.DisjointWires rCat)
      (shift : BitAssignment k → ℕ) (idx₀ : Fin (2 ^ N)) (w : Fin N), basisBits N
      ((rSys.concat rCat hSC).replaceIndex idx₀ (catModAddPerm k B shift ((rSys.concat rCat
      hSC).extractIndex idx₀))) w = if hw : w ∈ Set.range rCat.wires then basisBits B ⟨(regVal
      rCat (basisBits N idx₀) + shift (fun i ↦ basisBits N idx₀ (rSys i))) % 2 ^ B, Nat.mod_lt
      _ (Nat.two_pow_pos B)⟩ (Classical.choose hw) else basisBits N idx₀ w := by
    intro k rSys hSC shift idx₀ w
    let rSC := rSys.concat rCat hSC
    let β := basisBits N idx₀
    have hext_sys :
        (splitSysCatEquiv k B (rSC.extractIndex idx₀)).1 = fun i ↦ β (rSys i) := by
      funext i
      dsimp only [splitSysCatEquiv, Equiv.trans_apply]
      change basisBits (k + B) (rSC.extractIndex idx₀) (Fin.castAdd B i) = β (rSys i)
      simp [rSC, β]
    have hext_cat_fin : (splitSysCatEquiv k B (rSC.extractIndex idx₀)).2 =
        (basisBitsEquiv B).symm (fun i ↦ β (rCat i)) := by
      change (basisBitsEquiv B).symm
          (fun j ↦ basisBits (k + B) (rSC.extractIndex idx₀) (Fin.natAdd k j)) =
        (basisBitsEquiv B).symm (fun i ↦ β (rCat i))
      congr 1; funext j; simp [rSC, β]
    have hext_cat : (splitSysCatEquiv k B (rSC.extractIndex idx₀)).2.val = regVal rCat β := by
      rw [hext_cat_fin, regVal, bitsVal_eq_symm_val]
    have hcat_eq : catModAddPerm k B shift (rSC.extractIndex idx₀) =
        (splitSysCatEquiv k B).symm (fun i ↦ β (rSys i), ⟨(regVal rCat β + shift (fun i ↦ β
        (rSys i))) % 2 ^ B, Nat.mod_lt _ (Nat.two_pow_pos B)⟩) := by
      simp only [catModAddPerm, Equiv.trans_apply]
      congr 1; ext
      · dsimp only [catModAddMidPerm, Equiv.coe_fn_mk]
        exact congrFun hext_sys _
      · simp only [catModAddMidPerm, Equiv.coe_fn_mk, hext_sys, hext_cat]
    by_cases hwSC : w ∈ Set.range rSC.wires
    · rcases hwSC with ⟨idx, rfl⟩
      rw [rSC.basisBits_replaceIndex_apply, hcat_eq]
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.concat_apply_left]
        have hi_not : rSys i ∉ Set.range rCat.wires := by
          rintro ⟨q, hq⟩
          exact hSC.ne i q hq.symm
        rw [dite_eq_right hi_not]
        simp [splitSysCatEquiv, β]
      · rw [QRegister.concat_apply_right]
        have hj_mem : rCat j ∈ Set.range rCat.wires := ⟨j, rfl⟩
        rw [dite_eq_left hj_mem]
        have hj_eq : Classical.choose hj_mem = j :=
          rCat.wires.injective (Classical.choose_spec hj_mem)
        rw [hj_eq]
        simp [splitSysCatEquiv, β]
    · have hw_not : w ∉ Set.range rCat.wires := by
        rintro ⟨j, rfl⟩
        exact hwSC ⟨Fin.natAdd k j, QRegister.concat_apply_right rSys rCat hSC j⟩
      rw [rSC.basisBits_replaceIndex_of_not_mem idx₀ _ w hwSC, dite_eq_right hw_not]
  apply Subtype.ext
  ext i j
  have hCol : (rSC₁.embedUnitary (catModAddUnitary k₁ B shift₁)).1.mulVec (Pi.single j 1) =
      (rSC₂.embedUnitary (catModAddUnitary k₂ B shift₂)).1.mulVec (Pi.single j 1) := by
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, catModAddUnitary, catModAddUnitary,
      rSC₁.embedMatrix_mulVec_single_factors, rSC₂.embedMatrix_mulVec_single_factors,
      permutationUnitary_mulVec_single, permutationUnitary_mulVec_single,
      rSC₁.tensorState_single_replaceIndex, rSC₂.tensorState_single_replaceIndex]
    congr 1
    apply (basisBitsEquiv N).injective
    funext w
    change basisBits N (rSC₁.replaceIndex j _) w = basisBits N (rSC₂.replaceIndex j _) w
    rw [hKet rSys₁ h₁ shift₁ j w, hKet rSys₂ h₂ shift₂ j w, hShift (basisBits N j)]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hCol i
/-- Selector extracting `rSum42` (`42`) from `(posCoreWires + 42) + 7` (`= 4,083`). -/
def selSum42InCoreSum42PG7 : QRegister 42 ((posCoreWires + 42) + 7) :=
  QRegister.block posCoreWires 42 (by omega)
section ImplSections2To5
set_option exponentiation.threshold 8192
theorem selSum42InCoreSum42PG7_disj_selCore : selSum42InCoreSum42PG7.DisjointWires
    selCoreInCoreSum42PG7 :=
      (QRegExt.disjointWires_symm (QRegister.block_disjoint_of_le 0 posCoreWires posCoreWires 42
    (by omega) (by omega) (by omega)))
theorem selPG7InCoreSum42PG7_disj_selCore : selPG7InCoreSum42PG7.DisjointWires
    selCoreInCoreSum42PG7 :=
      (QRegExt.disjointWires_symm (QRegister.block_disjoint_of_le 0 posCoreWires (posCoreWires +
    42) 7 (by omega) le_rfl (by omega)))
theorem selSum42InCoreSum42PG7_disj_selPG7 : selSum42InCoreSum42PG7.DisjointWires
    selPG7InCoreSum42PG7 := QRegister.block_disjoint_of_le posCoreWires 42 (posCoreWires + 42)
    7 (by omega) le_rfl (by omega)
def rSum42InActB42 : QRegister 42 (((posCoreWires + 42) + 7) + 18) :=
  (selDataInAct ((posCoreWires + 42) + 7)).compose selSum42InCoreSum42PG7
theorem rSum42InActB42_apply (i : Fin 42) :
    (rSum42InActB42 i).val = posCoreWires + i.val := by
  simp [rSum42InActB42, selDataInAct_apply,
    selSum42InCoreSum42PG7]
theorem rElec0InActB42_disj_rSum42InActB42 : rElec0InActB42.DisjointWires rSum42InActB42 := by
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  rw [rElec0InActB42_apply, rSum42InActB42_apply] at hv
  have := i.isLt; have := posCoreWires_eq_4034
  omega
theorem rPartner18InActB42_disj_rSum42InActB42 :
    rPartner18InActB42.DisjointWires rSum42InActB42 := by
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  rw [rPartner18InActB42_apply, rSum42InActB42_apply] at hv
  have := j.isLt
  omega
theorem rCoreInActB42_disj_rPartner18InActB42 :
    rCoreInActB42.DisjointWires rPartner18InActB42 :=
  (selDataInAct_disj_selMeasInAct ((posCoreWires + 42) + 7)).compose_left selCoreInCoreSum42PG7
theorem rElec0InActB42_disj_rPG7InActB42 : rElec0InActB42.DisjointWires rPG7InActB42 := by
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  rw [rElec0InActB42_apply, rPG7InActB42_apply] at hv
  have := i.isLt; have := posCoreWires_eq_4034
  omega
theorem rPartner18InActB42_disj_rPG7InActB42 :
    rPartner18InActB42.DisjointWires rPG7InActB42 :=
  (QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct ((posCoreWires + 42) +
    7))).compose_right selPG7InCoreSum42PG7
theorem rSum42InActB42_disj_rPG7InActB42 : rSum42InActB42.DisjointWires rPG7InActB42 := by
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  rw [rSum42InActB42_apply, rPG7InActB42_apply] at hv
  have := i.isLt
  omega
/-- Catalyzed 7-step Stage-B 2-electron QFT + `rSum42` stream inner unitary on
`((posCoreWires + 42) + 7) + 18`. -/
noncomputable def uStageBTwoElecStreamInner (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : Unitary (2 ^ (((posCoreWires + 42) + 7) + 18)) :=
  let uAdd0 := (rElec0InActB42.concat rSum42InActB42
      rElec0InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uAddP := (rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uQft2 := rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat
  let uSand := (rCoreInActB42.concat rPartner18InActB42
      rCoreInActB42_disj_rPartner18InActB42).embedUnitary (diagSignUnitary (sandPhase18
      slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB
      B hB1 (by omega)))))
  uAdd0 * (uAddP * (uQft2⁻¹ * (uSand * (uQft2 * (uAddP⁻¹ * uAdd0⁻¹)))))
theorem unitary_inv_comm_of_comm {D : ℕ} (U : Unitary D) (P : Matrix (Fin D) (Fin D) ℂ)
    (hComm : U.1 * P = P * U.1) : (U⁻¹).1 * P = P * (U⁻¹).1 := by
  have hR : U.1 * (U⁻¹).1 = 1 := by rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
  have hL : (U⁻¹).1 * U.1 = 1 := by rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  calc (U⁻¹).1 * P
    _ = ((U⁻¹).1 * P) * (U.1 * (U⁻¹).1) := by rw [hR, Matrix.mul_one]
    _ = (U⁻¹).1 * (P * U.1) * (U⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = (U⁻¹).1 * (U.1 * P) * (U⁻¹).1 := by rw [← hComm]
    _ = ((U⁻¹).1 * U.1) * P * (U⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = P * (U⁻¹).1 := by rw [hL, Matrix.one_mul]
/-- **`P_slot0 partnerLensOnCoreSum42PG7` Commutation for
`uStageBTwoElecStreamInner` (`uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp`)**. -/
theorem uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 * P_slot0
    partnerLensOnCoreSum42PG7 = P_slot0 partnerLensOnCoreSum42PG7 *
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 := by
  let P := P_slot0 partnerLensOnCoreSum42PG7
  have hPEq : P = rCoreSkip0InActB42.embedMatrix (Matrix.diagonal dPartnerSkip0) :=
    P_slot0_partnerLensOnCoreSum42PG7_eq_embedMatrix_diagonal
  have hDisjE0Sum : (rElec0InActB42.concat rSum42InActB42
      rElec0InActB42_disj_rSum42InActB42).DisjointWires rCoreSkip0InActB42 := by
    refine QRegExt.disjointWires_concat_left ?_ ?_
    · rw [QRegister.disjoint_iff]; intro i j h
      have hv := congrArg Fin.val h
      rw [rElec0InActB42_apply, rCoreSkip0InActB42_apply] at hv
      have := i.isLt; omega
    · rw [QRegister.disjoint_iff]; intro i j h
      have hv := congrArg Fin.val h
      rw [rSum42InActB42_apply, rCoreSkip0InActB42_apply] at hv
      have := j.isLt; have := posCoreWires_eq_4034; omega
  have hDisjPSum : (rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).DisjointWires rCoreSkip0InActB42 := by
    refine QRegExt.disjointWires_concat_left ?_ ?_
    · rw [QRegister.disjoint_iff]; intro i j h
      have hv := congrArg Fin.val h
      rw [rPartner18InActB42_apply, rCoreSkip0InActB42_apply] at hv
      have := j.isLt; have := posCoreWires_eq_4034; omega
    · rw [QRegister.disjoint_iff]; intro i j h
      have hv := congrArg Fin.val h
      rw [rSum42InActB42_apply, rCoreSkip0InActB42_apply] at hv
      have := j.isLt; have := posCoreWires_eq_4034; omega
  let uAdd0 := (rElec0InActB42.concat rSum42InActB42
      rElec0InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uAddP := (rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uQft2 := rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat
  let uSand := (rCoreInActB42.concat rPartner18InActB42
      rCoreInActB42_disj_rPartner18InActB42).embedUnitary (diagSignUnitary (sandPhase18
      slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB
      B hB1 (by omega)))))
  have hCommAdd0 : uAdd0.1 * P = P * uAdd0.1 := by
    rw [hPEq, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisjE0Sum _ _
  have hCommAddP : uAddP.1 * P = P * uAddP.1 := by
    rw [hPEq, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisjPSum _ _
  have hCommQft2 : uQft2.1 * P = P * uQft2.1 := by
    rw [hPEq]
    exact rCatSlot0Partner_uQft2_comm_rCoreSkip0_diagonal dPartnerSkip0
  have hCommSand : uSand.1 * P = P * uSand.1 := by
    rw [hPEq, embedMatrix_diagonal_eq rCoreSkip0InActB42 dPartnerSkip0]
    exact isDiagUnitary_comm_diagonal (isDiagUnitary_embed _ ⟨_, rfl⟩) _
  have hCommSub0 := unitary_inv_comm_of_comm uAdd0 P hCommAdd0
  have hCommSubP := unitary_inv_comm_of_comm uAddP P hCommAddP
  have hCommQft2Inv := unitary_inv_comm_of_comm uQft2 P hCommQft2
  have hMul : ∀ {A B : Unitary (2 ^ (((posCoreWires + 42) + 7) + 18))},
      A.1 * P = P * A.1 → B.1 * P = P * B.1 → (A * B).1 * P = P * (A * B).1 := fun hA hB ↦ by
    rw [Submonoid.coe_mul, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  exact hMul hCommAdd0 (hMul hCommAddP (hMul hCommQft2Inv
    (hMul hCommSand (hMul hCommQft2 (hMul hCommSubP hCommSub0)))))
/-- Uncatalyzed effective 7-step Stage-B inner unitary on `((posCoreWires + 42) + 7) + 18`,
replacing both `activeTwoElecForestFullQftStage128` passes by pure 18-wire `uCoreHadamard18`
on `rElec0InActB42` and `rPartner18InActB42` (leaving `rPG7` untouched). -/
noncomputable def uStageBTwoElecStreamInnerEff (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : Unitary (2 ^ (((posCoreWires + 42) + 7) + 18)) :=
  let uAdd0 := (rElec0InActB42.concat rSum42InActB42
      rElec0InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uAddP := (rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uHad2 := rElec0InActB42.embedUnitary uCoreHadamard18 * rPartner18InActB42.embedUnitary
      uCoreHadamard18
  let uSand := (rCoreInActB42.concat rPartner18InActB42
      rCoreInActB42_disj_rPartner18InActB42).embedUnitary (diagSignUnitary (sandPhase18
      slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB
      B hB1 (by omega)))))
  uAdd0 * (uAddP * (uHad2⁻¹ * (uSand * (uHad2 * (uAddP⁻¹ * uAdd0⁻¹)))))
theorem rIdSlot0Partner_embedUnitary_uEff_eq : rIdSlot0Partner.embedUnitary
    activeTwoElecForestFullQftStage128.uEff = rElec0InActB42.embedUnitary uCoreHadamard18 *
    rPartner18InActB42.embedUnitary uCoreHadamard18 := by
  have hEff : activeTwoElecForestFullQftStage128.uEff =
      axisProdPrefix 6 hL6_le_654 (fun _ ↦ uCoreHadamard6) := rfl
  rw [hEff]
  dsimp only [axisProdPrefix]
  rw [embedUnitary_list_ofFn_prod rIdSlot0Partner]
  rw[List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
      List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons, List.prod_cons,
      List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
  have hAxE (off : ℕ) (hoff : off + 6 ≤ 18) (b : Fin 6) (hb : 6 * b.val = off) :
      rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 b) =
        rElec0InActB42.compose (QRegister.block off 6 hoff) := by
    apply qreg_ext
    intro q
    have hq := q.isLt
    have hb' := b.isLt
    rw [QRegister.compose_apply, QRegister.compose_apply]
    have hIdx : rAxisPrefix 6 hL6_le_654 b q = ⟨off + q.val, by omega⟩ := by
      ext
      simp [rAxisPrefix, rAxis654, hb]
    rw [hIdx, rIdSlot0Partner_apply]
    dsimp only
    have hlt : off + q.val < 18 := by omega
    simp only [hlt, ↓reduceDIte]
    congr 1
  have hAxP (off : ℕ) (hoff : off + 6 ≤ 18) (b : Fin 6) (hb : 6 * b.val = 18 + off) :
      rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 b) =
        rPartner18InActB42.compose (QRegister.block off 6 hoff) := by
    apply qreg_ext
    intro q
    have hq := q.isLt
    have hb' := b.isLt
    rw [QRegister.compose_apply, QRegister.compose_apply]
    have hIdx : rAxisPrefix 6 hL6_le_654 b q = ⟨18 + off + q.val, by omega⟩ := by
      ext
      simp [rAxisPrefix, rAxis654, hb]
    rw [hIdx, rIdSlot0Partner_apply]
    dsimp only
    have h18 : ¬ (18 + off + q.val < 18) := by omega
    have h36 : 18 + off + q.val < 36 := by omega
    simp only [h18, h36, ↓reduceDIte]
    congr 1
    ext
    simp
    omega
  change (rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 0)).embedUnitary uCoreHadamard6 *
      ((rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 1)).embedUnitary uCoreHadamard6 *
      ((rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 2)).embedUnitary uCoreHadamard6 *
      ((rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 3)).embedUnitary uCoreHadamard6 *
      ((rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 4)).embedUnitary uCoreHadamard6 *
       (rIdSlot0Partner.compose (rAxisPrefix 6 hL6_le_654 5)).embedUnitary uCoreHadamard6)))) = _
  rw [hAxE 0 (by decide) 0 rfl, hAxE 6 (by decide) 1 rfl, hAxE 12 (by decide) 2 rfl,
      hAxP 0 (by decide) 3 rfl, hAxP 6 (by decide) 4 rfl, hAxP 12 (by decide) 5 rfl]
  unfold uCoreHadamard18
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, _root_.mul_assoc]
end ImplSections2To5
end LocalStageBTwoElecQftStream218Inner
namespace LocalStageBTwoElecQftStream218Inner
open StageBTwoElecQftStream218Inner HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open PosSlots24PartnerMux288 hiding ite_pos ite_neg qreg_ext
open MidKickSub33 (pos24TailMag30MidpointB)
open QRegExt
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open DyadicQft64WalkCircuit288 (mulVec_col0_eq_phaseGradKet7)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (U_cat_B_normalized_col_zero_singleCat)
open PhaseGradCatalystCore (IntertwinesCat)
open StageAPosHeadConjugatedCircuit (uCoreHadamard18)
open StageAPointPhase128OnStep (activeTwoElecForestFullQftStage128)
section ImplSections2To5
set_option exponentiation.threshold 8192
theorem intertwinesCatOp_embed_of_disj {N k : ℕ} (rSub : QRegister k N) (rPG : QRegister 7 N)
    (hDisj : rSub.DisjointWires rPG) (U_cat7 : Unitary (2 ^ 7)) (V : Unitary (2 ^ k)) :
    IntertwinesCatOp (rPG.embedUnitary U_cat7).1 (rPG.basisOutcomeProjector 0)
    (rSub.embedUnitary V).1 (rSub.embedUnitary V).1 :=
  IntertwinesCatOp.refl_of_comm
    (by
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
      exact QRegister.embedMatrix_comm_of_disjoint rSub rPG hDisj V.1 U_cat7.1)
    (by
      rw [QRegister.embedUnitary_val]
      exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSub rPG hDisj V.1 0)
theorem intertwinesCatOp_inv {N : ℕ} {U_cat : Operator (2 ^ N)} (rPG : QRegister 7 N)
    (B_cat B_eff : Unitary (2 ^ N))
    (h : IntertwinesCatOp U_cat (rPG.basisOutcomeProjector 0) B_cat.1 B_eff.1) :
    IntertwinesCatOp U_cat (rPG.basisOutcomeProjector 0) (B_cat⁻¹).1 (B_eff⁻¹).1 := by
  have hP_sa : star (rPG.basisOutcomeProjector 0) = rPG.basisOutcomeProjector 0 := by
    rw [Matrix.star_eq_conjTranspose, QRegister.basisOutcomeProjector_conjTranspose]
  have hStar := IntertwinesCatOp.unitary_star hP_sa B_cat B_eff h
  have h1 : (B_cat⁻¹).1 = star B_cat.1 := by rw [← Unitary.star_eq_inv]; rfl
  have h2 : (B_eff⁻¹).1 = star B_eff.1 := by rw [← Unitary.star_eq_inv]; rfl
  rw [h1, h2]
  exact hStar
/-- General `IntertwinesCatOp` theorem for `uStageBTwoElecStreamInner` with respect to any 7-qubit
phase-gradient preparation unitary `U_cat7` preparing `DyadicQft64.phaseGradKet 7` on `|0^7⟩`. -/
theorem uStageBTwoElecStreamInner_intertwinesCatOp (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) (U_cat7 : Unitary (2 ^ 7)) (hcol0 : U_cat7.1.mulVec (Pi.single 0
    1) = DyadicQft64.phaseGradKet 7) : IntertwinesCatOp (rPG7InActB42.embedUnitary U_cat7).1
    (rPG7InActB42.basisOutcomeProjector 0)
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1
    (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 := by
  have hDisjE0SumPG : (rElec0InActB42.concat rSum42InActB42
      rElec0InActB42_disj_rSum42InActB42).DisjointWires rPG7InActB42 :=
    QRegExt.disjointWires_concat_left rElec0InActB42_disj_rPG7InActB42
      rSum42InActB42_disj_rPG7InActB42
  have hDisjPSumPG : (rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).DisjointWires rPG7InActB42 :=
    QRegExt.disjointWires_concat_left rPartner18InActB42_disj_rPG7InActB42
      rSum42InActB42_disj_rPG7InActB42
  have hDisjCorePPG : (rCoreInActB42.concat rPartner18InActB42
      rCoreInActB42_disj_rPartner18InActB42).DisjointWires rPG7InActB42 := by
    refine QRegExt.disjointWires_concat_left ?_ rPartner18InActB42_disj_rPG7InActB42
    rw [QRegister.disjoint_iff]; intro i m h
    have hv := congrArg Fin.val h
    rw [rCoreInActB42_apply, rPG7InActB42_apply] at hv
    have := i.isLt; omega
  have hQftFwd := activeTwoElecForestFullQftStage128.hIntertwines rIdSlot0Partner rPG7InActB42
      rIdSlot0Partner_disj_rPG7InActB42 U_cat7 hcol0
  change IntertwinesCatOp _ _
    (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat).1
    (rIdSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uEff).1 at hQftFwd
  rw [rIdSlot0Partner_embedUnitary_uEff_eq] at hQftFwd
  let uHad2 := rElec0InActB42.embedUnitary uCoreHadamard18 * rPartner18InActB42.embedUnitary
      uCoreHadamard18
  have hQftInv := intertwinesCatOp_inv rPG7InActB42
    (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat) uHad2 hQftFwd
  have hAdd0 := intertwinesCatOp_embed_of_disj _ rPG7InActB42 hDisjE0SumPG U_cat7 uElec18Sum42Add
  have hSub0 := intertwinesCatOp_inv rPG7InActB42
    ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).embedUnitary
      uElec18Sum42Add)
    ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).embedUnitary
      uElec18Sum42Add)
    hAdd0
  have hAddP := intertwinesCatOp_embed_of_disj _ rPG7InActB42 hDisjPSumPG U_cat7 uElec18Sum42Add
  have hSubP := intertwinesCatOp_inv rPG7InActB42
    ((rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42).embedUnitary
      uElec18Sum42Add)
    ((rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42).embedUnitary
      uElec18Sum42Add)
    hAddP
  have hSand := intertwinesCatOp_embed_of_disj _ rPG7InActB42 hDisjCorePPG U_cat7
      (diagSignUnitary (sandPhase18 slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0
      pos24TailSign (pos24TailMag30MidpointB B hB1 (by omega)))))
  unfold uStageBTwoElecStreamInner uStageBTwoElecStreamInnerEff
  simp only [Submonoid.coe_mul]
  exact hAdd0.mul (hAddP.mul (hQftInv.mul (hSand.mul (hQftFwd.mul (hSubP.mul hSub0)))))
/-- **`IntertwinesCat` for `uStageBTwoElecStreamInner` on `U_cat_B_normalized 7`**. -/
theorem uStageBTwoElecStreamInner_intertwinesCat_normalized7_zeroHyp (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) : PhaseGradCatalystCore.IntertwinesCat
    (rPG7InActB42.embedUnitary (U_cat_B_normalized 7)).1 (rPG7InActB42.basisOutcomeProjector 0)
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1
    (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 := by
  have hOp := uStageBTwoElecStreamInner_intertwinesCatOp B hB1 hB27 slot2SwappedTo0
    (U_cat_B_normalized 7)
    (mulVec_col0_eq_phaseGradKet7 (U_cat_B_normalized 7) (U_cat_B_normalized_col_zero_singleCat 7))
  exact ⟨hOp.1, hOp.2.1, hOp.2.2⟩
/-- **`catState7` Reduction of `uStageBTwoElecStreamInner`**:
Acting on `U_cat * P_Cat0` (`|cat_7⟩⟨0^7|` on `rPG7`), `uStageBTwoElecStreamInner` reduces
identically
to `uStageBTwoElecStreamInnerEff` (pure 18-wire `uCoreHadamard18` on `rElecSlot 0` and `rPartner18`)
leaving the 7-qubit phase-gradient catalyst `|cat_7⟩` invariant! -/
theorem uStageBTwoElecStreamInner_mul_catState7_eq_zeroHyp
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    let U_cat := (rPG7InActB42.embedUnitary (U_cat_B_normalized 7)).1
    let P_Cat0 := rPG7InActB42.basisOutcomeProjector 0
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 * U_cat * P_Cat0 =
      U_cat * (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * P_Cat0 ∧
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0) =
      (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0) := by
  intro U_cat P_Cat0
  have hInt :=
    uStageBTwoElecStreamInner_intertwinesCat_normalized7_zeroHyp B hB1 hB27 slot2SwappedTo0
  refine ⟨hInt.1, ?_⟩
  calc (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0)
    _ = (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 * U_cat * P_Cat0 := by
        rw [Matrix.mul_assoc]
    _ = U_cat * (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * P_Cat0 := hInt.1
    _ = (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * U_cat * P_Cat0 := by
        rw [← hInt.2.1]
    _ = (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0) := by
        rw [Matrix.mul_assoc]
end ImplSections2To5
end LocalStageBTwoElecQftStream218Inner
namespace LocalMidUnitaryConjZeroRoot
section ImplK3
set_option exponentiation.threshold 8192
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge
  (fullSysCoreWires fullSysBEWires fullSysRawAncWires disjointWires_concat_left)
open CatalystPrep (U_cat_B_normalized)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply kFull80 rCoreFull rSum0 rSum14In42 rSum14Full)
open Barrel3PassSelectStitch (rCat80)
open Leaf4Ext48TopStitch
  (disj_of_val_ne rCoreFull_disj_rSum0 rCoreSwapCtrl3PG3At rCoreSwapCtrl3PG3At_val_eq
  rCoreSwapCtrl3PG3At_disj_rSum0)
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42 rSum14InCoreSum42)
open DoubleDutyFoldedRealizesBridge
  (rPG7Full rPG7Full_val_eq hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full)
/-- The 48-qubit phase-gradient catalyst state projector on `fullSysBEWires 80 + 48`. -/
noncomputable def catState48 : Operator (2 ^ (fullSysBEWires 80 + 48)) :=
  (rCat80.embedUnitary (U_cat_B_normalized 48)).1 * rCat80.basisOutcomeProjector 0
/-- Full-space `fullSysCoreWires 80 + 42` register `rCoreFull ++ rSum0` inside `kFull80 = 4,128`. -/
def rCoreSum42Full : QRegister (fullSysCoreWires 80 + 42) kFull80 :=
  rCoreFull.concat rSum0 rCoreFull_disj_rSum0
theorem rCoreSum42Full_compose_rCore :
    rCoreSum42Full.compose (rCoreInCoreSum42 80) = rCoreFull := by
  apply qreg_ext; intro i
  have hcast : rCoreInCoreSum42 80 i = Fin.castAdd 42 i := by
    ext; simp [rCoreInCoreSum42]
  change rCoreSum42Full (rCoreInCoreSum42 80 i) = rCoreFull i
  rw [hcast, rCoreSum42Full, QRegister.concat_apply_left]
theorem rCoreSum42Full_compose_rSum14 (w : Fin 3) :
    rCoreSum42Full.compose (rSum14InCoreSum42 80 w) = rSum14Full w := by
  apply qreg_ext; intro i
  have hcast : rSum14InCoreSum42 80 w i = Fin.natAdd (fullSysCoreWires 80) (rSum14In42 w i) := by
    ext; simp [rSum14InCoreSum42, rSum14In42]; omega
  change rCoreSum42Full (rSum14InCoreSum42 80 w i) = rSum14Full w i
  rw [hcast, rCoreSum42Full, QRegister.concat_apply_right]
  rfl
theorem rCoreSum42Full_disj_rPG7Full : rCoreSum42Full.DisjointWires rPG7Full :=
  disjointWires_concat_left _ hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full
/-- `Ctrl` active register `(rCoreFull ++ rSum0) ++ rPG7Full` inside `kFull80`. -/
def rCoreSum42PG7Full : QRegister ((fullSysCoreWires 80 + 42) + 7) kFull80 :=
  rCoreSum42Full.concat rPG7Full rCoreSum42Full_disj_rPG7Full
theorem rCoreSwapCtrl3PG3At_disj_rPG7Full (off : ℕ) (hoff : off + 3 ≤ 41) :
    (rCoreSwapCtrl3PG3At off (by omega)).DisjointWires rPG7Full :=
  disj_of_val_ne fun i q ↦ by
    rw [rCoreSwapCtrl3PG3At_val_eq, rPG7Full_val_eq]
    have hi := i.isLt; have hq := q.isLt
    dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
      SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
    split_ifs <;> omega
/-- `Cat` (`PG3`-swapped, `off + 3 ≤ 41`, valid for all `off = k_idle ≤ 38`, including `11` and
  `12`!)
active register `(rCoreSwapCtrl3PG3At off ++ rSum0) ++ rPG7Full` inside `kFull80`. -/
def rCoreSwapPG3Sum42PG7Full (off : ℕ) (hoff : off + 3 ≤ 41) :
    QRegister ((fullSysCoreWires 80 + 42) + 7) kFull80 :=
  ((rCoreSwapCtrl3PG3At off (by omega)).concat rSum0
    (rCoreSwapCtrl3PG3At_disj_rSum0 off (by omega))).concat rPG7Full
    (disjointWires_concat_left _ (rCoreSwapCtrl3PG3At_disj_rPG7Full off hoff) rSum0_disj_rPG7Full)
/-- The 3 unused `Ctrl3` wires `[3951 .. 3954)` inside `(fullSysCoreWires 80 + 42) + 7`. -/
def rCtrl3InCoreSum42PG7 : QRegister 3 ((fullSysCoreWires 80 + 42) + 7) :=
  QRegister.block 3951 3 (by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega)
end ImplK3
end LocalMidUnitaryConjZeroRoot
end SharedScope
end
end SlimStageBDepsA

noncomputable section SlimStageBDepsB

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
section SharedScope
local instance (priority := 1000000) instNeZeroK14 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority :=
  1000000) instGroupUnitaryFast_SlimStageBDepsB (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_SlimStageBDepsB (D : ℕ) : Semigroup (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBDepsB D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
open StageBTwoElecQftStream218Inner
  (selCoreInCoreSum42PG7 selPG7InCoreSum42PG7 partnerLensOnCoreSum42PG7 rPG7InActB42)
section BodyAux
set_option maxRecDepth 131072
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_compose_of_disjoint disjointWires_concat_left)
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24Barrel3Pass (rDataElec dataActiveSlot)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot partnerLens216)
open ZeroHypSlot0CommAndHMidClosure
  (P_slot0 embedMatrix_selDataInAct_inj_on_Pm restrictOfCommSlot0 mul_comm_P_slot0
  uLensSwap_val_mul_self)
open LocalZeroHypSlot0CommAndHMidClosure (uMid_intertwines_uLensSwap_of_comm_P_slot0)
theorem eq_of_basisBits_eq_local {q : ℕ} {x y : Fin (2 ^ q)}
    (h : ∀ w : Fin q, basisBits q x w = basisBits q y w) : x = y :=
  (basisBitsEquiv q).injective (funext h)
theorem fullSysCoreWires_80_eq_4034 : fullSysCoreWires 80 = 4034 := rfl
/-- Selector extracting `posCoreWires + 42` (`4,076`) from `(posCoreWires + 42) + 7` (`= 4,083`). -/
def selCoreSum42InCoreSum42PG7 : QRegister (posCoreWires + 42) ((posCoreWires + 42) + 7) :=
  QRegister.block 0 (posCoreWires + 42) (by omega)
/-- Selector extracting `posCoreWires` (`4,034`) from `posCoreWires + 42` (`= 4,076`). -/
def selCoreInCoreSum42 : QRegister posCoreWires (posCoreWires + 42) :=
  QRegister.block 0 posCoreWires (by omega)
/-- Selector extracting `rSum42` (`42`) from `posCoreWires + 42` (`= 4,076`). -/
def selSum42InCoreSum42 : QRegister 42 (posCoreWires + 42) :=
  QRegister.block posCoreWires 42 le_rfl
/-- Concrete Stage-B partner `Slot18Lens` on `posCoreWires + 42 = 4,076` (post-`catState7`
  reduction). -/
noncomputable abbrev partnerLensOnCoreSum42 : Slot18Lens (posCoreWires + 42) :=
  partnerLens216 selCoreInCoreSum42
/-- Selector extracting `(rCore ++ rSum42, rPartner18)` (`(posCoreWires + 42) + 18`) inside
`((posCoreWires + 42) + 7) + 18`. -/
def selCSPartnerInActB42 :
    QRegister ((posCoreWires + 42) + 18) (((posCoreWires + 42) + 7) + 18) :=
  ((selDataInAct ((posCoreWires + 42) + 7)).compose selCoreSum42InCoreSum42PG7).concat
    (selMeasInAct ((posCoreWires + 42) + 7))
    ((selDataInAct_disj_selMeasInAct ((posCoreWires + 42) +
      7)).compose_left selCoreSum42InCoreSum42PG7)
theorem selCSPartnerInActB42_disj_rPG7InActB42 :
    selCSPartnerInActB42.DisjointWires rPG7InActB42 := by
  have hDisjData : selCoreSum42InCoreSum42PG7.DisjointWires selPG7InCoreSum42PG7 :=
    QRegister.block_disjoint_of_le 0 (posCoreWires + 42) (posCoreWires + 42) 7
      (by omega) le_rfl le_rfl
  exact disjointWires_concat_left _
    (disjointWires_compose_of_disjoint (selDataInAct ((posCoreWires + 42) + 7)) hDisjData)
    (QRegExt.disjointWires_symm ((selDataInAct_disj_selMeasInAct ((posCoreWires + 42) +
      7)).compose_left selPG7InCoreSum42PG7))
-- ============================================================================
-- Section 1: Zero-Hypothesis `uWriteSub = uLensWrite` (`hWriteEq`), Polymorphic
--            `partnerLens216` Pure-CNOT Load/Write (`8,634 T`), Generic
--            `PartnerTrueSwapCleanSpec`, & `172w` / `190w` Hybrid True-Swap
-- ============================================================================
section Part1_ZeroHypHWriteEqAndPartnerTrueSwap
theorem matrix_eq_of_mulVec_single_part1 {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ} (h : ∀ g :
    Fin d, A.mulVec (Pi.single g 1) = B.mulVec (Pi.single g 1)) : A = B := by
  ext i g
  have hgi := congrFun (h g) i
  simp only [Matrix.mulVec_single_one] at hgi
  exact hgi
end Part1_ZeroHypHWriteEqAndPartnerTrueSwap
section Part2_RestrictHomomorphismAndCatState7
/-- Uniqueness of `restrictOfCommSlot0 L uInner hComm` from its `uLensSwap L` intertwining on
  `Pm`. -/
theorem restrictOfCommSlot0_eq_of_intertwine {kData : ℕ} (L : Slot18Lens kData)
    (uInner : Unitary (2 ^ (kData + 18)))
    (hComm : uInner.1 * P_slot0 L = P_slot0 L * uInner.1) (uTarget : Unitary (2 ^ kData))
    (hInt : (uInner * uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 =
    (uLensSwap L).1 * ((selDataInAct kData).embedUnitary uTarget).1 * (selMeasInAct
    kData).basisOutcomeProjector 0) : restrictOfCommSlot0 L uInner hComm = uTarget := by
  let selD := selDataInAct kData
  let Pm := (selMeasInAct kData).basisOutcomeProjector 0
  have h1 : (uInner * uLensSwap L).1 * Pm =
      (uLensSwap L).1 * (selD.embedUnitary (restrictOfCommSlot0 L uInner hComm)).1 * Pm :=
    uMid_intertwines_uLensSwap_of_comm_P_slot0 L uInner hComm
  have hEqSwap : (uLensSwap L).1 * (selD.embedUnitary (restrictOfCommSlot0 L uInner hComm)).1
      * Pm = (uLensSwap L).1 * (selD.embedUnitary uTarget).1 * Pm := h1.symm.trans hInt
  have hCancel (M : Operator (2 ^ (kData + 18))) :
      (uLensSwap L).1 * ((uLensSwap L).1 * M * Pm) = M * Pm := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, uLensSwap_val_mul_self L, Matrix.one_mul]
  have hEq : (selD.embedUnitary (restrictOfCommSlot0 L uInner hComm)).1 * Pm =
      (selD.embedUnitary uTarget).1 * Pm :=
    (hCancel _).symm.trans ((congrArg ((uLensSwap L).1 * ·) hEqSwap).trans (hCancel _))
  apply Subtype.ext
  apply embedMatrix_selDataInAct_inj_on_Pm
  simpa only [QRegister.embedUnitary_val] using hEq
/-- `restrictOfCommSlot0 L 1` is `1`. -/
@[simp] theorem restrictOfCommSlot0_one {kData : ℕ} (L : Slot18Lens kData) (h1 : (1 : Unitary
    (2 ^ (kData + 18))).1 * P_slot0 L = P_slot0 L * (1 : Unitary (2 ^ (kData + 18))).1) :
    restrictOfCommSlot0 L 1 h1 = 1 := by
  apply restrictOfCommSlot0_eq_of_intertwine
  rw [one_mul, QRegister.embedUnitary_one, OneMemClass.coe_one, Matrix.mul_one]
/-- **`restrictOfCommSlot0` Multiplication Homomorphism (`restrictOfCommSlot0_mul`)**:
`restrictOfCommSlot0 L (U₁ * U₂) = restrictOfCommSlot0 L U₁ * restrictOfCommSlot0 L U₂`. -/
theorem restrictOfCommSlot0_mul {kData : ℕ} (L : Slot18Lens kData)
    (U₁ U₂ : Unitary (2 ^ (kData + 18))) (h₁ : U₁.1 * P_slot0 L = P_slot0 L * U₁.1)
    (h₂ : U₂.1 * P_slot0 L = P_slot0 L * U₂.1)
    (h₁₂ : (U₁ * U₂).1 * P_slot0 L = P_slot0 L * (U₁ * U₂).1) : restrictOfCommSlot0 L
    (U₁ * U₂) h₁₂ = restrictOfCommSlot0 L U₁ h₁ * restrictOfCommSlot0 L U₂ h₂ := by
  let selD := selDataInAct kData
  let Pm := (selMeasInAct kData).basisOutcomeProjector 0
  let S := uLensSwap L
  let V₁ := restrictOfCommSlot0 L U₁ h₁
  let V₂ := restrictOfCommSlot0 L U₂ h₂
  apply restrictOfCommSlot0_eq_of_intertwine
  have hInt1 : (U₁ * S).1 * Pm = S.1 * (selD.embedUnitary V₁).1 * Pm :=
    uMid_intertwines_uLensSwap_of_comm_P_slot0 L U₁ h₁
  have hInt2 : (U₂ * S).1 * Pm = S.1 * (selD.embedUnitary V₂).1 * Pm :=
    uMid_intertwines_uLensSwap_of_comm_P_slot0 L U₂ h₂
  have hCommPm : (selD.embedUnitary V₂).1 * Pm = Pm * (selD.embedUnitary V₂).1 := by
    rw [QRegister.embedUnitary_val]
    exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      selD (selMeasInAct kData) (selDataInAct_disj_selMeasInAct kData) V₂.1 0
  change ((U₁ * U₂) * S).1 * Pm = S.1 * (selD.embedUnitary (V₁ * V₂)).1 * Pm
  calc ((U₁ * U₂) * S).1 * Pm
      = U₁.1 * ((U₂ * S).1 * Pm) := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = U₁.1 * (S.1 * ((selD.embedUnitary V₂).1 * Pm)) := by
          rw [hInt2]; simp only [Matrix.mul_assoc]
    _ = ((U₁ * S).1 * Pm) * (selD.embedUnitary V₂).1 := by
          rw [hCommPm]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (S.1 * (selD.embedUnitary V₁).1 * Pm) * (selD.embedUnitary V₂).1 := by
          rw [hInt1]
    _ = S.1 * ((selD.embedUnitary V₁).1 * (selD.embedUnitary V₂).1) * Pm := by
          calc (S.1 * (selD.embedUnitary V₁).1 * Pm) * (selD.embedUnitary V₂).1
              = S.1 * (selD.embedUnitary V₁).1 * (Pm * (selD.embedUnitary V₂).1) := by
                  simp only [Matrix.mul_assoc]
            _ = S.1 * ((selD.embedUnitary V₁).1 * (selD.embedUnitary V₂).1) * Pm := by
                  rw [← hCommPm]; simp only [Matrix.mul_assoc]
    _ = S.1 * (selD.embedUnitary (V₁ * V₂)).1 * Pm := by
          rw [QRegister.embedUnitary_mul, Submonoid.coe_mul]
/-- **`restrictOfCommSlot0` Inverse Homomorphism (`restrictOfCommSlot0_inv`)**. -/
theorem restrictOfCommSlot0_inv {kData : ℕ} (L : Slot18Lens kData)
    (U : Unitary (2 ^ (kData + 18))) (h : U.1 * P_slot0 L = P_slot0 L * U.1)
    (hInv : (U⁻¹).1 * P_slot0 L = P_slot0 L * (U⁻¹).1) : restrictOfCommSlot0 L U⁻¹ hInv =
    (restrictOfCommSlot0 L U h)⁻¹ := by
  have h1 : (1 : Unitary (2 ^ (kData + 18))).1 * P_slot0 L =
      P_slot0 L * (1 : Unitary (2 ^ (kData + 18))).1 := by
    rw [OneMemClass.coe_one, Matrix.one_mul, Matrix.mul_one]
  have hProd : restrictOfCommSlot0 L U h * restrictOfCommSlot0 L U⁻¹ hInv = 1 := by
    rw [← restrictOfCommSlot0_mul L U U⁻¹ h hInv (mul_comm_P_slot0 L h hInv)]
    have hUU : U * U⁻¹ = 1 := mul_inv_cancel U
    have hEq1 : restrictOfCommSlot0 L (U * U⁻¹) (mul_comm_P_slot0 L h hInv) =
        restrictOfCommSlot0 L 1 h1 := by
      congr 1
    rw [hEq1, restrictOfCommSlot0_one L h1]
  exact mul_eq_one_iff_inv_eq.mp hProd |>.symm
/-- `uLensSwap partnerLensOnCoreSum42PG7` is the exact embedding of `uLensSwap
  partnerLensOnCoreSum42`
along `selCSPartnerInActB42` (leaving `rPG7InActB42` untouched!). -/
theorem uLensSwap_partnerLensOnCoreSum42PG7_eq_embed : uLensSwap partnerLensOnCoreSum42PG7 =
    selCSPartnerInActB42.embedUnitary (uLensSwap partnerLensOnCoreSum42) := by
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner,
      PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
  apply Subtype.ext
  apply matrix_eq_of_mulVec_single_part1; intro g
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
    ZeroHypElecHadHCompAndPass123Closure.permUnitary]
  rw [QRegister.embedUnitary_val]
  dsimp only
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.embedMatrix_permMatrix_mulVec_single]
  have hPerm : (ZeroHypElecHadHCompAndPass123Closure.permMatrix
      (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin partnerLensOnCoreSum42PG7)).mulVec
        (Pi.single g 1) =
      Pi.single (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin partnerLensOnCoreSum42PG7 g) 1 :=
        by
    funext i; rw [Matrix.mulVec_single_one]
    change (if i = _ then (1 : ℂ) else 0) = (Pi.single _ (1 : ℂ) : _ → ℂ) i
    by_cases h : i =
      ZeroHypElecHadHCompAndPass123Closure.lensSwapFin partnerLensOnCoreSum42PG7 g <;>
      simp [h]
  rw [hPerm]
  refine congrArg (fun idx ↦ Pi.single idx (1 : ℂ)) ?_
  have hCoreComp : selCoreSum42InCoreSum42PG7.compose selCoreInCoreSum42 = selCoreInCoreSum42PG7 :=
    by
    apply qreg_ext; intro q; apply Fin.ext
    simp [selCoreSum42InCoreSum42PG7, selCoreInCoreSum42, selCoreInCoreSum42PG7]
  have hDComp : selCSPartnerInActB42.compose (selDataInAct (posCoreWires + 42)) =
      (selDataInAct ((posCoreWires + 42) + 7)).compose selCoreSum42InCoreSum42PG7 := by
    apply qreg_ext; intro q
    rw [QRegister.compose_apply]
    have hq : selDataInAct (posCoreWires + 42) q = Fin.castAdd 18 q := selDataInAct_apply q
    rw [hq]; dsimp only [selCSPartnerInActB42]; rw [QRegister.concat_apply_left]
  have hMComp : selCSPartnerInActB42.compose (selMeasInAct (posCoreWires + 42)) =
      selMeasInAct ((posCoreWires + 42) + 7) := by
    apply qreg_ext; intro j
    rw [QRegister.compose_apply]
    have hj : selMeasInAct (posCoreWires + 42) j = Fin.natAdd (posCoreWires + 42) j :=
      selMeasInAct_apply (kData := posCoreWires + 42) j
    rw [hj]; dsimp only [selCSPartnerInActB42]; rw [QRegister.concat_apply_right]
  let z0 := selCSPartnerInActB42.extractIndex g
  have hSlotEq : partnerActiveSlot selCoreInCoreSum42 ((selDataInAct (posCoreWires +
    42)).extractIndex z0) =
      partnerActiveSlot selCoreInCoreSum42PG7 ((selDataInAct ((posCoreWires + 42) +
        7)).extractIndex g) := by
    have hCoreExtr : selCoreInCoreSum42.extractIndex ((selDataInAct (posCoreWires +
      42)).extractIndex z0) =
        selCoreInCoreSum42PG7.extractIndex ((selDataInAct ((posCoreWires + 42) +
          7)).extractIndex g) := by
      dsimp only [z0]
      rw [← QRegister.extractIndex_compose, ← QRegister.extractIndex_compose,
          ← QRegister.compose_assoc, hDComp, QRegister.compose_assoc, hCoreComp,
          QRegister.extractIndex_compose]
    apply Fin.ext
    dsimp only [partnerActiveSlot, dataActiveSlot]
    rw [hCoreExtr]
  have hSlotRegComp : ∀ s' : Fin 218,
      selCSPartnerInActB42.compose
        ((selDataInAct (posCoreWires + 42)).compose (rDataElec selCoreInCoreSum42 s')) =
        (selDataInAct ((posCoreWires + 42) + 7)).compose (rDataElec selCoreInCoreSum42PG7 s') := by
    intro s'
    rw [← QRegister.compose_assoc, hDComp]
    dsimp only [rDataElec]
    rw [← QRegister.compose_assoc,
      QRegister.compose_assoc _ selCoreSum42InCoreSum42PG7 selCoreInCoreSum42,
        hCoreComp, QRegister.compose_assoc]
  rw [lensSwapFin_eq_two_replaceIndex partnerLensOnCoreSum42PG7
        (partnerActiveSlot selCoreInCoreSum42PG7) (rDataElec selCoreInCoreSum42PG7)
        (fun _ ↦ rfl) (fun _ _ ↦ rfl) g,
      lensSwapFin_eq_two_replaceIndex partnerLensOnCoreSum42
        (partnerActiveSlot selCoreInCoreSum42) (rDataElec selCoreInCoreSum42)
        (fun _ ↦ rfl) (fun _ _ ↦ rfl) z0]
  let s :=
    partnerActiveSlot selCoreInCoreSum42PG7 ((selDataInAct ((posCoreWires + 42) +
    7)).extractIndex g)
  rw [hSlotEq]
  let rSlot0 := (selDataInAct (posCoreWires + 42)).compose (rDataElec selCoreInCoreSum42 s)
  let rMeas0 := selMeasInAct (posCoreWires + 42)
  have hOuterInner : ∀ {k₁ k₂ N : ℕ} (rOut : QRegister k₁ N) (rIn : QRegister k₂ k₁)
      (x : Fin (2 ^ N)) (y : Fin (2 ^ k₁)) (v : Fin (2 ^ k₂)), rOut.replaceIndex x
      (rIn.replaceIndex y v) = (rOut.compose rIn).replaceIndex (rOut.replaceIndex x y) v := by
    intro k₁ k₂ N rOut rIn x y v
    apply eq_of_basisBits_eq_local; intro w
    by_cases hwOut : w ∈ Set.range rOut.wires
    · rcases hwOut with ⟨i₁, rfl⟩
      rw [QRegister.basisBits_replaceIndex_apply]
      by_cases hwIn : i₁ ∈ Set.range rIn.wires
      · rcases hwIn with ⟨i₂, rfl⟩
        rw [QRegister.basisBits_replaceIndex_apply, ← QRegister.compose_apply,
            QRegister.basisBits_replaceIndex_apply]
      · rw [QRegister.basisBits_replaceIndex_of_not_mem rIn y v i₁ hwIn]
        have hwComp : rOut i₁ ∉ Set.range (rOut.compose rIn).wires := by
          rintro ⟨i₂, hi₂⟩; exact hwIn ⟨i₂, rOut.wires.injective hi₂⟩
        rw [QRegister.basisBits_replaceIndex_of_not_mem (rOut.compose rIn) _ v _ hwComp,
            QRegister.basisBits_replaceIndex_apply]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem rOut x _ w hwOut]
      have hwComp : w ∉ Set.range (rOut.compose rIn).wires := by
        rintro ⟨i₂, rfl⟩; exact hwOut ⟨rIn i₂, rfl⟩
      rw [QRegister.basisBits_replaceIndex_of_not_mem (rOut.compose rIn) _ v w hwComp,
          QRegister.basisBits_replaceIndex_of_not_mem rOut x y w hwOut]
  rw [hOuterInner selCSPartnerInActB42 rMeas0 g
        (rSlot0.replaceIndex z0 (rMeas0.extractIndex z0)) (rSlot0.extractIndex z0),
      hOuterInner selCSPartnerInActB42 rSlot0 g z0 (rMeas0.extractIndex z0)]
  dsimp only [z0]
  rw[QRegister.replaceIndex_extractIndex,
      ← QRegister.extractIndex_compose selCSPartnerInActB42 rMeas0 g,
      ← QRegister.extractIndex_compose selCSPartnerInActB42 rSlot0 g, hMComp, hSlotRegComp s]
/-- `P_slot0 partnerLensOnCoreSum42PG7` is the exact embedding of `P_slot0 partnerLensOnCoreSum42`
along `selCSPartnerInActB42`. -/
theorem P_slot0_partnerLensOnCoreSum42PG7_eq_embed : P_slot0 partnerLensOnCoreSum42PG7 =
    selCSPartnerInActB42.embedMatrix (P_slot0 partnerLensOnCoreSum42) := by
  have hMComp : selCSPartnerInActB42.compose (selMeasInAct (posCoreWires + 42)) =
      selMeasInAct ((posCoreWires + 42) + 7) := by
    apply qreg_ext; intro j; rw [QRegister.compose_apply]
    have hj : selMeasInAct (posCoreWires + 42) j = Fin.natAdd (posCoreWires + 42) j :=
      selMeasInAct_apply (kData := posCoreWires + 42) j
    rw [hj]; dsimp only [selCSPartnerInActB42]; rw [QRegister.concat_apply_right]
  have hPm : selCSPartnerInActB42.embedMatrix ((selMeasInAct (posCoreWires +
    42)).basisOutcomeProjector 0) =
      (selMeasInAct ((posCoreWires + 42) + 7)).basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hMComp,
        ← QRegister.basisOutcomeProjector]
  dsimp only [P_slot0]
  rw [uLensSwap_partnerLensOnCoreSum42PG7_eq_embed, ← hPm,
      QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
/-- Commutation with `P_slot0 partnerLensOnCoreSum42` lifts automatically along
  `selCSPartnerInActB42`
to commutation with `P_slot0 partnerLensOnCoreSum42PG7`. -/
theorem comm_P_slot0_embedCSPartner (uCore42 : Unitary (2 ^ ((posCoreWires + 42) + 18)))
    (hComm0 : uCore42.1 * P_slot0 partnerLensOnCoreSum42 = P_slot0 partnerLensOnCoreSum42 *
    uCore42.1) : (selCSPartnerInActB42.embedUnitary uCore42).1 * P_slot0
    partnerLensOnCoreSum42PG7 = P_slot0 partnerLensOnCoreSum42PG7 *
    (selCSPartnerInActB42.embedUnitary uCore42).1 := by
  rw [QRegister.embedUnitary_val, P_slot0_partnerLensOnCoreSum42PG7_eq_embed,
      ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul, hComm0]
/-- `restrictOfCommSlot0` commutes with embedding along `selCSPartnerInActB42` /
  `selCoreSum42InCoreSum42PG7`. -/
theorem restrictOfCommSlot0_embedCSPartner_eq
    (uCore42 : Unitary (2 ^ ((posCoreWires + 42) + 18))) (hComm0 : uCore42.1 * P_slot0
    partnerLensOnCoreSum42 = P_slot0 partnerLensOnCoreSum42 * uCore42.1) (hComm7 :
    (selCSPartnerInActB42.embedUnitary uCore42).1 * P_slot0 partnerLensOnCoreSum42PG7 =
    P_slot0 partnerLensOnCoreSum42PG7 * (selCSPartnerInActB42.embedUnitary uCore42).1) :
    restrictOfCommSlot0 partnerLensOnCoreSum42PG7 (selCSPartnerInActB42.embedUnitary uCore42)
    hComm7 = selCoreSum42InCoreSum42PG7.embedUnitary
    (restrictOfCommSlot0 partnerLensOnCoreSum42 uCore42 hComm0) := by
  apply restrictOfCommSlot0_eq_of_intertwine
  have hInt0 := uMid_intertwines_uLensSwap_of_comm_P_slot0 partnerLensOnCoreSum42 uCore42 hComm0
  have hLift := congrArg selCSPartnerInActB42.embedMatrix hInt0
  simp only [QRegister.embedMatrix_mul] at hLift
  have hMComp : selCSPartnerInActB42.compose (selMeasInAct (posCoreWires + 42)) =
      selMeasInAct ((posCoreWires + 42) + 7) := by
    apply qreg_ext; intro j; rw [QRegister.compose_apply]
    have hj : selMeasInAct (posCoreWires + 42) j = Fin.natAdd (posCoreWires + 42) j :=
      selMeasInAct_apply (kData := posCoreWires + 42) j
    rw [hj]; dsimp only [selCSPartnerInActB42]; rw [QRegister.concat_apply_right]
  have hDComp : selCSPartnerInActB42.compose (selDataInAct (posCoreWires + 42)) =
      (selDataInAct ((posCoreWires + 42) + 7)).compose selCoreSum42InCoreSum42PG7 := by
    apply qreg_ext; intro q; rw [QRegister.compose_apply]
    have hq : selDataInAct (posCoreWires + 42) q = Fin.castAdd 18 q := selDataInAct_apply q
    rw [hq]; dsimp only [selCSPartnerInActB42]; rw [QRegister.concat_apply_left]
  have hPm : selCSPartnerInActB42.embedMatrix ((selMeasInAct (posCoreWires +
    42)).basisOutcomeProjector 0) =
      (selMeasInAct ((posCoreWires + 42) + 7)).basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hMComp,
        ← QRegister.basisOutcomeProjector]
  rw [← QRegister.embedUnitary_val selCSPartnerInActB42 (uCore42 *
    uLensSwap partnerLensOnCoreSum42),
      QRegister.embedUnitary_mul, ← uLensSwap_partnerLensOnCoreSum42PG7_eq_embed,
      ← QRegister.embedUnitary_val selCSPartnerInActB42 (uLensSwap partnerLensOnCoreSum42),
      ← uLensSwap_partnerLensOnCoreSum42PG7_eq_embed,
      QRegister.embedUnitary_val (selDataInAct (posCoreWires + 42)),
      ← QRegister.embedMatrix_compose, hDComp, QRegister.embedMatrix_compose, hPm] at hLift
  simpa only [QRegister.embedUnitary_val] using hLift
/-- **General `C7` (`catState7`) Agreement Theorem on `((posCoreWires + 42) + 7)`
(`restrictOfCommSlot0_mul_embedPG7_eq_of_eq_on_C7`)**:
Whenever `uInner` and `uInnerEff` on `((posCoreWires + 42) + 7) + 18` agree when multiplied on the
right
by `rPG7InActB42.embedMatrix C7`,
their `restrictOfCommSlot0 partnerLensOnCoreSum42PG7` restrictions agree identically when multiplied
on
the right by `selPG7InCoreSum42PG7.embedMatrix C7`! -/
theorem restrictOfCommSlot0_mul_embedPG7_eq_of_eq_on_C7
    (uInner uInnerEff : Unitary (2 ^ (((posCoreWires + 42) + 7) + 18))) (hComm : uInner.1 *
    P_slot0 partnerLensOnCoreSum42PG7 = P_slot0 partnerLensOnCoreSum42PG7 * uInner.1)
    (hCommEff : uInnerEff.1 * P_slot0 partnerLensOnCoreSum42PG7 = P_slot0
    partnerLensOnCoreSum42PG7 * uInnerEff.1) (C7 : Operator (2 ^ 7)) (hEqC7 : uInner.1 *
    rPG7InActB42.embedMatrix C7 = uInnerEff.1 * rPG7InActB42.embedMatrix C7) :
    (restrictOfCommSlot0 partnerLensOnCoreSum42PG7 uInner hComm).1 *
    selPG7InCoreSum42PG7.embedMatrix C7 =
    (restrictOfCommSlot0 partnerLensOnCoreSum42PG7 uInnerEff hCommEff).1 *
    selPG7InCoreSum42PG7.embedMatrix C7 := by
  let kData := (posCoreWires + 42) + 7
  let L7 := partnerLensOnCoreSum42PG7
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let Pm := selM.basisOutcomeProjector 0
  let S := uLensSwap L7
  let V := restrictOfCommSlot0 L7 uInner hComm
  let VEff := restrictOfCommSlot0 L7 uInnerEff hCommEff
  have hPGAct : selD.embedMatrix (selPG7InCoreSum42PG7.embedMatrix C7) =
    rPG7InActB42.embedMatrix C7 :=
    (QRegister.embedMatrix_compose selD selPG7InCoreSum42PG7 C7).symm
  have hCommPG_Pm : rPG7InActB42.embedMatrix C7 * Pm = Pm * rPG7InActB42.embedMatrix C7 :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      rPG7InActB42 selM ((selDataInAct_disj_selMeasInAct kData).compose_left selPG7InCoreSum42PG7)
        C7 0
  have hCommS_PG : S.1 * rPG7InActB42.embedMatrix C7 = rPG7InActB42.embedMatrix C7 * S.1 := by
    dsimp only [S, L7]
    rw [uLensSwap_partnerLensOnCoreSum42PG7_eq_embed, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint
      selCSPartnerInActB42 rPG7InActB42 selCSPartnerInActB42_disj_rPG7InActB42 _ C7
  have hInt := uMid_intertwines_uLensSwap_of_comm_P_slot0 L7 uInner hComm
  have hIntEff := uMid_intertwines_uLensSwap_of_comm_P_slot0 L7 uInnerEff hCommEff
  have hSwapEq : S.1 * (selD.embedMatrix (V.1 * selPG7InCoreSum42PG7.embedMatrix C7) * Pm) =
      S.1 * (selD.embedMatrix (VEff.1 * selPG7InCoreSum42PG7.embedMatrix C7) * Pm) := by
    rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, hPGAct,
        ← QRegister.embedUnitary_val selD V, ← QRegister.embedUnitary_val selD VEff]
    calc S.1 * ((selD.embedUnitary V).1 * rPG7InActB42.embedMatrix C7 * Pm)
        = S.1 * (selD.embedUnitary V).1 * (rPG7InActB42.embedMatrix C7 * Pm) := by
            simp only [Matrix.mul_assoc]
      _ = (S.1 * (selD.embedUnitary V).1 * Pm) * rPG7InActB42.embedMatrix C7 := by
            rw [hCommPG_Pm]; simp only [Matrix.mul_assoc]
      _ = ((uInner * S).1 * Pm) * rPG7InActB42.embedMatrix C7 := by
            rw [← hInt]
      _ = uInner.1 * S.1 * (Pm * rPG7InActB42.embedMatrix C7) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = uInner.1 * (S.1 * rPG7InActB42.embedMatrix C7) * Pm := by
            rw [← hCommPG_Pm]; simp only [Matrix.mul_assoc]
      _ = (uInner.1 * rPG7InActB42.embedMatrix C7) * S.1 * Pm := by
            rw [hCommS_PG]; simp only [Matrix.mul_assoc]
      _ = (uInnerEff.1 * rPG7InActB42.embedMatrix C7) * S.1 * Pm := by
            rw [hEqC7]
      _ = uInnerEff.1 * (rPG7InActB42.embedMatrix C7 * S.1) * Pm := by
            simp only [Matrix.mul_assoc]
      _ = uInnerEff.1 * S.1 * (rPG7InActB42.embedMatrix C7 * Pm) := by
            rw [← hCommS_PG]; simp only [Matrix.mul_assoc]
      _ = ((uInnerEff * S).1 * Pm) * rPG7InActB42.embedMatrix C7 := by
            rw [hCommPG_Pm]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (S.1 * (selD.embedUnitary VEff).1 * Pm) * rPG7InActB42.embedMatrix C7 := by
            rw [hIntEff]
      _ = S.1 * (selD.embedUnitary VEff).1 * (Pm * rPG7InActB42.embedMatrix C7) := by
            simp only [Matrix.mul_assoc]
      _ = S.1 * ((selD.embedUnitary VEff).1 * rPG7InActB42.embedMatrix C7 * Pm) := by
            rw [← hCommPG_Pm]; simp only [Matrix.mul_assoc]
  apply embedMatrix_selDataInAct_inj_on_Pm
  have hMul := congrArg (fun M ↦ S.1 * M) hSwapEq
  dsimp only [S] at hMul
  have hL : (uLensSwap L7).1 *
    ((uLensSwap L7).1 * (selD.embedMatrix (V.1 * selPG7InCoreSum42PG7.embedMatrix C7) * Pm)) =
      selD.embedMatrix (V.1 * selPG7InCoreSum42PG7.embedMatrix C7) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L7, Matrix.one_mul]
  have hR : (uLensSwap L7).1 *
    ((uLensSwap L7).1 * (selD.embedMatrix (VEff.1 * selPG7InCoreSum42PG7.embedMatrix C7) * Pm)) =
      selD.embedMatrix (VEff.1 * selPG7InCoreSum42PG7.embedMatrix C7) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L7, Matrix.one_mul]
  exact hL.symm.trans (hMul.trans hR)
/-- **Master `catState7` (`C7`) Dimension-Reduction Theorem
(`restrictOfCommSlot0_partnerLens_mul_embedPG7_eq_zeroHyp`)**:
Reduces `restrictOfCommSlot0 partnerLensOnCoreSum42PG7 uInner` on `(posCoreWires + 42) + 7` (`4,083`
wires)
directly to `selCoreSum42InCoreSum42PG7.embedUnitary (restrictOfCommSlot0 partnerLensOnCoreSum42
uCore42)`
on `posCoreWires + 42` (`4,076` wires) whenever `uInner` reduces to
`selCSPartnerInActB42.embedUnitary uCore42`
on `C7 : Operator (2 ^ 7)` (such as `catState7 := (U_cat_B_normalized 7).1 * P_Cat0`)! -/
theorem restrictOfCommSlot0_partnerLens_mul_embedPG7_eq_zeroHyp
    (uInner : Unitary (2 ^ (((posCoreWires + 42) + 7) + 18)))
    (uCore42 : Unitary (2 ^ ((posCoreWires + 42) + 18))) (hComm : uInner.1 * P_slot0
    partnerLensOnCoreSum42PG7 = P_slot0 partnerLensOnCoreSum42PG7 * uInner.1) (hComm0 :
    uCore42.1 * P_slot0 partnerLensOnCoreSum42 = P_slot0 partnerLensOnCoreSum42 * uCore42.1)
    (C7 : Operator (2 ^ 7)) (hEqC7 : uInner.1 * rPG7InActB42.embedMatrix C7 =
    (selCSPartnerInActB42.embedUnitary uCore42).1 * rPG7InActB42.embedMatrix C7) :
    (restrictOfCommSlot0 partnerLensOnCoreSum42PG7 uInner hComm).1 *
    selPG7InCoreSum42PG7.embedMatrix C7 = (selCoreSum42InCoreSum42PG7.embedUnitary
    (restrictOfCommSlot0 partnerLensOnCoreSum42 uCore42 hComm0)).1 *
    selPG7InCoreSum42PG7.embedMatrix C7 := by
  have hComm7 := comm_P_slot0_embedCSPartner uCore42 hComm0
  rw [restrictOfCommSlot0_mul_embedPG7_eq_of_eq_on_C7 uInner
        (selCSPartnerInActB42.embedUnitary uCore42) hComm hComm7 C7 hEqC7,
      restrictOfCommSlot0_embedCSPartner_eq uCore42 hComm0 hComm7]
end Part2_RestrictHomomorphismAndCatState7
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAux
open StageBTwoElecQftStream218Inner (posCoreWires_eq_4034)
section BodyAux
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_concat_left)
open PosSlots24BranchConcrete (posCoreWires rElecSlot rPartnerIdx)
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open PosSlots24PartnerMux288 (sandPhase18)
open PosSlots24PartnerMuxZeroT123 (aliasPartner217 aliasPartner217_lt)
open MidKickSub33 (pos24TailMag30MidpointB)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply embedUnitary_inv_symm)
open Leaf4Ext48TopStitch (disj_of_val_ne)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply)
open ElecHadTrueSwapLocalCompClosure (partnerLens216_tbl_eq)
open ZeroHypSlot0CommAndHMidClosure
  (P_slot0 P_slot0_eq_diagonal restrictOfCommSlot0 mul_comm_P_slot0 inv_comm_P_slot0
  diagSignUnitary_embed_comm_P_slot0)
section Part3A_Core42InnerAndCatState7
open StageBTwoElecQftStream218Inner
  (rCoreInActB42 rElec0InActB42 rPartner18InActB42 rCoreInActB42_apply rElec0InActB42_apply
  rPartner18InActB42_apply)
open LocalStageBTwoElecQftStream218Inner
  (uElec18Sum42Add uStageBTwoElecStreamInner uStageBTwoElecStreamInnerEff
  uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp
  uStageBTwoElecStreamInner_mul_catState7_eq_zeroHyp rSum42InActB42 rSum42InActB42_apply
  rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  rCoreInActB42_disj_rPartner18InActB42)
open PartnerAndAnchorSlot18LensAndMidBA (rElecSlot_ofFin_val)
open ElecHadTrueSwapLocalCompClosure (rPartnerIdx_ofFin_val partnerTblVal216_eq_extract)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open StageAPosHeadConjugatedCircuit (uCoreHadamard18)
open QRegExt
open CatalystPrep (U_cat_B_normalized)
/-- Core `posCoreWires` (`4,034`) inside `(posCoreWires + 42) + 18`. -/
def rCoreInCS42P : QRegister posCoreWires ((posCoreWires + 42) + 18) :=
  (selDataInAct (posCoreWires + 42)).compose selCoreInCoreSum42
/-- Electron `0` (`[0 .. 18)`) inside `(posCoreWires + 42) + 18`. -/
def rElec0InCS42P : QRegister 18 ((posCoreWires + 42) + 18) :=
  rCoreInCS42P.compose (rElecSlot (QRegExt.ofFin posCoreWires) ⟨0, by decide⟩)
/-- `rSum42` (`[4034 .. 4076)`) inside `(posCoreWires + 42) + 18`. -/
def rSum42InCS42P : QRegister 42 ((posCoreWires + 42) + 18) :=
  (selDataInAct (posCoreWires + 42)).compose selSum42InCoreSum42
/-- `rPartner18` (`[4076 .. 4094)`) inside `(posCoreWires + 42) + 18`. -/
def rPartner18InCS42P : QRegister 18 ((posCoreWires + 42) + 18) :=
  selMeasInAct (posCoreWires + 42)
theorem rCoreInCS42P_apply (i : Fin posCoreWires) : (rCoreInCS42P i).val = i.val := by
  simp [rCoreInCS42P, selCoreInCoreSum42, selDataInAct_apply]
theorem rElec0InCS42P_apply (q : Fin 18) : (rElec0InCS42P q).val = q.val := by
  rw [rElec0InCS42P, QRegister.compose_apply, rCoreInCS42P_apply, rElecSlot_ofFin_val]; simp
theorem rSum42InCS42P_apply (s : Fin 42) : (rSum42InCS42P s).val = posCoreWires + s.val := by
  simp [rSum42InCS42P, selSum42InCoreSum42, selDataInAct_apply]
theorem rPartner18InCS42P_apply (q : Fin 18) :
    (rPartner18InCS42P q).val = (posCoreWires + 42) + q.val := by
  simp [rPartner18InCS42P, selMeasInAct_apply]
theorem rElec0InCS42P_disj_rSum42InCS42P : rElec0InCS42P.DisjointWires rSum42InCS42P :=
  disj_of_val_ne fun q s ↦ by
    rw [rElec0InCS42P_apply, rSum42InCS42P_apply]
    have := q.isLt; have := posCoreWires_eq_4034; omega
theorem rPartner18InCS42P_disj_rSum42InCS42P : rPartner18InCS42P.DisjointWires rSum42InCS42P :=
  disj_of_val_ne fun q s ↦ by
    rw [rPartner18InCS42P_apply, rSum42InCS42P_apply]
    have := s.isLt; omega
theorem rCoreInCS42P_disj_rPartner18InCS42P : rCoreInCS42P.DisjointWires rPartner18InCS42P :=
  disj_of_val_ne fun i q ↦ by
    rw [rCoreInCS42P_apply, rPartner18InCS42P_apply]
    have := i.isLt; omega
/-- Step-7 Electron-0 stream-add unitary on `(posCoreWires + 42) + 18`. -/
noncomputable def uAdd0Core42 : Unitary (2 ^ ((posCoreWires + 42) + 18)) :=
  (rElec0InCS42P.concat rSum42InCS42P rElec0InCS42P_disj_rSum42InCS42P).embedUnitary uElec18Sum42Add
/-- Step-6 Partner-18 stream-add unitary on `(posCoreWires + 42) + 18`. -/
noncomputable def uAddPCore42 : Unitary (2 ^ ((posCoreWires + 42) + 18)) :=
  (rPartner18InCS42P.concat rSum42InCS42P rPartner18InCS42P_disj_rSum42InCS42P).embedUnitary
    uElec18Sum42Add
/-- Step-3/5 2-electron pure-Hadamard QFT unitary on `(posCoreWires + 42) + 18`. -/
noncomputable def uHad2Core42 : Unitary (2 ^ ((posCoreWires + 42) + 18)) :=
  rElec0InCS42P.embedUnitary uCoreHadamard18 * rPartner18InCS42P.embedUnitary uCoreHadamard18
/-- Step-4 orbit-table Coulomb diagonal unitary on `(posCoreWires + 42) + 18`. -/
noncomputable def uSandCore42 (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    Unitary (2 ^ ((posCoreWires + 42) + 18)) := (rCoreInCS42P.concat rPartner18InCS42P
    rCoreInCS42P_disj_rPartner18InCS42P).embedUnitary (diagSignUnitary (sandPhase18
    slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B
    hB1 (by omega)))))
/-- Uncatalyzed 7-step Stage-B inner unitary directly on `(posCoreWires + 42) + 18` (`4,094`
  wires). -/
noncomputable def uStageBTwoElecStreamInnerCore42 (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : Unitary (2 ^ ((posCoreWires + 42) + 18)) := uAdd0Core42 *
    (uAddPCore42 * (uHad2Core42⁻¹ * (uSandCore42 B hB1 hB27 slot2SwappedTo0 * (uHad2Core42 *
    (uAddPCore42⁻¹ * uAdd0Core42⁻¹)))))
theorem selCSPartner_apply_left (i : Fin (posCoreWires + 42)) :
    (selCSPartnerInActB42 (Fin.castAdd 18 i)).val = i.val := by
  simp [selCSPartnerInActB42, QRegister.concat_apply_left, selDataInAct_apply,
    selCoreSum42InCoreSum42PG7]
theorem selCSPartner_apply_right (q : Fin 18) :
    (selCSPartnerInActB42 (Fin.natAdd (posCoreWires + 42) q)).val =
      ((posCoreWires + 42) + 7) + q.val := by
  simp [selCSPartnerInActB42, QRegister.concat_apply_right, selMeasInAct_apply]
theorem selCSPartner_compose_rCore :
    selCSPartnerInActB42.compose rCoreInCS42P = rCoreInActB42 := by
  apply qreg_ext; intro i; ext
  have h : rCoreInCS42P i = Fin.castAdd 18 ⟨i.val, by omega⟩ := by
    ext; exact rCoreInCS42P_apply i
  rw [QRegister.compose_apply, h, selCSPartner_apply_left, rCoreInActB42_apply]
theorem selCSPartner_compose_rElec0 :
    selCSPartnerInActB42.compose rElec0InCS42P = rElec0InActB42 := by
  apply qreg_ext; intro q; ext
  have h : rElec0InCS42P q = Fin.castAdd 18 ⟨q.val, by
    have := q.isLt; have :=
    posCoreWires_eq_4034; omega⟩ := by
    ext; exact rElec0InCS42P_apply q
  rw [QRegister.compose_apply, h, selCSPartner_apply_left, rElec0InActB42_apply]
theorem selCSPartner_compose_rSum42 :
    selCSPartnerInActB42.compose rSum42InCS42P = rSum42InActB42 := by
  apply qreg_ext; intro s; ext
  have h : rSum42InCS42P s = Fin.castAdd 18 ⟨posCoreWires + s.val, by omega⟩ := by
    ext; exact rSum42InCS42P_apply s
  rw [QRegister.compose_apply, h, selCSPartner_apply_left, rSum42InActB42_apply]
theorem selCSPartner_compose_rPartner18 :
    selCSPartnerInActB42.compose rPartner18InCS42P = rPartner18InActB42 := by
  apply qreg_ext; intro q; ext
  have h : rPartner18InCS42P q = Fin.natAdd (posCoreWires + 42) q := by
    ext; exact rPartner18InCS42P_apply q
  rw [QRegister.compose_apply, h, selCSPartner_apply_right, rPartner18InActB42_apply]
/-- Embedding `uStageBTwoElecStreamInnerCore42` along `selCSPartnerInActB42` equals
`uStageBTwoElecStreamInnerEff` identically! -/
theorem selCSPartner_embedUnitary_uStageBTwoElecStreamInnerCore42_eq (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) : selCSPartnerInActB42.embedUnitary
    (uStageBTwoElecStreamInnerCore42 B hB1 hB27 slot2SwappedTo0) =
    uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0 := by
  have hConcatEq : ∀ {m₁ m₂ : ℕ} (r₁ : QRegister m₁ ((posCoreWires + 42) + 18))
      (r₂ : QRegister m₂ ((posCoreWires + 42) + 18)) (h₁₂ : r₁.DisjointWires r₂)
      (r₁' : QRegister m₁ (((posCoreWires + 42) + 7) + 18))
      (r₂' : QRegister m₂ (((posCoreWires + 42) + 7) + 18)) (h₁₂' : r₁'.DisjointWires r₂')
      (he₁ : selCSPartnerInActB42.compose r₁ = r₁')
      (he₂ : selCSPartnerInActB42.compose r₂ = r₂'), selCSPartnerInActB42.compose
      (r₁.concat r₂ h₁₂) = r₁'.concat r₂' h₁₂' := by
    intro m₁ m₂ r₁ r₂ h₁₂ r₁' r₂' h₁₂' he₁ he₂
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
        ← he₁]; rfl
    · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
        ← he₂]; rfl
  have hE0Sum := hConcatEq rElec0InCS42P rSum42InCS42P rElec0InCS42P_disj_rSum42InCS42P
    rElec0InActB42 rSum42InActB42 rElec0InActB42_disj_rSum42InActB42
    selCSPartner_compose_rElec0 selCSPartner_compose_rSum42
  have hPSum := hConcatEq rPartner18InCS42P rSum42InCS42P rPartner18InCS42P_disj_rSum42InCS42P
    rPartner18InActB42 rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
    selCSPartner_compose_rPartner18 selCSPartner_compose_rSum42
  have hCoreP := hConcatEq rCoreInCS42P rPartner18InCS42P rCoreInCS42P_disj_rPartner18InCS42P
    rCoreInActB42 rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
    selCSPartner_compose_rCore selCSPartner_compose_rPartner18
  unfold uStageBTwoElecStreamInnerCore42 uStageBTwoElecStreamInnerEff
    uAdd0Core42 uAddPCore42 uHad2Core42 uSandCore42
  simp only [QRegister.embedUnitary_mul, ← embedUnitary_inv_symm,
    ← QRegister.embedUnitary_compose, hE0Sum, hPSum, hCoreP,
    selCSPartner_compose_rElec0, selCSPartner_compose_rPartner18]
/-- Non-slot-0 core subregister (`posCoreWires - 18` wires `[18 .. posCoreWires)`) inside
  `(posCoreWires + 42) + 18`. -/
def rCoreSkip0InCS42P : QRegister (posCoreWires - 18) ((posCoreWires + 42) + 18) :=
  rCoreInCS42P.compose
    (QRegister.block 18 (posCoreWires - 18) (by have := posCoreWires_eq_4034; omega))
theorem rCoreSkip0InCS42P_apply (j : Fin (posCoreWires - 18)) :
    (rCoreSkip0InCS42P j).val = 18 + j.val := by
  rw [rCoreSkip0InCS42P, QRegister.compose_apply, rCoreInCS42P_apply]
  simp
theorem basisBits_rCoreInCS42P_of_ge_18
    (x : Fin (2 ^ ((posCoreWires + 42) + 18)))
    (k : Fin posCoreWires) (hk : 18 ≤ k.val) :
    basisBits posCoreWires (rCoreInCS42P.extractIndex x) k =
      basisBits (posCoreWires - 18) (rCoreSkip0InCS42P.extractIndex x)
        ⟨k.val - 18, by have := k.isLt; omega⟩ := by
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  apply congrArg (basisBits _ _)
  ext
  rw [rCoreInCS42P_apply, rCoreSkip0InCS42P_apply]; dsimp; omega
theorem partnerTblCore42_eq_of_rCoreSkip0_extractIndex_eq
    {x y : Fin (2 ^ ((posCoreWires + 42) + 18))}
    (hSkip : rCoreSkip0InCS42P.extractIndex x = rCoreSkip0InCS42P.extractIndex y) :
    partnerLensOnCoreSum42.tbl ((selDataInAct (posCoreWires + 42)).extractIndex x) =
      partnerLensOnCoreSum42.tbl ((selDataInAct (posCoreWires + 42)).extractIndex y) := by
  have hCoreEx : ∀ z : Fin (2 ^ ((posCoreWires + 42) + 18)), selCoreInCoreSum42.extractIndex
      ((selDataInAct (posCoreWires + 42)).extractIndex z) = rCoreInCS42P.extractIndex z :=
    fun z ↦
      (QRegister.extractIndex_compose (selDataInAct (posCoreWires + 42)) selCoreInCoreSum42 z).symm
  rw [partnerLens216_tbl_eq, partnerLens216_tbl_eq, hCoreEx x, hCoreEx y,
      partnerTblVal216_eq_extract, partnerTblVal216_eq_extract]
  have hHighBits : ∀ (k : Fin posCoreWires), 18 ≤ k.val →
      basisBits posCoreWires (rCoreInCS42P.extractIndex x) k =
        basisBits posCoreWires (rCoreInCS42P.extractIndex y) k := fun k hk ↦ by
    rw [basisBits_rCoreInCS42P_of_ge_18 x k hk, basisBits_rCoreInCS42P_of_ge_18 y k hk, hSkip]
  have hPartEq : regVal (rPartnerIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires (rCoreInCS42P.extractIndex x)) = regVal
      (rPartnerIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires (rCoreInCS42P.extractIndex y)) := by
    unfold regVal _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    have hd18 : 18 ≤ (rPartnerIdx (QRegExt.ofFin posCoreWires) d).val := by
      rw [rPartnerIdx_ofFin_val]; omega
    dsimp only; rw [hHighBits _ hd18]
  have hLt : ∀ z : Fin (2 ^ posCoreWires), aliasPartner217 (regVal (rPartnerIdx
      (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires z)) + 1 < 218 :=
    fun z ↦ by
      have hv : regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires z) <
        256 := by
        simpa using regVal_lt_two_pow (rPartnerIdx (QRegExt.ofFin posCoreWires))
          (basisBits posCoreWires z)
      have := aliasPartner217_lt hv; omega
  apply (basisBitsEquiv 18).injective
  funext q
  change basisBits 18 _ q = basisBits 18 _ q
  rw [QRegister.basisBits_extractIndex (rElecSlot _ _),
      QRegister.basisBits_extractIndex (rElecSlot _ _)]
  have hSlotEq : (⟨aliasPartner217 (regVal (rPartnerIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires (rCoreInCS42P.extractIndex x))) + 1, hLt
      (rCoreInCS42P.extractIndex x)⟩ : Fin 218) = ⟨aliasPartner217 (regVal (rPartnerIdx
      (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires (rCoreInCS42P.extractIndex y)))
      + 1, hLt (rCoreInCS42P.extractIndex y)⟩ := by
    ext; dsimp only; rw [hPartEq]
  rw [hSlotEq]
  refine hHighBits _ ?_
  rw [rElecSlot_ofFin_val]; dsimp only; omega
noncomputable def dPartnerSkip0Core42 (s : Fin (2 ^ (posCoreWires - 18))) : ℂ := if
    partnerLensOnCoreSum42.tbl ((selDataInAct (posCoreWires + 42)).extractIndex
    (rCoreSkip0InCS42P.replaceIndex ⟨0, Nat.two_pow_pos _⟩ s)) = 0 then 1 else 0
theorem P_slot0_partnerLensOnCoreSum42_eq_embedMatrix_diagonal :
    P_slot0 partnerLensOnCoreSum42 =
      rCoreSkip0InCS42P.embedMatrix (Matrix.diagonal dPartnerSkip0Core42) := by
  rw [P_slot0_eq_diagonal, embedMatrix_diagonal_eq rCoreSkip0InCS42P dPartnerSkip0Core42]
  apply congrArg Matrix.diagonal; funext xy
  dsimp only [dPartnerSkip0Core42]
  have hTbl := partnerTblCore42_eq_of_rCoreSkip0_extractIndex_eq (x := xy)
    (y := rCoreSkip0InCS42P.replaceIndex ⟨0, Nat.two_pow_pos _⟩ (rCoreSkip0InCS42P.extractIndex xy))
    (QRegister.extractIndex_replaceIndex rCoreSkip0InCS42P ⟨0,
      Nat.two_pow_pos _⟩ (rCoreSkip0InCS42P.extractIndex xy)).symm
  rw [hTbl]
theorem rElec0InCS42P_disj_rCoreSkip0 : rElec0InCS42P.DisjointWires rCoreSkip0InCS42P :=
  disj_of_val_ne fun q j ↦ by
    rw [rElec0InCS42P_apply, rCoreSkip0InCS42P_apply]; have := q.isLt; omega
theorem rSum42InCS42P_disj_rCoreSkip0 : rSum42InCS42P.DisjointWires rCoreSkip0InCS42P :=
  disj_of_val_ne fun s j ↦ by
    rw [rSum42InCS42P_apply, rCoreSkip0InCS42P_apply]
    have := j.isLt; have := posCoreWires_eq_4034; omega
theorem rPartner18InCS42P_disj_rCoreSkip0 : rPartner18InCS42P.DisjointWires rCoreSkip0InCS42P :=
  disj_of_val_ne fun q j ↦ by
    rw [rPartner18InCS42P_apply, rCoreSkip0InCS42P_apply]
    have := j.isLt; have := posCoreWires_eq_4034; omega
theorem uAdd0Core42_comm_P_slot0 : uAdd0Core42.1 * P_slot0 partnerLensOnCoreSum42 = P_slot0
    partnerLensOnCoreSum42 * uAdd0Core42.1 := by
  rw [uAdd0Core42, QRegister.embedUnitary_val,
    P_slot0_partnerLensOnCoreSum42_eq_embedMatrix_diagonal]
  exact QRegister.embedMatrix_comm_of_disjoint _ _
    (disjointWires_concat_left _ rElec0InCS42P_disj_rCoreSkip0 rSum42InCS42P_disj_rCoreSkip0) _ _
theorem uAddPCore42_comm_P_slot0 : uAddPCore42.1 * P_slot0 partnerLensOnCoreSum42 = P_slot0
    partnerLensOnCoreSum42 * uAddPCore42.1 := by
  rw [uAddPCore42, QRegister.embedUnitary_val,
    P_slot0_partnerLensOnCoreSum42_eq_embedMatrix_diagonal]
  exact QRegister.embedMatrix_comm_of_disjoint _ _
    (disjointWires_concat_left _ rPartner18InCS42P_disj_rCoreSkip0 rSum42InCS42P_disj_rCoreSkip0) _
      _
theorem uHad2Core42_comm_P_slot0 : uHad2Core42.1 * P_slot0 partnerLensOnCoreSum42 = P_slot0
    partnerLensOnCoreSum42 * uHad2Core42.1 := by
  unfold uHad2Core42
  refine mul_comm_P_slot0 partnerLensOnCoreSum42 ?_ ?_
  · rw [QRegister.embedUnitary_val, P_slot0_partnerLensOnCoreSum42_eq_embedMatrix_diagonal]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ rElec0InCS42P_disj_rCoreSkip0 _ _
  · rw [QRegister.embedUnitary_val, P_slot0_partnerLensOnCoreSum42_eq_embedMatrix_diagonal]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ rPartner18InCS42P_disj_rCoreSkip0 _ _
theorem uSandCore42_comm_P_slot0 (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uSandCore42 B hB1 hB27 slot2SwappedTo0).1 * P_slot0 partnerLensOnCoreSum42 =
      P_slot0 partnerLensOnCoreSum42 * (uSandCore42 B hB1 hB27 slot2SwappedTo0).1 :=
  diagSignUnitary_embed_comm_P_slot0 partnerLensOnCoreSum42 _ _
theorem uStageBTwoElecStreamInnerCore42_comm_P_slot0
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uStageBTwoElecStreamInnerCore42 B hB1 hB27 slot2SwappedTo0).1 *
      P_slot0 partnerLensOnCoreSum42 =
      P_slot0 partnerLensOnCoreSum42 *
        (uStageBTwoElecStreamInnerCore42 B hB1 hB27 slot2SwappedTo0).1 := by
  unfold uStageBTwoElecStreamInnerCore42
  exact mul_comm_P_slot0 _ uAdd0Core42_comm_P_slot0 (mul_comm_P_slot0 _
    uAddPCore42_comm_P_slot0 (mul_comm_P_slot0 _ (inv_comm_P_slot0 _ uHad2Core42_comm_P_slot0)
    (mul_comm_P_slot0 _ (uSandCore42_comm_P_slot0 B hB1 hB27 slot2SwappedTo0)
    (mul_comm_P_slot0 _ uHad2Core42_comm_P_slot0 (mul_comm_P_slot0 _ (inv_comm_P_slot0 _
    uAddPCore42_comm_P_slot0) (inv_comm_P_slot0 _ uAdd0Core42_comm_P_slot0))))))
/-- **7-Factor `restrictOfCommSlot0` Homomorphism Decomposition of
`uStageBTwoElecStreamInnerCore42`**:
Decomposes `restrictOfCommSlot0 partnerLensOnCoreSum42 (uStageBTwoElecStreamInnerCore42 ...)` into
`R(uAdd0) * (R(uAddP) * ((R(uHad2))⁻¹ * (R(uSand) * (R(uHad2) * ((R(uAddP))⁻¹ * (R(uAdd0))⁻¹)))))`!
-/
theorem restrictOfCommSlot0_uStageBTwoElecStreamInnerCore42_eq_seven_factors
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    let L := partnerLensOnCoreSum42
    let rAdd0 := restrictOfCommSlot0 L uAdd0Core42 uAdd0Core42_comm_P_slot0
    let rAddP := restrictOfCommSlot0 L uAddPCore42 uAddPCore42_comm_P_slot0
    let rHad2 := restrictOfCommSlot0 L uHad2Core42 uHad2Core42_comm_P_slot0
    let rSand := restrictOfCommSlot0 L (uSandCore42 B hB1 hB27 slot2SwappedTo0)
      (uSandCore42_comm_P_slot0 B hB1 hB27 slot2SwappedTo0)
    restrictOfCommSlot0 L (uStageBTwoElecStreamInnerCore42 B hB1 hB27 slot2SwappedTo0)
      (uStageBTwoElecStreamInnerCore42_comm_P_slot0 B hB1 hB27 slot2SwappedTo0) =
      rAdd0 * (rAddP * (rHad2⁻¹ * (rSand * (rHad2 * (rAddP⁻¹ * rAdd0⁻¹))))) := by
  intro L rAdd0 rAddP rHad2 rSand
  have cHadInv := inv_comm_P_slot0 L uHad2Core42_comm_P_slot0
  have cAddPInv := inv_comm_P_slot0 L uAddPCore42_comm_P_slot0
  have cAdd0Inv := inv_comm_P_slot0 L uAdd0Core42_comm_P_slot0
  have cSand := uSandCore42_comm_P_slot0 B hB1 hB27 slot2SwappedTo0
  have c67 := mul_comm_P_slot0 L cAddPInv cAdd0Inv
  have c567 := mul_comm_P_slot0 L uHad2Core42_comm_P_slot0 c67
  have c4567 := mul_comm_P_slot0 L cSand c567
  have c34567 := mul_comm_P_slot0 L cHadInv c4567
  have c234567 := mul_comm_P_slot0 L uAddPCore42_comm_P_slot0 c34567
  have cFull := mul_comm_P_slot0 L uAdd0Core42_comm_P_slot0 c234567
  change restrictOfCommSlot0 L (uAdd0Core42 * (uAddPCore42 * (uHad2Core42⁻¹ * (uSandCore42 B
    hB1 hB27 slot2SwappedTo0 * (uHad2Core42 * (uAddPCore42⁻¹ * uAdd0Core42⁻¹)))))) cFull =
    restrictOfCommSlot0 L uAdd0Core42 uAdd0Core42_comm_P_slot0 * (restrictOfCommSlot0 L
    uAddPCore42 uAddPCore42_comm_P_slot0 * ((restrictOfCommSlot0 L uHad2Core42
    uHad2Core42_comm_P_slot0)⁻¹ * (restrictOfCommSlot0 L (uSandCore42 B hB1 hB27
    slot2SwappedTo0) cSand * (restrictOfCommSlot0 L uHad2Core42 uHad2Core42_comm_P_slot0 *
    ((restrictOfCommSlot0 L uAddPCore42 uAddPCore42_comm_P_slot0)⁻¹ * (restrictOfCommSlot0 L
    uAdd0Core42 uAdd0Core42_comm_P_slot0)⁻¹)))))
  rw[restrictOfCommSlot0_mul L _ _ uAdd0Core42_comm_P_slot0 c234567,
      restrictOfCommSlot0_mul L _ _ uAddPCore42_comm_P_slot0 c34567,
      restrictOfCommSlot0_mul L _ _ cHadInv c4567, restrictOfCommSlot0_mul L _ _ cSand c567,
      restrictOfCommSlot0_mul L _ _ uHad2Core42_comm_P_slot0 c67,
      restrictOfCommSlot0_mul L _ _ cAddPInv cAdd0Inv,
      restrictOfCommSlot0_inv L uHad2Core42 uHad2Core42_comm_P_slot0 cHadInv,
      restrictOfCommSlot0_inv L uAddPCore42 uAddPCore42_comm_P_slot0 cAddPInv,
      restrictOfCommSlot0_inv L uAdd0Core42 uAdd0Core42_comm_P_slot0 cAdd0Inv]
/-- Canonical 7-qubit phase-gradient catalyst state operator `|cat_7⟩⟨0^7|` (`U_cat_B_normalized
  7 * P_{|0^7⟩}`). -/
noncomputable def catState7 : Operator (2 ^ 7) :=
  (U_cat_B_normalized 7).1 * (QRegExt.idReg 7).basisOutcomeProjector 0
theorem embedMatrix_catState7_eq {N : ℕ} (rPG : QRegister 7 N) : rPG.embedMatrix catState7 =
    (rPG.embedUnitary (U_cat_B_normalized 7)).1 * rPG.basisOutcomeProjector 0 := by
  have hProj : rPG.embedMatrix ((QRegExt.idReg 7).basisOutcomeProjector 0) =
      rPG.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, embedMatrix_diagonal_eq,
        QRegister.basisOutcomeProjector_eq_diagonal]
    congr 1; funext z
    have hid : ∀ y : Fin (2 ^ 7), (QRegExt.idReg 7).extractIndex y = y := fun y ↦ by
      apply eq_of_basisBits_eq_local
      intro i
      exact (QRegExt.idReg _).basisBits_extractIndex _ i
    rw [hid]
  rw [catState7, QRegister.embedMatrix_mul, QRegister.embedUnitary_val, hProj]
/-- **`catState7` Reduction of
`restrictOfCommSlot0 partnerLensOnCoreSum42PG7 (uStageBTwoElecStreamInner ...)`
(`restrictOfCommSlot0_uStageBTwoElecStreamInner_mul_catState7_zeroHyp`)**:
On `selPG7InCoreSum42PG7.embedMatrix catState7`, the catalyzed `4,083`-wire Stage-B partner-swapped
restriction reduces identically to `selCoreSum42InCoreSum42PG7.embedUnitary` of the uncatalyzed
`4,076`-wire `uStageBTwoElecStreamInnerCore42` restriction! -/
theorem restrictOfCommSlot0_uStageBTwoElecStreamInner_mul_catState7_zeroHyp
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    let uInner := uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0
    let hComm := uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp B hB1 hB27 slot2SwappedTo0
    let uCore42 := uStageBTwoElecStreamInnerCore42 B hB1 hB27 slot2SwappedTo0
    let hComm0 := uStageBTwoElecStreamInnerCore42_comm_P_slot0 B hB1 hB27 slot2SwappedTo0
    (restrictOfCommSlot0 partnerLensOnCoreSum42PG7 uInner hComm).1 *
        selPG7InCoreSum42PG7.embedMatrix catState7 =
      (selCoreSum42InCoreSum42PG7.embedUnitary
        (restrictOfCommSlot0 partnerLensOnCoreSum42 uCore42 hComm0)).1 *
        selPG7InCoreSum42PG7.embedMatrix catState7 := by
  intro uInner hComm uCore42 hComm0
  refine restrictOfCommSlot0_partnerLens_mul_embedPG7_eq_zeroHyp uInner uCore42 hComm hComm0
    catState7 ?_
  dsimp only [uInner, uCore42]
  have hrPG : rPG7InActB42 = StageBTwoElecQftStream218Inner.rPG7InActB42 := rfl
  rw [embedMatrix_catState7_eq, hrPG,
      (uStageBTwoElecStreamInner_mul_catState7_eq_zeroHyp B hB1 hB27 slot2SwappedTo0).2,
      ← selCSPartner_embedUnitary_uStageBTwoElecStreamInnerCore42_eq B hB1 hB27 slot2SwappedTo0]
end Part3A_Core42InnerAndCatState7
section Part3B_Stream218Algebra
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open QRegExt
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42)
open LocalStageBTwoElecQftStream218Inner (uElec18Sum42Add)
/-- 42-wire `rSum42` block `[fullSysCoreWires mPayload .. + 42)` inside `fullSysCoreWires
  mPayload + 42`. -/
def rSum42InCoreSum42 (mPayload : ℕ) : QRegister 42 (fullSysCoreWires mPayload + 42) :=
  QRegister.block (fullSysCoreWires mPayload) 42 le_rfl
/-- 18-wire electron `e` (`[18 * e .. 18 * e + 18)`) inside `fullSysCoreWires mPayload`. -/
def rElecSlotInCore (mPayload : ℕ) (e : Fin 218) : QRegister 18 (fullSysCoreWires mPayload) :=
  QRegister.block (18 * e.val) 18 (by
    have := e.isLt
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega)
theorem rCoreInCoreSum42_disj_rSum42 (mPayload : ℕ) :
    (rCoreInCoreSum42 mPayload).DisjointWires (rSum42InCoreSum42 mPayload) :=
  QRegister.block_disjoint_of_le 0 (fullSysCoreWires mPayload) (fullSysCoreWires mPayload) 42
    (by omega) le_rfl (by omega)
/-- 3-axis 18-wire electron `e` addition into `rSum42` on `fullSysCoreWires mPayload + 42`. -/
noncomputable def uElecSlotSum42Add (mPayload : ℕ) (e : Fin 218) : Unitary
    (2 ^ (fullSysCoreWires mPayload + 42)) := (((rCoreInCoreSum42 mPayload).compose
    (rElecSlotInCore mPayload e)).concat (rSum42InCoreSum42 mPayload)
    ((rCoreInCoreSum42_disj_rSum42 mPayload).compose_left _)).embedUnitary uElec18Sum42Add
/-- Global 218-electron momentum-stream addition unitary on `fullSysCoreWires mPayload + 42`. -/
noncomputable def uStream218CoreSum42 (mPayload : ℕ) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 42)) :=
  (List.ofFn fun e : Fin 218 ↦ uElecSlotSum42Add mPayload e).prod
end Part3B_Stream218Algebra
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAux
section BodyAux
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply kFull80 rCoreFull pSum42Zero E_rawStream42)
open Leaf4Ext48TopStitch (rCoreSum42Full disj_of_val_ne)
section Part3B_Stream218Algebra
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes (slot2AxisSum slot2AxisSum_lt)
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42 rSum14InCoreSum42)
open Slot0SubAdd14And217Stream (rSum14Slice42 selCoreSum14In42)
open LocalStageBTwoElecQftStream218Inner
  (rAxis6In18 elec18AxisWire elec18AxisVal elec18AxisVal_eq_sum uElec18AxisAdd14 selElec18Sum14In42
  compose_selElec18Sum14In42 uElec18Sum42Add embedUnitary_catModAddUnitary_congr_sys)
open InterWalkRSum42Hoist (rSum14Full rCSFull hCoreFull_disj_Sum14)
open HoistInitStream1300And164 (IsSlot2StreamUnitary uStreamFullOf)
open HeldStreamEStream42Interface (uStreamFullOf_012_mul_pSum42Zero_eq_E_rawStream42)
theorem unitary_eq_of_mulVec_single {D : ℕ} {U₁ U₂ : Unitary D} (h : ∀ j : Fin D, U₁.1.mulVec
    (Pi.single j 1) = U₂.1.mulVec (Pi.single j 1)) : U₁ = U₂ := by
  apply Subtype.ext; ext i j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun (h j) i
/-- Generic 3-axis `catModAddUnitary` unitary on `fullSysCoreWires mPayload + 42` for a per-axis
  shift `F`. -/
noncomputable def uCoreShiftSum42 (mPayload : ℕ)
    (F : Fin 3 → BitAssignment (fullSysCoreWires mPayload) → ℕ) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 42)) :=
  (selCoreSum14In42 mPayload 0).embedUnitary (catModAddUnitary (fullSysCoreWires mPayload) 14 (F 0))
    *
    ((selCoreSum14In42 mPayload 1).embedUnitary
      (catModAddUnitary (fullSysCoreWires mPayload) 14 (F 1)) *
      (selCoreSum14In42 mPayload 2).embedUnitary
        (catModAddUnitary (fullSysCoreWires mPayload) 14 (F 2)))
theorem catModAdd_concat_mulVec_single {N k B : ℕ}
    (rSys : QRegister k N) (rCat : QRegister B N) (hSC : rSys.DisjointWires rCat)
    (shift : BitAssignment k → ℕ) (idx₀ : Fin (2 ^ N)) :
    let idx₁ := (rSys.concat rCat hSC).replaceIndex idx₀
      (catModAddPerm k B shift ((rSys.concat rCat hSC).extractIndex idx₀))
    ((rSys.concat rCat hSC).embedUnitary (catModAddUnitary k B shift)).1.mulVec (Pi.single idx₀ 1) =
      Pi.single idx₁ 1 ∧
    (∀ w : Fin N, w ∉ Set.range rCat.wires → basisBits N idx₁ w = basisBits N idx₀ w) ∧
    (∀ j : Fin B, basisBits N idx₁ (rCat j) =
      basisBits B ⟨(regVal rCat (basisBits N idx₀) +
        shift (fun i ↦ basisBits N idx₀ (rSys i))) % 2 ^ B,
        Nat.mod_lt _ (Nat.two_pow_pos B)⟩ j) := by
  intro idx₁
  let rSC := rSys.concat rCat hSC
  let β := basisBits N idx₀
  have hmv : (rSC.embedUnitary (catModAddUnitary k B shift)).1.mulVec (Pi.single idx₀ 1) =
      Pi.single idx₁ 1 := by
    rw [QRegister.embedUnitary_val, catModAddUnitary, rSC.embedMatrix_mulVec_single_factors,
        permutationUnitary_mulVec_single, rSC.tensorState_single_replaceIndex]
  have hext_sys : (splitSysCatEquiv k B (rSC.extractIndex idx₀)).1 = fun i ↦ β (rSys i) := by
    funext i
    dsimp only [splitSysCatEquiv, Equiv.trans_apply]
    change basisBits (k + B) (rSC.extractIndex idx₀) (Fin.castAdd B i) = β (rSys i)
    simp [rSC, β]
  have hext_cat_fin : (splitSysCatEquiv k B (rSC.extractIndex idx₀)).2 =
      (basisBitsEquiv B).symm (fun i ↦ β (rCat i)) := by
    change (basisBitsEquiv B).symm
        (fun j ↦ basisBits (k + B) (rSC.extractIndex idx₀) (Fin.natAdd k j)) =
      (basisBitsEquiv B).symm (fun i ↦ β (rCat i))
    congr 1; funext j; simp [rSC, β]
  have hext_cat : (splitSysCatEquiv k B (rSC.extractIndex idx₀)).2.val = regVal rCat β := by
    rw [hext_cat_fin, regVal, bitsVal_eq_symm_val]
  have hcat_eq : catModAddPerm k B shift (rSC.extractIndex idx₀) = (splitSysCatEquiv k B).symm
      (fun i ↦ β (rSys i), ⟨(regVal rCat β + shift (fun i ↦ β (rSys i))) % 2 ^ B, Nat.mod_lt _
      (Nat.two_pow_pos B)⟩) := by
    simp only [catModAddPerm, Equiv.trans_apply]
    congr 1; ext
    · dsimp only [catModAddMidPerm, Equiv.coe_fn_mk]; exact congrFun hext_sys _
    · simp only [catModAddMidPerm, Equiv.coe_fn_mk, hext_sys, hext_cat]
  refine ⟨hmv, fun w hw_not ↦ ?_, fun j ↦ ?_⟩
  · by_cases hwSC : w ∈ Set.range rSC.wires
    · rcases hwSC with ⟨idx, rfl⟩
      by_cases hi : idx.val < k
      · let i0 : Fin k := ⟨idx.val, hi⟩
        have hidx : idx = Fin.castAdd B i0 := by ext; rfl
        rw [hidx]
        change basisBits N (rSC.replaceIndex idx₀ _) (rSC (Fin.castAdd B i0)) =
          basisBits N idx₀ (rSC (Fin.castAdd B i0))
        rw [rSC.basisBits_replaceIndex_apply, hcat_eq]
        simp [rSC, splitSysCatEquiv, β]
      · let q : Fin B := ⟨idx.val - k, by omega⟩
        have hidx : idx = Fin.natAdd k q := by ext; dsimp [q]; omega
        exfalso
        apply hw_not
        refine ⟨q, ?_⟩
        rw [hidx]
        exact (QRegister.concat_apply_right rSys rCat hSC q).symm
    · exact rSC.basisBits_replaceIndex_of_not_mem idx₀ _ w hwSC
  · have hrc : rCat j = rSC (Fin.natAdd k j) := (QRegister.concat_apply_right rSys rCat hSC j).symm
    rw [hrc]; change basisBits N (rSC.replaceIndex idx₀ _) (rSC (Fin.natAdd k j)) = _
    rw [rSC.basisBits_replaceIndex_apply, hcat_eq]
    simp [splitSysCatEquiv, β]
theorem rSum14Slice_eq_rSum14InCoreSum42 (mPayload : ℕ) (w : Fin 3) :
    (rSum42InCoreSum42 mPayload).compose (rSum14Slice42 w) = rSum14InCoreSum42 mPayload w := by
  apply qreg_ext; intro j; ext
  simp [rSum42InCoreSum42, rSum14Slice42, rSum14InCoreSum42]; omega
theorem selCoreSum14In42_eq_concat (mPayload : ℕ) (w : Fin 3) : selCoreSum14In42 mPayload w =
    (rCoreInCoreSum42 mPayload).concat (rSum14InCoreSum42 mPayload w) (by
    rw [← rSum14Slice_eq_rSum14InCoreSum42]
    exact (rCoreInCoreSum42_disj_rSum42 mPayload).compose_right (rSum14Slice42 w)) := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_) idx
  · simp [selCoreSum14In42, rCoreInCoreSum42, QRegister.concat_apply_left]
  · simp [selCoreSum14In42, rSum14Slice42, rSum14InCoreSum42, QRegister.concat_apply_right]; omega
theorem rSum14InCoreSum42_disj_of_ne (mPayload : ℕ) {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) :
    (rSum14InCoreSum42 mPayload w₁).DisjointWires (rSum14InCoreSum42 mPayload w₂) :=
  disj_of_val_ne fun i₁ i₂ ↦ by
    have hne' : w₁.val ≠ w₂.val := Fin.val_ne_of_ne hne
    have := i₁.isLt; have := i₂.isLt; have := w₁.isLt; have := w₂.isLt
    simp [rSum14InCoreSum42]; omega
theorem selCoreSum14_catModAdd_mulVec_single {mPayload : ℕ} (w : Fin 3)
    (g : BitAssignment (fullSysCoreWires mPayload) → ℕ)
    (idx₀ : Fin (2 ^ (fullSysCoreWires mPayload + 42))) : ∃ idx₁ : Fin
    (2 ^ (fullSysCoreWires mPayload + 42)), ((selCoreSum14In42 mPayload w).embedUnitary
    (catModAddUnitary (fullSysCoreWires mPayload) 14 g)).1.mulVec (Pi.single idx₀ 1) =
    Pi.single idx₁ 1 ∧ (∀ q : Fin (fullSysCoreWires mPayload), basisBits _ idx₁
    (rCoreInCoreSum42 mPayload q) = basisBits _ idx₀ (rCoreInCoreSum42 mPayload q)) ∧ (∀ (w' :
    Fin 3), w' ≠ w → ∀ j : Fin 14, basisBits _ idx₁ (rSum14InCoreSum42 mPayload w' j) =
    basisBits _ idx₀ (rSum14InCoreSum42 mPayload w' j)) ∧ (∀ j : Fin 14, basisBits _ idx₁
    (rSum14InCoreSum42 mPayload w j) = basisBits 14 ⟨(regVal (rSum14InCoreSum42 mPayload w)
    (basisBits _ idx₀) + g (fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 mPayload q))) % 2 ^ 14,
    Nat.mod_lt _ (Nat.two_pow_pos 14)⟩ j) := by
  have hDisj : (rCoreInCoreSum42 mPayload).DisjointWires (rSum14InCoreSum42 mPayload w) := by
    rw [← rSum14Slice_eq_rSum14InCoreSum42]
    exact (rCoreInCoreSum42_disj_rSum42 mPayload).compose_right (rSum14Slice42 w)
  obtain ⟨hmv, hout, hin⟩ := catModAdd_concat_mulVec_single
    (rCoreInCoreSum42 mPayload) (rSum14InCoreSum42 mPayload w) hDisj g idx₀
  refine ⟨_, ?_, fun q ↦ hout _ fun ⟨j, hj⟩ ↦ hDisj.ne q j hj.symm, fun w' hne j ↦ hout _ fun
    ⟨j', hj'⟩ ↦ (rSum14InCoreSum42_disj_of_ne mPayload hne).ne j j' hj'.symm, hin⟩
  rw [selCoreSum14In42_eq_concat mPayload w]
  exact hmv
/-- Explicit computational-basis ket action of `uCoreShiftSum42 mPayload F` across all 3 axes. -/
theorem uCoreShiftSum42_mulVec_single {mPayload : ℕ}
    (F : Fin 3 → BitAssignment (fullSysCoreWires mPayload) → ℕ)
    (idx₀ : Fin (2 ^ (fullSysCoreWires mPayload + 42))) : ∃ idx₁ : Fin
    (2 ^ (fullSysCoreWires mPayload + 42)), (uCoreShiftSum42 mPayload F).1.mulVec
    (Pi.single idx₀ 1) = Pi.single idx₁ 1 ∧ (∀ q : Fin (fullSysCoreWires mPayload), basisBits
    _ idx₁ (rCoreInCoreSum42 mPayload q) = basisBits _ idx₀ (rCoreInCoreSum42 mPayload q)) ∧
    (∀ (w : Fin 3) (j : Fin 14), basisBits _ idx₁ (rSum14InCoreSum42 mPayload w j) = basisBits
    14 ⟨(regVal (rSum14InCoreSum42 mPayload w) (basisBits _ idx₀) + F w (fun q ↦ basisBits _
    idx₀ (rCoreInCoreSum42 mPayload q))) % 2 ^ 14, Nat.mod_lt _ (Nat.two_pow_pos 14)⟩ j) := by
  obtain ⟨i₂, h₂, hc₂, ho₂, hi₂⟩ := selCoreSum14_catModAdd_mulVec_single 2 (F 2) idx₀
  obtain ⟨i₁, h₁, hc₁, ho₁, hi₁⟩ := selCoreSum14_catModAdd_mulVec_single 1 (F 1) i₂
  obtain ⟨i₀, h₀, hc₀, ho₀, hi₀⟩ := selCoreSum14_catModAdd_mulVec_single 0 (F 0) i₁
  have hγ₂ : (fun q ↦ basisBits _ i₂ (rCoreInCoreSum42 mPayload q)) =
      (fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 mPayload q)) := funext hc₂
  have hγ₁ : (fun q ↦ basisBits _ i₁ (rCoreInCoreSum42 mPayload q)) =
      (fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 mPayload q)) := funext fun q ↦
        (hc₁ q).trans (hc₂ q)
  refine ⟨i₀, ?_, fun q ↦ (hc₀ q).trans ((hc₁ q).trans (hc₂ q)), fun w j ↦ ?_⟩
  · unfold uCoreShiftSum42
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₂, h₁, h₀]
  · have hw : w = 0 ∨ w = 1 ∨ w = 2 := by fin_cases w <;> decide
    rcases hw with rfl | rfl | rfl
    · rw [hi₀ j, hγ₁]
      have hrv : regVal (rSum14InCoreSum42 mPayload 0) (basisBits _ i₁) =
          regVal (rSum14InCoreSum42 mPayload 0) (basisBits _ idx₀) :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun k ↦
          (ho₁ 0 (by decide) k).trans (ho₂ 0 (by decide) k)
      rw [hrv]
    · rw [ho₀ 1 (by decide) j, hi₁ j, hγ₂]
      have hrv : regVal (rSum14InCoreSum42 mPayload 1) (basisBits _ i₂) =
          regVal (rSum14InCoreSum42 mPayload 1) (basisBits _ idx₀) :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun k ↦
          ho₂ 1 (by decide) k
      rw [hrv]
    · rw [ho₀ 2 (by decide) j, ho₁ 2 (by decide) j, hi₂ j]
theorem eq_of_core_and_sum14_eq {mPayload : ℕ}
    {x y : Fin (2 ^ (fullSysCoreWires mPayload + 42))} (hCore : ∀ q : Fin (fullSysCoreWires
    mPayload), basisBits _ x (rCoreInCoreSum42 mPayload q) = basisBits _ y (rCoreInCoreSum42
    mPayload q)) (hSum : ∀ (w : Fin 3) (j : Fin 14), basisBits _ x (rSum14InCoreSum42 mPayload
    w j) = basisBits _ y (rSum14InCoreSum42 mPayload w j)) : x = y := by
  apply eq_of_basisBits_eq_local; intro u
  by_cases hu : u.val < fullSysCoreWires mPayload
  · have hq : u = rCoreInCoreSum42 mPayload ⟨u.val, hu⟩ := by
      ext; simp [rCoreInCoreSum42]
    rw [hq]; exact hCore _
  · have huLt := u.isLt
    let d := u.val - fullSysCoreWires mPayload
    have hd42 : d < 42 := by omega
    let w : Fin 3 := ⟨d / 14, by omega⟩
    let j : Fin 14 := ⟨d % 14, Nat.mod_lt d (by decide)⟩
    have hwj : u = rSum14InCoreSum42 mPayload w j := by
      ext; simp [rSum14InCoreSum42, w, j, d]; omega
    rw [hwj]; exact hSum w j
theorem regVal_eq_of_basisBits_fin {B : ℕ} {N : ℕ} (r : QRegister B N) (idx : Fin (2 ^ N))
    (v : Fin (2 ^ B)) (h : ∀ j : Fin B, basisBits N idx (r j) = basisBits B v j) : regVal r
    (basisBits N idx) = v.val := by
  have hfn : (fun j ↦ basisBits N idx (r j)) = basisBits B v := funext h
  rw [regVal, hfn, bitsVal_eq_symm_val]
  exact congrArg Fin.val ((basisBitsEquiv B).symm_apply_apply v)
theorem uCoreShiftSum42_zero (mPayload : ℕ) : uCoreShiftSum42 mPayload (fun _ _ ↦ 0) = 1 := by
  refine unitary_eq_of_mulVec_single fun idx₀ ↦ ?_
  obtain ⟨idx₁, hmv, hc, hs⟩ :=
    uCoreShiftSum42_mulVec_single (mPayload := mPayload) (fun _ _ ↦ 0) idx₀
  rw [hmv, OneMemClass.coe_one, Matrix.one_mulVec]
  apply congrArg (fun idx ↦ Pi.single idx (1 : ℂ))
  refine eq_of_core_and_sum14_eq hc fun w j ↦ ?_
  rw [hs w j]
  have hlt : regVal (rSum14InCoreSum42 mPayload w) (basisBits _ idx₀) < 2 ^ 14 :=
    regVal_lt_two_pow _ _
  have hfin : (⟨(regVal (rSum14InCoreSum42 mPayload w) (basisBits _ idx₀) + 0) % 2 ^ 14,
      Nat.mod_lt _ (Nat.two_pow_pos 14)⟩ : Fin (2 ^ 14)) =
      (basisBitsEquiv 14).symm (fun k ↦ basisBits _ idx₀ (rSum14InCoreSum42 mPayload w k)) := by
    ext; simp only [Nat.add_zero, Nat.mod_eq_of_lt hlt]
    rw [regVal]
    exact bitsVal_eq_symm_val _
  rw [hfin]
  exact congrFun ((basisBitsEquiv 14).apply_symm_apply _) j
theorem uCoreShiftSum42_mul (mPayload : ℕ)
    (F₁ F₂ : Fin 3 → BitAssignment (fullSysCoreWires mPayload) → ℕ) :
    uCoreShiftSum42 mPayload F₁ * uCoreShiftSum42 mPayload F₂ =
      uCoreShiftSum42 mPayload (fun w γ ↦ F₁ w γ + F₂ w γ) := by
  refine unitary_eq_of_mulVec_single fun idx₀ ↦ ?_
  obtain ⟨idx₂, hmv₂, hc₂, hs₂⟩ := uCoreShiftSum42_mulVec_single F₂ idx₀
  obtain ⟨idx₁, hmv₁, hc₁, hs₁⟩ := uCoreShiftSum42_mulVec_single F₁ idx₂
  obtain ⟨idx₃, hmv₃, hc₃, hs₃⟩ :=
    uCoreShiftSum42_mulVec_single (fun w γ ↦ F₁ w γ + F₂ w γ) idx₀
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hmv₂, hmv₁, hmv₃]
  apply congrArg (fun idx ↦ Pi.single idx (1 : ℂ))
  have hγ₂ : (fun q ↦ basisBits _ idx₂ (rCoreInCoreSum42 mPayload q)) =
      (fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 mPayload q)) := funext hc₂
  refine eq_of_core_and_sum14_eq (fun q ↦ (hc₁ q).trans ((hc₂ q).trans (hc₃ q).symm)) fun w j ↦ ?_
  rw [hs₁ w j, hs₃ w j, hγ₂]
  have hrv₂ := regVal_eq_of_basisBits_fin (rSum14InCoreSum42 mPayload w) idx₂ _ (hs₂ w)
  rw [hrv₂]
  apply congrArg (fun v ↦ basisBits 14 v j); ext; dsimp only
  rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm (F₂ w _) (F₁ w _)]
theorem uCoreShiftSum42_list_ofFn_prod (mPayload : ℕ) :
    ∀ {L : ℕ} (G : Fin L → Fin 3 → BitAssignment (fullSysCoreWires mPayload) → ℕ),
      (List.ofFn fun i : Fin L ↦ uCoreShiftSum42 mPayload (G i)).prod =
        uCoreShiftSum42 mPayload (fun w γ ↦ ∑ i : Fin L, G i w γ)
  | 0, _ => by simp [uCoreShiftSum42_zero]
  | L + 1, G => by
      rw[List.ofFn_succ, List.prod_cons,
          uCoreShiftSum42_list_ofFn_prod mPayload (fun i ↦ G i.succ), uCoreShiftSum42_mul]
      apply congrArg (uCoreShiftSum42 mPayload); funext w γ
      exact (Fin.sum_univ_succ fun i : Fin (L + 1) ↦ G i w γ).symm
/-- `uElecSlotSum42Add mPayload e` equals `uCoreShiftSum42` with Electron `e`'s 6-bit momentum
  `rElecSlotAxis _ e w`. -/
theorem uElecSlotSum42Add_eq_uCoreShiftSum42 (mPayload : ℕ) (e : Fin 218) : uElecSlotSum42Add
    mPayload e = uCoreShiftSum42 mPayload
    (fun w γ ↦ regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ) := by
  let rC := rCoreInCoreSum42 mPayload
  let rS42 := rSum42InCoreSum42 mPayload
  let rE := rC.compose (rElecSlotInCore mPayload e)
  have hCS42 := rCoreInCoreSum42_disj_rSum42 mPayload
  have hES42 : rE.DisjointWires rS42 := hCS42.compose_left _
  have hAxis : ∀ w : Fin 3,
      ((rE.concat rS42 hES42).compose (selElec18Sum14In42 w)).embedUnitary (uElec18AxisAdd14 w) =
        (selCoreSum14In42 mPayload w).embedUnitary
          (catModAddUnitary (fullSysCoreWires mPayload) 14
            (fun γ ↦ regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ)) := fun w ↦ by
    have hComp2 : selCoreSum14In42 mPayload w =
        rC.concat (rS42.compose (rSum14Slice42 w)) (hCS42.compose_right (rSum14Slice42 w)) := rfl
    rw [compose_selElec18Sum14In42 rE rS42 hES42 w, hComp2]
    refine embedUnitary_catModAddUnitary_congr_sys rE rC (rS42.compose (rSum14Slice42 w))
      (hES42.compose_right _) (hCS42.compose_right _) (elec18AxisVal w) _ fun β ↦ ?_
    rw [elec18AxisVal_eq_sum]
    unfold regVal _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hWire : rE (elec18AxisWire w r) = rC (rElecSlotAxis (QRegExt.idReg _) e w r) := by
      have := e.isLt; have := w.isLt; have := r.isLt
      ext
      simp [rE, rC, rCoreInCoreSum42, rElecSlotInCore, elec18AxisWire, rAxis6In18,
        rElecSlotAxis, QRegister.slice,
        QRegister.compose, QRegExt.idReg]
      omega
    dsimp only; rw [hWire, mul_comm]
  unfold uElecSlotSum42Add uElec18Sum42Add
  dsimp only [rE, rS42, rC] at hAxis
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, hAxis]
  refine unitary_eq_of_mulVec_single fun idx₀ ↦ ?_
  obtain ⟨j₀, m₀, c₀, o₀, i₀⟩ := selCoreSum14_catModAdd_mulVec_single 0 _ idx₀
  obtain ⟨j₁, m₁, c₁, o₁, i₁⟩ := selCoreSum14_catModAdd_mulVec_single 1 _ j₀
  obtain ⟨j₂, m₂, c₂, o₂, i₂⟩ := selCoreSum14_catModAdd_mulVec_single 2 _ j₁
  obtain ⟨k₁, mk, ck, sk⟩ := uCoreShiftSum42_mulVec_single
    (fun w γ ↦ regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ) idx₀
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at mk ⊢
  rw [m₀, m₁, m₂, mk]
  apply congrArg (fun idx ↦ Pi.single idx (1 : ℂ))
  have hγ₀ : (fun q ↦ basisBits _ j₀ (rCoreInCoreSum42 mPayload q)) =
      (fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 mPayload q)) := funext c₀
  have hγ₁ : (fun q ↦ basisBits _ j₁ (rCoreInCoreSum42 mPayload q)) =
      (fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 mPayload q)) := funext fun q ↦ (c₁ q).trans (c₀ q)
  refine eq_of_core_and_sum14_eq
    (fun q ↦ (c₂ q).trans ((c₁ q).trans ((c₀ q).trans (ck q).symm))) fun w j ↦ ?_
  rw [sk w j]
  have hw : w = 0 ∨ w = 1 ∨ w = 2 := by fin_cases w <;> decide
  rcases hw with rfl | rfl | rfl
  · rw [o₂ 0 (by decide) j, o₁ 0 (by decide) j, i₀ j]
  · rw [o₂ 1 (by decide) j, i₁ j, hγ₀]
    rw [_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun k ↦
      o₀ 1 (by decide) k]
  · rw [i₂ j, hγ₁]
    rw [_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun k ↦
      (o₁ 2 (by decide) k).trans (o₀ 2 (by decide) k)]
section OpaqueShiftAlgebra
/-- **Global 218-Electron Stream Unitary Formula (`uStream218CoreSum42 = uCoreShiftSum42
  slot2AxisSum`)**. -/
theorem uStream218CoreSum42_eq_uCoreShiftSum42 (mPayload : ℕ) :
    uStream218CoreSum42 mPayload = uCoreShiftSum42 mPayload slot2AxisSum := by
  unfold uStream218CoreSum42 slot2AxisSum
  simp only [uElecSlotSum42Add_eq_uCoreShiftSum42]
  exact uCoreShiftSum42_list_ofFn_prod mPayload _
end OpaqueShiftAlgebra
theorem rCoreSum42Full_eq :
    rCoreSum42Full = LocalMidUnitaryConjZeroRoot.rCoreSum42Full := rfl
/-- **`uStream218CoreSum42 80` Computes `E_rawStream42` on `pSum42Zero`**. -/
theorem rCoreSum42Full_uStream218CoreSum42_mul_pSum42Zero_eq_E_rawStream42 :
    (rCoreSum42Full.embedUnitary (uStream218CoreSum42 80)).1 * pSum42Zero = E_rawStream42 := by
  let uAx (w : Fin 3) : Unitary (2 ^ (fullSysCoreWires 80 + 14)) :=
    catModAddUnitary (fullSysCoreWires 80) 14 (slot2AxisSum w)
  have hCS (w : Fin 3) : rCoreSum42Full.compose (selCoreSum14In42 80 w) = rCSFull w := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_) idx
    · rw [QRegister.compose_apply, selCoreSum14In42_eq_concat, QRegister.concat_apply_left,
          rCSFull, QRegister.concat_apply_left, rCoreSum42Full_eq]
      exact congrArg (fun r : QRegister _ _ ↦ r iC)
        LocalMidUnitaryConjZeroRoot.rCoreSum42Full_compose_rCore
    · rw [QRegister.compose_apply, selCoreSum14In42_eq_concat, QRegister.concat_apply_right,
          rCSFull, QRegister.concat_apply_right, rCoreSum42Full_eq]
      exact congrArg (fun r : QRegister _ _ ↦ r j14)
        (LocalMidUnitaryConjZeroRoot.rCoreSum42Full_compose_rSum14 w)
  have hEmbed : rCoreSum42Full.embedUnitary (uStream218CoreSum42 80) =
      uStreamFullOf uAx 0 * (uStreamFullOf uAx 1 * uStreamFullOf uAx 2) := by
    rw [uStream218CoreSum42_eq_uCoreShiftSum42]
    unfold uCoreShiftSum42 uStreamFullOf
    dsimp only [uAx]
    simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, hCS]
  have hIsStr : IsSlot2StreamUnitary uAx := fun w β₀ hz ↦ by
    let idx₀ := (basisBitsEquiv kFull80).symm β₀
    have hb₀ : basisBits kFull80 idx₀ = β₀ := (basisBitsEquiv kFull80).apply_symm_apply β₀
    let rSC := rCoreFull.concat (rSum14Full w) (hCoreFull_disj_Sum14 w)
    let idx₁ :=
      rSC.replaceIndex idx₀
      (catModAddPerm (fullSysCoreWires 80) 14 (slot2AxisSum w) (rSC.extractIndex idx₀))
    obtain ⟨hmv, hout, hin⟩ := catModAdd_concat_mulVec_single
      rCoreFull (rSum14Full w) (hCoreFull_disj_Sum14 w) (slot2AxisSum w) idx₀
    refine ⟨basisBits kFull80 idx₁, ?_, fun g hg ↦ ?_, fun j ↦ ?_⟩
    · change
        ((rCoreFull.concat (rSum14Full w) (hCoreFull_disj_Sum14 w)).embedUnitary (uAx w)).1.mulVec
          (Pi.single idx₀ 1) = Pi.single ((basisBitsEquiv kFull80).symm (basisBits kFull80 idx₁)) 1
      have hsymm₁ : (basisBitsEquiv kFull80).symm (basisBits kFull80 idx₁) = idx₁ :=
        (basisBitsEquiv kFull80).symm_apply_apply idx₁
      rw [hsymm₁]; exact hmv
    · rw [hout g (fun ⟨j, hj⟩ ↦ hg ((QRegister.mem_image _ _).mpr ⟨j, hj⟩)), hb₀]
    · have hrv0 : regVal (rSum14Full w) (basisBits kFull80 idx₀) = 0 := by
        rw [hb₀, regVal, funext hz]; rfl
      have hlt := slot2AxisSum_lt w (fun q ↦ β₀ (rCoreFull q))
      rw [hin j, hrv0, hb₀, Nat.zero_add]
      have hfin : (⟨slot2AxisSum w (fun q ↦ β₀ (rCoreFull q)) % 2 ^ 14,
          Nat.mod_lt _ (Nat.two_pow_pos 14)⟩ : Fin (2 ^ 14)) =
          ⟨slot2AxisSum w (fun q ↦ β₀ (rCoreFull q)), hlt⟩ := by
        ext; exact Nat.mod_eq_of_lt hlt
      rw [hfin, basisBits_eq_testBit]
  rw [hEmbed]
  exact uStreamFullOf_012_mul_pSum42Zero_eq_E_rawStream42 hIsStr
end Part3B_Stream218Algebra
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAux
section BodyAlt
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure
section Part3CD_Part
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosSlots24BranchConcrete (posCoreWires rElecSlot rPartnerIdx)
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open PosSlots24PartnerMux288 (sandPhase18)
open PosSlots24Barrel3Pass (rDataElec dataActiveSlot)
open MidKickSub33 (pos24TailMag30MidpointB)
open PosPostPrep80MergedVepS3 (uSwapCore3967)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply embedUnitary_inv_symm kFull80)
open Leaf4Ext48TopStitch (CommutesWithReg disj_of_val_ne)
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42)
open StageAPosHeadConjugatedCircuit (uCoreHadamard18)
open QRegExt
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure
  (uLensSwap partnerActiveSlot partnerActiveSlot_eq_of_partner_eq partnerLens216
  rPartnerIdx_ofFin_val)
open ZeroHypSlot0CommAndHMidClosure
  (P_slot0 restrictOfCommSlot0 embedMatrix_selDataInAct_inj_on_Pm uLensSwap_val_mul_self
  mul_comm_P_slot0 inv_comm_P_slot0)
open LocalZeroHypSlot0CommAndHMidClosure (uMid_intertwines_uLensSwap_of_comm_P_slot0)
open StageAPointPhase128OnStep (activeTwoElecForestFullQftStage128)
open StageBTwoElecQftStream218Inner
  (rCatSlot0Partner rCoreInActB42 rElec0InActB42 rPartner18InActB42 rCoreInActB42_apply
  rPartner18InActB42_apply)
open LocalStageBTwoElecQftStream218Inner
  (uElec18Sum42Add uStageBTwoElecStreamInner uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp
  rSum42InActB42 rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  rCoreInActB42_disj_rPartner18InActB42)
open LocalMidUnitaryConjZeroRoot (rCoreSum42PG7Full)
theorem restrictOfCommSlot0_partnerLens216_embed_eq {kSub kData : ℕ}
    (selSub : QRegister kSub kData) (selCoreSub : QRegister posCoreWires kSub)
    (selCore : QRegister posCoreWires kData) (hCoreComp : selSub.compose selCoreSub = selCore)
    (uSub : Unitary (2 ^ (kSub + 18))) (hComm0 : uSub.1 * P_slot0 (partnerLens216 selCoreSub)
    = P_slot0 (partnerLens216 selCoreSub) * uSub.1) (hComm : ((selSubPartnerInAct
    selSub).embedUnitary uSub).1 * P_slot0 (partnerLens216 selCore) = P_slot0 (partnerLens216
    selCore) * ((selSubPartnerInAct selSub).embedUnitary uSub).1) : restrictOfCommSlot0
    (partnerLens216 selCore) ((selSubPartnerInAct selSub).embedUnitary uSub) hComm =
    selSub.embedUnitary (restrictOfCommSlot0 (partnerLens216 selCoreSub) uSub hComm0) := by
  let rSP := selSubPartnerInAct selSub
  apply restrictOfCommSlot0_eq_of_intertwine
  have hInt0 := uMid_intertwines_uLensSwap_of_comm_P_slot0 (partnerLens216 selCoreSub) uSub hComm0
  have hLift := congrArg rSP.embedMatrix hInt0
  simp only [QRegister.embedMatrix_mul] at hLift
  have hMComp : rSP.compose (selMeasInAct kSub) = selMeasInAct kData := by
    apply qreg_ext; intro j; rw [QRegister.compose_apply, selMeasInAct_apply (kData := kSub) j]
    dsimp only [rSP, selSubPartnerInAct]; rw [QRegister.concat_apply_right]
  have hDComp : rSP.compose (selDataInAct kSub) = (selDataInAct kData).compose selSub := by
    apply qreg_ext; intro q; rw [QRegister.compose_apply, selDataInAct_apply q]
    dsimp only [rSP, selSubPartnerInAct]; rw [QRegister.concat_apply_left]
  have hPm : rSP.embedMatrix ((selMeasInAct kSub).basisOutcomeProjector 0) =
      (selMeasInAct kData).basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hMComp,
      ← QRegister.basisOutcomeProjector]
  have hSwap := uLensSwap_partnerLens216_eq_embed selSub selCoreSub selCore hCoreComp
  rw [← QRegister.embedUnitary_val rSP (uSub * uLensSwap (partnerLens216 selCoreSub)),
      QRegister.embedUnitary_mul, ← hSwap,
      ← QRegister.embedUnitary_val rSP (uLensSwap (partnerLens216 selCoreSub)),
      ← hSwap, QRegister.embedUnitary_val (selDataInAct kSub),
      ← QRegister.embedMatrix_compose, hDComp, QRegister.embedMatrix_compose, hPm] at hLift
  simpa only [QRegister.embedUnitary_val] using hLift
theorem commutesWithReg_restrictOfCommSlot0 {k kData : ℕ}
    (L : Slot18Lens kData) (rSub : QRegister k kData)
    (uInner : Unitary (2 ^ (kData + 18)))
    (hComm : uInner.1 * P_slot0 L = P_slot0 L * uInner.1)
    (hInnerSub : CommutesWithReg ((selDataInAct kData).compose rSub) uInner.1)
    (hSwapSub : CommutesWithReg ((selDataInAct kData).compose rSub) (uLensSwap L).1) :
    CommutesWithReg rSub (restrictOfCommSlot0 L uInner hComm).1 := fun B ↦ by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let Pm := selM.basisOutcomeProjector 0
  let S := uLensSwap L
  let V := restrictOfCommSlot0 L uInner hComm
  let BD := (selD.compose rSub).embedMatrix B
  have hBDEq : selD.embedMatrix (rSub.embedMatrix B) = BD :=
    (QRegister.embedMatrix_compose selD rSub B).symm
  have hBDPm : BD * Pm = Pm * BD :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (selD.compose rSub) selM ((selDataInAct_disj_selMeasInAct kData).compose_left rSub) B 0
  have hBDS : S.1 * BD = BD * S.1 := hSwapSub B
  have hBDU : uInner.1 * BD = BD * uInner.1 := hInnerSub B
  have hInt := uMid_intertwines_uLensSwap_of_comm_P_slot0 L uInner hComm
  have hSwapEq : S.1 * (selD.embedMatrix (V.1 * rSub.embedMatrix B) * Pm) =
      S.1 * (selD.embedMatrix (rSub.embedMatrix B * V.1) * Pm) := by
    rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, hBDEq,
        ← QRegister.embedUnitary_val selD V]
    calc S.1 * ((selD.embedUnitary V).1 * BD * Pm)
        = (S.1 * (selD.embedUnitary V).1 * Pm) * BD := by
            rw [Matrix.mul_assoc (selD.embedUnitary V).1 BD Pm, hBDPm]; simp only [Matrix.mul_assoc]
      _ = ((uInner * S).1 * Pm) * BD := by rw [← hInt]
      _ = uInner.1 * (S.1 * BD) * Pm := by
            rw [Submonoid.coe_mul, Matrix.mul_assoc (uInner.1 * S.1) Pm BD, ← hBDPm]
            simp only [Matrix.mul_assoc]
      _ = BD * ((uInner * S).1 * Pm) := by
            rw [hBDS, ← Matrix.mul_assoc uInner.1 BD S.1, hBDU]
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = BD * (S.1 * (selD.embedUnitary V).1 * Pm) := by rw [hInt]
      _ = S.1 * (BD * (selD.embedUnitary V).1 * Pm) := by
            rw [← Matrix.mul_assoc BD, ← Matrix.mul_assoc BD S.1, ← hBDS]
            simp only [Matrix.mul_assoc]
  apply embedMatrix_selDataInAct_inj_on_Pm
  have hMul := congrArg (fun M ↦ S.1 * M) hSwapEq
  dsimp only [S] at hMul
  have hL : (uLensSwap L).1 *
    ((uLensSwap L).1 * (selD.embedMatrix (V.1 * rSub.embedMatrix B) * Pm)) =
      selD.embedMatrix (V.1 * rSub.embedMatrix B) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L, Matrix.one_mul]
  have hR : (uLensSwap L).1 *
    ((uLensSwap L).1 * (selD.embedMatrix (rSub.embedMatrix B * V.1) * Pm)) =
      selD.embedMatrix (rSub.embedMatrix B * V.1) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L, Matrix.one_mul]
  exact hL.symm.trans (hMul.trans hR)
-- ============================================================================
-- Section 3C-2: Core / Core+PG7 / Seg / Full Stage-B Unitaries
-- ============================================================================
theorem selCoreInCoreSum42_compose_idReg :
    selCoreInCoreSum42.compose (QRegExt.idReg posCoreWires) = selCoreInCoreSum42 := rfl
theorem selCoreSum42_compose_core :
    selCoreSum42InCoreSum42PG7.compose selCoreInCoreSum42 = selCoreInCoreSum42PG7 := by
  apply qreg_ext; intro i; ext
  simp [selCoreSum42InCoreSum42PG7, selCoreInCoreSum42, selCoreInCoreSum42PG7]
def rElec0InCoreP : QRegister 18 (posCoreWires + 18) :=
  (selDataInAct posCoreWires).compose (rElecSlot (QRegExt.ofFin posCoreWires) ⟨0, by decide⟩)
def rPartner18InCoreP : QRegister 18 (posCoreWires + 18) := selMeasInAct posCoreWires
noncomputable def uHad2CoreP : Unitary (2 ^ (posCoreWires + 18)) :=
  rElec0InCoreP.embedUnitary uCoreHadamard18 * rPartner18InCoreP.embedUnitary uCoreHadamard18
noncomputable def uInnerCoreP (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    Unitary (2 ^ (posCoreWires + 18)) :=
  uHad2CoreP⁻¹ * (uSandCoreP B hB1 hB27 slot2SwappedTo0 * uHad2CoreP)
theorem selSubPartner_coreInSum42_uHad2 :
    (selSubPartnerInAct selCoreInCoreSum42).embedUnitary uHad2CoreP = uHad2Core42 := by
  have hE0 : (selSubPartnerInAct selCoreInCoreSum42).compose rElec0InCoreP = rElec0InCS42P := by
    apply qreg_ext; intro q; rw [QRegister.compose_apply]
    have hq : rElec0InCoreP q = Fin.castAdd 18 (rElecSlot (QRegExt.ofFin posCoreWires) ⟨0,
      by decide⟩ q) :=
      selDataInAct_apply _
    rw [hq, selSubPartnerInAct, QRegister.concat_apply_left]; rfl
  have hP : (selSubPartnerInAct selCoreInCoreSum42).compose rPartner18InCoreP = rPartner18InCS42P :=
    by
    apply qreg_ext; intro q; rw [QRegister.compose_apply]
    have hq : rPartner18InCoreP q = Fin.natAdd posCoreWires q :=
      selMeasInAct_apply (kData := posCoreWires) q
    rw [hq, selSubPartnerInAct, QRegister.concat_apply_right]; rfl
  unfold uHad2CoreP uHad2Core42
  rw [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose,
    ← QRegister.embedUnitary_compose, hE0, hP]
theorem selSubPartner_coreInSum42_uSand (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤
    27) (slot2SwappedTo0 : Bool) :
    (selSubPartnerInAct selCoreInCoreSum42).embedUnitary (uSandCoreP B hB1 hB27 slot2SwappedTo0) =
      uSandCore42 B hB1 hB27 slot2SwappedTo0 := by
  have hCP : (selSubPartnerInAct selCoreInCoreSum42).compose
      ((selDataInAct posCoreWires).concat (selMeasInAct posCoreWires)
        (selDataInAct_disj_selMeasInAct posCoreWires)) =
      rCoreInCS42P.concat rPartner18InCS42P rCoreInCS42P_disj_rPartner18InCS42P := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
    · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
          selDataInAct_apply, selSubPartnerInAct, QRegister.concat_apply_left]; rfl
    · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
          selMeasInAct_apply (kData :=
            posCoreWires), selSubPartnerInAct, QRegister.concat_apply_right]; rfl
  unfold uSandCoreP uSandCore42
  rw [← QRegister.embedUnitary_compose, hCP]
theorem uHad2CoreP_comm_P_slot0 :
    uHad2CoreP.1 * P_slot0 partnerLensOnCore = P_slot0 partnerLensOnCore * uHad2CoreP.1 :=
  comm_P_slot0_partnerLens216_of_embed selCoreInCoreSum42 (QRegExt.idReg posCoreWires)
    selCoreInCoreSum42 selCoreInCoreSum42_compose_idReg uHad2CoreP <| by
    rw [selSubPartner_coreInSum42_uHad2]; exact uHad2Core42_comm_P_slot0
theorem uInnerCoreP_comm_P_slot0 (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uInnerCoreP B hB1 hB27 slot2SwappedTo0).1 * P_slot0 partnerLensOnCore =
      P_slot0 partnerLensOnCore * (uInnerCoreP B hB1 hB27 slot2SwappedTo0).1 :=
  mul_comm_P_slot0 _ (inv_comm_P_slot0 _ uHad2CoreP_comm_P_slot0)
    (mul_comm_P_slot0 _ (uSandCoreP_comm_P_slot0 B hB1 hB27 slot2SwappedTo0)
      uHad2CoreP_comm_P_slot0)
noncomputable def uStageBCoreRaw (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : Unitary
    (2 ^ posCoreWires) := restrictOfCommSlot0 partnerLensOnCore
    (uInnerCoreP B (by omega) hB27 true) (uInnerCoreP_comm_P_slot0 B (by omega) hB27 true)
set_option exponentiation.threshold 4200 in
noncomputable def uStageBCore (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  uSwapCore3967 * (uStageBCoreRaw B hB6 hB27 * uSwapCore3967)
noncomputable def uStageBStream218PG7Raw (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : Unitary
    (2 ^ ((posCoreWires + 42) + 7)) := restrictOfCommSlot0 partnerLensOnCoreSum42PG7
    (uStageBTwoElecStreamInner B (by omega) hB27 true)
    (uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp B (by omega) hB27 true)
set_option exponentiation.threshold 4200 in
/-- Canonical `4,083`-wire `(rCore ++ rSum42) ++ rPG7` Stage-B catalyzed stream unitary
  (`uSwapCore3967`-wrapped). -/
noncomputable def uStageBStream218PG7 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    Unitary (2 ^ ((fullSysCoreWires 80 + 42) + 7)) :=
  selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 *
    (uStageBStream218PG7Raw B hB6 hB27 * selCoreInCoreSum42PG7.embedUnitary uSwapCore3967)
/-- Canonical `4,128`-wire (`kFull80`) Stage-B full-space unitary, shared by BOTH `Ctrl` and
  `Cat`! -/
noncomputable def uStageBFull (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : Unitary (2 ^ kFull80) :=
    rCoreSum42PG7Full.embedUnitary (uStageBStream218PG7 B hB6 hB27)
theorem selSubPartner_corePG7_uInner (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤
    27) (slot2SwappedTo0 : Bool) :
    (selSubPartnerInAct selCorePG7InCoreSum42PG7).embedUnitary
      (uInnerCorePG7P B hB1 hB27 slot2SwappedTo0) =
      let uQft2 := rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat
      let uSand := (rCoreInActB42.concat rPartner18InActB42
          rCoreInActB42_disj_rPartner18InActB42).embedUnitary (diagSignUnitary (sandPhase18
          slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign
          (pos24TailMag30MidpointB B hB1 (by omega)))))
      uQft2⁻¹ * (uSand * uQft2) := by
  have hQft : (selSubPartnerInAct selCorePG7InCoreSum42PG7).embedUnitary uQft2CorePG7P =
      rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat := by
    unfold uQft2CorePG7P
    rw [← QRegister.embedUnitary_compose (selSubPartnerInAct selCorePG7InCoreSum42PG7)
          rCatSlot0PartnerCorePG7 activeTwoElecForestFullQftStage128.uCat,
        selSubPartner_corePG7_compose_rCat]
  have hCP : (selSubPartnerInAct selCorePG7InCoreSum42PG7).compose
      ((selSubPartnerInAct selCoreInCorePG7).compose
        ((selDataInAct posCoreWires).concat (selMeasInAct posCoreWires)
          (selDataInAct_disj_selMeasInAct posCoreWires))) =
      rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42 := by
    apply qreg_ext; intro idx; apply Fin.ext
    refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
    · rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.concat_apply_left,
        QRegister.concat_apply_left,
          selDataInAct_apply]
      dsimp only [selSubPartnerInAct]
      rw [QRegister.concat_apply_left, QRegister.compose_apply, selDataInAct_apply,
          QRegister.concat_apply_left, QRegister.compose_apply,
          rCoreInActB42_apply, selDataInAct_apply, Fin.val_castAdd,
          ← QRegister.compose_apply selCorePG7InCoreSum42PG7 selCoreInCorePG7,
            selCorePG7_compose_core]
      simp [selCoreInCoreSum42PG7]
    · rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.concat_apply_right,
        QRegister.concat_apply_right,
          selMeasInAct_apply (kData := posCoreWires)]
      dsimp only [selSubPartnerInAct]
      rw [QRegister.concat_apply_right, selMeasInAct_apply (kData := posCoreWires + 7),
          QRegister.concat_apply_right, rPartner18InActB42_apply, selMeasInAct_apply,
            Fin.val_natAdd]
  unfold uInnerCorePG7P uSandCoreP
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← embedUnitary_inv_symm, hQft,
      ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, QRegister.compose_assoc,
        hCP]
private theorem unitaryD_mul_inv_rev {D : ℕ} (a b : Operator.Unitary D) : (a * b)⁻¹ = b⁻¹ *
    a⁻¹ := _root_.mul_inv_rev a b
private theorem unitaryD_mul_assoc {D : ℕ} (a b c : Operator.Unitary D) : a * b * c = a *
    (b * c) := mul_assoc a b c
theorem uStageBStream218PG7Raw_eq_five_factors (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    let rAdd0 := restrictOfCommSlot0 partnerLensOnCoreSum42 uAdd0Core42 uAdd0Core42_comm_P_slot0
    let rAddP := restrictOfCommSlot0 partnerLensOnCoreSum42 uAddPCore42 uAddPCore42_comm_P_slot0
    uStageBStream218PG7Raw B hB6 hB27 =
      selCoreSum42InCoreSum42PG7.embedUnitary (rAdd0 * rAddP) *
        (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B hB6 hB27) *
          (selCoreSum42InCoreSum42PG7.embedUnitary (rAdd0 * rAddP))⁻¹) := by
  intro rAdd0 rAddP
  let L := partnerLensOnCoreSum42PG7
  let uAdd0B := (selSubPartnerInAct selCoreSum42InCoreSum42PG7).embedUnitary uAdd0Core42
  let uAddPB := (selSubPartnerInAct selCoreSum42InCoreSum42PG7).embedUnitary uAddPCore42
  let uMidB := (selSubPartnerInAct selCorePG7InCoreSum42PG7).embedUnitary
    (uInnerCorePG7P B (by omega) hB27 true)
  have hEqInner : uStageBTwoElecStreamInner B (by omega) hB27 true =
      uAdd0B * (uAddPB * (uMidB * (uAddPB⁻¹ * uAdd0B⁻¹))) := by
    have hE0 : (selSubPartnerInAct selCoreSum42InCoreSum42PG7).compose
        (rElec0InCS42P.concat rSum42InCS42P rElec0InCS42P_disj_rSum42InCS42P) =
        rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42 := by
      apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
            ← selCSPartner_compose_rElec0]; rfl
      · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
            ← selCSPartner_compose_rSum42]; rfl
    have hPS : (selSubPartnerInAct selCoreSum42InCoreSum42PG7).compose
        (rPartner18InCS42P.concat rSum42InCS42P rPartner18InCS42P_disj_rSum42InCS42P) =
        rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42 := by
      apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
            ← selCSPartner_compose_rPartner18]; rfl
      · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
            ← selCSPartner_compose_rSum42]; rfl
    dsimp only [uAdd0B, uAddPB, uMidB]
    rw [selSubPartner_corePG7_uInner B (by omega) hB27 true]
    unfold uStageBTwoElecStreamInner uAdd0Core42 uAddPCore42
    simp only [← QRegister.embedUnitary_compose, hE0, hPS, mul_assoc]
  have cA0 := comm_P_slot0_partnerLens216_embed selCoreSum42InCoreSum42PG7 selCoreInCoreSum42
    selCoreInCoreSum42PG7 selCoreSum42_compose_core uAdd0Core42 uAdd0Core42_comm_P_slot0
  have cAP := comm_P_slot0_partnerLens216_embed selCoreSum42InCoreSum42PG7 selCoreInCoreSum42
    selCoreInCoreSum42PG7 selCoreSum42_compose_core uAddPCore42 uAddPCore42_comm_P_slot0
  have cMid := comm_P_slot0_partnerLens216_embed selCorePG7InCoreSum42PG7 selCoreInCorePG7
    selCoreInCoreSum42PG7 selCorePG7_compose_core _
      (uInnerCorePG7P_comm_P_slot0 B (by omega) hB27 true)
  have cA0i := inv_comm_P_slot0 L cA0
  have cAPi := inv_comm_P_slot0 L cAP
  have c45 := mul_comm_P_slot0 L cAPi cA0i
  have c345 := mul_comm_P_slot0 L cMid c45
  have c2345 := mul_comm_P_slot0 L cAP c345
  have c12345 := mul_comm_P_slot0 L cA0 c2345
  have hLHS : uStageBStream218PG7Raw B hB6 hB27 =
      restrictOfCommSlot0 L (uAdd0B * (uAddPB * (uMidB * (uAddPB⁻¹ * uAdd0B⁻¹)))) c12345 := by
    unfold uStageBStream218PG7Raw; congr 1
  rw [hLHS,
      restrictOfCommSlot0_mul L _ _ cA0 c2345,
      restrictOfCommSlot0_mul L _ _ cAP c345,
      restrictOfCommSlot0_mul L _ _ cMid c45,
      restrictOfCommSlot0_mul L _ _ cAPi cA0i,
      restrictOfCommSlot0_inv L uAddPB cAP cAPi,
      restrictOfCommSlot0_inv L uAdd0B cA0 cA0i,
      restrictOfCommSlot0_partnerLens216_embed_eq selCoreSum42InCoreSum42PG7 selCoreInCoreSum42
        selCoreInCoreSum42PG7 selCoreSum42_compose_core uAdd0Core42 uAdd0Core42_comm_P_slot0 cA0,
      restrictOfCommSlot0_partnerLens216_embed_eq selCoreSum42InCoreSum42PG7 selCoreInCoreSum42
        selCoreInCoreSum42PG7 selCoreSum42_compose_core uAddPCore42 uAddPCore42_comm_P_slot0 cAP,
      restrictOfCommSlot0_partnerLens216_embed_eq selCorePG7InCoreSum42PG7 selCoreInCorePG7
        selCoreInCoreSum42PG7 selCorePG7_compose_core _
          (uInnerCorePG7P_comm_P_slot0 B (by omega) hB27 true) cMid]
  change selCoreSum42InCoreSum42PG7.embedUnitary rAdd0 *
    (selCoreSum42InCoreSum42PG7.embedUnitary rAddP * (selCorePG7InCoreSum42PG7.embedUnitary
    (uStageBCorePG7Raw B hB6 hB27) * ((selCoreSum42InCoreSum42PG7.embedUnitary rAddP)⁻¹ *
    (selCoreSum42InCoreSum42PG7.embedUnitary rAdd0)⁻¹))) =
    selCoreSum42InCoreSum42PG7.embedUnitary (rAdd0 * rAddP) *
    (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B hB6 hB27) *
    (selCoreSum42InCoreSum42PG7.embedUnitary (rAdd0 * rAddP))⁻¹)
  rw [QRegister.embedUnitary_mul, unitaryD_mul_inv_rev, unitaryD_mul_assoc]
theorem partnerActiveSlot_ne_zero {kData : ℕ} (selC : QRegister posCoreWires kData)
    (d : Fin (2 ^ kData)) : partnerActiveSlot selC d ≠ 0 := by
  intro h; have hv := congrArg Fin.val h
  dsimp [partnerActiveSlot, dataActiveSlot] at hv; omega
theorem eq_of_basisBits_eq_s3 {q : ℕ} {x y : Fin (2 ^ q)}
    (h : ∀ w : Fin q, basisBits q x w = basisBits q y w) : x = y :=
  (basisBitsEquiv q).injective (funext h)
theorem uLensSwap_partnerLens216_mulVec_apply {kData : ℕ}
    (selC : QRegister posCoreWires kData) (state : Fin (2 ^ (kData + 18)) → ℂ)
    (out : Fin (2 ^ (kData + 18))) : ((uLensSwap (partnerLens216 selC)).1.mulVec state) out =
    state (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin
      (partnerLens216 selC) out) := by
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selC)
  have hSingle : ∀ z,
    (uLensSwap (partnerLens216 selC)).1.mulVec (Pi.single z 1) = Pi.single (f z) 1 := by
    intro z
    rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
    dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
      ZeroHypElecHadHCompAndPass123Closure.permUnitary]
    funext i; rw [Matrix.mulVec_single_one]
    change (if i = f z then (1 : ℂ) else 0) = (Pi.single (f z) (1 : ℂ) : _ → ℂ) i
    by_cases h : i = f z <;> simp [h]
  have hInv : ∀ z, f (f z) = z := by
    intro z
    have h2 : ((uLensSwap (partnerLens216 selC)).1 *
      (uLensSwap (partnerLens216 selC)).1).mulVec (Pi.single z 1) =
        (1 : Operator _).mulVec (Pi.single z 1) := by
      rw [uLensSwap_val_mul_self]
    rw [← Matrix.mulVec_mulVec, hSingle z, hSingle (f z), Matrix.one_mulVec] at h2
    have hz := congrFun h2 z
    by_cases h : f (f z) = z
    · exact h
    · simp [Pi.single_eq_of_ne (Ne.symm h)] at hz
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
    ZeroHypElecHadHCompAndPass123Closure.permUnitary,
    ZeroHypElecHadHCompAndPass123Closure.permMatrix]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hiff : ∀ j, (out = f j) ↔ (j = f out) :=
    fun j ↦ ⟨fun h ↦ by rw [h, hInv], fun h ↦ by rw [h, hInv]⟩
  dsimp only [f] at hiff
  simp only [hiff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
theorem partnerActiveSlot_cs42p_eq_of_partnerIdx_eq
    {x y : Fin (2 ^ ((posCoreWires + 42) + 18))}
    (h : ∀ q : Fin 8, basisBits _ x (rCoreInCS42P (rPartnerIdx (QRegExt.ofFin posCoreWires) q)) =
      basisBits _ y (rCoreInCS42P (rPartnerIdx (QRegExt.ofFin posCoreWires) q))) :
    partnerActiveSlot selCoreInCoreSum42 ((selDataInAct (posCoreWires + 42)).extractIndex x) =
      partnerActiveSlot selCoreInCoreSum42 ((selDataInAct (posCoreWires + 42)).extractIndex y) := by
  apply partnerActiveSlot_eq_of_partner_eq
  apply eq_of_basisBits_eq_s3; intro q
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact h q
set_option exponentiation.threshold 4200 in
theorem rAdd0_eq_uElecSlotSum42Add_zero : restrictOfCommSlot0 partnerLensOnCoreSum42
    uAdd0Core42 uAdd0Core42_comm_P_slot0 = uElecSlotSum42Add 80 0 := by
  apply restrictOfCommSlot0_eq_of_intertwine
  have hEmbed : (selDataInAct (posCoreWires + 42)).embedUnitary (uElecSlotSum42Add 80 0) =
    uAdd0Core42 := by
    have hComp : (selDataInAct (posCoreWires + 42)).compose
        (((rCoreInCoreSum42 80).compose (rElecSlotInCore 80 0)).concat (rSum42InCoreSum42 80)
          ((rCoreInCoreSum42_disj_rSum42 80).compose_left _)) =
        rElec0InCS42P.concat rSum42InCS42P rElec0InCS42P_disj_rSum42InCS42P := by
      apply qreg_ext; intro idx; apply Fin.ext
      refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) idx
      · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
            rElec0InCS42P_apply]
        simp [selDataInAct_apply, rCoreInCoreSum42, rElecSlotInCore]
      · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
            rSum42InCS42P_apply]
        simp [selDataInAct_apply, rSum42InCoreSum42, fullSysCoreWires_80_eq_4034,
          posCoreWires_eq_4034]
    unfold uElecSlotSum42Add uAdd0Core42
    rw [← QRegister.embedUnitary_compose, hComp]
  rw [hEmbed, Submonoid.coe_mul]
  refine congrArg (fun M ↦ M * (selMeasInAct (posCoreWires + 42)).basisOutcomeProjector 0) ?_
  let r₀ := rElec0InCS42P.concat rSum42InCS42P rElec0InCS42P_disj_rSum42InCS42P
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin partnerLensOnCoreSum42
  have hDisjSlot : ∀ s : Fin 218, s ≠ 0 →
      r₀.DisjointWires ((selDataInAct (posCoreWires +
        42)).compose (rDataElec selCoreInCoreSum42 s)) := by
    intro s hs; refine disj_of_val_ne fun idx q ↦ ?_
    have hs1 : 1 ≤ s.val := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hs)
    have hSlotVal : (((selDataInAct (posCoreWires +
      42)).compose (rDataElec selCoreInCoreSum42 s)) q).val =
        18 * s.val + q.val := by
      have := s.isLt; have := q.isLt
      simp [selDataInAct_apply, rDataElec, selCoreInCoreSum42, rElecSlot, QRegister.slice,
        QRegExt.ofFin]
    rw [hSlotVal]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left, rElec0InCS42P_apply]; have := i.isLt; omega
    · rw [QRegister.concat_apply_right, rSum42InCS42P_apply]
      have := s.isLt; have := q.isLt; have := posCoreWires_eq_4034; omega
  have hDisjMeas : r₀.DisjointWires (selMeasInAct (posCoreWires + 42)) := by
    refine disj_of_val_ne fun idx q ↦ ?_
    rw [selMeasInAct_apply, Fin.val_natAdd]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left, rElec0InCS42P_apply]; have := i.isLt; omega
    · rw [QRegister.concat_apply_right, rSum42InCS42P_apply]; have := j.isLt; omega
  ext out inp
  have hCol : (uAdd0Core42.1 * (uLensSwap partnerLensOnCoreSum42).1).mulVec (Pi.single inp 1) out =
      ((uLensSwap partnerLensOnCoreSum42).1 * uAdd0Core42.1).mulVec (Pi.single inp 1) out := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uLensSwap_partnerLens216_mulVec_apply]
    unfold uAdd0Core42; rw [QRegister.embedUnitary_val]
    change (r₀.embedMatrix uElec18Sum42Add.1).mulVec _ out =
      (r₀.embedMatrix uElec18Sum42Add.1).mulVec _ (f out)
    rw [r₀.embedMatrix_mulVec_apply, r₀.embedMatrix_mulVec_apply]
    let s :=
      partnerActiveSlot selCoreInCoreSum42 ((selDataInAct (posCoreWires + 42)).extractIndex out)
    have hs0 : s ≠ 0 := partnerActiveSlot_ne_zero _ _
    have hf : ∀ z,
      partnerActiveSlot selCoreInCoreSum42 ((selDataInAct (posCoreWires + 42)).extractIndex z) = s →
        f z = (selMeasInAct (posCoreWires + 42)).replaceIndex
          (((selDataInAct (posCoreWires +
            42)).compose (rDataElec selCoreInCoreSum42 s)).replaceIndex z
            ((selMeasInAct (posCoreWires + 42)).extractIndex z))
          (((selDataInAct (posCoreWires +
            42)).compose (rDataElec selCoreInCoreSum42 s)).extractIndex z) := by
      intro z hz
      have h1 := lensSwapFin_eq_two_replaceIndex partnerLensOnCoreSum42
        (partnerActiveSlot selCoreInCoreSum42) (rDataElec selCoreInCoreSum42) (fun _ ↦
          rfl) (fun _ _ ↦ rfl) z
      dsimp only at h1; rw [hz] at h1; exact h1
    have hEx : r₀.extractIndex (f out) = r₀.extractIndex out := by
      rw[hf out rfl, r₀.extractIndex_replaceIndex_of_disjoint _ hDisjMeas,
          r₀.extractIndex_replaceIndex_of_disjoint _ (hDisjSlot s hs0)]
    refine Finset.sum_congr rfl fun idx _ ↦ ?_
    rw [uLensSwap_partnerLens216_mulVec_apply, hEx]
    have hSlotIdx : partnerActiveSlot selCoreInCoreSum42
        ((selDataInAct (posCoreWires + 42)).extractIndex (r₀.replaceIndex out idx)) = s := by
      refine partnerActiveSlot_cs42p_eq_of_partnerIdx_eq fun q ↦ ?_
      refine r₀.basisBits_replaceIndex_of_not_mem out idx _ ?_
      rintro ⟨u, hu⟩
      refine Fin.addCases (fun i hi ↦ ?_) (fun j hj ↦ ?_) u hu
      · have hv := congrArg Fin.val hi
        rw [QRegister.concat_apply_left, rElec0InCS42P_apply, rCoreInCS42P_apply,
          rPartnerIdx_ofFin_val] at hv
        have := i.isLt; omega
      · have hv := congrArg Fin.val hj
        rw [QRegister.concat_apply_right, rSum42InCS42P_apply, rCoreInCS42P_apply,
          rPartnerIdx_ofFin_val] at hv
        have := q.isLt; have := posCoreWires_eq_4034; omega
    have hRep : r₀.replaceIndex (f out) idx = f (r₀.replaceIndex out idx) := by
      rw [hf out rfl, hf (r₀.replaceIndex out idx) hSlotIdx,
          (selMeasInAct (posCoreWires +
            42)).extractIndex_replaceIndex_of_disjoint r₀ (QRegExt.disjointWires_symm hDisjMeas),
          ((selDataInAct (posCoreWires +
            42)).compose (rDataElec selCoreInCoreSum42 s)).extractIndex_replaceIndex_of_disjoint
            r₀ (hDisjSlot s hs0).symm,
          r₀.replaceIndex_comm_of_disjoint _ hDisjMeas,
          r₀.replaceIndex_comm_of_disjoint _ (hDisjSlot s hs0)]
    change uElec18Sum42Add.1 _ idx * (Pi.single inp 1 : _ → ℂ) (f (r₀.replaceIndex out idx)) =
      uElec18Sum42Add.1 _ idx * (Pi.single inp 1 : _ → ℂ) (r₀.replaceIndex (f out) idx)
    rw [hRep]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hCol
end Part3CD_Part
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAlt
end SharedScope
end
end SlimStageBDepsB

noncomputable section Slot3BoothOpt

section
namespace Slot3BoothOptAux
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
local instance (priority := 100) instNeZeroTwoPowBoothOptExt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (TempPhaseProg cleanRem ValidCleanRem ctxCliffAlloc RealizesCleanUnitary_seq_asym)
open MeasureBranchHadamardSem (bit_cases RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open Prod57BoothHoist
  (bitsVal_injective bitsVal_castSucc_split p57CleanDiagProj p57CleanDiagProj_conjTranspose
  p57CleanDiagProj_mono p57SeqClean_prog_inv)
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned (p57Realizes_congr_prog)
open Slot3Norm1s36_161w
open Slot3Norm1s36CoreWideBooth
  (n1sUKW411 n1s_uKW411_range n1sOut32W411 n1sMantW411 n1s_tier_bounds n1sBoothInv
  n1sLowRowRevStatic n1s_lowRowRev_spec n1sDLowRowRev n1s_dLowRowRev_props n1sBoothPrefixRevStatic
  n1s_boothPrefixRev_spec)
open Slot3Norm1s36CoreWide (n1s_dyn_count_seq)
open Leaf3Slot3ZRet193
  (zrInBoothDomB zrCtxInBoothDom zr_p57ToDynWith_not_mem_support_of_dom
  zr_dCleanMsbSub_not_mem_support zr_bLowR_inBoothDom zr_accSlice_inBoothDom zr_cRowSetup_inBoothDom
  zr_cliff_inv_inBoothDom)
open Slot3BoothAndBarrelOpt (bitsVal_fin1 bitsVal_fin4)
theorem bitsVal_fin2 (f : Fin 2 → ZMod 2) : bitsVal f = (f 0).val + 2 * (f 1).val := by
  rw [bitsVal_castSucc_split, bitsVal_fin1]
  rfl
theorem bitsVal_fin5 (f : Fin 5 → ZMod 2) :
    bitsVal f = (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val + 16 * (f 4).val := by
  rw [bitsVal_castSucc_split, bitsVal_fin4]
  rfl
def n1sCustomInv (P : BitAssignment 411 → ℕ) (β : BitAssignment 411) : Prop :=
  bitsVal (fun j : Fin 32 ↦ β (n1sOut32W411 j)) = P β
/-- Predicate stating that `P` depends only on wires outside `n1sOut32W411`. -/
def NonOut32Congr (P : BitAssignment 411 → ℕ) : Prop := ∀ (β δ : BitAssignment 411),
    (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → δ q = β q) → P δ = P β
/-- Unified bundle of static properties for a Booth step on `Wire 411` with `rem = 411 - 379`. -/
def N1sProgStep379 (p : TempPhaseProg 411) (InvIn InvOut : BitAssignment 411 → Prop) : Prop :=
    ValidCleanRem 411 (411 - 379) p ∧ ∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
    p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧ (∀ q : Wire 411, (∀ k : Fin
    32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧ (InvIn β → InvOut (p.evalBits β))
theorem N1sProgStep379.seq {p₁ p₂ : TempPhaseProg 411}
    {Inv₀ Inv₁ Inv₂ : BitAssignment 411 → Prop} (h₁ : N1sProgStep379 p₁ Inv₀ Inv₁)
    (h₂ : N1sProgStep379 p₂ Inv₁ Inv₂) : N1sProgStep379 (.seq p₁ p₂) Inv₀ Inv₂ := by
  obtain ⟨hv₁, hEv₁⟩ := h₁
  obtain ⟨hv₂, hEv₂⟩ := h₂
  refine ⟨⟨411 - 379, by decide, hv₁, hv₂, fun β hβ ↦ (hEv₁ β hβ).2.1⟩, fun β hβ ↦ ?_⟩
  obtain ⟨hs₁, hcl₁, hnon₁, hinv₁⟩ := hEv₁ β hβ
  obtain ⟨hs₂, hcl₂, hnon₂, hinv₂⟩ := hEv₂ (p₁.evalBits β) hcl₁
  exact ⟨by
    dsimp only [TempPhaseProg.evalSign]; rw [hs₁, hs₂, add_zero],
    hcl₂,
    fun q hq ↦ (hnon₂ q hq).trans (hnon₁ q hq),
    fun hi₀ ↦ hinv₂ (hinv₁ hi₀)⟩
theorem N1sProgStep379.congr_in {p : TempPhaseProg 411}
    {Inv₀ Inv₀' Inv₁ : BitAssignment 411 → Prop} (h : N1sProgStep379 p Inv₀ Inv₁) (hImp : ∀ β
    : BitAssignment 411, cleanRem 411 (411 - 379) β → Inv₀' β → Inv₀ β) : N1sProgStep379 p
    Inv₀' Inv₁ := ⟨h.1, fun β hβ ↦ ⟨(h.2 β hβ).1, (h.2 β hβ).2.1, (h.2 β hβ).2.2.1, fun hi ↦
    (h.2 β hβ).2.2.2 (hImp β hβ hi)⟩⟩
theorem N1sProgStep379.congr_out {p : TempPhaseProg 411}
    {Inv₀ Inv₁ Inv₁' : BitAssignment 411 → Prop} (h : N1sProgStep379 p Inv₀ Inv₁) (hImp : ∀ β
    : BitAssignment 411, cleanRem 411 (411 - 379) β → Inv₁ β → Inv₁' β) : N1sProgStep379 p
    Inv₀ Inv₁' := ⟨h.1, fun β hβ ↦ ⟨(h.2 β hβ).1, (h.2 β hβ).2.1, (h.2 β hβ).2.2.1, fun hi ↦
    hImp (p.evalBits β) (h.2 β hβ).2.1 ((h.2 β hβ).2.2.2 hi)⟩⟩
/-- Unified bundle of dynamic + static properties for a reverse Booth step on `rBooth : QRegister
  411 n`. -/
def N1sDynStep379 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rBooth : QRegister 411 n) (p : TempPhaseProg 411) (d : DynamicCircuit Var n)
    (tCount : ℕ) (InvIn InvOut : BitAssignment 411 → Prop) : Prop := N1sProgStep379 p InvIn
    InvOut ∧ d.count PrimitiveGate.T = tCount ∧ d.count PrimitiveGate.TOFF = 0 ∧
    PreservesStoreConst d ∧ (∀ x : Wire n, (∀ q : Wire 411, zrInBoothDomB q = true → x ≠
    rBooth q) → x ∉ d.support) ∧ RealizesCleanUnitary v
    (p57CleanDiagProj rBooth (411 - 379) (by decide) InvIn) d
    ((((p.onRegister rBooth).toToffCircuit).eval))
theorem N1sDynStep379.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rBooth : QRegister 411 n} {p₁ p₂ : TempPhaseProg 411}
    {d₁ d₂ : DynamicCircuit Var n} {t₁ t₂ : ℕ} {Inv₀ Inv₁ Inv₂ : BitAssignment 411 → Prop}
    (h₁ : N1sDynStep379 v rBooth p₁ d₁ t₁ Inv₀ Inv₁)
    (h₂ : N1sDynStep379 v rBooth p₂ d₂ t₂ Inv₁ Inv₂) : N1sDynStep379 v rBooth (.seq p₁ p₂)
    (.seq d₁ d₂) (t₁ + t₂) Inv₀ Inv₂ := by
  obtain ⟨hp₁, hcT₁, hcToff₁, hPr₁, hSup₁, hR₁⟩ := h₁
  obtain ⟨hp₂, hcT₂, hcToff₂, hPr₂, hSup₂, hR₂⟩ := h₂
  have hSeq := RealizesCleanUnitary_seq_asym
      (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) Inv₀)
      (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) Inv₁) hR₁ hR₂
      (p57SeqClean_prog_inv rBooth p₁ (by decide) (by decide) (fun γ hcr hi ↦ ⟨(hp₁.2 γ
      hcr).2.1, (hp₁.2 γ hcr).2.2.2 hi⟩))
  have hMul : (((p₂.onRegister rBooth).toToffCircuit).eval) *
      (((p₁.onRegister rBooth).toToffCircuit).eval) =
      ((((TempPhaseProg.seq p₁ p₂).onRegister rBooth).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul] at hSeq
  refine ⟨hp₁.seq hp₂,
    by rw [n1s_dyn_count_seq, hcT₁, hcT₂],
    by rw [n1s_dyn_count_seq, hcToff₁, hcToff₂],
    PreservesStoreConst.seq hPr₁ hPr₂,
    fun x hx ↦ by
      simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
      exact ⟨hSup₁ x hx, hSup₂ x hx⟩,
    hSeq⟩
theorem N1sDynStep379.congr_in {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rBooth : QRegister 411 n} {p : TempPhaseProg 411}
    {d : DynamicCircuit Var n} {tCount : ℕ} {Inv₀ Inv₀' Inv₁ : BitAssignment 411 → Prop}
    (h : N1sDynStep379 v rBooth p d tCount Inv₀ Inv₁) (hImp : ∀ β : BitAssignment 411,
    cleanRem 411 (411 - 379) β → Inv₀' β → Inv₀ β) : N1sDynStep379 v rBooth p d tCount Inv₀'
    Inv₁ := by
  obtain ⟨hp, hcT, hcToff, hPr, hSup, hR⟩ := h
  refine ⟨hp.congr_in hImp, hcT, hcToff, hPr, hSup, RealizesCleanUnitary.mono_proj
    (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) Inv₀)
    (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) Inv₀')
    (p57CleanDiagProj_mono rBooth (by decide) (by decide) le_rfl hImp) hR⟩
theorem n1s_dynStep379_realizes_prefixRev (t : Norm1sTier) (m : ℕ) (hm : m ≤ t.kBits)
    (hm_ne1 : t.dCut = 18 → m ≠ 1) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rBooth : QRegister 411 n} {p : TempPhaseProg 411}
    {d : DynamicCircuit Var n} {tCount : ℕ} (hStep : N1sDynStep379 v rBooth p d tCount
    (n1sBoothInv t m) (fun β ↦ ∀ k : Fin 32, β (n1sOut32W411 k) = 0)) : RealizesCleanUnitary v
    (p57CleanDiagProj rBooth (411 - 379) (by decide) (n1sBoothInv t m)) d
    ((((n1sBoothPrefixRevStatic t m hm).onRegister rBooth).toToffCircuit).eval) := by
  obtain ⟨⟨_, hEvOpt⟩, _, _, _, _, hReal⟩ := hStep
  obtain ⟨_, hEvOrig⟩ := n1s_boothPrefixRev_spec t m hm
  refine p57Realizes_congr_prog v rBooth (411 - 379) (by decide) (n1sBoothInv t m) p
    (n1sBoothPrefixRevStatic t m hm) d hReal
    (fun β hβ _ ↦ ((hEvOpt β hβ).1).trans ((hEvOrig β hβ).1).symm) (fun β hβ hInvm ↦ ?_)
  obtain ⟨_, _, hnonOpt, hvalOpt⟩ := hEvOpt β hβ
  obtain ⟨_, _, hnonOrig, hvalOrig⟩ := hEvOrig β hβ
  have hzOpt := hvalOpt hInvm
  have hInv0 := hvalOrig hm_ne1 hInvm
  have hbits0 : bitsVal (fun k : Fin 32 ↦
    (n1sBoothPrefixRevStatic t m hm).evalBits β (n1sOut32W411 k)) =
      bitsVal (fun _ : Fin 32 ↦ (0 : ZMod 2)) := by
    simpa [n1sBoothInv, norm1sHwRowsAux, bitsVal] using hInv0
  have hzOrig := congrFun (bitsVal_injective hbits0)
  funext q
  by_cases hq : ∃ k : Fin 32, q = n1sOut32W411 k
  · obtain ⟨k, rfl⟩ := hq
    exact (hzOpt k).trans (hzOrig k).symm
  · exact (hnonOpt q (fun k hk ↦ hq ⟨k, hk⟩)).trans (hnonOrig q (fun k hk ↦ hq ⟨k, hk⟩)).symm
theorem n1s_rowVal_sh18_eq (β : BitAssignment 411) (uW : Wire 411) : norm1sRowVal 18 0
    (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β uW = 1)) = (β uW).val := by
  unfold norm1sRowVal
  rw [ite_eq_left (by decide : 0 < 18), ite_eq_left (rfl : 18 - 0 = 18)]
  rcases bit_cases (β uW) with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide
theorem n1s_rowVal_sh17_eq (dCut r : ℕ) (hr : r < dCut) (hsh : dCut - r = 17)
    (β : BitAssignment 411) (uW : Wire 411) :
    norm1sRowVal dCut r (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β uW = 1)) =
      (β (n1sMantW411 ⟨17, by decide⟩) + (1 + β uW)).val + 2 * (β uW).val := by
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  have hxm : bitsVal (fun j : Fin 1 ↦ β (n1sMantW411 ⟨17 + j.val, by omega⟩)) = mS / 2 ^ 17 :=
    Slot3Norm1s36CoreWideBooth.n1s_mantSlice_bitsVal β 17 1 (by decide)
  rw [bitsVal_fin1] at hxm
  have hm17_div : mS / 2 ^ 17 = (β (n1sMantW411 ⟨17, by decide⟩)).val := hxm.symm
  unfold norm1sRowVal
  rw [ite_eq_left hr, hsh, ite_eq_right (by decide : ¬(17 = 18)), ite_eq_left (by decide : 17 < 18)]
  dsimp only
  change (if decide (β uW = 1) = true then 2 ^ 1 + mS / 2 ^ 17 else 2 ^ 1 - 1 - mS / 2 ^ 17) = _
  rw [hm17_div]
  rcases bit_cases (β (n1sMantW411 ⟨17, by decide⟩)) with hm | hm <;>
    rcases bit_cases (β uW) with hu | hu <;>
    (rw [hm, hu]; decide)
/-! ### `dCut = 17` 5-Row Forward & Reverse Base (`-12 T` Fwd, `-20 T` Rev) -/
theorem zr_dLowRowRev_not_mem_support_step (t : Norm1sTier) (m : ℕ)
    (hm1 : 1 ≤ m) (hmd : m < t.dCut) (hw2 : 2 ≤ 18 - (t.dCut - m))
    {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) :
    x ∉ (n1sDLowRowRev t m hm1 hmd hw2 v rBooth).support := by
  have hb := n1s_tier_bounds t
  dsimp only [n1sDLowRowRev]
  have hu320 : (n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩).val < 320 :=
    lt_trans (n1s_uKW411_range t _).2 (by decide)
  have hsetup := zr_cRowSetup_inBoothDom (n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩) hu320
      (lt_trans hu320 (by decide)) (t.dCut - m) (18 - (t.dCut - m)) (by omega)
  refine zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _
    (zr_dCleanMsbSub_not_mem_support v rBooth x hx (18 - (t.dCut - m)) 383 _
      (by decide) (by omega) _ _ _ _ _ _ _ _ _ _ _ _
      (zr_bLowR_inBoothDom _ _) (zr_accSlice_inBoothDom _ _ _)
      (decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega))) (by decide))
    _ ?_
  dsimp only [ctxCliffAlloc, zrCtxInBoothDom]
  rw [Bool.true_and]
  exact (Bool.and_eq_true _ _).mpr ⟨hsetup, zr_cliff_inv_inBoothDom _ hsetup⟩
theorem n1s_dLowRowRev_chain_prefixRev (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m)
    (hmd : m < t.dCut) (hw2 : 2 ≤ 18 - (t.dCut - m)) (hm_le : m + 1 ≤ t.kBits) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rBooth : QRegister 411 n) {dRest : DynamicCircuit Var n}
    (hPrRest : PreservesStoreConst dRest) (hRRest : RealizesCleanUnitary v (p57CleanDiagProj
    rBooth (411 - 379) (by decide) (n1sBoothInv t m)) dRest ((((n1sBoothPrefixRevStatic t m
    (by omega)).onRegister rBooth).toToffCircuit).eval)) : PreservesStoreConst
    (.seq (n1sDLowRowRev t m hm1 hmd hw2 v rBooth) dRest) ∧ RealizesCleanUnitary v
    (p57CleanDiagProj rBooth (411 - 379) (by decide) (n1sBoothInv t (m + 1)))
    (.seq (n1sDLowRowRev t m hm1 hmd hw2 v rBooth) dRest) ((((n1sBoothPrefixRevStatic t (m +
    1) hm_le).onRegister rBooth).toToffCircuit).eval) := by
  obtain ⟨_, _, hPr1, hR1⟩ := n1s_dLowRowRev_props t m hm1 hmd hw2 v rBooth
  obtain ⟨_, hEv1⟩ := n1s_lowRowRev_spec t m hm1 hmd hw2
  refine ⟨PreservesStoreConst.seq hPr1 hPrRest, ?_⟩
  have hStepEq : n1sBoothPrefixRevStatic t (m + 1) hm_le =
      .seq (n1sLowRowRevStatic t m hm1 hmd hw2) (n1sBoothPrefixRevStatic t m (by omega)) := by
    rcases m with _ | m'
    · omega
    · rcases m' with _ | m''
      · have hd18 : t.dCut ≠ 18 := by omega
        dsimp only [n1sBoothPrefixRevStatic]
        exact dite_eq_right hd18
      · dsimp only [n1sBoothPrefixRevStatic]
        exact dite_eq_left hmd
  rw [hStepEq]
  have hSeq := RealizesCleanUnitary_seq_asym (p57CleanDiagProj_conjTranspose rBooth (411 -
      379) (by decide) (n1sBoothInv t (m + 1))) (p57CleanDiagProj_conjTranspose rBooth (411 -
      379) (by decide) (n1sBoothInv t m)) hR1 hRRest (p57SeqClean_prog_inv rBooth
      (n1sLowRowRevStatic t m hm1 hmd hw2) (by decide) (by decide) (fun γ hcr hi ↦ ⟨(hEv1 γ
      hcr).2.1, ((hEv1 γ hcr).2.2.2 hi).1⟩))
  have hMul : (((n1sBoothPrefixRevStatic t m (by omega)).onRegister rBooth).toToffCircuit).eval *
      (((n1sLowRowRevStatic t m hm1 hmd hw2).onRegister rBooth).toToffCircuit).eval =
      ((((TempPhaseProg.seq (n1sLowRowRevStatic t m hm1 hmd hw2)
        (n1sBoothPrefixRevStatic t m (by omega))).onRegister rBooth).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul] at hSeq
  exact hSeq
end
end Slot3BoothOptAux
end
end Slot3BoothOpt

end QuantumComputation.Specs.StoppingPowerSolution
end
