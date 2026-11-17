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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Keep9Symp14Data
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18LoadSpec
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA

/-!
# Low-Scratch (`25` Scratch, `(88 + 2 * R + 2 * G)` `T`) H-Gadget Symplectic `14`-Plane QROM Loader

Implements a `{Var : Type}`-computable `25`-scratch (`25 ≤ sScr`), `(88 + 2 * R + 2 * G)`-`T`,
`0`-`TOFF` grouped Hadamard-gadget symplectic `14`-plane QROM loader from a `128`-wire one-hot
register (`418 T` on the Keep-9 `optSymp14Plan` witness with `R = 147, G = 18`).

## Mechanism
- **Vanishing top column ANF coefficients**: Every `30`-column parity-extended mask satisfies
  `colMaskAnf col 30 = 0` and `colMaskAnf col 31 = 0`, so every `rcColAff` and Lempel schedule step
  only references the first `29` non-constant `5`-bit ANF monomials (`1 .. 29`).
- **`80-T` `29`-monomial encoder (`24` scratch + `wG`)**: Prepares all `29` degree-`≤ 4` `5`-bit
  monomials across the `5` index wires and `24` scratch wires using `28 T` deterministic W-state
  one-hot expansion on `x₀..x₃`, a `0-T` Mobius CNOT butterfly, and `13` clean AND gates (`52 T`),
  uncomputed in `0 T` via measurement-based uncomputation (`revUncomputeDyn`).
- **`8-T` top-monomial carry-phase fixup**: Evaluates the `m = 30` (`x₁x₂x₃x₄`) and `m = 31`
  (`x₀x₁x₂x₃x₄`) terms of `totPhi P` via two `4-T` temporary AND sandwiches onto `wG`.

## References
- A. Lempel, "Matrix factorization over GF(2) and trace-orthogonal bases of GF(2^n),"
  *SIAM J. Comput.* **4**(2), 175-186 (1975), DOI: 10.1137/0204014.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity,"
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: 10.22331/q-2018-06-18-74.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, "Trading T gates for dirty qubits in state
  preparation and unitary synthesis," *Quantum* **8**, 1375 (2024),
  DOI: 10.22331/q-2024-06-17-1375.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18Bound322HGadgetQrom
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
    QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
    CoherentAlias AliasPrep
  Mobius126OneHot MidReflCtxRetain StepBound148Borrow
  Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 StepAnfAndCoin14Core StepKeep9Symp14Data
  HGadgetSympQrom OptKeep9Symp14Data Inner18Load Inner18HadWSuperLegsA
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GroupUnary (
  RevCompute predProj predProj_conjTranspose
  predProj_idem restrictPred restrictPred_coe)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepOuter8Pi145Outer (
  predProj_mulVec_ket TransRealizes
  EquivRev WSplitValid InvWSplitDet splitRevLoop dWExpandDet1 dWExpandDet1_count_toff
  dWExpandDet1_count_t)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2Folded184Select (
  revComputeDyn revUncomputeDyn
  count_revComputeDyn_toff count_revComputeDyn_t count_revUncomputeDyn_toff count_revUncomputeDyn_t)
open _root_.Function (update update_of_ne update_self update_idem update_eq_self)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit (
  xorWireUnitary xorWireUnitary_mulVec_ket phaseFlipUnitary
  phaseFlipUnitary_mulVec_ket xMeasUnloadWireDyn count_xMeasUnloadWireDyn_toff
  count_xMeasUnloadWireDyn_t wp_xMeasUnloadWireDyn_update_self cleanFinsetProj
  restrictAssertionToCleanFinset restrictAssertionToCleanFinset_coe
  restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM (
  zeroProjOn zeroProjOn_mulVec_ket
  zeroProjOn_conjTranspose bitSign bitSign_add bit_cases basisBits_symm czMaskCircuit
  count_czMaskCircuit_toff count_czMaskCircuit_t ket_czMaskCircuit monoEval monoEval_zero anfCoeffs
  disjoint_image_of_disjointWires)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance instNeZeroTwoPowHg25 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Reversible-Sandwich `WpZeroSet` Lifting & `NoHi29` Variable Support -/

theorem wpZeroSet_equivRev_diag {Var : Type} [Fintype Var] [DecidableEq Var] {N k : ℕ}
    (v : Var) (rZero : QRegister k N) (S_out S_mid : Finset (Wire N))
    (hSub : rZero.image ⊆ S_out) (p : RevCompute N) (encDyn : DynamicCircuit Var N)
    (hEq : EquivRev v (fun β ↦ decide (∀ j : Fin k, β (rZero j) = 0)) p encDyn)
    (hClean : ∀ β : BitAssignment N, (∀ w ∈ S_out, β w = 0) → ∀ w ∈ S_mid, p.fwdBits β w = 0)
    {φ : BitAssignment N → ZMod 2} {mid : DynamicCircuit Var N}
    (hMid : WpZeroSet v S_mid (diagKetUnitary φ) mid) :
    WpZeroSet v S_out (diagKetUnitary (fun β ↦ φ (p.fwdBits β)))
      (.seq encDyn (.seq mid (revUncomputeDyn v p))) := by
  let S_enc : BitAssignment N → Bool := fun β ↦ decide (∀ j : Fin k, β (rZero j) = 0)
  obtain ⟨hval, m, hbij, hfwd⟩ := hEq
  have hEnc : TransRealizes v S_enc (fun γ ↦ S_enc (p.invBits γ)) p.toCircuit.eval encDyn :=
    hbij.to_transRealizes_revCompute p hfwd
  have hDec : TransRealizes v (fun γ ↦ S_enc (p.invBits γ)) S_enc
      p.toCircuit.eval⁻¹ (revUncomputeDyn v p) :=
    TransRealizes.uncomputeDyn v p S_enc hval
  obtain ⟨hEncWpFn, hDecWpFn⟩ :=
    transRealizes_extract_enc_dec v rZero p rfl hval hEnc hDec
  let P_out := zeroProjOn S_out
  let Q_mid := zeroProjOn S_mid
  let P_enc := predProj S_enc
  let P_post := predProj (fun γ ↦ S_enc (p.invBits γ))
  let U_enc := p.toCircuit.eval
  let E_enc := U_enc.1 * P_enc
  let W_out := diagKetUnitary φ
  let G_out := diagKetUnitary (fun β ↦ φ (p.fwdBits β))
  have hSencOfOut {β : BitAssignment N} (h0 : ∀ w ∈ S_out, β w = 0) : S_enc β = true :=
    decide_eq_true fun j ↦ h0 _ (hSub ((rZero.mem_image _).mpr ⟨j, rfl⟩))
  have hPE : P_post * E_enc = E_enc := by
    dsimp only [E_enc]
    rw [hEnc.map_proj, ← Matrix.mul_assoc, predProj_idem]
  have hUinvE : U_enc.1ᴴ * E_enc = P_enc := by
    dsimp only [E_enc]
    rw [← Matrix.mul_assoc, ← star_eq_conjTranspose, U_enc.prop.1, one_mul]
  have hEket {β : BitAssignment N} (hS : S_enc β = true) :
      E_enc.mulVec (SelectSwapQROM.ket β) = SelectSwapQROM.ket (p.fwdBits β) := by
    dsimp only [E_enc]
    rw [← mulVec_mulVec, predProj_mulVec_ket, ite_eq_left hS]
    exact p.toCircuit_mulVec_ket β
  have hGinP : P_enc * ((1 : Operator (2 ^ N)) * P_out) = (1 : Operator (2 ^ N)) * P_out := by
    refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
    simp only [one_mul, ← mulVec_mulVec, P_out, zeroProjOn_mulVec_ket]
    by_cases h0 : ∀ w ∈ S_out, β w = 0
    · rw [ite_eq_left h0, predProj_mulVec_ket, ite_eq_left (hSencOfOut h0)]
    · rw [ite_eq_right h0, mulVec_zero]
  have hGoutP : P_enc * (G_out.1 * P_out) = G_out.1 * P_out := by
    refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
    simp only [← mulVec_mulVec, P_out, zeroProjOn_mulVec_ket]
    by_cases h0 : ∀ w ∈ S_out, β w = 0
    · rw [ite_eq_left h0, diagKetUnitary_mulVec_ket, mulVec_smul, predProj_mulVec_ket,
        ite_eq_left (hSencOfOut h0)]
    · rw [ite_eq_right h0, mulVec_zero, mulVec_zero]
  have hInterIn : E_enc * ((1 : Operator (2 ^ N)) * P_out) =
      (1 : Operator (2 ^ N)) * (Q_mid * (E_enc * P_out)) := by
    refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
    simp only [one_mul, ← mulVec_mulVec, P_out, Q_mid, zeroProjOn_mulVec_ket]
    by_cases h0 : ∀ w ∈ S_out, β w = 0
    · rw [ite_eq_left h0, hEket (hSencOfOut h0), zeroProjOn_mulVec_ket, ite_eq_left (hClean β h0)]
    · rw [ite_eq_right h0, mulVec_zero, mulVec_zero]
  have hInterOut : E_enc * (G_out.1 * P_out) = W_out.1 * (Q_mid * (E_enc * P_out)) := by
    refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
    simp only [← mulVec_mulVec, P_out, Q_mid, zeroProjOn_mulVec_ket]
    by_cases h0 : ∀ w ∈ S_out, β w = 0
    · rw [ite_eq_left h0, diagKetUnitary_mulVec_ket, mulVec_smul, hEket (hSencOfOut h0),
        zeroProjOn_mulVec_ket, ite_eq_left (hClean β h0), diagKetUnitary_mulVec_ket]
    · rw [ite_eq_right h0, mulVec_zero, mulVec_zero, mulVec_zero, mulVec_zero]
  refine ⟨by simp [DynamicCircuit.count, hEnc.toff_zero, hMid.1, hDec.toff_zero],
    fun Θ hΘ σ val ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · simpa only [DynamicCircuit.compile_seq, wp_qSeq] using
      hEnc.update_self _ (hMid.2.1 _ (hDec.update_self Θ hΘ)) σ val
  · funext σ
    apply Subtype.ext
    apply HermitianMat.ext
    let Ψ_dec := wp (revUncomputeDyn v p).compile Θ
    have hΨ_dec : IsVInv14 v Ψ_dec := hDec.update_self Θ hΘ
    have hΨ_mid : IsVInv14 v (wp mid.compile Ψ_dec) := hMid.2.1 Ψ_dec hΨ_dec
    have hMidMat : Q_mid * ((1 : Operator (2 ^ N))ᴴ * (wp mid.compile Ψ_dec σ).1.mat * 1) * Q_mid =
        Q_mid * (W_out.1ᴴ * (Ψ_dec σ).1.mat * W_out.1) * Q_mid := by
      have hv := congrArg (fun x : Observable (Fin (2 ^ N)) ↦ x.1.mat)
        (congrFun (hMid.2.2 Ψ_dec hΨ_dec) σ)
      have hWQ : diagKetUnitary φ = W_out := rfl
      have hQM : zeroProjOn S_mid = Q_mid := rfl
      have hQMH : Q_midᴴ = Q_mid := zeroProjOn_conjTranspose S_mid
      simp only [SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap,
        Observable.conj_coe, HermitianMat.conj_apply_mat, Unitary.coe_star,
        star_eq_conjTranspose, hWQ, hQM, hQMH, Matrix.conjTranspose_conjTranspose] at hv
      simpa only [conjTranspose_one, one_mul, mul_one] using hv
    have hEncRaw : P_enc * (wp encDyn.compile (wp mid.compile Ψ_dec) σ).1.mat * P_enc =
        E_encᴴ * (wp mid.compile Ψ_dec σ).1.mat * E_enc := by
      have hv := congrArg (fun x : Observable (Fin (2 ^ N)) ↦ x.1.mat)
        (congrFun (hEncWpFn (wp mid.compile Ψ_dec) hΨ_mid) σ)
      simp only [restrictPred_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
        HermitianMat.conj_apply_mat, Unitary.coe_star, star_eq_conjTranspose,
        conjTranspose_conjTranspose, predProj_conjTranspose] at hv
      have hPEq : P_enc = predProj (fun β ↦ decide (∀ j : Fin k, β (rZero j) = 0)) := rfl
      rw [← hPEq] at hv
      rw [hv]
      simp only [E_enc, P_enc, U_enc, conjTranspose_mul, predProj_conjTranspose, Matrix.mul_assoc]
    have hUinv : ((p.toCircuit.eval⁻¹ : Unitary (2 ^ N))).1 = U_enc.1ᴴ := by
      simp [U_enc, star_eq_conjTranspose]
    have hDecRaw : P_post * (Ψ_dec σ).1.mat * P_post =
        P_post * (U_enc.1 * (Θ σ).1.mat * U_enc.1ᴴ) * P_post := by
      simpa only [P_post, Ψ_dec, restrictPred_coe, qcWpQAssign, qcQAssignObsMap,
        Observable.conj_coe, HermitianMat.conj_apply_mat, hUinv, Unitary.coe_star,
        star_eq_conjTranspose, conjTranspose_conjTranspose, predProj_conjTranspose] using
        congrArg (fun x : Observable (Fin (2 ^ N)) ↦ x.1.mat) (congrFun (hDecWpFn Θ hΘ) σ)
    have hSeq : wp (encDyn.seq (mid.seq (revUncomputeDyn v p))).compile Θ =
        wp encDyn.compile (wp mid.compile Ψ_dec) := by
      simp only [Ψ_dec, DynamicCircuit.compile_seq, wp_qSeq]
    have hLHS : (SelectSwapQROM.restrictZeroSet
          (wp (encDyn.seq (mid.seq (revUncomputeDyn v p))).compile Θ) S_out σ).1.mat =
        P_out * ((1 : Operator (2 ^ N))ᴴ *
          (wp encDyn.compile (wp mid.compile Ψ_dec) σ).1.mat * 1) * P_out := by
      rw [hSeq]
      simp [P_out, SelectSwapQROM.restrictZeroSet_coe, HermitianMat.conj_apply_mat,
        zeroProjOn_conjTranspose]
    have hRHS : (SelectSwapQROM.restrictZeroSet (qcWpQAssign G_out Θ) S_out σ).1.mat =
        P_out * (G_out.1ᴴ * (Θ σ).1.mat * G_out.1) * P_out := by
      simp [P_out, SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap,
        Observable.conj_coe, HermitianMat.conj_apply_mat, Unitary.coe_star,
        star_eq_conjTranspose, zeroProjOn_conjTranspose]
    rw [hLHS, hRHS]
    exact turnaroundMatrixCalc P_out P_enc P_post Q_mid U_enc.1 E_enc 1 G_out.1 1 W_out.1
      (wp encDyn.compile (wp mid.compile Ψ_dec) σ).1.mat (wp mid.compile Ψ_dec σ).1.mat
      (Ψ_dec σ).1.mat (Θ σ).1.mat (zeroProjOn_conjTranspose _) (zeroProjOn_conjTranspose _)
      (predProj_conjTranspose _) (predProj_conjTranspose _) hPE hUinvE hGinP hGoutP
      hInterIn hInterOut hEncRaw hMidMat hDecRaw

/-- `4-T`, `0-TOFF` temporary-AND `czMaskCircuit` phase sandwich on clean wire `wG`. -/
def andCzMaskDyn {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ wG : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁G : c₁ ≠ wG) (h₂G : c₂ ≠ wG)
    (rHot : QRegister 128 N) (hGH : ∀ c : Fin 128, wG ≠ rHot c)
    (mask : Fin 128 → ZMod 2) : DynamicCircuit Var N :=
  let p := RevCompute.andGate c₁ c₂ wG h₁₂ h₁G h₂G
  .seq (revComputeDyn p)
    (.seq (.circuit (czMaskCircuit wG 128 rHot hGH mask)) (revUncomputeDyn v p))

@[simp] theorem count_andCzMaskDyn_toff {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ wG : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁G : c₁ ≠ wG) (h₂G : c₂ ≠ wG)
    (rHot : QRegister 128 N) (hGH : ∀ c : Fin 128, wG ≠ rHot c) (mask : Fin 128 → ZMod 2) :
    (andCzMaskDyn v c₁ c₂ wG h₁₂ h₁G h₂G rHot hGH mask).count .TOFF = 0 := by
  simp [andCzMaskDyn, DynamicCircuit.count, count_revComputeDyn_toff, count_revUncomputeDyn_toff]

@[simp] theorem count_andCzMaskDyn_t {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ wG : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁G : c₁ ≠ wG) (h₂G : c₂ ≠ wG)
    (rHot : QRegister 128 N) (hGH : ∀ c : Fin 128, wG ≠ rHot c) (mask : Fin 128 → ZMod 2) :
    (andCzMaskDyn v c₁ c₂ wG h₁₂ h₁G h₂G rHot hGH mask).count .T = 4 := by
  simp [andCzMaskDyn, DynamicCircuit.count, count_revComputeDyn_t, count_revUncomputeDyn_t,
    RevCompute.numAnd]

theorem wpZeroSet_andCzMaskDyn {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) (c₁ c₂ wG : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁G : c₁ ≠ wG) (h₂G : c₂ ≠ wG)
    (rHot : QRegister 128 N) (hGH : ∀ c : Fin 128, wG ≠ rHot c)
    (mask : Fin 128 → ZMod 2) (S : Finset (Wire N)) (hwS : wG ∈ S) :
    WpZeroSet v S
      (diagKetUnitary fun γ ↦ (γ c₁ * γ c₂) * ∑ c : Fin 128, mask c * γ (rHot c))
      (andCzMaskDyn v c₁ c₂ wG h₁₂ h₁G h₂G rHot hGH mask) := by
  let p := RevCompute.andGate c₁ c₂ wG h₁₂ h₁G h₂G
  let rZ := QRegister.singleton wG
  have hSub : rZ.image ⊆ S := fun w hw ↦ by
    obtain ⟨i, rfl⟩ := (rZ.mem_image w).mp hw
    simpa [rZ] using hwS
  have hEq : EquivRev v (fun β ↦ decide (∀ j : Fin 1, β (rZ j) = 0)) p (revComputeDyn p) :=
    EquivRev.ofRevCompute v _ p fun β h0 ↦ by
      have hw0 : β wG = 0 := by simpa [rZ] using of_decide_eq_true h0 0
      simp [p, RevCompute.validOn, hw0]
  have hMid : WpZeroSet v ∅
      (diagKetUnitary fun δ ↦ δ wG * ∑ c : Fin 128, mask c * δ (rHot c))
      (.circuit (czMaskCircuit wG 128 rHot hGH mask)) := by
    refine WpZeroSet.congr_unitary
      (WpZeroSet.of_circuit v ∅ (czMaskCircuit wG 128 rHot hGH mask) (by simp)) fun δ _ ↦ ?_
    rw [ket_sdk_eq δ, ket_czMaskCircuit, diagKetUnitary_mulVec_ket]
  have hSand := wpZeroSet_equivRev_diag v rZ S ∅ hSub p (revComputeDyn p) hEq
    (fun _ _ _ hw ↦ nomatch hw) hMid
  refine WpZeroSet.congr_unitary hSand fun β hS0 ↦ ?_
  rw [ket_sdk_eq β, diagKetUnitary_mulVec_ket, diagKetUnitary_mulVec_ket]
  refine congrArg (· • SelectSwapQROM.ket β) (congrArg bitSign ?_)
  dsimp only [p, RevCompute.fwdBits]
  rw [update_self, hS0 wG hwS, zero_add]
  refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun c _ ↦ ?_)
  rw [update_of_ne (hGH c).symm]

attribute [irreducible] andCzMaskDyn

/-- Predicate asserting that `Var157` never uses monomials `29` or `30` (`m = 30, 31`). -/
def NoHi29 : Var157 → Prop
  | .inl _ => True
  | .inr u => u.val < 29

theorem colMaskAnf_eq_col24Anf5 (col : Fin 30 → Bool) : colMaskAnf col = col24Anf5 col := by
  unfold colMaskAnf col24Anf5 col24ZMod5 b2z
  rfl

theorem monoVars_colMaskAnf_29 (col : Fin 30 → Bool) :
    monoVars (colMaskAnf col) 31 le_rfl = monoVars (colMaskAnf col) 29 (by decide) := by
  have hst (f : Fin 32 → ZMod 2) (m : ℕ) (hm : m + 1 ≤ 31) (hz : f ⟨m + 1, by omega⟩ = 0) :
      monoVars f (m + 1) hm = monoVars f m (Nat.le_of_succ_le hm) := by
    conv_lhs => unfold monoVars
    have hb : z2b (f ⟨m + 1, by omega⟩) = false := by
      rw [hz]
      rfl
    rw [hb]
    rfl
  rw [colMaskAnf_eq_col24Anf5, hst _ 30 le_rfl (col24Anf5_31 col),
    hst _ 29 (by decide) (col24Anf5_30 col)]

theorem noHi29_rowVars (row : Fin 126 → Bool) :
    ∀ (m : ℕ) (hm : m ≤ 126) {v : Var157}, v ∈ rowVars row m hm → NoHi29 v
  | 0, _, _, hv => nomatch hv
  | m + 1, hm, v, hv => by
      dsimp only [rowVars] at hv
      by_cases hr : row ⟨m, hm⟩
      · rw [ite_eq_left hr] at hv
        rcases List.mem_cons.mp hv with rfl | htl
        · trivial
        · exact noHi29_rowVars row m (Nat.le_of_succ_le hm) htl
      · rw [ite_eq_right hr] at hv
        exact noHi29_rowVars row m (Nat.le_of_succ_le hm) hv

theorem noHi29_monoVars (colAnf : Fin 32 → ZMod 2) :
    ∀ (m : ℕ) (_hm29 : m ≤ 29) (hm31 : m ≤ 31) {v : Var157}, v ∈ monoVars colAnf m hm31 → NoHi29 v
  | 0, _, _, _, hv => nomatch hv
  | m + 1, hm29, hm31, v, hv => by
      dsimp only [monoVars] at hv
      by_cases hc : z2b (colAnf ⟨m + 1, by omega⟩)
      · rw [ite_eq_left hc] at hv
        rcases List.mem_cons.mp hv with rfl | htl
        · exact hm29
        · exact noHi29_monoVars colAnf m (Nat.le_of_succ_le hm29) (Nat.le_of_succ_le hm31) htl
      · rw [ite_eq_right hc] at hv
        exact noHi29_monoVars colAnf m (Nat.le_of_succ_le hm29) (Nat.le_of_succ_le hm31) hv

theorem noHi29_rcColAff (row : Fin 126 → Bool) (col : Fin 30 → Bool) :
    ∀ {v : Var157}, v ∈ (rcColAff row col).2 → NoHi29 v := by
  intro v hv
  dsimp only [rcColAff] at hv
  rw [monoVars_colMaskAnf_29] at hv
  rcases List.mem_append.mp hv with h1 | h2
  · exact noHi29_rowVars row 126 le_rfl h1
  · exact noHi29_monoVars (colMaskAnf col) 29 le_rfl (by decide) h2

theorem noHi29_togVar {v : Var157} (hv : NoHi29 v) :
    ∀ {l : List Var157}, (∀ x ∈ l, NoHi29 x) → ∀ y ∈ togVar v l, NoHi29 y
  | [], _, y, hy => by
      rcases List.mem_singleton.mp hy with rfl
      exact hv
  | x :: xs, hl, y, hy => by
      dsimp only [togVar] at hy
      by_cases h : v = x
      · rw [ite_eq_left h] at hy
        exact hl y (List.mem_cons.mpr (Or.inr hy))
      · rw [ite_eq_right h] at hy
        rcases List.mem_cons.mp hy with rfl | hys
        · exact hl y (List.mem_cons.mpr (Or.inl rfl))
        · exact noHi29_togVar hv (fun z hz ↦ hl z (List.mem_cons.mpr (Or.inr hz))) y hys

theorem noHi29_xorLin :
    ∀ {l1 l2 : List Var157}, (∀ x ∈ l1, NoHi29 x) → (∀ x ∈ l2, NoHi29 x) →
      ∀ y ∈ xorLin l1 l2, NoHi29 y
  | [], _, _, hl2 => hl2
  | x :: _, _, hl1, hl2 =>
      noHi29_togVar (hl1 x (List.mem_cons.mpr (Or.inl rfl)))
        (noHi29_xorLin (fun z hz ↦ hl1 z (List.mem_cons.mpr (Or.inr hz))) hl2)

theorem noHi29_xorAff {a b : AffForm Var157} (ha : ∀ x ∈ a.2, NoHi29 x)
    (hb : ∀ x ∈ b.2, NoHi29 x) : ∀ y ∈ (xorAff a b).2, NoHi29 y :=
  noHi29_xorLin ha hb

theorem noHi29_posTail :
    ∀ {pref : AffForm Var157} {ps : List (AffPair Var157)},
      (∀ x ∈ pref.2, NoHi29 x) → (∀ p ∈ ps, (∀ x ∈ p.1.2, NoHi29 x) ∧ ∀ x ∈ p.2.2, NoHi29 x) →
      ∀ st ∈ posTail pref ps, ∀ y ∈ st.2, NoHi29 y
  | _, [], _, _, _, hst => nomatch hst
  | pref, (u, v) :: ps, hpr, hps, st, hst => by
      obtain ⟨hu, hv⟩ := hps (u, v) (List.mem_cons.mpr (Or.inl rfl))
      rcases List.mem_cons.mp hst with rfl | htl
      · exact noHi29_xorAff (noHi29_xorAff hpr hu) hv
      · exact noHi29_posTail (noHi29_xorAff hpr hu)
          (fun p hp ↦ hps p (List.mem_cons.mpr (Or.inr hp))) st htl

theorem noHi29_negTail :
    ∀ {pref : AffForm Var157} {ps : List (AffPair Var157)},
      (∀ x ∈ pref.2, NoHi29 x) → (∀ p ∈ ps, (∀ x ∈ p.1.2, NoHi29 x) ∧ ∀ x ∈ p.2.2, NoHi29 x) →
      ∀ st ∈ negTail pref ps, ∀ y ∈ st.2, NoHi29 y
  | _, [], _, _, _, hst => nomatch hst
  | pref, (u, v) :: ps, hpr, hps, st, hst => by
      obtain ⟨hu, hv⟩ := hps (u, v) (List.mem_cons.mpr (Or.inl rfl))
      rcases List.mem_cons.mp hst with rfl | htl
      · exact noHi29_xorAff hpr hv
      · exact noHi29_negTail (noHi29_xorAff hpr hu)
          (fun p hp ↦ hps p (List.mem_cons.mpr (Or.inr hp))) st htl

theorem noHi29_sumU {pref : AffForm Var157} {ps : List (AffPair Var157)}
    (hpr : ∀ x ∈ pref.2, NoHi29 x)
    (hps : ∀ p ∈ ps, (∀ x ∈ p.1.2, NoHi29 x) ∧ ∀ x ∈ p.2.2, NoHi29 x) :
    ∀ y ∈ (sumU pref ps).2, NoHi29 y := by
  induction ps generalizing pref with
  | nil => exact hpr
  | cons hd tl ih =>
      exact ih (noHi29_xorAff hpr (hps hd (List.mem_cons.mpr (Or.inl rfl))).1)
        (fun p hp ↦ hps p (List.mem_cons.mpr (Or.inr hp)))

theorem noHi29_dFrom :
    ∀ {prev : AffForm Var157} {ts : List (AffForm Var157)},
      (∀ x ∈ prev.2, NoHi29 x) → (∀ t ∈ ts, ∀ x ∈ t.2, NoHi29 x) →
      ∀ st ∈ dFrom prev ts, ∀ y ∈ st.2, NoHi29 y
  | _, [], _, _, _, hst => nomatch hst
  | _, t :: ts, hpr, hts, st, hst => by
      have ht := hts t (List.mem_cons.mpr (Or.inl rfl))
      rcases List.mem_cons.mp hst with rfl | htl
      · exact noHi29_xorAff hpr ht
      · exact noHi29_dFrom ht (fun s hs ↦ hts s (List.mem_cons.mpr (Or.inr hs))) st htl

theorem noHi29_lastFrom {prev : AffForm Var157} {ts : List (AffForm Var157)}
    (hpr : ∀ x ∈ prev.2, NoHi29 x) (hts : ∀ t ∈ ts, ∀ x ∈ t.2, NoHi29 x) :
    ∀ y ∈ (lastFrom prev ts).2, NoHi29 y := by
  induction ts generalizing prev with
  | nil => exact hpr
  | cons t ts ih =>
      exact ih (hts t (List.mem_cons.mpr (Or.inl rfl)))
        (fun s hs ↦ hts s (List.mem_cons.mpr (Or.inr hs)))

theorem noHi29_affPairs {R G : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) :
    ∀ p ∈ P.affPairs g, (∀ x ∈ p.1.2, NoHi29 x) ∧ ∀ x ∈ p.2.2, NoHi29 x := by
  intro p hp
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
  exact ⟨fun _ hx ↦ noHi29_rcColAff _ _ hx, fun _ hx ↦ noHi29_rcColAff _ _ hx⟩

theorem noHi29_lempelSch {R G : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) :
    let sch := lempelSch (P.affPairs g)
    (∀ st ∈ sch.1, ∀ v ∈ st.2, NoHi29 v) ∧
      (∀ st ∈ sch.2.1, ∀ v ∈ st.2, NoHi29 v) ∧
      (∀ v ∈ sch.2.2.2, NoHi29 v) := by
  have hz : ∀ x ∈ (zeroAff : AffForm Var157).2, NoHi29 x := fun _ hx ↦ nomatch hx
  have hp := noHi29_affPairs P g
  have hpTgts : ∀ t ∈ (zeroAff :: posTail zeroAff (P.affPairs g)), ∀ x ∈ t.2, NoHi29 x := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | htl
    · exact hz
    · exact noHi29_posTail hz hp t htl
  have hnTgts : ∀ t ∈ (sumU zeroAff (P.affPairs g) :: negTail zeroAff (P.affPairs g)),
      ∀ x ∈ t.2, NoHi29 x := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | htl
    · exact noHi29_sumU hz hp
    · exact noHi29_negTail hz hp t htl
  have hLast1 := noHi29_lastFrom hz hpTgts
  exact ⟨noHi29_dFrom hz hpTgts, noHi29_dFrom hLast1 hnTgts, noHi29_lastFrom hLast1 hnTgts⟩

theorem evLin_eq_of_mem {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ v ∈ l, f v = g v) → evLin f l = evLin g l
  | [], _ => rfl
  | x :: xs, h => by
      simp only [evLin, h x (List.mem_cons.mpr (Or.inl rfl)),
        evLin_eq_of_mem fun z hz ↦ h z (List.mem_cons.mpr (Or.inr hz))]

theorem evStep_eq_of_mem {α : Type} {f g : α → Bool} {st : AffForm α}
    (h : ∀ v ∈ st.2, f v = g v) : evStep f st = evStep g st := by
  simp only [evStep, evLin_eq_of_mem h]

theorem runSignG_eq_of_mem (neg : Bool) {α : Type} {f g : α → Bool} :
    ∀ {sts : List (AffForm α)} (acc : Bool) (s : Bool × Bool × Bool),
      (∀ st ∈ sts, ∀ v ∈ st.2, f v = g v) → runSignG neg f sts acc s = runSignG neg g sts acc s
  | [], _, _, _ => rfl
  | st :: sts, acc, s, h => by
      simp only [runSignG, evStep_eq_of_mem (h st (List.mem_cons.mpr (Or.inl rfl))),
        runSignG_eq_of_mem neg _ _ fun t ht ↦ h t (List.mem_cons.mpr (Or.inr ht))]

theorem evalHGad_eq_of_mem {α : Type} {f g : α → Bool}
    {ps ns : List (AffForm α)} {uc : Bool} {ul : List α}
    (hps : ∀ st ∈ ps, ∀ v ∈ st.2, f v = g v) (hns : ∀ st ∈ ns, ∀ v ∈ st.2, f v = g v)
    (hul : ∀ v ∈ ul, f v = g v) :
    evalHGad f ps ns uc ul = evalHGad g ps ns uc ul := by
  simp only [evalHGad, runSignG_eq_of_mem false _ _ hps, runSignG_eq_of_mem true _ _ hns,
    evStep_eq_of_mem (st := (uc, ul)) hul]

theorem xorPairs_eq_of_mem {α : Type} {f g : α → Bool} :
    ∀ {ps : List (AffPair α)},
      (∀ p ∈ ps, (∀ v ∈ p.1.2, f v = g v) ∧ ∀ v ∈ p.2.2, f v = g v) →
      xorPairs f ps = xorPairs g ps
  | [], _ => rfl
  | (u, v) :: ps, h => by
      obtain ⟨hu, hv⟩ := h (u, v) (List.mem_cons.mpr (Or.inl rfl))
      simp only [xorPairs, evStep_eq_of_mem hu, evStep_eq_of_mem hv,
        xorPairs_eq_of_mem fun p hp ↦ h p (List.mem_cons.mpr (Or.inr hp))]

/-! ## Section 2: `Mid29Layout` & `(8 + 2 * R + 2 * G)`-`T` Diagonal Mid-Body -/

/-- Bundled registers and pairwise non-aliasing proofs for the `29`-monomial diagonal mid-body. -/
structure Mid29Layout (N : ℕ) where
  rHot : QRegister 128 N
  rMono : QRegister 29 N
  wG : Wire N
  rOut : QRegister 14 N
  hHotMono : ∀ c u, rHot c ≠ rMono u
  hHotG : ∀ c, rHot c ≠ wG
  hMonoG : ∀ u, rMono u ≠ wG
  hGOut : ∀ k, wG ≠ rOut k
  hHotOut : ∀ c k, rHot c ≠ rOut k
  hMonoOut : ∀ u k, rMono u ≠ rOut k

/-- Map `Var157` into `(rH, rM : QRegister 29 N)` (mapping unused indices `29, 30` to `rM 0`). -/
def vWire29 {N : ℕ} (rH : QRegister 128 N) (rM : QRegister 29 N) : Var157 → Wire N
  | .inl j => rH ⟨j.val, by omega⟩
  | .inr u => if h : u.val < 29 then rM ⟨u.val, h⟩ else rM 0

/-- Map `Var157` to a typed `CtrlWire N t` disjoint from target `t`. -/
def vCtrl29 {N : ℕ} (rH : QRegister 128 N) (rM : QRegister 29 N) (t : Wire N)
    (hHT : ∀ c : Fin 128, rH c ≠ t) (hMT : ∀ u : Fin 29, rM u ≠ t) : Var157 → CtrlWire N t
  | .inl j => ⟨rH ⟨j.val, by omega⟩, hHT ⟨j.val, by omega⟩⟩
  | .inr u => if h : u.val < 29 then ⟨rM ⟨u.val, h⟩, hMT ⟨u.val, h⟩⟩ else ⟨rM 0, hMT 0⟩

/-- Wire environment `Var157 → Bool` read from `(M.rHot, M.rMono)` on `γ`. -/
def vEnv29 {N : ℕ} (M : Mid29Layout N) (γ : BitAssignment N) : Var157 → Bool :=
  fun v ↦ z2b (γ (vWire29 M.rHot M.rMono v))

theorem v29_upd {N : ℕ} (M : Mid29Layout N) {w : Wire N} (hHot : ∀ c, M.rHot c ≠ w)
    (hMono : ∀ u, M.rMono u ≠ w) (γ : BitAssignment N) (b : ZMod 2) :
    vEnv29 M (update γ w b) = vEnv29 M γ := by
  funext v
  rcases v with j | u
  · exact congrArg z2b (update_of_ne (hHot ⟨j.val, by omega⟩) b γ)
  · dsimp only [vEnv29, vWire29]
    by_cases h : u.val < 29
    · simp only [h, ↓reduceDIte, update_of_ne (hMono ⟨u.val, h⟩) b γ]
    · simp only [h, ↓reduceDIte, update_of_ne (hMono 0) b γ]

theorem ctrl_v29 {N : ℕ} (M : Mid29Layout N) (t : Wire N) (hHot : ∀ c, M.rHot c ≠ t)
    (hMono : ∀ u, M.rMono u ≠ t) (γ : BitAssignment N) :
    (fun c : CtrlWire N t ↦ z2b (γ c.1)) ∘ vCtrl29 M.rHot M.rMono t hHot hMono = vEnv29 M γ := by
  funext x
  rcases x with _ | u
  · rfl
  · dsimp only [Function.comp, vCtrl29, vEnv29, vWire29]
    by_cases h : u.val < 29
    · simp [h]
    · simp [h]

/-- Raw Boolean inner-product bit `s1_g(γ)` of group `g` on `Mid29Layout`. -/
def rgBit29 {R G N : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) (M : Mid29Layout N)
    (γ : BitAssignment N) : Bool :=
  xorPairs (vEnv29 M γ) (P.affPairs g)

/-- Raw Boolean carry bit `s2_g(γ)` of group `g` on `Mid29Layout`. -/
def rgCarry29 {R G N : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) (M : Mid29Layout N)
    (γ : BitAssignment N) : Bool :=
  let sch := lempelSch (P.affPairs g)
  (evalHGad (vEnv29 M γ) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2).2.2.2

/-- Raw diagonal phase of group `g` on `Mid29Layout`. -/
def rgPhase29 {R G N : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) (M : Mid29Layout N)
    (γ : BitAssignment N) : ZMod 2 :=
  b2z (rgCarry29 P g M γ) + b2z (rgBit29 P g M γ) * ∑ k : Fin 14, b2z (P.groupW g k) * γ (M.rOut k)

/-- Compute-and-CZ-fanout circuit of group `g` on `Mid29Layout`. -/
def grpComp29C {R G N : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) (M : Mid29Layout N) :
    Circuit N :=
  let sch := lempelSch (P.affPairs g)
  let emb := vCtrl29 M.rHot M.rMono M.wG M.hHotG M.hMonoG
  Circuit.seq
    (hGadC M.wG (sch.1.map (mapAff emb)) (sch.2.1.map (mapAff emb)) sch.2.2.1 (sch.2.2.2.map emb))
    (czMaskCircuit M.wG 14 M.rOut M.hGOut (fun k ↦ b2z (P.groupW g k)))

/-- `(2 * groupLen g + 2)`-`T` diagonal circuit of group `g` on `Mid29Layout`. -/
def grpStep29D {Var : Type} {R G N : ℕ} (v : Var) (P : HGadgetSymp14Plan R G) (g : Fin G)
    (M : Mid29Layout N) : DynamicCircuit Var N :=
  .seq (.circuit (grpComp29C P g M))
    (xMeasUnloadWireDyn v M.wG (.circuit (andPairsC M.wG ((P.affPairs g).map fun p ↦
      (mapAff (vCtrl29 M.rHot M.rMono M.wG M.hHotG M.hMonoG) p.1,
       mapAff (vCtrl29 M.rHot M.rMono M.wG M.hHotG M.hMonoG) p.2)))))

@[simp] theorem count_grpStep29D_toff {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G)
    (g : Fin G) (M : Mid29Layout N) : (grpStep29D v P g M).count .TOFF = 0 := by
  simp [grpStep29D, grpComp29C, DynamicCircuit.count, count_xMeasUnloadWireDyn_toff]

@[simp] theorem count_grpStep29D_t {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G)
    (g : Fin G) (M : Mid29Layout N) :
    (grpStep29D v P g M).count .T = 2 * P.groupLen g + 2 := by
  have hl := lempel_lens (P.affPairs g)
  have hp : (P.affPairs g).length = P.groupLen g := by simp [HGadgetSymp14Plan.affPairs]
  simp only [grpStep29D, grpComp29C, DynamicCircuit.count, Circuit.count_seq, count_hGadgetCirc_t,
    List.length_map, hl.1, hl.2, hp, count_czMaskCircuit_t, count_xMeasUnloadWireDyn_t,
    count_andPairsCirc_t]
  omega

theorem wpZeroSet_grpStep29D {Var : Type} [Fintype Var] [DecidableEq Var] {R G N : ℕ}
    (v : Var) (P : HGadgetSymp14Plan R G) (g : Fin G) (M : Mid29Layout N)
    (S : Finset (Wire N)) (hwS : M.wG ∈ S) :
    WpZeroSet v S (diagKetUnitary (rgPhase29 P g M)) (grpStep29D v P g M) := by
  let f1 := fun γ ↦ b2z (rgBit29 P g M γ)
  have hf1G : ∀ β b, f1 (update β M.wG b) = f1 β := fun _ _ ↦ by
    simp only [f1, rgBit29, v29_upd M M.hHotG M.hMonoG]
  set U_w := xorWireUnitary M.wG f1 hf1G
  set D_g := diagKetUnitary (rgPhase29 P g M)
  set U_pre := U_w * D_g
  set cComp := grpComp29C P g M
  set emb := vCtrl29 M.rHot M.rMono M.wG M.hHotG M.hMonoG
  set mappedPairs := (P.affPairs g).map fun p ↦ (mapAff emb p.1, mapAff emb p.2)
  set cFix := andPairsC M.wG mappedPairs
  have hCompWp : WpZeroSet v S U_pre (.circuit cComp) := by
    refine WpZeroSet.congr_unitary (WpZeroSet.of_circuit v S cComp (by simp [cComp, grpComp29C]))
      fun γ hS0 ↦ ?_
    have hg0 : γ M.wG = 0 := hS0 M.wG hwS
    obtain ⟨hacc, hs0, hs1⟩ := evalHGad_lempel (vEnv29 M γ) (P.affPairs g)
    set sch := lempelSch (P.affPairs g)
    let pSt := sch.1.map (mapAff emb)
    let nSt := sch.2.1.map (mapAff emb)
    have hevMap : evalHGad (fun c ↦ z2b (γ c.1)) pSt nSt sch.2.2.1 (sch.2.2.2.map emb) =
        evalHGad (vEnv29 M γ) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2 := by
      simpa [pSt, nSt, emb, ctrl_v29] using
        evalHGad_map (fun c ↦ z2b (γ c.1)) emb sch.1 sch.2.1 sch.2.2
    have hlen8 : (pSt.length : ZMod 8) + 7 * (nSt.length : ZMod 8) = 0 := by
      have hl := lempel_lens (P.affPairs g)
      dsimp only [pSt, nSt, sch]
      rw [List.length_map, List.length_map, hl.1, hl.2]
      have h8 (x : ZMod 8) : x + 7 * x = 0 := by
        calc x + 7 * x = 8 * x := by ring
          _ = 0 := by rw [show (8 : ZMod 8) = 0 from rfl, zero_mul]
      exact h8 _
    have hG1 := ket_hGad_zero M.wG pSt nSt sch.2.2.1 (sch.2.2.2.map emb) hlen8 γ hg0
      (by rwa [hevMap]) (by rwa [hevMap])
    rw [hevMap] at hG1
    have hs1_eq : b2z (evalHGad (vEnv29 M γ) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2).2.2.1 = f1 γ :=
      congrArg b2z hs1
    dsimp only [cComp, grpComp29C]
    change (Circuit.seq (hGadC M.wG pSt nSt sch.2.2.1 (sch.2.2.2.map emb))
      (czMaskCircuit M.wG 14 M.rOut
      M.hGOut (fun k ↦ b2z (P.groupW g k)))).eval.1.mulVec (XMeasCircuit.ket γ) = _
    rw [eval_seq_mv, hG1, hs1_eq, mulVec_smul, ket_sdk_eq (update γ M.wG (f1 γ)), ket_czMaskCircuit,
      ← ket_sdk_eq (update γ M.wG (f1 γ)), smul_smul, ← bitSign_add, update_self]
    dsimp only [U_pre, D_g, U_w]
    rw [Submonoid.coe_mul, ← mulVec_mulVec, ket_sdk_eq γ, diagKetUnitary_mulVec_ket, ← ket_sdk_eq γ,
      mulVec_smul, xorWireUnitary_mulVec_ket, hg0, zero_add]
    refine congrArg (· • XMeasCircuit.ket (update γ M.wG (f1 γ))) (congrArg bitSign ?_)
    dsimp only [rgPhase29, rgCarry29, f1, sch]
    refine congrArg₂ (· + ·) rfl (congrArg₂ (· * ·) rfl ?_)
    exact Finset.sum_congr rfl fun k _ ↦ by rw [update_of_ne (M.hGOut k).symm]
  have hFixWp : WpZeroSet v S (phaseFlipUnitary f1) (.circuit cFix) := by
    refine WpZeroSet.congr_unitary (WpZeroSet.of_circuit v S cFix (by simp [cFix])) fun γ hS0 ↦ ?_
    dsimp only [cFix]
    rw [ket_andPairsCirc_zero M.wG mappedPairs γ (hS0 M.wG hwS), phaseFlipUnitary_mulVec_ket]
    refine congrArg (· • XMeasCircuit.ket γ) (congrArg bitSign ?_)
    dsimp only [mappedPairs, emb, f1, rgBit29]
    rw [xorPairs_map, ctrl_v29]
  have hZP : zeroProjOn S = cleanFinsetProj S := by
    unfold zeroProjOn cleanFinsetProj
    congr 1
  have hR2Z (Ψ : Store Var → Observable (Fin (2 ^ N))) :
      SelectSwapQROM.restrictZeroSet Ψ S = restrictAssertionToCleanFinset Ψ S :=
    funext fun σ ↦ Subtype.ext
      (by rw [SelectSwapQROM.restrictZeroSet_coe, restrictAssertionToCleanFinset_coe, hZP])
  refine ⟨count_grpStep29D_toff v P g M, fun Θ _ σ val ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · dsimp only [grpStep29D]
    rw [DynamicCircuit.compile_seq, wp_qSeq, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile (Var := Var)]
    simp only [qcWpQAssign, wp_xMeasUnloadWireDyn_update_self]
  · set Ψ := wp (xMeasUnloadWireDyn v M.wG (.circuit cFix)).compile Θ
    have hΨ : IsVInv14 v Ψ :=
      fun σ val ↦ wp_xMeasUnloadWireDyn_update_self v M.wG (.circuit cFix) Θ σ val
    have hSeq :
        wp (grpStep29D v P g M).compile Θ = wp (DynamicCircuit.circuit cComp).compile Ψ := by
      dsimp only [grpStep29D, cComp, cFix, mappedPairs, emb]
      rw [DynamicCircuit.compile_seq, wp_qSeq]
    rw [hSeq, hCompWp.2.2 Ψ hΨ]
    dsimp only [U_pre]
    rw [← qc_wp_qAssign_comp D_g U_w Ψ]
    have hCommDH : zeroProjOn S * D_g.1ᴴ = D_g.1ᴴ * zeroProjOn S := by
      have hCommD : zeroProjOn S * D_g.1 = D_g.1 * zeroProjOn S := by
        refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
        rw [← mulVec_mulVec, ← mulVec_mulVec, ket_sdk_eq β, zeroProjOn_mulVec_ket]
        dsimp only [D_g]
        rw [diagKetUnitary_mulVec_ket, mulVec_smul, zeroProjOn_mulVec_ket]
        by_cases h0 : ∀ w ∈ S, β w = 0
        · rw [ite_eq_left h0, diagKetUnitary_mulVec_ket]
        · rw [ite_eq_right h0, mulVec_zero, smul_zero]
      simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using (congrArg (·ᴴ) hCommD).symm
    have hMbu := restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn v M.wG S hwS
      f1 hf1G (.circuit cFix) Θ hΘ ((hR2Z _).symm.trans ((hFixWp.2.2 Θ hΘ).trans (hR2Z _)))
    rw [← hR2Z, ← hR2Z] at hMbu
    funext σ
    apply Subtype.ext
    rw [rZero_wp_coe, rZero_wp_coe, hCommDH, ← conj_conj, ← conj_conj,
      ← SelectSwapQROM.restrictZeroSet_coe, ← SelectSwapQROM.restrictZeroSet_coe]
    dsimp only [U_w, Ψ]
    rw [hMbu]

attribute [irreducible] grpComp29C grpStep29D

/-- Loop executing groups `0 .. n - 1` (`n ≤ G`) on `Mid29Layout`. -/
def grpsLoop29D {Var : Type} {R G N : ℕ} (v : Var) (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) :
    (n : ℕ) → n ≤ G → DynamicCircuit Var N
  | 0, _ => .circuit .identity
  | n + 1, hn => .seq (grpsLoop29D v P M n (Nat.le_of_succ_le hn)) (grpStep29D v P ⟨n, hn⟩ M)

@[simp] theorem count_grpsLoop29D_toff {Var : Type} {R G N : ℕ} (v : Var)
    (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) :
    ∀ (n : ℕ) (hn : n ≤ G), (grpsLoop29D v P M n hn).count .TOFF = 0
  | 0, _ => rfl
  | n + 1, hn => by
      simp [grpsLoop29D, count_grpsLoop29D_toff v P M n (Nat.le_of_succ_le hn)]

theorem count_grpsLoop29D_t {Var : Type} {R G N : ℕ} (v : Var) (P : HGadgetSymp14Plan R G)
    (M : Mid29Layout N) :
    ∀ (n : ℕ) (hn : n ≤ G), (grpsLoop29D v P M n hn).count .T = 2 * prefLen P.groupLen n hn + 2 * n
  | 0, _ => rfl
  | n + 1, hn => by
      simp only [grpsLoop29D, DynamicCircuit.count, count_grpStep29D_t,
        count_grpsLoop29D_t v P M n (Nat.le_of_succ_le hn), prefLen]
      omega

/-- Raw prefix XOR of groups `0 .. n - 1` (`n ≤ G`) on plane `k` at `γ`. -/
def rGrps29P {R G N : ℕ} (P : HGadgetSymp14Plan R G) (k : Fin 14) (M : Mid29Layout N)
    (γ : BitAssignment N) : (n : ℕ) → n ≤ G → Bool
  | 0, _ => false
  | n + 1, hn =>
      xor (rGrps29P P k M γ n (Nat.le_of_succ_le hn))
        (P.groupW ⟨n, hn⟩ k && rgBit29 P ⟨n, hn⟩ M γ)

/-- Raw prefix carry phase `∑_{i < n} b2z (rgCarry29 i)` (`n ≤ G`). -/
def rCarry29P {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) (γ : BitAssignment N) :
    (n : ℕ) → n ≤ G → ZMod 2
  | 0, _ => 0
  | n + 1, hn => rCarry29P P M γ n (Nat.le_of_succ_le hn) + b2z (rgCarry29 P ⟨n, hn⟩ M γ)

theorem wpZeroSet_grpsLoop29D {Var : Type} [Fintype Var] [DecidableEq Var] {R G N : ℕ}
    (v : Var) (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) (S : Finset (Wire N))
    (hwS : M.wG ∈ S) :
    ∀ (n : ℕ) (hn : n ≤ G),
      WpZeroSet v S (diagKetUnitary fun γ ↦
        rCarry29P P M γ n hn + ∑ k : Fin 14, γ (M.rOut k) * b2z (rGrps29P P k M γ n hn))
        (grpsLoop29D v P M n hn)
  | 0, _ => by
      rw [grpsLoop29D]
      refine WpZeroSet.congr_unitary (WpZeroSet.of_circuit v S .identity rfl) fun γ _ ↦ ?_
      rw [Circuit.eval_identity, Submonoid.coe_one, one_mulVec, ket_sdk_eq γ,
        diagKetUnitary_mulVec_ket]
      simp [rCarry29P, rGrps29P, b2z]
  | n + 1, hn => by
      rw [grpsLoop29D]
      have ih := wpZeroSet_grpsLoop29D v P M S hwS n (Nat.le_of_succ_le hn)
      have hStep := wpZeroSet_grpStep29D v P ⟨n, hn⟩ M S hwS
      refine WpZeroSet.congr_unitary (WpZeroSet.seq_diag_left ih hStep) fun γ _ ↦ ?_
      rw [Submonoid.coe_mul, ← mulVec_mulVec, ket_sdk_eq γ, diagKetUnitary_mulVec_ket, mulVec_smul,
        diagKetUnitary_mulVec_ket, diagKetUnitary_mulVec_ket, smul_smul, ← bitSign_add]
      refine congrArg (· • SelectSwapQROM.ket γ) (congrArg bitSign ?_)
      have hSum :
          b2z (rgBit29 P ⟨n, hn⟩ M γ) * ∑ k : Fin 14, b2z (P.groupW ⟨n, hn⟩ k) * γ (M.rOut k) =
          ∑ k : Fin 14,
            γ (M.rOut k) * (b2z (P.groupW ⟨n, hn⟩ k) * b2z (rgBit29 P ⟨n, hn⟩ M γ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      simp only [rgPhase29, rCarry29P, rGrps29P, b2z_xor, b2z_and, mul_add,
        Finset.sum_add_distrib, hSum]
      ring

/-- Raw diagonal bit on plane `k` at `γ` on `Mid29Layout`. -/
def rDiag29B {R G N : ℕ} (P : HGadgetSymp14Plan R G) (k : Fin 14) (M : Mid29Layout N)
    (γ : BitAssignment N) : Bool :=
  evStep (vEnv29 M γ) (rcColAff (P.rowDiag k) (P.colDiag k))

/-- Mapped diagonal affine form on plane `k` on `Mid29Layout`. -/
def diag29Aff {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) (k : Fin 14) :
    AffForm (CtrlWire N (M.rOut k)) :=
  mapAff (vCtrl29 M.rHot M.rMono (M.rOut k) (fun c ↦ M.hHotOut c k) (fun u ↦ M.hMonoOut u k))
    (rcColAff (P.rowDiag k) (P.colDiag k))

/-- `0-T`, `0-TOFF` row + column diagonal `14`-plane CZ loop (`m ≤ 14`) on `Mid29Layout`. -/
def diag29Circ {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) :
    (m : ℕ) → m ≤ 14 → Circuit N
  | 0, _ => .identity
  | m + 1, hm =>
      Circuit.seq (diag29Circ P M m (Nat.le_of_succ_le hm))
        (czStepC (M.rOut ⟨m, hm⟩) (diag29Aff P M ⟨m, hm⟩).1 (diag29Aff P M ⟨m, hm⟩).2)

@[simp] theorem count_diag29Circ_toff {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) :
    ∀ (m : ℕ) (hm : m ≤ 14), (diag29Circ P M m hm).count .TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [diag29Circ, count_diag29Circ_toff P M m (Nat.le_of_succ_le hm)]

@[simp] theorem count_diag29Circ_t {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) :
    ∀ (m : ℕ) (hm : m ≤ 14), (diag29Circ P M m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [diag29Circ, count_diag29Circ_t P M m (Nat.le_of_succ_le hm)]

theorem ket_diag29Circ {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N)
    (γ : BitAssignment N) :
    ∀ (m : ℕ) (hm : m ≤ 14),
      (diag29Circ P M m hm).eval.1.mulVec (XMeasCircuit.ket γ) =
        bitSign (∑ j : Fin m,
          γ (M.rOut ⟨j.val, j.isLt.trans_le hm⟩) *
            b2z (rDiag29B P ⟨j.val, j.isLt.trans_le hm⟩ M γ)) • XMeasCircuit.ket γ
  | 0, _ => by
      rw [diag29Circ, Circuit.eval_identity, Submonoid.coe_one, one_mulVec, Fin.sum_univ_zero,
        bitSign_zero2, one_smul]
  | m + 1, hm => by
      set aff := diag29Aff P M ⟨m, hm⟩
      have hStep := ket_czStep_upd (M.rOut ⟨m, hm⟩) aff.1 aff.2 γ (z2b (γ (M.rOut ⟨m, hm⟩)))
      rw [b2z_z2b, update_eq_self, b2z_and, b2z_z2b] at hStep
      have hAff : evStep (fun c ↦ z2b (γ c.1)) (aff.1, aff.2) = rDiag29B P ⟨m, hm⟩ M γ := by
        change evStep (fun c ↦ z2b (γ c.1)) (diag29Aff P M ⟨m, hm⟩) = _
        dsimp only [diag29Aff]
        rw [evalStep_map, ctrl_v29]
        rfl
      rw [diag29Circ, eval_seq_mv, ket_diag29Circ P M γ m (Nat.le_of_succ_le hm), mulVec_smul,
        hStep, hAff, smul_smul, ← bitSign_add, Fin.sum_univ_castSucc]
      rfl

/-- `0-T` degree-`≤ 4` (`0 .. 29`) sector carry-phase fixup circuit on `Mid29Layout`. -/
def fix029C {N : ℕ} (M : Mid29Layout N) (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2) : Circuit N :=
  hotCtxPhaseLoop 29 128 M.rHot M.rMono M.hHotMono
    (fun c ↦ anfCoeffs 5 (φ c) ⟨0, by decide⟩)
    (fun c u ↦ anfCoeffs 5 (φ c) ⟨u.val + 1, by omega⟩) 128 le_rfl

/-- `8-T`, `0-TOFF` full `32`-monomial sector carry-phase fixup on `Mid29Layout`. -/
def fix29Dyn {Var : Type} {N : ℕ} (v : Var) (M : Mid29Layout N)
    (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2) : DynamicCircuit Var N :=
  .seq (.circuit (fix029C M φ))
    (.seq
      (andCzMaskDyn v (M.rMono ⟨15, by decide⟩) (M.rMono ⟨13, by decide⟩) M.wG
        (M.rMono.wires.injective.ne (by decide)) (M.hMonoG _) (M.hMonoG _) M.rHot
        (fun c ↦ (M.hHotG c).symm) (fun c ↦ anfCoeffs 5 (φ c) ⟨30, by decide⟩))
      (andCzMaskDyn v (M.rMono ⟨15, by decide⟩) (M.rMono ⟨14, by decide⟩) M.wG
        (M.rMono.wires.injective.ne (by decide)) (M.hMonoG _) (M.hMonoG _) M.rHot
        (fun c ↦ (M.hHotG c).symm) (fun c ↦ anfCoeffs 5 (φ c) ⟨31, by decide⟩)))

@[simp] theorem count_fix29Dyn_toff {Var : Type} {N : ℕ} (v : Var) (M : Mid29Layout N)
    (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2) : (fix29Dyn v M φ).count .TOFF = 0 := by
  simp [fix29Dyn, fix029C, DynamicCircuit.count, count_hotCtxPhaseLoop_toff2]

@[simp] theorem count_fix29Dyn_t {Var : Type} {N : ℕ} (v : Var) (M : Mid29Layout N)
    (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2) : (fix29Dyn v M φ).count .T = 8 := by
  simp [fix29Dyn, fix029C, DynamicCircuit.count, count_hotCtxPhaseLoop_t2]

/-- Raw `ZMod 2` phase polynomial evaluated by `fix29Dyn` on `γ`. -/
def rFix29P {N : ℕ} (M : Mid29Layout N) (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2)
    (γ : BitAssignment N) : ZMod 2 :=
  (∑ c : Fin 128, γ (M.rHot c) * (anfCoeffs 5 (φ c) ⟨0, by decide⟩ +
      ∑ u : Fin 29, anfCoeffs 5 (φ c) ⟨u.val + 1, by omega⟩ * γ (M.rMono u))) +
    (γ (M.rMono ⟨15, by decide⟩) * γ (M.rMono ⟨13, by decide⟩)) *
      (∑ c : Fin 128, anfCoeffs 5 (φ c) ⟨30, by decide⟩ * γ (M.rHot c)) +
    (γ (M.rMono ⟨15, by decide⟩) * γ (M.rMono ⟨14, by decide⟩)) *
      (∑ c : Fin 128, anfCoeffs 5 (φ c) ⟨31, by decide⟩ * γ (M.rHot c))

theorem wpZeroSet_fix29Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) (M : Mid29Layout N) (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2)
    (S : Finset (Wire N)) (hwS : M.wG ∈ S) :
    WpZeroSet v S (diagKetUnitary (rFix29P M φ)) (fix29Dyn v M φ) := by
  have h0 : WpZeroSet v S
      (diagKetUnitary fun γ ↦ ∑ c : Fin 128, γ (M.rHot c) *
        (anfCoeffs 5 (φ c) ⟨0, by decide⟩ +
          ∑ u : Fin 29, anfCoeffs 5 (φ c) ⟨u.val + 1, by omega⟩ * γ (M.rMono u)))
      (.circuit (fix029C M φ)) := by
    refine WpZeroSet.congr_unitary
      (WpZeroSet.of_circuit v S (fix029C M φ) (by simp [fix029C, count_hotCtxPhaseLoop_toff2]))
      fun γ _ ↦ ?_
    rw [fix029C, ket_hotCtxPhaseLoop, ket_sdk_eq γ, diagKetUnitary_mulVec_ket]
  have h30 := wpZeroSet_andCzMaskDyn v (M.rMono ⟨15, by decide⟩) (M.rMono ⟨13, by decide⟩) M.wG
    (M.rMono.wires.injective.ne (by decide)) (M.hMonoG _) (M.hMonoG _) M.rHot
    (fun c ↦ (M.hHotG c).symm) (fun c ↦ anfCoeffs 5 (φ c) ⟨30, by decide⟩) S hwS
  have h31 := wpZeroSet_andCzMaskDyn v (M.rMono ⟨15, by decide⟩) (M.rMono ⟨14, by decide⟩) M.wG
    (M.rMono.wires.injective.ne (by decide)) (M.hMonoG _) (M.hMonoG _) M.rHot
    (fun c ↦ (M.hHotG c).symm) (fun c ↦ anfCoeffs 5 (φ c) ⟨31, by decide⟩) S hwS
  rw [fix29Dyn]
  refine WpZeroSet.congr_unitary (WpZeroSet.seq_diag_left h0 (WpZeroSet.seq_diag_left h30 h31))
    fun γ _ ↦ ?_
  simp only [Submonoid.coe_mul, ← mulVec_mulVec, ket_sdk_eq γ, diagKetUnitary_mulVec_ket,
    mulVec_smul, smul_smul, ← bitSign_add]
  refine congrArg (· • SelectSwapQROM.ket γ) (congrArg bitSign ?_)
  dsimp only [rFix29P]
  ring

/-- `(8 + 2 * R + 2 * G)`-`T`, `0-TOFF` diagonal mid-body on `Mid29Layout`. -/
def mid29Dyn {Var : Type} {R G N : ℕ} (v : Var) (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) :
    DynamicCircuit Var N :=
  .seq (grpsLoop29D v P M G le_rfl)
    (.seq (.circuit (diag29Circ P M 14 le_rfl)) (fix29Dyn v M (totPhi P)))

@[simp] theorem count_mid29Dyn_toff {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G)
    (M : Mid29Layout N) : (mid29Dyn v P M).count .TOFF = 0 := by
  simp [mid29Dyn, DynamicCircuit.count]

@[simp] theorem count_mid29Dyn_t {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G)
    (M : Mid29Layout N) : (mid29Dyn v P M).count .T = 8 + 2 * R + 2 * G := by
  simp only [mid29Dyn, DynamicCircuit.count, count_grpsLoop29D_t, pref_sum, P.sum_groupLen,
    count_diag29Circ_t, count_fix29Dyn_t]
  omega

/-- Raw `14`-plane Boolean word on `γ` for `Mid29Layout`. -/
def rMid29W {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N) (γ : BitAssignment N)
    (k : Fin 14) : Bool :=
  xor (rGrps29P P k M γ G le_rfl) (rDiag29B P k M γ)

/-- Raw residual carry-mismatch phase on `γ` for `Mid29Layout`. -/
def rDel29S2 {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N)
    (γ : BitAssignment N) : ZMod 2 :=
  rCarry29P P M γ G le_rfl + rFix29P M (totPhi P) γ

/-- Raw diagonal phase of `mid29Dyn` on `γ`. -/
def rMid29P {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N)
    (γ : BitAssignment N) : ZMod 2 :=
  rDel29S2 P M γ + ∑ k : Fin 14, γ (M.rOut k) * b2z (rMid29W P M γ k)

theorem rawMid29Word_upd {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : Mid29Layout N)
    {w : Wire N} (hHot : ∀ c, M.rHot c ≠ w) (hMono : ∀ u, M.rMono u ≠ w)
    (β : BitAssignment N) (b : ZMod 2) :
    rMid29W P M (update β w b) = rMid29W P M β := by
  funext k
  dsimp only [rMid29W, rDiag29B]
  rw [v29_upd M hHot hMono]
  congr 1
  suffices ∀ n hn, rGrps29P P k M (update β w b) n hn = rGrps29P P k M β n hn from this G le_rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ _ ihm => simp only [rGrps29P, ihm (Nat.le_of_succ_le hn), rgBit29, v29_upd M hHot hMono]

theorem wpZeroSet_mid29Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {R G N : ℕ}
    (v : Var) (P : HGadgetSymp14Plan R G) (M : Mid29Layout N)
    (S : Finset (Wire N)) (hwS : M.wG ∈ S) :
    WpZeroSet v S (diagKetUnitary (rMid29P P M)) (mid29Dyn v P M) := by
  have hLoop := wpZeroSet_grpsLoop29D v P M S hwS G le_rfl
  have hDiag : WpZeroSet v S
      (diagKetUnitary fun γ ↦ ∑ k : Fin 14, γ (M.rOut k) * b2z (rDiag29B P k M γ))
      (.circuit (diag29Circ P M 14 le_rfl)) := by
    refine WpZeroSet.congr_unitary (WpZeroSet.of_circuit v S (diag29Circ P M 14 le_rfl) (by simp))
      fun γ _ ↦ ?_
    rw [ket_diag29Circ P M γ 14 le_rfl, ket_sdk_eq γ, diagKetUnitary_mulVec_ket]
  have hFix := wpZeroSet_fix29Dyn v M (totPhi P) S hwS
  rw [mid29Dyn]
  refine WpZeroSet.congr_unitary
    (WpZeroSet.seq_diag_left hLoop (WpZeroSet.seq_diag_left hDiag hFix))
    fun γ _ ↦ ?_
  simp only [Submonoid.coe_mul, ← mulVec_mulVec, ket_sdk_eq γ, diagKetUnitary_mulVec_ket,
    mulVec_smul, smul_smul, ← bitSign_add]
  refine congrArg (· • SelectSwapQROM.ket γ) (congrArg bitSign ?_)
  simp only [rMid29P, rDel29S2, rMid29W, b2z_xor, mul_add, Finset.sum_add_distrib]
  ring

attribute [irreducible] grpsLoop29D diag29Circ fix029C fix29Dyn mid29Dyn

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18Bound322HGadgetQrom
