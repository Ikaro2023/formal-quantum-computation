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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellRouter57

/-!
# Wire-Trimming Simulation Primitives & Pure `57`-AND `π145` `SELECT` Branch Equations

Provides reusable wire-trimming simulation primitives (`trimLeftReg ..
diagProjSimulates_of_onRegister`) and proves the pure two-body, one-body `SiZero`, and idle branch
identities for `select57PureUnitary`.

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellRouter57Pure
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge Solution.CompactStepFast176Select
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open Solution.LowBitPi145Select
open Solution.ZeroRcHotPrepMid21Fast WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Solution.BellRouter57

/-! ## Section 1: Wire-Trimming Simulation Primitives -/

/-- Direct `m`-wire prefix register inside `m + d` wires (`i ↦ i`). -/
def trimLeftReg (m d : ℕ) : QRegister m (m + d) :=
  ⟨⟨fun i ↦ ⟨i.val, by omega⟩, fun _ _ h ↦ Fin.ext (congrArg (Fin.val : Fin (m + d) → ℕ) h)⟩⟩
/-- Projects a `k`-wire register on `m + d` wires whose image lies `< m` onto `m` wires. -/
def projReg {k m d : ℕ} (r : QRegister k (m + d)) (hr : ∀ i, (r i).val < m) : QRegister k m :=
  ⟨⟨fun i ↦ ⟨(r i).val, hr i⟩,
    fun _ _ h ↦ r.wires.injective (Fin.ext (congrArg (Fin.val : Fin m → ℕ) h))⟩⟩
@[simp] theorem trimLeftReg_apply_val (m d : ℕ) (i : Fin m) :
    (trimLeftReg m d i).val = i.val := rfl
@[simp] theorem projReg_apply_val {k m d : ℕ} (r : QRegister k (m + d))
    (hr : ∀ i, (r i).val < m) (i : Fin k) : (projReg r hr i).val = (r i).val := rfl
@[simp] theorem compose_trimLeftReg_projReg {k m d : ℕ} (r : QRegister k (m + d))
    (hr : ∀ i, (r i).val < m) : (trimLeftReg m d).compose (projReg r hr) = r :=
  CoherentAlias.qreg_ext fun _ ↦ rfl
theorem disj_projReg {k₁ k₂ m d : ℕ} {r₁ : QRegister k₁ (m + d)} {r₂ : QRegister k₂ (m + d)}
    (hr₁ : ∀ i, (r₁ i).val < m) (hr₂ : ∀ j, (r₂ j).val < m) (hd : r₁.DisjointWires r₂) :
    (projReg r₁ hr₁).DisjointWires (projReg r₂ hr₂) :=
  QRegister.disjoint_iff.mpr fun i j h ↦
    QRegister.disjoint_iff.mp hd i j (Fin.ext (congrArg (Fin.val : Fin m → ℕ) h))
/-- Trims a `Circuit (m + d)` supported on wires `< m` onto `m` wires. -/
def trimCircuit (m d : ℕ) : Circuit (m + d) → Circuit m
  | .identity => .identity
  | .gate g r => if hr : ∀ i, (r i).val < m then .gate g (projReg r hr) else .identity
  | .seq c₁ c₂ => .seq (trimCircuit m d c₁) (trimCircuit m d c₂)
/-- Computable check that all gates of a `Circuit (m + d)` act on wires `< m`. -/
def inLeftCircuitB (m d : ℕ) : Circuit (m + d) → Bool
  | .identity => true
  | .gate _ r => decide (∀ i, (r i).val < m)
  | .seq c₁ c₂ => inLeftCircuitB m d c₁ && inLeftCircuitB m d c₂
theorem onRegister_trimLeftReg_trimCircuit (m d : ℕ) (c : Circuit (m + d))
    (h : inLeftCircuitB m d c = true) : (trimCircuit m d c).onRegister (trimLeftReg m d) = c := by
  induction c with
  | identity => rfl
  | gate g r => simp only [inLeftCircuitB, decide_eq_true_eq] at h; simp [trimCircuit, h]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [inLeftCircuitB, Bool.and_eq_true] at h; simp [trimCircuit, ih₁ h.1, ih₂ h.2]
/-- Trims a `DynamicCircuit Var (m + d)` supported on wires `< m` onto `m` wires. -/
def trimDyn {Var : Type} (m d : ℕ) : DynamicCircuit Var (m + d) → DynamicCircuit Var m :=
  DynamicCircuit.qcFold (fun c ↦ .circuit (trimCircuit m d c))
    (fun v r ↦ if hr : ∀ i, (r i).val < m then .measure v (projReg r hr) else .identity)
    DynamicCircuit.qcRawQIf .seq
/-- Computable check that all gates and measurements of a `DynamicCircuit` act on wires `< m`. -/
def inLeftDynB {Var : Type} (m d : ℕ) : DynamicCircuit Var (m + d) → Bool :=
  DynamicCircuit.qcFold (inLeftCircuitB m d) (fun _ r ↦ decide (∀ i, (r i).val < m))
    (fun _ t f ↦ t && f) (fun p₁ p₂ ↦ p₁ && p₂)
theorem onRegister_trimLeftReg_trimDyn {Var : Type} (m d : ℕ) (P : DynamicCircuit Var (m + d))
    (h : inLeftDynB m d P = true) : (trimDyn m d P).onRegister (trimLeftReg m d) = P := by
  induction P using DynamicCircuit.qcInd with
  | circuit c => simp only [inLeftDynB, DynamicCircuit.qcFold_circuit] at h
                 simp [trimDyn, onRegister_trimLeftReg_trimCircuit m d c h]
  | measure v r => simp only [inLeftDynB, DynamicCircuit.qcFold_measure, decide_eq_true_eq] at h
                   simp [trimDyn, h]
  | qIf cond t f iht ihf =>
      simp only [inLeftDynB, DynamicCircuit.qcFold_qIf, Bool.and_eq_true] at h
      rw [trimDyn, DynamicCircuit.qcFold_qIf]
      dsimp only [DynamicCircuit.onRegister]; rw [DynamicCircuit.qcFold_qIf]
      change DynamicCircuit.qcRawQIf cond ((trimDyn m d t).onRegister (trimLeftReg m d))
        ((trimDyn m d f).onRegister (trimLeftReg m d)) = _; rw [iht h.1, ihf h.2]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [inLeftDynB, DynamicCircuit.qcFold_seq, Bool.and_eq_true] at h
      rw [trimDyn, DynamicCircuit.qcFold_seq, DynamicCircuit.onRegister_seq]
      change DynamicCircuit.seq ((trimDyn m d p₁).onRegister (trimLeftReg m d))
        ((trimDyn m d p₂).onRegister (trimLeftReg m d)) = _; rw [ih₁ h.1, ih₂ h.2]
theorem embedMatrix_ketPredProj {m N : ℕ} (r : QRegister m N) (S : BitAssignment m → Prop) :
    r.embedMatrix (ketPredProj S) = ketPredProj (fun β ↦ S (fun i ↦ β (r i))) := by
  classical
  apply OneHotSimulates.matrix_ext_ket; intro β
  rw [OneHotSimulates.embedMatrix_mulVec_ket, ketPredProj_mulVec_ket,
    Finset.sum_eq_single (UnsignedGivens.localIdx r β)]
  · have hb : basisBits m (UnsignedGivens.localIdx r β) = fun i ↦ β (r i) :=
      UnsignedGivens.basisBits_symm_eq (fun i ↦ β (r i))
    have hloc : ketPredProj S (UnsignedGivens.localIdx r β) (UnsignedGivens.localIdx r β) =
        if S (fun i ↦ β (r i)) then 1 else 0 := by simp [ketPredProj, hb]
    have hwr : OneHotSimulates.writeReg β r (basisBits m (UnsignedGivens.localIdx r β)) = β := by
      funext w; by_cases hw : w ∈ Set.range r.wires
      · obtain ⟨i, rfl⟩ := hw; rw [OneHotSimulates.writeReg_apply_reg, congrFun hb i]
      · exact OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hw
    rw [hloc, hwr]; by_cases hS : S (fun i ↦ β (r i)) <;> simp [hS]
  · intro l _ hl; simp [ketPredProj, hl]
  · simp
theorem ketPredProj_le_one {N : ℕ} (S : BitAssignment N → Prop) :
    ketPredProj S * (ketPredProj S)ᴴ ≤ 1 := by
  classical
  have hP : IsDiagProj (ketPredProj S) := ⟨S, rfl⟩
  rw [hP.conjTranspose_eq, hP.mul_self]; change (1 - ketPredProj S).PosSemidef
  have hsub : 1 - ketPredProj S =
      Matrix.diagonal (fun g : Fin (2 ^ N) ↦ if S (basisBits N g) then (0 : ℂ) else 1) := by
    ext i j; by_cases hij : i = j
    · subst hij; by_cases hS : S (basisBits N i) <;> simp [ketPredProj, hS]
    · simp [hij, ketPredProj]
  rw [hsub, Matrix.posSemidef_diagonal_iff]; intro g
  by_cases hS : S (basisBits N g) <;> simp [hS]
theorem diagProjSimulates_onRegister {m N : ℕ} (r : QRegister m N) (S : BitAssignment m → Prop)
    (U : Unitary (2 ^ m)) (p : DynamicCircuit Unit m)
    (hSim : DiagProjSimulates (ketPredProj S) U p) :
    DiagProjSimulates (ketPredProj (fun β ↦ S (fun i ↦ β (r i)))) (r.embedUnitary U)
      (p.onRegister r) := by
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have : NeZero (2 ^ N) := ⟨(Nat.two_pow_pos N).ne'⟩
  let S' (β : BitAssignment N) : Prop := S (fun i ↦ β (r i))
  have hP' : IsDiagProj (ketPredProj S') := ⟨S', rfl⟩
  have hcomm' : (r.embedUnitary U).1 * ketPredProj S' = ketPredProj S' * (r.embedUnitary U).1 := by
    rw [← embedMatrix_ketPredProj, QRegister.embedUnitary_val, ← r.embedMatrix_mul,
      ← r.embedMatrix_mul, hSim.2.1]
  refine ⟨hP', hcomm', fun M ↦ ?_⟩
  let σ₀ : Store Unit := fun _ ↦ 0
  obtain ⟨M', hM'_def⟩ : ∃ M', wp (p.onRegister r).compile (fun _ ↦ M) σ₀ = M' := ⟨_, rfl⟩
  have hwp_const : wp (p.onRegister r).compile (fun _ ↦ M) = fun _ ↦ M' :=
    Solution.CleanDyn.cqAssertion_eq_of_pullbackAssertion_eq r _ _ fun φ hφ ↦ by
      funext σ
      obtain ⟨M_m, hwp_m, _⟩ := hSim.2.2 (Solution.CleanDyn.pullbackObs r φ hφ M)
      have hpb_at (τ : Store Unit) : Solution.CleanDyn.pullbackAssertion r φ hφ
          (wp (p.onRegister r).compile (fun _ ↦ M)) τ = M_m := by
        have h := congrFun (Solution.CleanDyn.pullbackAssertion_wp_onRegister r φ hφ p (fun _ ↦
          M)) τ
        have hconst : Solution.CleanDyn.pullbackAssertion r φ hφ (fun _ : Store Unit ↦ M) =
            fun _ ↦ Solution.CleanDyn.pullbackObs r φ hφ M := rfl
        rw [hconst, hwp_m] at h; exact h
      change Solution.CleanDyn.pullbackAssertion r φ hφ (wp (p.onRegister r).compile (fun _ ↦
        M)) σ =
        Solution.CleanDyn.pullbackObs r φ hφ M'
      rw [hpb_at σ, ← hM'_def]; exact (hpb_at σ₀).symm
  refine ⟨M', hwp_const, ?_⟩
  let K₁ := ketPredProj S'; let K₂ := K₁ * (r.embedUnitary U).1ᴴ
  have hK₁ : K₁ᴴ = K₁ := hP'.conjTranspose_eq
  have hK₂ : K₂ * K₂ᴴ ≤ 1 := by
    dsimp only [K₂, K₁]; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (r.embedUnitary U).1ᴴ,
      unitary_conjTranspose_mul_self_eq, Matrix.one_mul]; exact ketPredProj_le_one S'
  let Θ₁ : QCAssertion Unit (2 ^ N) := fun _ ↦
    ⟨M'.1.conj K₁, M'.1.conj_nonneg K₁ M'.2.1, (HermitianMat.conj_mono M'.2.2).trans
      (HermitianMat.conj_one_le_one K₁ (ketPredProj_le_one S'))⟩
  let Θ₂ : QCAssertion Unit (2 ^ N) := fun _ ↦
    ⟨M.1.conj K₂, M.1.conj_nonneg K₂ M.2.1,
      (HermitianMat.conj_mono M.2.2).trans (HermitianMat.conj_one_le_one K₂ hK₂)⟩
  have hΘ := Solution.CleanDyn.cqAssertion_eq_of_pullbackAssertion_eq r Θ₁ Θ₂ fun φ hφ ↦ by
    funext σ; apply Subtype.ext
    rw [Solution.CleanDyn.pullbackAssertion, Solution.CleanDyn.pullbackAssertion,
      Solution.CleanDyn.pullbackObs_coe, Solution.CleanDyn.pullbackObs_coe]
    change (M'.1.conj K₁).conj (Solution.CleanDyn.envIso r φ)ᴴ =
      (M.1.conj K₂).conj (Solution.CleanDyn.envIso r φ)ᴴ; ext1
    obtain ⟨M_m, hwp_m, hproj_m⟩ := hSim.2.2 (Solution.CleanDyn.pullbackObs r φ hφ M)
    have hMm : (Solution.CleanDyn.pullbackObs r φ hφ M').1.mat = M_m.1.mat := by
      have h := congrFun (Solution.CleanDyn.pullbackAssertion_wp_onRegister r φ hφ p (fun _ ↦ M)) σ₀
      have hconst : Solution.CleanDyn.pullbackAssertion r φ hφ (fun _ : Store Unit ↦ M) =
          fun _ ↦ Solution.CleanDyn.pullbackObs r φ hφ M := rfl
      rw [hconst, hwp_m] at h
      exact congrArg (fun x : Observable (Fin (2 ^ m)) ↦ x.1.mat)
        ((congrArg (Solution.CleanDyn.pullbackObs r φ hφ) hM'_def.symm).trans h)
    have hMm' : (Solution.CleanDyn.envIso r φ)ᴴ * M'.1.mat * Solution.CleanDyn.envIso r φ =
        M_m.1.mat := by
      simpa only [Solution.CleanDyn.pullbackObs_coe, HermitianMat.conj_apply_mat,
        Matrix.conjTranspose_conjTranspose] using hMm
    have hproj_m_mat : ketPredProj S * M_m.1.mat * ketPredProj S =
        ketPredProj S * (U.1ᴴ * ((Solution.CleanDyn.envIso r φ)ᴴ * M.1.mat *
          Solution.CleanDyn.envIso r φ) *
          U.1) * ketPredProj S := by
      have h0 : ketPredProj S * M_m.1.mat * ketPredProj S =
          ketPredProj S * (U.1ᴴ * (Solution.CleanDyn.pullbackObs r φ hφ M).1.mat * U.1) *
            ketPredProj S := hproj_m
      simpa only [Solution.CleanDyn.pullbackObs_coe, HermitianMat.conj_apply_mat,
        Matrix.conjTranspose_conjTranspose] using h0
    have hP_env : K₁ * Solution.CleanDyn.envIso r φ = Solution.CleanDyn.envIso r φ *
        ketPredProj S := by
      dsimp only [K₁, S']; rw [← embedMatrix_ketPredProj]
      exact Solution.CleanDyn.embedMatrix_mul_envIso _ _ _
    have hcP : (Solution.CleanDyn.envIso r φ)ᴴ * K₁ = ketPredProj S *
        (Solution.CleanDyn.envIso r φ)ᴴ := by
      have h := congrArg Matrix.conjTranspose hP_env
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hK₁, hSim.1.conjTranspose_eq] at h
    have hcU : (Solution.CleanDyn.envIso r φ)ᴴ * (r.embedUnitary U).1ᴴ =
        U.1ᴴ * (Solution.CleanDyn.envIso r φ)ᴴ := by
      simpa only [Matrix.conjTranspose_mul, QRegister.embedUnitary_val] using
        congrArg Matrix.conjTranspose (Solution.CleanDyn.embedMatrix_mul_envIso r φ U.1)
    have hU_env : (r.embedUnitary U).1 * Solution.CleanDyn.envIso r φ =
      Solution.CleanDyn.envIso r φ * U.1 :=
      Solution.CleanDyn.embedMatrix_mul_envIso r φ U.1
    have hcU' (X : Matrix (Fin (2 ^ N)) (Fin (2 ^ m)) ℂ) : (Solution.CleanDyn.envIso r φ)ᴴ *
        ((r.embedUnitary U).1ᴴ * X) = U.1ᴴ * ((Solution.CleanDyn.envIso r φ)ᴴ * X) := by
      rw [← Matrix.mul_assoc, hcU, Matrix.mul_assoc]
    have hU' (X : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) : (r.embedUnitary U).1 *
        (Solution.CleanDyn.envIso r φ * X) = Solution.CleanDyn.envIso r φ * (U.1 * X) := by
      rw [← Matrix.mul_assoc, hU_env, Matrix.mul_assoc]
    simp only [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose, K₂,
      Matrix.conjTranspose_mul, hK₁]
    calc (Solution.CleanDyn.envIso r φ)ᴴ * (K₁ * M'.1.mat * K₁) * Solution.CleanDyn.envIso r φ
        = ((Solution.CleanDyn.envIso r φ)ᴴ * K₁) * M'.1.mat * (K₁ *
            Solution.CleanDyn.envIso r φ) := by
            simp only [Matrix.mul_assoc]
      _ = ketPredProj S * ((Solution.CleanDyn.envIso r φ)ᴴ * M'.1.mat *
          Solution.CleanDyn.envIso r φ) *
            ketPredProj S := by rw [hcP, hP_env]; simp only [Matrix.mul_assoc]
      _ = ketPredProj S * (U.1ᴴ * ((Solution.CleanDyn.envIso r φ)ᴴ * M.1.mat *
          Solution.CleanDyn.envIso r φ) *
            U.1) * ketPredProj S := by rw [hMm', hproj_m_mat]
      _ = ((Solution.CleanDyn.envIso r φ)ᴴ * K₁) * (r.embedUnitary U).1ᴴ * M.1.mat *
            (r.embedUnitary U).1 * (K₁ * Solution.CleanDyn.envIso r φ) := by
            rw [hcP, hP_env]; simp only [Matrix.mul_assoc, hcU', hU']
      _ = (Solution.CleanDyn.envIso r φ)ᴴ * (K₁ * (r.embedUnitary U).1ᴴ * M.1.mat *
            ((r.embedUnitary U).1 * K₁)) * Solution.CleanDyn.envIso r φ := by
            simp only [Matrix.mul_assoc]
  have h0 : (Θ₁ σ₀).1.mat = (Θ₂ σ₀).1.mat :=
    congrArg (fun x : Observable (Fin (2 ^ N)) ↦ x.1.mat) (congrFun hΘ σ₀)
  change (M'.1.conj K₁).mat = (M.1.conj K₂).mat at h0
  simp only [HermitianMat.conj_apply_mat, K₂, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hK₁] at h0
  calc ketPredProj S' * M'.1.mat * ketPredProj S'
      = K₁ * M'.1.mat * K₁ := rfl
    _ = (K₁ * (r.embedUnitary U).1ᴴ) * M.1.mat * ((r.embedUnitary U).1 * K₁) := h0
    _ = ketPredProj S' * ((r.embedUnitary U).1ᴴ * M.1.mat * (r.embedUnitary U).1) *
          ketPredProj S' := by dsimp only [K₁]; simp only [Matrix.mul_assoc]
theorem diagProjSimulates_of_onRegister {m N : ℕ} (r : QRegister m N)
    (S_m : BitAssignment m → Prop) (S_N : BitAssignment N → Prop) (U_m : Unitary (2 ^ m))
    (p : DynamicCircuit Unit m)
    (hSimN : DiagProjSimulates (ketPredProj S_N) (r.embedUnitary U_m) (p.onRegister r))
    (hComm_m : U_m.1 * ketPredProj S_m = ketPredProj S_m * U_m.1)
    (hS_iff : ∀ x : Fin (2 ^ m),
      S_N (basisBits N (r.basisSplitEquiv.symm (x, 0))) ↔ S_m (basisBits m x)) :
    DiagProjSimulates (ketPredProj S_m) U_m p := by
  classical
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have : NeZero (2 ^ N) := ⟨(Nat.two_pow_pos N).ne'⟩
  have hPm : IsDiagProj (ketPredProj S_m) := ⟨S_m, rfl⟩
  have hPN : IsDiagProj (ketPredProj S_N) := ⟨S_N, rfl⟩
  let φ₀ : (r.Environment → ZMod 2) → ℂ := Pi.single 0 1
  have hφ₀_sum : (∑ e, Complex.normSq (φ₀ e)) = 1 := by
    rw [Finset.sum_eq_single 0]; · simp [φ₀]
    · intro b _ hb; simp [φ₀, hb]
    · simp
  have hφ₀ : ∑ e, Complex.normSq (φ₀ e) ≤ 1 := hφ₀_sum.le; let V := Solution.CleanDyn.envIso r φ₀
  have hVV : Vᴴ * V = 1 := by
    rw [Solution.CleanDyn.envIso_conjTranspose_mul_self, ← Complex.ofReal_sum, hφ₀_sum,
      Complex.ofReal_one, one_smul]
  have hV_apply (g : Fin (2 ^ N)) (x : Fin (2 ^ m)) :
      V g x = if g = r.basisSplitEquiv.symm (x, 0) then 1 else 0 := by
    have hf := congrFun (r.tensorState_single_factors (r.basisSplitEquiv.symm (x, 0))) g
    have hx : r.extractIndex (r.basisSplitEquiv.symm (x, 0)) = x := by
      rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    have he : (r.basisSplitEquiv (r.basisSplitEquiv.symm (x, 0))).2 = 0 := by
      rw [Equiv.apply_symm_apply]
    rw [hx, he] at hf
    simpa only [V, Solution.CleanDyn.envIso, φ₀, Pi.single_apply, eq_comm] using hf
  have hPV : ketPredProj S_N * V = V * ketPredProj S_m := by
    ext g x; rw [ketPredProj, ketPredProj, Matrix.diagonal_mul, Matrix.mul_diagonal, hV_apply]
    by_cases hg : g = r.basisSplitEquiv.symm (x, 0)
    · subst hg; simp only [↓reduceIte, mul_one, one_mul]; exact if_congr (hS_iff x) rfl rfl
    · simp [hg]
  have hVP : Vᴴ * ketPredProj S_N = ketPredProj S_m * Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, hPN.conjTranspose_eq, hPm.conjTranspose_eq] using
      congrArg Matrix.conjTranspose hPV
  refine ⟨hPm, hComm_m, fun M ↦ ?_⟩
  let M_N := Solution.CleanDyn.embedObservable r M
  have hpb_id : Solution.CleanDyn.pullbackObs r φ₀ hφ₀ M_N = M := by
    apply Subtype.ext; ext1; dsimp only [M_N, V]
    rw [Solution.CleanDyn.pullbackObs_coe, HermitianMat.conj_apply_mat,
      Solution.CleanDyn.embedObservable_mat,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        Solution.CleanDyn.embedMatrix_mul_envIso,
      ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  obtain ⟨M'_N, hwp_N, hproj_N⟩ := hSimN.2.2 M_N
  let M' := Solution.CleanDyn.pullbackObs r φ₀ hφ₀ M'_N
  have hwp_p : wp p.compile (fun _ ↦ M) = fun _ ↦ M' := by
    have hfun : Solution.CleanDyn.pullbackAssertion r φ₀ hφ₀ (fun _ : Store Unit ↦ M_N) = fun _ ↦
      M :=
      funext fun _ ↦ hpb_id
    rw [← hfun, ← Solution.CleanDyn.pullbackAssertion_wp_onRegister r φ₀ hφ₀ p
      (fun _ : Store Unit ↦ M_N), hwp_N]; rfl
  refine ⟨M', hwp_p, ?_⟩
  have hMm_eq : M'.1.mat = Vᴴ * M'_N.1.mat * V := by
    dsimp only [M', V]; rw [Solution.CleanDyn.pullbackObs_coe, HermitianMat.conj_apply_mat,
      Matrix.conjTranspose_conjTranspose]
  have hproj_N_mat : ketPredProj S_N * M'_N.1.mat * ketPredProj S_N =
      ketPredProj S_N * ((r.embedUnitary U_m).1ᴴ * M_N.1.mat * (r.embedUnitary U_m).1) *
        ketPredProj S_N := hproj_N
  have hUV : (r.embedUnitary U_m).1 * V = V * U_m.1 :=
    Solution.CleanDyn.embedMatrix_mul_envIso r φ₀ U_m.1
  have hVU : Vᴴ * (r.embedUnitary U_m).1ᴴ = U_m.1ᴴ * Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, QRegister.embedUnitary_val] using
      congrArg Matrix.conjTranspose hUV
  change ketPredProj S_m * M'.1.mat * ketPredProj S_m =
    ketPredProj S_m * (U_m.1ᴴ * M.1.mat * U_m.1) * ketPredProj S_m
  calc ketPredProj S_m * M'.1.mat * ketPredProj S_m
      = (ketPredProj S_m * Vᴴ) * M'_N.1.mat * (V * ketPredProj S_m) := by
          rw [hMm_eq]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * (ketPredProj S_N * M'_N.1.mat * ketPredProj S_N) * V := by
          rw [← hVP, ← hPV]; simp only [Matrix.mul_assoc]
    _ = (Vᴴ * ketPredProj S_N) * (r.embedUnitary U_m).1ᴴ * r.embedMatrix M.1.mat *
          (r.embedUnitary U_m).1 * (ketPredProj S_N * V) := by
          rw [hproj_N_mat]; simp only [M_N, Solution.CleanDyn.embedObservable_mat, Matrix.mul_assoc]
    _ = ketPredProj S_m * (U_m.1ᴴ * (Vᴴ * (r.embedMatrix M.1.mat * V)) * U_m.1) *
          ketPredProj S_m := by
          rw [hVP, hPV]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Vᴴ (r.embedUnitary U_m).1ᴴ, hVU,
            ← Matrix.mul_assoc (r.embedUnitary U_m).1 V, hUV]
          simp only [Matrix.mul_assoc]
    _ = ketPredProj S_m * (U_m.1ᴴ * M.1.mat * U_m.1) * ketPredProj S_m := by
          rw [Solution.CleanDyn.embedMatrix_mul_envIso, ← Matrix.mul_assoc Vᴴ V, hVV,
            Matrix.one_mul]

/-! ## Section 2: Pure `57`-AND `π145` `SiZero` `SELECT` Unitaries & Branch Action -/

theorem y12OfState2457_ge126_parts (oddPass : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32)
    (si neg : Bool) (h126 : 126 ≤ xo'.val) :
    let y12 := y12OfState24 specA57 (specB57 oddPass) (pack16 xo' so b si neg)
    (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = ctrl10OneBody oddPass xo' si ∧
      y12 10 = so ∧ y12 11 = false := by
  obtain ⟨_, _, _, h1B⟩ := pre3_pack16_2 oddPass xo' so b si neg
  obtain ⟨hw8_0, h15_so, hCanon⟩ := h1B h126
  refine ⟨?_, ?_, ?_⟩
  · funext j; dsimp only [y12OfState24]; rw [dite_eq_left j.isLt]
    dsimp only [specB57, ctrl10OneBody]; rw [ctrl10_mergeMaskPost, hCanon]
  · dsimp only [y12OfState24]; rw [dite_eq_right (by decide), ite_eq_left (by decide)]
    dsimp only [sigSelOfState24, specB57]; exact h15_so
  · dsimp only [y12OfState24]; rw [dite_eq_right (by decide), ite_eq_right (by decide)]
    dsimp only [signBitOfState24]; rw [hw8_0]; rfl

theorem y12OfState2457_of_ge126 (oddPass : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32)
    (si neg : Bool) (h126 : 126 ≤ xo'.val) :
    y12OfState24 specA57 (specB57 oddPass) (pack16 xo' so b si neg) =
      y12OfState24 specA57 (specB57 oddPass) (pack16 xo' so 0 si false) := by
  obtain ⟨hc1, hs1, hp1⟩ := y12OfState2457_ge126_parts oddPass xo' so b si neg h126
  obtain ⟨hc0, hs0, hp0⟩ := y12OfState2457_ge126_parts oddPass xo' so 0 si false h126
  funext j; by_cases hj10 : j.val < 10
  · exact (congrFun hc1 ⟨j.val, hj10⟩).trans (congrFun hc0 ⟨j.val, hj10⟩).symm
  · by_cases hjEq10 : j = 10
    · subst hjEq10; exact hs1.trans hs0.symm
    · have hjEq11 : j = 11 := Fin.ext (by
        have := j.isLt; have : j.val ≠ 10 := fun e ↦ hjEq10 (Fin.ext e); omega)
      subst hjEq11; exact hp1.trans hp0.symm

theorem y12OfState2457_lt126_parts (oddPass : Bool) (xo' : Fin 256) (so : Bool)
    (b : Fin 32) (si neg : Bool) (hxo' : xo'.val < 126) :
    let y12 := y12OfState24 specA57 (specB57 oddPass) (pack16 xo' so b si neg)
    let r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
    (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) =
        ctrl10OfState24 (step24_2 (postB57 oddPass) (twoBodyRIn r b)) ∧
      y12 10 = si ∧ y12 11 = neg := by
  obtain ⟨_, _, h2B, _⟩ := pre3_pack16_2 oddPass xo' so b si neg
  obtain ⟨hw8_0, h15_3, h16_neg, hCanon⟩ := h2B hxo'
  refine ⟨?_, ?_, ?_⟩
  · funext j; dsimp only [y12OfState24]; rw [dite_eq_left j.isLt]; dsimp only [specB57]
    rw [ctrl10_mergeMaskPost, hCanon, twoBodyPostIn_eq_rIn oddPass xo' hxo' b]
  · dsimp only [y12OfState24]; rw [dite_eq_right (by decide), ite_eq_left (by decide)]
    dsimp only [sigSelOfState24, specB57]; exact h15_3
  · dsimp only [y12OfState24]; rw [dite_eq_right (by decide), ite_eq_right (by decide)]
    dsimp only [signBitOfState24]; rw [hw8_0, h16_neg]; rfl

/-- Boolean check on `(r : Fin 9, b32 : Fin 32)` for two-body active bit, row index, and phase. -/
def checkTwoBodyR (oddPass : Bool) (r : Fin 9) (b32 : Fin 32) : Bool :=
  fastWithRun24 (postB57 oddPass) (twoBodyRIn r b32) fun s1 ↦
    let f10 := fastCtrl10 s1
    (bal145ActOf10 actFlip145 f10 == decide (b32.val < 29)) &&
      (!bal145ActOf10 actFlip145 f10 ||
        (bal145RowIdxOf10 (orbitalOfPi14557 oddPass) f10 ==
          ⟨58 + 29 * r.val + min b32.val 28, by have := r.isLt; omega⟩)) &&
      (bal145PhaseOf10 actFlip145 (negMaskPi14557 oddPass) f10 == decide (b32.val < 29))

theorem twoBodyR_even_ok : BlockEncodingCircuit.allPow2 4 0 (fun r ↦
    if hr : r < 9 then BlockEncodingCircuit.allPow2 5 0 (fun b ↦
      if b < 30 then checkTwoBodyR false ⟨r, hr⟩ ⟨b % 32, Nat.mod_lt _ (by decide)⟩ else true)
    else true) = true := by decide +kernel

theorem twoBodyR_odd_ok : BlockEncodingCircuit.allPow2 4 0 (fun r ↦
    if hr : r < 9 then BlockEncodingCircuit.allPow2 5 0 (fun b ↦
      if b < 30 then checkTwoBodyR true ⟨r, hr⟩ ⟨b % 32, Nat.mod_lt _ (by decide)⟩ else true)
    else true) = true := by decide +kernel

theorem twoBodyR_ok (oddPass : Bool) (r : Fin 9) (b : Fin 32) (hb : b.val < 30) :
    checkTwoBodyR oddPass r b = true := by
  have hr4 : r.val < 2 ^ 4 := by have := r.isLt; omega
  have hbr : (⟨b.val % 32, Nat.mod_lt _ (by decide)⟩ : Fin 32) = b :=
    Fin.ext (Nat.mod_eq_of_lt b.isLt)
  cases oddPass
  · have h1 := BlockEncodingCircuit.allPow2_zero_true twoBodyR_even_ok r.val hr4
    rw [dite_eq_left r.isLt] at h1;
      have h2 := BlockEncodingCircuit.allPow2_zero_true h1 b.val b.isLt
    rwa [ite_eq_left hb, hbr] at h2
  · have h1 := BlockEncodingCircuit.allPow2_zero_true twoBodyR_odd_ok r.val hr4
    rw [dite_eq_left r.isLt] at h1;
      have h2 := BlockEncodingCircuit.allPow2_zero_true h1 b.val b.isLt
    rwa [ite_eq_left hb, hbr] at h2

/-- Active predicate on `(oddPass, xo', bit2)` for `126 ≤ xo'.val` under `SiZero`. -/
def oneBodyActive2 (oddPass : Bool) (xo' : Fin 256) (bit2 : Bool) : Bool :=
  (!bit2) && xor (inPass1Pi145Xo xo') (decide (xo'.val < 184) && oddPass)

/-- Boolean check on `(oddPass, xo', bit2)` for `126 ≤ xo'.val` (one-body and `184 ≤ xo'` pad). -/
def checkGe126 (oddPass : Bool) (xo' : Fin 256) (bit2 : Bool) : Bool :=
  fastWithSPre oddPass xo' fun sp ↦
    fastWithRun24 (postB57 oddPass) (ge126PostIn oddPass sp bit2) fun s1 ↦
      let f10 := fastCtrl10 s1; let xo := pi145XoEquiv xo'
      if oneBodyActive2 oddPass xo' bit2 then
        (bal145ActOf10 actFlip145 f10 == true) &&
          (bal145RowIdxOf10 (orbitalOfPi14557 oddPass) f10 == rowIdxOf xo 0) &&
          (bal145PhaseOf10 actFlip145 (negMaskPi14557 oddPass) f10 == negPhaseOf xo 0 1)
      else !bal145ActOf10 actFlip145 f10

theorem ge126_even_ok : BlockEncodingCircuit.allPow2 8 0 (fun q ↦ if 126 ≤ q then
    let xo' : Fin 256 := ⟨q % 256, Nat.mod_lt _ (by decide)⟩
    checkGe126 false xo' false && checkGe126 false xo' true else true) = true := by
  decide +kernel

theorem ge126_odd_ok : BlockEncodingCircuit.allPow2 8 0 (fun q ↦ if 126 ≤ q then
    let xo' : Fin 256 := ⟨q % 256, Nat.mod_lt _ (by decide)⟩
    checkGe126 true xo' false && checkGe126 true xo' true else true) = true := by
  decide +kernel

theorem ge126_ok (oddPass : Bool) (xo' : Fin 256) (h126 : 126 ≤ xo'.val) (bit2 : Bool) :
    checkGe126 oddPass xo' bit2 = true := by
  have hxq : (⟨xo'.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = xo' :=
    Fin.ext (Nat.mod_eq_of_lt xo'.isLt)
  cases oddPass
  · have h1 := BlockEncodingCircuit.allPow2_zero_true ge126_even_ok xo'.val xo'.isLt
    rw [ite_eq_left h126] at h1; dsimp only at h1; rw [hxq, Bool.and_eq_true] at h1
    cases bit2 <;> [exact h1.1; exact h1.2]
  · have h1 := BlockEncodingCircuit.allPow2_zero_true ge126_odd_ok xo'.val xo'.isLt
    rw [ite_eq_left h126] at h1; dsimp only at h1; rw [hxq, Bool.and_eq_true] at h1
    cases bit2 <;> [exact h1.1; exact h1.2]

theorem r57Branch_twoBody (oddPass : Bool) (xo' : Fin 256) (so : Fin 2) (b : Fin 32)
    (si : Fin 2) (neg : Bool) (hk126 : xo'.val < 126) (hb30 : b.val < 30)
    (hBit : neg = negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b) :
    selectGenCoreBranch 0
        (fun m10 ↦ phase2Bal145PhasedBranch actFlip145 (orbitalOfPi14557 oddPass)
          (negMaskPi14557 oddPass) (finOfBits 10 m10))
        (y12OfState24 specA57 (specB57 oddPass)
          (pack16 xo' (decide (so = 1)) b (decide (si = 1)) neg)) =
      selectBranchUnitary (pi145XoEquiv xo') so b si := by
  rw [hBit]; let xo := pi145XoEquiv xo'; let negP := negInPadded (rcBitsOfXo xo) b
  let x16 := pack16 xo' (decide (so = 1)) b (decide (si = 1)) negP
  let y12 := y12OfState24 specA57 (specB57 oddPass) x16
  obtain ⟨hf10, hy10, hy11⟩ :=
    y12OfState2457_lt126_parts oddPass xo' (decide (so = 1)) b (decide (si = 1)) negP hk126
  have hr := twoBodyR_ok oddPass (rDiv14OfRc (rcBitsOfXo xo)) b hb30
  dsimp only [checkTwoBodyR] at hr; rw [fastWithRun24_eq, fastCtrl10_eq] at hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hr; rcases hr with ⟨⟨hc0, hrowR⟩, hphR⟩
  have hpi := pi145XoEquiv_hpi xo' (by omega); have hn58 : ¬ xo.val < 58 := by dsimp [xo]; omega
  have h2b : isOneBodyXo xo = false := decide_eq_false hn58
  have hf10B : (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) =
      ctrl10OfState24 (specB57 oddPass (specA57 x16)) :=
    funext fun j ↦ dite_eq_left j.isLt
  refine y12_bal145_eq_selectBranchUnitary actFlip145 (orbitalOfPi14557 oddPass)
    (negMaskPi14557 oddPass) y12 xo so b si
    (by rw [hf10B]; exact ctrl10_pair8_lt145_2 oddPass x16)
    (by dsimp only [y12, x16]; rw [hf10, hc0]; dsimp [enROf]
        rw [ite_eq_right (by rw [h2b]; decide)])
    (fun hact ↦ ?_)
    (by dsimp only [y12, x16]; rw [hy10]; unfold sigSelOf; rw [ite_eq_right (by rw [h2b]; decide)])
    (by dsimp only [y12, x16]; rw [hy11, hf10, hphR]; dsimp [negPhaseOf]
        rw [ite_eq_right (by rw [h2b]; decide)])
  dsimp only [y12, x16] at hact ⊢; rw [hf10] at hact ⊢; rw [hact] at hrowR
  have hrow : rowIdxOf xo b =
      ⟨58 + 29 * (rDiv14OfRc (rcBitsOfXo xo)).val + min b.val 28,
        by have := (rDiv14OfRc (rcBitsOfXo xo)).isLt; omega⟩ := by
    dsimp [rowIdxOf]; exact dite_eq_right hn58
  exact (by simpa [beq_iff_eq] using hrowR : _ = _).trans hrow.symm

theorem r57Branch_ge126 (oddPass : Bool) (xo' : Fin 256) (so : Fin 2) (b : Fin 32)
    (si : Fin 2) (neg : Bool) (h126 : 126 ≤ xo'.val) :
    selectGenCoreBranch 0
        (fun m10 ↦ phase2Bal145PhasedBranch actFlip145 (orbitalOfPi14557 oddPass)
          (negMaskPi14557 oddPass) (finOfBits 10 m10))
        (y12OfState24 specA57 (specB57 oddPass)
          (pack16 xo' (decide (so = 1)) b (decide (si = 1)) neg)) =
      if oneBodyActive2 oddPass xo' (decide (si = 1)) then
        selectBranchUnitary (pi145XoEquiv xo') so b 1 else 1 := by
  let xo := pi145XoEquiv xo'; let b_4 := decide (si = 1)
  let x16 := pack16 xo' (decide (so = 1)) b b_4 neg
  let y12 := y12OfState24 specA57 (specB57 oddPass) x16
  obtain ⟨hf10, hy10, hy11⟩ :=
    y12OfState2457_ge126_parts oddPass xo' (decide (so = 1)) b b_4 neg h126
  dsimp only [ctrl10OneBody] at hf10
  have hf10B : (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) =
      ctrl10OfState24 (specB57 oddPass (specA57 x16)) :=
    funext fun j ↦ dite_eq_left j.isLt
  have hc := ge126_ok oddPass xo' h126 b_4; dsimp only [checkGe126] at hc
  rw [fastWithSPre_eq, fastWithRun24_eq, fastCtrl10_eq] at hc
  change (if oneBodyActive2 oddPass xo' b_4 then _ else _) = true at hc
  by_cases hAct : oneBodyActive2 oddPass xo' b_4 = true
  · rw [ite_eq_left hAct] at hc ⊢; simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with ⟨⟨hact1, hrow1⟩, hph1⟩
    have hlt184 : xo'.val < 184 := by
      by_contra hge
      have hp1 : inPass1Pi145Xo xo' = false := by
        dsimp only [inPass1Pi145Xo]; exact decide_eq_false (by omega)
      have hd184 : decide (xo'.val < 184) = false := decide_eq_false hge
      simp [oneBodyActive2, hp1, hd184] at hAct
    have hxo58 : xo.val < 58 := pi145XoEquiv_h1B xo' h126 hlt184
    have h1b : isOneBodyXo xo = true := decide_eq_true hxo58
    have hen : enROf xo b 1 = true := by dsimp [enROf]; rw [ite_eq_left h1b]; rfl
    have hrowEq : rowIdxOf xo 0 = rowIdxOf xo b := by
      dsimp [rowIdxOf]; rw [dite_eq_left hxo58, dite_eq_left hxo58]
    have hphEq : negPhaseOf xo 0 1 = negPhaseOf xo b 1 := by
      dsimp [negPhaseOf]; rw [ite_eq_left h1b, ite_eq_left h1b]
    have hsig : sigSelOf xo so 1 = so := by unfold sigSelOf; rw [ite_eq_left h1b]
    refine y12_bal145_eq_selectBranchUnitary actFlip145 (orbitalOfPi14557 oddPass)
      (negMaskPi14557 oddPass) y12 xo so b 1
      (by rw [hf10B]; exact ctrl10_pair8_lt145_2 oddPass x16)
      (by dsimp only [y12, x16]; rw [hf10, hen]; exact hact1)
      (fun _ ↦ by dsimp only [y12, x16]; rw [hf10, hrow1, hrowEq])
      (by dsimp only [y12, x16]; rw [hy10, hsig])
      (by dsimp only [y12, x16]; rw [hy11, hf10, hph1, hphEq]; cases negPhaseOf xo b 1 <;> rfl)
  · simp only [Bool.not_eq_true] at hAct; rw [hAct] at hc ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true'] at hc ⊢
    exact y12_bal145_eq_one_of_act_false actFlip145 (orbitalOfPi14557 oddPass)
      (negMaskPi14557 oddPass) y12
      (by rw [hf10B]; exact ctrl10_pair8_lt145_2 oddPass x16)
      (by dsimp only [y12, x16]; rw [hf10]; exact hc) (by dsimp only [y12, x16]; exact hy11)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellRouter57Pure
end
