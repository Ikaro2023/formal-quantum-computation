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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseWarmR1
/-!
# Terminal `r = 1` CSWAP Symmetry-Filtered Off-Diagonal Stationary-chord Readout
(`CswapWarmR1`)
Upgrades the terminal (`r = 1`, `m = 2`) two-slot readout from uncorrelated per-slot
projective or
cold Stationary-chord search to a zero-query coherent collision + swap-test symmetry filter
followed by
off-diagonal stationary-eigenvector weak-measurement Stationary-chord search:
1. **Zero-query collision & CSWAP symmetry filter (`cswapFilterUnitary`)**:
   Given two slots in `(planeVec A θ₁ ⊗ |0⟩) ⊗ (planeVec A γ ⊗ |0⟩)` (`A = S \ T`, `A.card =
   1`,
   `θ₁ = halfAngleSet n 1`, `θ₁ ≤ γ ≤ 4 / 5`), flags diagonal collisions `x_0 = x_1` onto
   marker
   bit `1` (`o = 2`, exact probability `1 / 2^n`) and splits the off-diagonal subspace `x_0 ≠
   x_1`
   via a flag-`0`-controlled address swap (`H_{b_0} · CSWAP · H_{b_0}`) into:
   - **`o = 1` (antisymmetric `x_0 ≠ x_1`, exact probability `sin²(γ - θ₁) / 2`)**: supported
     exclusively on `oddSet n 2 A`, so a single deflated parallel oracle query + marker
     measurement
     recovers the unique remaining target `x* ∈ A` with probability `1`.
   - **`o = 0` (symmetric `x_0 ≠ x_1`, probability `1 - sin²(γ - θ₁) / 2 - 1 / 2^n`)**:
   collapses
     onto the exact 2D off-diagonal Grover plane `offDiagPlaneVec n A γ_sym` with
     `tan γ_sym ≥ tan γ / √2` and half-step angle `θ_ne = halfAngleSet n 2 = arcsin √(2 /
     2^n)`.
2. **Off-diagonal Stationary-chord ramp + stationary `.qWhile` loop (`o = 0`)**:
   Executes `K_w = ⌈(π / 4 - γ_sym) / (2 * θ_ne)⌉₊` pure unitary off-diagonal Grover steps (`s
   = 1`)
   to reach `β_lock ∈ [π / 4, π / 4 + 2 * θ_ne]`, runs a stationary weak-measurement `.qWhile`
   loop
   at `s_lock = lockedRatio β_lock θ_ne` (`(1 - α²)⁻¹ ≈ √(2^n) / (4√2)`), and extracts `x*` in
   `1`
   final deflated oracle query.
-/
@[expose] public section
@[local simp] private theorem _fin4_mk_eq_zero {v : ℕ} (h : v < 2 ^ 2) : (⟨v, h⟩ : Fin (2 ^ 2)) = 0
  ↔ v = 0 := ⟨fun e => congrArg Fin.val e, fun hv => Fin.ext hv⟩
@[local simp] private theorem _fin4_zero_eq_mk {v : ℕ} (h : v < 2 ^ 2) : (0 : Fin (2 ^ 2)) = ⟨v, h⟩
  ↔ 0 = v := ⟨fun e => congrArg Fin.val e, fun hv => Fin.ext hv⟩
@[local simp] private theorem _tb1_0 : (0 : ℕ).testBit 1 = false := rfl
@[local simp] private theorem _tb1_1 : (1 : ℕ).testBit 1 = false := rfl
@[local simp] private theorem _tb1_2 : (2 : ℕ).testBit 1 = true := rfl
@[local simp] private theorem _tb1_3 : (3 : ℕ).testBit 1 = true := rfl
@[local simp] private theorem _mod2_1 : (1 : ℕ) % 2 = 1 := rfl
@[local simp] private theorem _mod2_3 : (3 : ℕ) % 2 = 1 := rfl
@[local simp] private theorem _f21_0 : (0 : Fin (2 ^ 1)).val = 0 := rfl
@[local simp] private theorem _f21_1 : (1 : Fin (2 ^ 1)).val = 1 := rfl
@[local simp] private theorem _f1_0 : (0 : Fin 1).val = 0 := rfl
@[local simp] private theorem _zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl
@[local simp] private theorem _ba_zero_apply (q : ℕ) (i : Fin q) :
    (0 : BitAssignment q) i = 0 := rfl
@[local simp] private theorem _z2_01 : ((0 : ZMod 2) = 1) ↔ False :=
  ⟨fun h => Nat.zero_ne_one (congrArg Fin.val h), False.elim⟩
@[local simp] private theorem _z2_10 : ((1 : ZMod 2) = 0) ↔ False :=
  ⟨fun h => Nat.one_ne_zero (congrArg Fin.val h), False.elim⟩
namespace QuantumComputation.Specs.GroverFindAll.Warm2
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation
/-! ## 1. Generic Rank-1 Reflection Unitary & Pre/Post Oracle Step Combinator -/
theorem vecProj_mulVec {d : ℕ} (ψ v : Fin d → ℂ) : vecProj ψ *ᵥ v = (star ψ ⬝ᵥ v) • ψ := by
  funext i; simp only [Matrix.mulVec, dotProduct, vecProj_apply, Pi.star_apply, Pi.smul_apply,
    smul_eq_mul]
  calc ∑ j : Fin d, ψ i * star (ψ j) * v j = ψ i * ∑ j : Fin d, star (ψ j) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = (∑ j : Fin d, star (ψ j) * v j) * ψ i := mul_comm _ _
/-- Householder reflection matrix `(2: ℂ) • vecProj ψ - 1` across a unit vector `ψ`. -/
def unitReflectMat {d : ℕ} (ψ : Fin d → ℂ) : Operator d :=
  (2 : ℂ) • vecProj ψ - 1
/-- Bundled unitary `2 |ψ⟩⟨ψ| - I` for any normalized state `star ψ ⬝ᵥ ψ = 1`. -/
noncomputable def unitReflectUnitary {d : ℕ} (ψ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    Unitary d :=
  ⟨unitReflectMat ψ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have hcj : (unitReflectMat ψ)ᴴ = unitReflectMat ψ := by
      dsimp only [unitReflectMat]
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, vecProj_conjTranspose,
        Matrix.conjTranspose_one]
      norm_num
    rw [hcj]
    dsimp only [unitReflectMat]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, vecProj_mul_self hψ]
    ext i j
    change _ = (1 : Matrix (Fin d) (Fin d) ℂ) i j
    by_cases hij : i = j <;>
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hij] <;> ring⟩
theorem unitReflectUnitary_mulVec {d : ℕ} {ψ : Fin d → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (v : Fin d → ℂ) :
  (unitReflectUnitary ψ hψ).1 *ᵥ v = (2 * (star ψ ⬝ᵥ v)) • ψ - v := by
  change ((2 : ℂ) • vecProj ψ - 1) *ᵥ v = _; rw [Matrix.sub_mulVec, Matrix.smul_mulVec,
    vecProj_mulVec, Matrix.one_mulVec, smul_smul]
theorem isRealMatrix_unitReflectUnitary {d : ℕ} {ψ : Fin d → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (hreal : ∀ i,
  (ψ i).im = 0) : IsRealMatrix (unitReflectUnitary ψ hψ).1 := by
  intro i j; change (((2 : ℂ) • vecProj ψ - 1) i j).im = 0; simp only [Matrix.sub_apply,
    Matrix.smul_apply, vecProj_apply, smul_eq_mul, Matrix.one_apply]; have hi := hreal i; have hj :=
    hreal j; by_cases hij : i = j <;> simp [hij, Complex.mul_im, hi, hj]
theorem isRealMatrix_embedUnitary {k n : ℕ} (r : QRegister k n) {U : Unitary (2 ^ k)} (hU :
  IsRealMatrix U.1) : IsRealMatrix (r.embedUnitary U).1 := by
  rw [QRegister.embedUnitary_val]; exact isRealMatrix_embedMatrix r hU
/-- Generic `1`-query circuit sandwiching `.oracle (oracleReg n m k)` between two real local
  unitaries `Upre` and `Upost` via `phaseI`. -/
noncomputable def rawPrePostOracleCircuit {Var : Type} (n m k : ℕ)
    (Upre Upost : Unitary (2 ^ ((n + 1) * m))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (.step (phaseI ((oracleReg n m k).embedUnitary Upre)))
    (.seq (.oracle (oracleReg n m k))
      (.step (phaseI ((oracleReg n m k).embedUnitary Upost))))
theorem zeroStepCost_rawPrePostOracleCircuit {Var : Type} {n m k : ℕ} {Upre Upost : Unitary (2 ^ ((n
  + 1) * m))} (hpre : IsRealMatrix Upre.1) (hpost : IsRealMatrix Upost.1) : ZeroStepCost
  (rawPrePostOracleCircuit (Var := Var) n m k Upre Upost) :=
  ⟨zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _ hpre),
    ⟨trivial, zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _ hpost)⟩⟩
theorem costBound_rawPrePostOracleCircuit {Var : Type} [DecidableEq Var] {n m k : ℕ} {Upre Upost :
  Unitary (2 ^ ((n + 1) * m))} (hpre : IsRealMatrix Upre.1) (hpost : IsRealMatrix Upost.1) (A :
  Finset (Fin (2 ^ n))) : CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A))
  ((rawPrePostOracleCircuit (Var := Var) n m k Upre Upost).compile QProg.qAssign
  (parallelMarkingOracle m A)) 1 := by
  let oracle := parallelMarkingOracle m A
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) oracle
  have hc_pre := costBound_phaseI_step (Var := Var) A ((oracleReg n m k).embedUnitary Upre)
    (isRealMatrix_embedMatrix _ hpre)
  have hc_or : CostBound (Var := Var) model (QProg.qAssign ((oracleReg n m k).embedUnitary oracle))
    1 := by
    have hex : ∃ r : QRegister ((n + 1) * m) (findAllQubits n m k), (oracleReg n m k).embedUnitary
      oracle = r.embedUnitary oracle := ⟨oracleReg n m k, rfl⟩
    have h1 : model.unitaryCost ((oracleReg n m k).embedUnitary oracle) = 1 :=
      (by simp [model, CostModel.ofEmbeddedOracle, hex]); simpa [h1] using CostBound.qAssign (Var :=
      Var) model ((oracleReg n m k).embedUnitary oracle)
  have hc_post := costBound_phaseI_step (Var := Var) A ((oracleReg n m k).embedUnitary Upost)
    (isRealMatrix_embedMatrix _ hpost); simp only [rawPrePostOracleCircuit,
    OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
    OracleDynamicCircuit.compile_oracle]; simpa using CostBound.seq hc_pre (CostBound.seq hc_or
    hc_post)
theorem interp_rawPrePostOracleCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ) (Upre Upost :
  Unitary (2 ^ ((n + 1) * m))) (A : Finset (Fin (2 ^ n))) : interp ((rawPrePostOracleCircuit (Var :=
  Var) n m k Upre Upost).compile QProg.qAssign (parallelMarkingOracle m A)) = interp (QProg.qAssign
  ((oracleReg n m k).embedUnitary (Upost * parallelMarkingOracle m A * Upre))) := by
  apply qMonad_ext; intro Δ; simp only [rawPrePostOracleCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle, interp_qSeq,
    QMonad.Q.toStateFun_bind, interp_qAssign]; change CQState.qAssign (phaseI _) (CQState.qAssign _
    (CQState.qAssign (phaseI _) Δ)) = CQState.qAssign _ Δ; rw [cqState_qAssign_phaseI,
    cqState_qAssign_phaseI, cqState_qAssign_comp, cqState_qAssign_comp]; congr 1; rw [← (oracleReg n
    m k).embedUnitary_mul, ← (oracleReg n m k).embedUnitary_mul, mul_assoc]
theorem wp_rawPrePostOracleCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ) (Upre Upost : Unitary
  (2 ^ ((n + 1) * m))) (A : Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n
    m k)) :
  wp ((rawPrePostOracleCircuit (Var := Var) n m k Upre Upost).compile QProg.qAssign
  (parallelMarkingOracle m A)) Θ = Θ.qAssign ((oracleReg n m k).embedUnitary (Upost *
  parallelMarkingOracle m A * Upre)) := by
  simp only [rawPrePostOracleCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle, wp_qSeq, wp_qAssign,
    qAssign_phaseI]; rw [CQAssertion.qAssign_qAssign, CQAssertion.qAssign_qAssign]; congr 1
  rw [← (oracleReg n m k).embedUnitary_mul, ← (oracleReg n m k).embedUnitary_mul, mul_assoc]
theorem dotProduct_tensorState_pair {k n : ℕ} (r : QRegister k n) (v₁ v₂ : Fin (2 ^ k) → ℂ) (e₁ e₂ :
  (r.Environment → ZMod 2) → ℂ) : star (r.tensorState v₁ e₁) ⬝ᵥ r.tensorState v₂ e₂ = (star v₁ ⬝ᵥ
  v₂) * (star e₁ ⬝ᵥ e₂) := by
  simp only [dotProduct, QRegister.tensorState, Pi.star_apply]
  rw [← r.basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]; simp_rw [←
    QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply, star_mul]; rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ ↦ by ring
/-! ## 2. Two-Slot Coordinate & Environment Lemmas (`m = 2`) -/
/-- Slot `0` of `Fin 2`. -/
abbrev s0 : Fin 2 := 0
/-- Slot `1` of `Fin 2`. -/
abbrev s1 : Fin 2 := 1
theorem fin2_eq_s0_or_s1 (i : Fin 2) : i = s0 ∨ i = s1 := by fin_cases i <;> simp [s0, s1]
theorem localFlagEnvWire_ne (n : ℕ) : localFlagEnvWire n 2 s0 ≠ localFlagEnvWire n 2 s1 := by
  intro heq; have hval := congrArg (fun w ↦ w.1.val) heq; dsimp only [localFlagEnvWire,
    localSlotReg, localMarkerReg, s0, s1] at hval; simp only [QRegister.block_apply_val,
    Fin.val_zero, Fin.val_one] at hval; omega
theorem localAddrEnv_eq_flag0_or_flag1 (n : ℕ) (ew : (localAddrReg n 2).Environment) : ew =
  localFlagEnvWire n 2 s0 ∨ ew = localFlagEnvWire n 2 s1 := by
  rcases ew with ⟨w, hw⟩; have hwlt : w.val < (n + 1) * 2 := w.isLt; generalize hq_def : w.val / (n
    + 1) = q; generalize hr_def : w.val % (n + 1) = r_mod
  have hdiv : q < 2 := hq_def ▸ Nat.div_lt_of_lt_mul (by linarith); have hdm : (n + 1) * q + r_mod =
    w.val := (by rw [← hq_def, ← hr_def]; exact Nat.div_add_mod w.val (n + 1))
  by_cases hrem : r_mod = 0
  · rcases (show q = 0 ∨ q = 1 by omega) with hq0 | hq1
    · left; have hw0 : w.val = 0 := (by rw [hq0, hrem] at hdm; omega)
      apply Subtype.ext; apply Fin.ext; dsimp only [localFlagEnvWire, localSlotReg, localMarkerReg,
        s0]; simp only [QRegister.block_apply_val, Fin.val_zero]; omega
    · right; have hw1 : w.val = n + 1 := (by rw [hq1, hrem] at hdm; omega)
      apply Subtype.ext; apply Fin.ext; dsimp only [localFlagEnvWire, localSlotReg, localMarkerReg,
        s1]; simp only [QRegister.block_apply_val, Fin.val_zero, Fin.val_one]; omega
  · exfalso; have hmod : r_mod < n + 1 := hr_def ▸ Nat.mod_lt w.val (by omega)
    let i : Fin 2 := ⟨q, hdiv⟩; let r : Fin n := ⟨r_mod - 1, by omega⟩
    have hcomm : q * (n + 1) = (n + 1) * q := Nat.mul_comm _ _; apply hw; refine ⟨finProdFinEquiv
      (i, r), ?_⟩; rw [localAddrReg_finProdFinEquiv]; apply Fin.ext; dsimp only [localSlotReg,
      localIdxReg, i, r]; simp only [QRegister.block_apply_val]; omega
/-- Environment assignment on `(localAddrReg n 2).Environment` encoding a 2-bit marker mask
  `o`. -/
def envOfMask (n : ℕ) (o : Fin (2 ^ 2)) (ew : (localAddrReg n 2).Environment) : ZMod 2 :=
  if ew = localFlagEnvWire n 2 s0 then
    if o.val.testBit 0 then 1 else 0
  else
    if o.val.testBit 1 then 1 else 0
@[simp]
theorem envOfMask_zero (n : ℕ) : envOfMask n 0 = 0 := by funext ew; simp [envOfMask]
@[simp]
theorem envOfMask_three (n : ℕ) : envOfMask n ⟨3, by decide⟩ = 1 := by
  funext ew; by_cases h : ew = localFlagEnvWire n 2 s0
  · simp [envOfMask, h]
  · simp only [envOfMask, h, ↓reduceIte, Pi.one_apply]; rfl
theorem envOfMask_s0 (n : ℕ) (o : Fin (2 ^ 2)) : envOfMask n o (localFlagEnvWire n 2 s0) = if
  o.val.testBit 0 then 1 else 0 := by simp [envOfMask]
theorem envOfMask_s1 (n : ℕ) (o : Fin (2 ^ 2)) : envOfMask n o (localFlagEnvWire n 2 s1) = if
  o.val.testBit 1 then 1 else 0 := by simp [envOfMask, (localFlagEnvWire_ne n).symm]
theorem envOfMask_injective (n : ℕ) : Function.Injective (envOfMask n) := by
  intro a b hab; have h0 := congrFun hab (localFlagEnvWire n 2 s0)
  have h1 := congrFun hab (localFlagEnvWire n 2 s1); simp only [envOfMask, ↓reduceIte,
    (localFlagEnvWire_ne n).symm] at h0 h1
  revert h0 h1; fin_cases a <;> fin_cases b <;> simp
theorem basisSplit_snd_eq_envOfMask_iff (n : ℕ) (z : Fin (2 ^ ((n + 1) * 2))) (o : Fin (2 ^ 2)) :
  ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n o ↔ (localAllMarkersReg n 2).extractIndex z
  = o := by
  constructor
  · intro hE; apply (basisBits 2).injective; funext i; rw [QRegister.basisBits_extractIndex,
      localAllMarkersReg_apply, ← (localSlotReg n 2 i).basisBits_extractIndex, ← (localMarkerReg
      n).basisBits_extractIndex]; change basisBits 1 (localSlotFlag n 2 z i) 0 = basisBits 2 o i
    rw [basisBits_localSlotFlag, hE, basisBits_eq_testBit]; fin_cases i
    · simp [envOfMask]
    · simp [envOfMask, (localFlagEnvWire_ne n).symm]
  · intro ho; funext ew
    have hbit (i : Fin 2) : ((localAddrReg n 2).basisSplitEquiv z).2 (localFlagEnvWire n 2 i) = if
      o.val.testBit i.val then 1 else 0 := by
      rw [← basisBits_localSlotFlag]; have hi := congrFun (congrArg (basisBits 2) ho) i
      rw [QRegister.basisBits_extractIndex, localAllMarkersReg_apply, ← (localSlotReg n 2
        i).basisBits_extractIndex, ← (localMarkerReg n).basisBits_extractIndex] at hi
      conv_rhs at hi => rw [basisBits_eq_testBit]
      exact hi
    rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
    · simpa [envOfMask] using hbit s0
    · simpa [envOfMask, (localFlagEnvWire_ne n).symm] using hbit s1
theorem basisOutcomeProjector_allMarkers_oracle_tensorState {n k : ℕ} (v : Fin (2 ^ 2) → Fin (2 ^ (2
  * n)) → ℂ) (o : Fin (2 ^ 2)) :
    let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ :=
      Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 (1 : ℂ)
    (allMarkersReg n 2 k).basisOutcomeProjector o *ᵥ (oracleReg n 2 k).tensorState (∑ m : Fin (2 ^
      2), (localAddrReg n 2).tensorState (v m) (Pi.single (envOfMask n m) (1 : ℂ))) env0 =
      (oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState (v o) (Pi.single (envOfMask n o)
      (1 : ℂ))) env0 := by
  intro env0; funext z
  rw [(allMarkersReg n 2 k).basisOutcomeProjector_mulVec]; dsimp only [QRegister.tensorState]
  rw [allMarkersReg, QRegister.extractIndex_compose]
  simp only [Finset.sum_apply, QRegister.tensorState]
  by_cases ho : (localAllMarkersReg n 2).extractIndex ((oracleReg n 2 k).extractIndex z) = o
  · rw [ite_eq_left ho]
    have hE : ((localAddrReg n 2).basisSplitEquiv ((oracleReg n 2 k).extractIndex z)).2 =
        envOfMask n o := (basisSplit_snd_eq_envOfMask_iff n _ o).2 ho
    rw [hE]; congr 1; rw [Finset.sum_eq_single o]
    · intro m _ hm
      have hne : envOfMask n o ≠ envOfMask n m := fun h ↦ hm (envOfMask_injective n h.symm)
      simp [Pi.single_eq_of_ne hne]
    · intro habs; exact (habs (Finset.mem_univ o)).elim
  · rw [ite_eq_right ho]
    have hne : ((localAddrReg n 2).basisSplitEquiv ((oracleReg n 2 k).extractIndex z)).2 ≠
        envOfMask n o := fun hE ↦ ho ((basisSplit_snd_eq_envOfMask_iff n _ o).1 hE)
    simp [Pi.single_eq_of_ne hne]
theorem prodSlotLocalVec_zero_flags_eq_tensorState {n : ℕ} (v0 v1 : Fin (2 ^ n) → ℂ) :
  prodSlotLocalVec (![slotPairVec v0 (Pi.single 0 1), slotPairVec v1 (Pi.single 0 1)]) =
  (localAddrReg n 2).tensorState (fun u ↦ v0 (addrEquiv n 2 u s0) * v1 (addrEquiv n 2 u s1))
  (Pi.single 0 1) := by
  funext z; dsimp only [prodSlotLocalVec, QRegister.tensorState]; rw [Fin.prod_univ_two]
  change slotPairVec v0 (Pi.single 0 1) ((localSlotReg n 2 s0).extractIndex z) * slotPairVec v1
    (Pi.single 0 1) ((localSlotReg n 2 s1).extractIndex z) = _; dsimp only [slotPairVec]
  rw [addrEquiv_extractIndex_localAddrReg, addrEquiv_extractIndex_localAddrReg]
  dsimp only [localSlotAddr]; by_cases hE : ((localAddrReg n 2).basisSplitEquiv z).2 = 0
  · have hf0 := localSlotFlag_of_env_zero z hE s0; have hf1 := localSlotFlag_of_env_zero z hE s1
    dsimp only [localSlotFlag] at hf0 hf1; rw [hE, hf0, hf1]; simp
  · rw [Pi.single_eq_of_ne hE, mul_zero]
    have hex : ¬ (localSlotFlag n 2 z s0 = 0 ∧ localSlotFlag n 2 z s1 = 0) := by
      rintro ⟨hf0, hf1⟩; apply hE
      have hm : (localAllMarkersReg n 2).extractIndex z = 0 := by
        apply (basisBits 2).injective; funext i; rw [QRegister.basisBits_extractIndex,
          localAllMarkersReg_apply, ← (localSlotReg n 2 i).basisBits_extractIndex, ← (localMarkerReg
          n).basisBits_extractIndex]; change basisBits 1 (localSlotFlag n 2 z i) 0 = basisBits 2 0 i
        rcases fin2_eq_s0_or_s1 i with rfl | rfl
        · rw [hf0, basisBits_zero, basisBits_zero, Pi.zero_apply, Pi.zero_apply]
        · rw [hf1, basisBits_zero, basisBits_zero, Pi.zero_apply, Pi.zero_apply]
      simpa using (basisSplit_snd_eq_envOfMask_iff n z 0).2 hm
    by_cases hf0 : localSlotFlag n 2 z s0 = 0
    · have hf1 : localSlotFlag n 2 z s1 ≠ 0 := fun h ↦ hex ⟨hf0, h⟩
      dsimp only [localSlotFlag] at hf1; simp [Pi.single_eq_of_ne hf1]
    · dsimp only [localSlotFlag] at hf0; simp [Pi.single_eq_of_ne hf0]
/-! ## 3. Address Swap, Collision Flag, and CSWAP Symmetry Filter (`0` Queries) -/
/-- Involutive address-tuple swap `(x_0, x_1) ↦ (x_1, x_0)` on `2 * n` address wires. -/
def swapAddrPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ (2 * n))) :=
  (addrEquiv n 2).trans <|
    (Equiv.piCongrLeft' (fun _ : Fin 2 ↦ Fin (2 ^ n)) (Equiv.swap s0 s1)).trans
      (addrEquiv n 2).symm
@[simp]
theorem addrEquiv_swapAddrPerm_s0 (n : ℕ) (u : Fin (2 ^ (2 * n))) : addrEquiv n 2 (swapAddrPerm n u)
  s0 = addrEquiv n 2 u s1 := by simp [swapAddrPerm, Equiv.piCongrLeft'_apply]
@[simp]
theorem addrEquiv_swapAddrPerm_s1 (n : ℕ) (u : Fin (2 ^ (2 * n))) : addrEquiv n 2 (swapAddrPerm n u)
  s1 = addrEquiv n 2 u s0 := by simp [swapAddrPerm, Equiv.piCongrLeft'_apply]
theorem swapAddrPerm_involutive (n : ℕ) : Function.Involutive (swapAddrPerm n) := by
  intro u; apply (addrEquiv n 2).injective; funext i; fin_cases i <;> simp
theorem swapAddrPerm_eq_self_of_diag {n : ℕ} {u : Fin (2 ^ (2 * n))} (hdiag : addrEquiv n 2 u s0 =
  addrEquiv n 2 u s1) : swapAddrPerm n u = u := by
  apply (addrEquiv n 2).injective; funext i; fin_cases i
  · exact (addrEquiv_swapAddrPerm_s0 n u).trans hdiag.symm
  · exact (addrEquiv_swapAddrPerm_s1 n u).trans hdiag
/-- Collision-detection reversible gate XORing `[x_0 = x_1]` into marker wire `1`. -/
noncomputable def collisionFlagPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ ((n + 1) * 2))) :=
  (localAddrReg n 2).basisSplitEquiv.trans <|
    Equiv.trans
      ({ toFun := fun p : Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2) ↦
          (p.1, Function.update p.2 (localFlagEnvWire n 2 s1)
            (p.2 (localFlagEnvWire n 2 s1) +
              if addrEquiv n 2 p.1 s0 = addrEquiv n 2 p.1 s1 then (1 : ZMod 2) else 0))
         invFun := fun p : Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2) ↦
          (p.1, Function.update p.2 (localFlagEnvWire n 2 s1)
            (p.2 (localFlagEnvWire n 2 s1) +
              if addrEquiv n 2 p.1 s0 = addrEquiv n 2 p.1 s1 then (1 : ZMod 2) else 0))
         left_inv := fun p ↦ by
           ext1
           · rfl
           · funext ew
             by_cases h : ew = localFlagEnvWire n 2 s1
             · subst h
               simp only [Function.update_self]
               generalize
                 (if addrEquiv n 2 p.1 s0 = addrEquiv n 2 p.1 s1 then (1 : ZMod 2) else 0) = b
               rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
             · simp [Function.update_of_ne h]
         right_inv := fun p ↦ by
           ext1
           · rfl
           · funext ew
             by_cases h : ew = localFlagEnvWire n 2 s1
             · subst h
               simp only [Function.update_self]
               generalize
                 (if addrEquiv n 2 p.1 s0 = addrEquiv n 2 p.1 s1 then (1 : ZMod 2) else 0) = b
               rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
             · simp [Function.update_of_ne h] } :
        Equiv.Perm (Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2)))
      (localAddrReg n 2).basisSplitEquiv.symm
theorem collisionFlagPerm_involutive (n : ℕ) : Function.Involutive (collisionFlagPerm n) := by
  intro z; dsimp only [collisionFlagPerm, Equiv.trans_apply, Equiv.coe_fn_mk]
  rw [Equiv.apply_symm_apply, ← (localAddrReg n 2).basisSplitEquiv.injective.eq_iff,
    Equiv.apply_symm_apply]; ext1
  · rfl
  · funext ew; by_cases h : ew = localFlagEnvWire n 2 s1
    · subst h; simp only [Function.update_self]; generalize (if addrEquiv n 2 ((localAddrReg n
        2).basisSplitEquiv z).1 s0 = addrEquiv n 2 ((localAddrReg n 2).basisSplitEquiv z).1 s1 then
        (1 : ZMod 2) else 0) = b; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp [Function.update_of_ne h]
/-- Controlled-SWAP permutation swapping `x_0 ↔ x_1` conditioned on marker wire `0 = 1`. -/
noncomputable def cswapPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ ((n + 1) * 2))) :=
  (localAddrReg n 2).basisSplitEquiv.trans <|
    Equiv.trans
      ({ toFun := fun p : Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2) ↦
          (if p.2 (localFlagEnvWire n 2 s0) = (1 : ZMod 2) then swapAddrPerm n p.1 else p.1, p.2)
         invFun := fun p : Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2) ↦
          (if p.2 (localFlagEnvWire n 2 s0) = (1 : ZMod 2) then swapAddrPerm n p.1 else p.1, p.2)
         left_inv := fun p ↦ by
           ext1
           · dsimp only
             split_ifs with h
             · exact swapAddrPerm_involutive n p.1
             · rfl
           · rfl
         right_inv := fun p ↦ by
           ext1
           · dsimp only
             split_ifs with h
             · exact swapAddrPerm_involutive n p.1
             · rfl
           · rfl } :
        Equiv.Perm (Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2)))
      (localAddrReg n 2).basisSplitEquiv.symm
theorem cswapPerm_involutive (n : ℕ) : Function.Involutive (cswapPerm n) := by
  intro z; dsimp only [cswapPerm, Equiv.trans_apply, Equiv.coe_fn_mk]; rw [Equiv.apply_symm_apply, ←
    (localAddrReg n 2).basisSplitEquiv.injective.eq_iff, Equiv.apply_symm_apply]
  ext1
  · dsimp only; split_ifs with h
    · exact swapAddrPerm_involutive n _
    · rfl
  · rfl
/-- Flag-`0` bit-flip permutation mapping `(1, 0)` to `(0, 0)` on
  `(localAddrReg n 2).Environment`. -/
noncomputable def flipFlag0Perm (n : ℕ) : Equiv.Perm (Fin (2 ^ ((n + 1) * 2))) :=
  (localAddrReg n 2).basisSplitEquiv.trans <|
    Equiv.trans
      ({ toFun := fun p : Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2) ↦
          (p.1, Function.update p.2 (localFlagEnvWire n 2 s0)
            (p.2 (localFlagEnvWire n 2 s0) + (1 : ZMod 2)))
         invFun := fun p : Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2) ↦
          (p.1, Function.update p.2 (localFlagEnvWire n 2 s0)
            (p.2 (localFlagEnvWire n 2 s0) + (1 : ZMod 2)))
         left_inv := fun p ↦ by
           ext1
           · rfl
           · funext ew
             by_cases h : ew = localFlagEnvWire n 2 s0
             · subst h; simp [add_assoc, CharTwo.add_self_eq_zero]
             · simp [Function.update_of_ne h]
         right_inv := fun p ↦ by
           ext1
           · rfl
           · funext ew
             by_cases h : ew = localFlagEnvWire n 2 s0
             · subst h; simp [add_assoc, CharTwo.add_self_eq_zero]
             · simp [Function.update_of_ne h] } :
        Equiv.Perm (Fin (2 ^ (2 * n)) × ((localAddrReg n 2).Environment → ZMod 2)))
      (localAddrReg n 2).basisSplitEquiv.symm
theorem flipFlag0Perm_involutive (n : ℕ) : Function.Involutive (flipFlag0Perm n) := by
  intro z; dsimp only [flipFlag0Perm, Equiv.trans_apply, Equiv.coe_fn_mk]
  rw [Equiv.apply_symm_apply, ← (localAddrReg n 2).basisSplitEquiv.injective.eq_iff,
    Equiv.apply_symm_apply]; ext1
  · rfl
  · funext ew; by_cases h : ew = localFlagEnvWire n 2 s0
    · subst h; simp [add_assoc, CharTwo.add_self_eq_zero]
    · simp [Function.update_of_ne h]
/-- Real Hadamard gate on marker wire `0` (`localFlagReg n 2 s0`). -/
noncomputable def hadFlag0Unitary (n : ℕ) : Unitary (2 ^ ((n + 1) * 2)) :=
  (localFlagReg n 2 s0).embedUnitary
    (rotReflectUnitary (1 / √2) (1 / √2) (by
      rw [div_pow, Real.sq_sqrt (by positivity)]
      norm_num))
/-- Zero-query collision + CSWAP symmetry filter unitary on `(n + 1) * 2` wires:
  flags diagonal collisions onto `b_1 = 1` (`o = 2`) and applies `H_{b_0} · CSWAP ·
  H_{b_0}`. -/
noncomputable def cswapFilterUnitary (n : ℕ) : Unitary (2 ^ ((n + 1) * 2)) :=
  hadFlag0Unitary n * permutationUnitary (cswapPerm n) *
    hadFlag0Unitary n * permutationUnitary (collisionFlagPerm n)
theorem isRealMatrix_cswapFilterUnitary (n : ℕ) : IsRealMatrix (cswapFilterUnitary n).1 := by
  have hH : IsRealMatrix (hadFlag0Unitary n).1 := isRealMatrix_embedMatrix _
    (isRealMatrix_rotReflectMat _ _); exact isRealMatrix_mul (isRealMatrix_mul (isRealMatrix_mul hH
    (isRealMatrix_permutationUnitary (cswapPerm n))) hH) (isRealMatrix_permutationUnitary
    (collisionFlagPerm n))
theorem hadFlag0_mulVec_tensorState {n : ℕ} (v : Fin (2 ^ (2 * n)) → ℂ) (b0 b1 : Bool) :
    let m0 : Fin (2 ^ 2) := ⟨if b1 then 2 else 0, by cases b1 <;> norm_num⟩
    let m1 : Fin (2 ^ 2) := ⟨(if b1 then 2 else 0) + 1, by cases b1 <;> norm_num⟩
    let mIn : Fin (2 ^ 2) := if b0 then m1 else m0
    (hadFlag0Unitary n).1 *ᵥ (localAddrReg n 2).tensorState v (Pi.single (envOfMask n mIn) (1 : ℂ))
      = ((1 / √2 : ℝ) : ℂ) • (localAddrReg n 2).tensorState v (Pi.single (envOfMask n m0) (1 : ℂ)) +
      ((if b0 then -(1 / √2) else 1 / √2 : ℝ) : ℂ) • (localAddrReg n 2).tensorState v (Pi.single
      (envOfMask n m1) (1 : ℂ)) := by
  intro m0 m1 mIn; funext z; let rF := localFlagReg n 2 s0; let rA := localAddrReg n 2
  have hrf_eq (w : Fin (2 ^ ((n + 1) * 2))) : localSlotFlag n 2 w s0 = rF.extractIndex w :=
    (QRegister.extractIndex_compose (localSlotReg n 2 s0) (localMarkerReg n) w).symm
  change (rF.embedMatrix (rotReflectMat (1 / √2) (1 / √2)) *ᵥ rA.tensorState v (Pi.single (envOfMask
    n mIn) (1 : ℂ))) z = (((1 / √2 : ℝ) : ℂ) • rA.tensorState v (Pi.single (envOfMask n m0) (1 : ℂ))
    + ((if b0 then -(1 / √2) else 1 / √2 : ℝ) : ℂ) • rA.tensorState v (Pi.single (envOfMask n m1) (1
    : ℂ))) z; rw [Matrix.mulVec, dotProduct, ← rF.basisSplitEquiv.symm.sum_comp,
    Fintype.sum_prod_type]
  have hdisj : rF.DisjointWires rA := by
    rw [QRegister.disjoint_iff]; intro w1 w2 hw; have hm : rF w1 = (localFlagEnvWire n 2 s0).1 :=
      (by fin_cases w1; rfl); rw [hm] at hw; exact (localFlagEnvWire n 2 s0).2 ⟨w2, hw.symm⟩
  -- Only `envF = (rF.basisSplitEquiv z).2` survives in `embedMatrix`
  have hsum_env (bf : Fin (2 ^ 1)) : ∑ ef : rF.Environment → ZMod 2, rF.embedMatrix (rotReflectMat
    (1 / √2) (1 / √2)) z (rF.basisSplitEquiv.symm (bf, ef)) * rA.tensorState v (Pi.single (envOfMask
    n mIn) (1 : ℂ)) (rF.basisSplitEquiv.symm (bf, ef)) = rotReflectMat (1 / √2) (1 / √2)
    (rF.extractIndex z) bf * rA.tensorState v (Pi.single (envOfMask n mIn) (1 : ℂ)) (rF.replaceIndex
    z bf) := by
    rw [Fintype.sum_eq_single (rF.basisSplitEquiv z).2]
    · have hrep : rF.basisSplitEquiv.symm (bf, (rF.basisSplitEquiv z).2) = rF.replaceIndex z bf :=
        rfl; rw [hrep, rF.embedMatrix_apply]
      have heq_snd : (rF.basisSplitEquiv (rF.replaceIndex z bf)).2 = (rF.basisSplitEquiv z).2 :=
        (by dsimp only [QRegister.replaceIndex]; rw [Equiv.apply_symm_apply])
      have hex_bf : rF.extractIndex (rF.replaceIndex z bf) = bf := by
        rw [← QRegister.basisSplitEquiv_apply_fst]; dsimp only [QRegister.replaceIndex]
        rw [Equiv.apply_symm_apply]
      rw [heq_snd, ite_eq_left rfl, mul_one, hex_bf]
    · intro ef hef; rw [rF.embedMatrix_apply, Equiv.apply_symm_apply, ite_eq_right (Ne.symm hef),
        mul_zero, zero_mul]
  simp_rw [hsum_env, sum_fin_pow_one]
  have hexA (bf : Fin (2 ^ 1)) : rA.extractIndex (rF.replaceIndex z bf) = rA.extractIndex z :=
    rA.extractIndex_replaceIndex_of_disjoint rF (QRegister.disjoint_comm.1 hdisj) z bf
  have hsndA (bf : Fin (2 ^ 1)) : (rA.basisSplitEquiv (rF.replaceIndex z bf)).2 = Function.update
    (rA.basisSplitEquiv z).2 (localFlagEnvWire n 2 s0) (basisBits 1 bf 0) := by
    funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
    · rw [Function.update_self, ← basisBits_localSlotFlag, hrf_eq]
      have hex : rF.extractIndex (rF.replaceIndex z bf) = bf := by
        rw [← QRegister.basisSplitEquiv_apply_fst]; dsimp only [QRegister.replaceIndex]
        rw [Equiv.apply_symm_apply]
      rw [hex]
    · rw [Function.update_of_ne (localFlagEnvWire_ne n).symm, QRegister.basisSplitEquiv_apply_snd,
        QRegister.basisSplitEquiv_apply_snd]
      refine rF.basisBits_replaceIndex_of_not_mem z bf (localFlagEnvWire n 2 s1).1 ?_; rintro ⟨u,
        hu⟩; fin_cases u; exact localFlagEnvWire_ne n (Subtype.ext hu)
  have hfz : rF.extractIndex z = 0 ∨ rF.extractIndex z = 1 := eq_zero_or_one_fin_pow_one
    (rF.extractIndex z)
  have hupd_eq (bf : Fin (2 ^ 1)) : Function.update (rA.basisSplitEquiv z).2 (localFlagEnvWire n 2
    s0) (basisBits 1 bf 0) = envOfMask n mIn ↔ (bf = (if b0 then 1 else 0)) ∧ (rA.basisSplitEquiv
    z).2 (localFlagEnvWire n 2 s1) = (if b1 then 1 else 0) := by
    constructor
    · intro h; have h0 := congrFun h (localFlagEnvWire n 2 s0)
      have h1 := congrFun h (localFlagEnvWire n 2 s1); rw [Function.update_self,
        basisBits_eq_testBit, envOfMask_s0] at h0; rw [Function.update_of_ne (localFlagEnvWire_ne
        n).symm, envOfMask_s1] at h1; dsimp only [mIn, m0, m1] at h0 h1; refine ⟨?_, ?_⟩
      · rcases eq_zero_or_one_fin_pow_one bf with rfl | rfl <;> cases b0 <;> cases b1 <;>
          first | (simp; done) | (exfalso; simp at h0)
      · rw [h1]; cases b0 <;> cases b1 <;> simp
    · rintro ⟨hbf, hs1_eq⟩; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
      · rw [Function.update_self, hbf, basisBits_eq_testBit, envOfMask_s0]; dsimp only [mIn, m0, m1]
        cases b0 <;> cases b1 <;> simp
      · rw [Function.update_of_ne (localFlagEnvWire_ne n).symm, hs1_eq, envOfMask_s1]
        dsimp only [mIn, m0, m1]; cases b0 <;> cases b1 <;> simp
  have henv_m0 : (rA.basisSplitEquiv z).2 = envOfMask n m0 ↔ rF.extractIndex z = 0 ∧
    (rA.basisSplitEquiv z).2 (localFlagEnvWire n 2 s1) = (if b1 then 1 else 0) := by
    constructor
    · intro h
      have h0 : basisBits 1 (rF.extractIndex z) 0 = (rA.basisSplitEquiv z).2 (localFlagEnvWire n 2
        s0) := hrf_eq z ▸ basisBits_localSlotFlag n 2 z s0; rw [basisBits_eq_testBit, h,
        envOfMask_s0] at h0
      have h1 := congrFun h (localFlagEnvWire n 2 s1); rw [envOfMask_s1] at h1
      dsimp only [m0] at h0 h1; refine ⟨?_, ?_⟩
      · rcases eq_zero_or_one_fin_pow_one (rF.extractIndex z) with hfz0 | hfz1
        · exact hfz0
        · exfalso; rw [hfz1] at h0; cases b1 <;> simp at h0
      · rw [h1]; cases b1 <;> simp
    · rintro ⟨hf0, hs1_eq⟩; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
      · rw [← basisBits_localSlotFlag, hrf_eq, hf0, basisBits_eq_testBit, envOfMask_s0]
        dsimp only [m0]; cases b1 <;> simp
      · rw [hs1_eq, envOfMask_s1]; dsimp only [m0]; cases b1 <;> simp
  have henv_m1 : (rA.basisSplitEquiv z).2 = envOfMask n m1 ↔ rF.extractIndex z = 1 ∧
    (rA.basisSplitEquiv z).2 (localFlagEnvWire n 2 s1) = (if b1 then 1 else 0) := by
    constructor
    · intro h
      have h0 : basisBits 1 (rF.extractIndex z) 0 = (rA.basisSplitEquiv z).2 (localFlagEnvWire n 2
        s0) := hrf_eq z ▸ basisBits_localSlotFlag n 2 z s0; rw [basisBits_eq_testBit, h,
        envOfMask_s0] at h0
      have h1 := congrFun h (localFlagEnvWire n 2 s1); rw [envOfMask_s1] at h1
      dsimp only [m1] at h0 h1; refine ⟨?_, ?_⟩
      · rcases eq_zero_or_one_fin_pow_one (rF.extractIndex z) with hfz0 | hfz1
        · exfalso; rw [hfz0] at h0; cases b1 <;> simp at h0
        · exact hfz1
      · rw [h1]; cases b1 <;> simp
    · rintro ⟨hf1, hs1_eq⟩; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
      · rw [← basisBits_localSlotFlag, hrf_eq, hf1, basisBits_eq_testBit, envOfMask_s0]
        dsimp only [m1]; cases b1 <;> simp
      · rw [hs1_eq, envOfMask_s1]; dsimp only [m1]; cases b1 <;> simp
  dsimp only [QRegister.tensorState, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [hexA 0, hexA 1,
    hsndA 0, hsndA 1]; simp only [Pi.single_apply, hupd_eq, henv_m0, henv_m1]
  by_cases hs1_b : (rA.basisSplitEquiv z).2 (localFlagEnvWire n 2 s1) = (if b1 then 1 else 0)
  · rcases hfz with hfz0 | hfz1 <;> cases b0
    · rw [hfz0]; simp [hs1_b, rotReflectMat]
    · rw [hfz0]; simp [hs1_b, rotReflectMat]
    · rw [hfz1]; simp [hs1_b, rotReflectMat]
    · rw [hfz1]; simp [hs1_b, rotReflectMat]
  · cases b1 <;> simp_all
theorem collisionFlagPerm_mulVec_zero {n : ℕ} (v : Fin (2 ^ (2 * n)) → ℂ) :
    let vOff : Fin (2 ^ (2 * n)) → ℂ :=
      fun u ↦ if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then 0 else v u
    let vDiag : Fin (2 ^ (2 * n)) → ℂ :=
      fun u ↦ if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then v u else 0
    (permutationUnitary (collisionFlagPerm n)).1 *ᵥ (localAddrReg n 2).tensorState v (Pi.single
      (envOfMask n 0) (1 : ℂ)) = (localAddrReg n 2).tensorState vOff (Pi.single (envOfMask n 0) (1 :
      ℂ)) + (localAddrReg n 2).tensorState vDiag (Pi.single (envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ
      rfl : 2 < 2 ^ 2)⟩) (1 : ℂ)) := by
  intro vOff vDiag; funext z
  change (Equiv.Perm.permMatrix ℂ (collisionFlagPerm n)⁻¹ *ᵥ
    (localAddrReg n 2).tensorState v (Pi.single (envOfMask n 0) (1 : ℂ))) z = _
  rw [Matrix.permMatrix_mulVec, Function.comp_apply,
    show (collisionFlagPerm n)⁻¹ z = collisionFlagPerm n z by
      simpa [Equiv.symm_apply_eq] using (collisionFlagPerm_involutive n z).symm]
  dsimp only [QRegister.tensorState, Pi.add_apply]
  have hsp : (localAddrReg n 2).basisSplitEquiv (collisionFlagPerm n z) = (((localAddrReg n
    2).basisSplitEquiv z).1, Function.update ((localAddrReg n 2).basisSplitEquiv z).2
    (localFlagEnvWire n 2 s1) (((localAddrReg n 2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s1) +
    if addrEquiv n 2 ((localAddrReg n 2).basisSplitEquiv z).1 s0 = addrEquiv n 2 ((localAddrReg n
    2).basisSplitEquiv z).1 s1 then (1 : ZMod 2) else 0)) := by
    dsimp only [collisionFlagPerm, Equiv.trans_apply, Equiv.coe_fn_mk]; rw [Equiv.apply_symm_apply]
  have hex : (localAddrReg n 2).extractIndex (collisionFlagPerm n z) =
      (localAddrReg n 2).extractIndex z := by
    rw [← QRegister.basisSplitEquiv_apply_fst, hsp, QRegister.basisSplitEquiv_apply_fst]
  rw [hex, hsp, QRegister.basisSplitEquiv_apply_fst]; dsimp only [vOff, vDiag]
  by_cases hd : addrEquiv n 2 ((localAddrReg n 2).extractIndex z) s0 =
      addrEquiv n 2 ((localAddrReg n 2).extractIndex z) s1
  · simp only [hd, ↓reduceIte, zero_mul, zero_add]
    have heq_e : Function.update ((localAddrReg n 2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s1)
      (((localAddrReg n 2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s1) + (1 : ZMod 2)) =
      envOfMask n 0 ↔ ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ := by
      constructor
      · intro h; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
        · have h0 := congrFun h (localFlagEnvWire n 2 s0)
          rw [Function.update_of_ne (localFlagEnvWire_ne n)] at h0; simpa [envOfMask] using h0
        · have h1 := congrFun h (localFlagEnvWire n 2 s1)
          rw [Function.update_self, envOfMask_zero, Pi.zero_apply] at h1
          have hz1 : ((localAddrReg n 2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s1) = 1 := by
            have := congrArg (· + (1 : ZMod 2)) h1
            simpa [add_assoc, CharTwo.add_self_eq_zero] using this
          rw [hz1, envOfMask_s1]; simp
      · intro h; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
        · rw [Function.update_of_ne (localFlagEnvWire_ne n), h]; simp [envOfMask]
        · rw [Function.update_self, h, envOfMask_s1, envOfMask_zero, Pi.zero_apply]; simp
    by_cases h2 : ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩
    · rw [heq_e.2 h2, h2]; simp only [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (mt heq_e.1 h2), Pi.single_eq_of_ne h2]
  · simp only [hd, ↓reduceIte, add_zero, Function.update_eq_self, zero_mul]
theorem cswapPerm_mulVec_tensorState {n : ℕ} (v : Fin (2 ^ (2 * n)) → ℂ) (o : Fin (2 ^ 2)) :
  (permutationUnitary (cswapPerm n)).1 *ᵥ (localAddrReg n 2).tensorState v (Pi.single (envOfMask n
  o) (1 : ℂ)) = (localAddrReg n 2).tensorState (if o.val.testBit 0 then fun u ↦ v (swapAddrPerm n u)
  else v) (Pi.single (envOfMask n o) (1 : ℂ)) := by
  funext z
  change (Equiv.Perm.permMatrix ℂ (cswapPerm n)⁻¹ *ᵥ
    (localAddrReg n 2).tensorState v (Pi.single
    (envOfMask n o) (1 : ℂ))) z = _
  rw [Matrix.permMatrix_mulVec, Function.comp_apply,
    show (cswapPerm n)⁻¹ z = cswapPerm n z by
      simpa [Equiv.symm_apply_eq] using (cswapPerm_involutive n z).symm]
  dsimp only [QRegister.tensorState]
  have hsp : (localAddrReg n 2).basisSplitEquiv (cswapPerm n z) = (if ((localAddrReg n
    2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s0) = (1 : ZMod 2) then swapAddrPerm n
    ((localAddrReg n 2).basisSplitEquiv z).1 else ((localAddrReg n 2).basisSplitEquiv z).1,
    ((localAddrReg n 2).basisSplitEquiv z).2) :=
    (by dsimp only [cswapPerm, Equiv.trans_apply, Equiv.coe_fn_mk]; rw [Equiv.apply_symm_apply])
  have hex : (localAddrReg n 2).extractIndex (cswapPerm n z) = if ((localAddrReg n
    2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s0) = (1 : ZMod 2) then swapAddrPerm n
    ((localAddrReg n 2).extractIndex z) else (localAddrReg n 2).extractIndex z :=
    (by rw [← QRegister.basisSplitEquiv_apply_fst, hsp, QRegister.basisSplitEquiv_apply_fst])
  rw [hex, hsp]; by_cases hE : ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n o
  · rw [hE, Pi.single_eq_same, mul_one, mul_one]
    have h0 : envOfMask n o (localFlagEnvWire n 2 s0) = if o.val.testBit 0 then 1 else 0 :=
      (by simp [envOfMask]); rw [h0]; cases o.val.testBit 0 <;> simp
  · simp [Pi.single_eq_of_ne hE]
theorem flipFlag0Perm_mulVec_one {n : ℕ} (v : Fin (2 ^ (2 * n)) → ℂ) :
    (permutationUnitary (flipFlag0Perm n)).1 *ᵥ
        (localAddrReg n 2).tensorState v (Pi.single (envOfMask n ⟨1, by decide⟩) (1 : ℂ)) =
      (localAddrReg n 2).tensorState v (Pi.single 0 (1 : ℂ)) := by
  funext z
  change (Equiv.Perm.permMatrix ℂ (flipFlag0Perm n)⁻¹ *ᵥ
    (localAddrReg n 2).tensorState v (Pi.single
    (envOfMask n ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) (1 : ℂ))) z = _
  rw [Matrix.permMatrix_mulVec, Function.comp_apply,
    show (flipFlag0Perm n)⁻¹ z = flipFlag0Perm n z by
      simpa [Equiv.symm_apply_eq] using (flipFlag0Perm_involutive n z).symm]
  dsimp only [QRegister.tensorState]; have hsp : (localAddrReg n 2).basisSplitEquiv (flipFlag0Perm n
    z) = (((localAddrReg n 2).basisSplitEquiv z).1, Function.update ((localAddrReg n
    2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s0) (((localAddrReg n 2).basisSplitEquiv z).2
    (localFlagEnvWire n 2 s0) + (1 : ZMod 2))) :=
    (by dsimp only [flipFlag0Perm, Equiv.trans_apply, Equiv.coe_fn_mk]; rw [Equiv.apply_symm_apply])
  have hex : (localAddrReg n 2).extractIndex (flipFlag0Perm n z) = (localAddrReg n 2).extractIndex z
    := (by rw [← QRegister.basisSplitEquiv_apply_fst, hsp, QRegister.basisSplitEquiv_apply_fst])
  rw [hex, hsp]; dsimp only
  have heq_e : Function.update ((localAddrReg n 2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s0)
    (((localAddrReg n 2).basisSplitEquiv z).2 (localFlagEnvWire n 2 s0) + (1 : ZMod 2)) = envOfMask
    n ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ↔ ((localAddrReg n 2).basisSplitEquiv z).2 = 0
    := by
    constructor
    · intro h; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
      · have h0 := congrFun h (localFlagEnvWire n 2 s0); rw [Function.update_self] at h0
        have hm1 : envOfMask n ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ (localFlagEnvWire n 2
          s0) = 1 := (by simp [envOfMask]); rw [hm1] at h0
        have := congrArg (· + (1 : ZMod 2)) h0
        simpa [add_assoc, CharTwo.add_self_eq_zero] using this
      · have h1 := congrFun h (localFlagEnvWire n 2 s1); rw [Function.update_of_ne
          (localFlagEnvWire_ne n).symm, envOfMask_s1] at h1; rw [h1, Pi.zero_apply]; simp
    · intro h; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
      · rw [Function.update_self, h, Pi.zero_apply, zero_add]; simp [envOfMask]
      · rw [Function.update_of_ne (localFlagEnvWire_ne n).symm, h, Pi.zero_apply, envOfMask_s1]
        simp
  by_cases h0 : ((localAddrReg n 2).basisSplitEquiv z).2 = 0
  · rw [heq_e.2 h0, h0]; simp only [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (mt heq_e.1 h0), Pi.single_eq_of_ne h0]
theorem cswapFilterUnitary_mulVec_zero {n : ℕ} (v : Fin (2 ^ (2 * n)) → ℂ) :
    let vOff : Fin (2 ^ (2 * n)) → ℂ :=
      fun u ↦ if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then 0 else v u
    let vDiag : Fin (2 ^ (2 * n)) → ℂ :=
      fun u ↦ if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then v u else 0
    let vSym : Fin (2 ^ (2 * n)) → ℂ :=
      fun u ↦ ((1 / 2 : ℝ) : ℂ) * (vOff u + vOff (swapAddrPerm n u))
    let vAnti : Fin (2 ^ (2 * n)) → ℂ :=
      fun u ↦ ((1 / 2 : ℝ) : ℂ) * (vOff u - vOff (swapAddrPerm n u))
    (cswapFilterUnitary n).1 *ᵥ (localAddrReg n 2).tensorState v (Pi.single (envOfMask n 0) (1 : ℂ))
      = ∑ o : Fin (2 ^ 2), (localAddrReg n 2).tensorState (if o = 0 then vSym else if o = ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then vAnti else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl
      : 2 < 2 ^ 2)⟩ then vDiag else 0) (Pi.single (envOfMask n o) (1 : ℂ)) := by
  intro vOff vDiag vSym vAnti
  have hmul : (cswapFilterUnitary n).1 = (hadFlag0Unitary n).1 * ((permutationUnitary (cswapPerm
    n)).1 * ((hadFlag0Unitary n).1 * (permutationUnitary (collisionFlagPerm n)).1)) := by
    simp only [cswapFilterUnitary, Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    collisionFlagPerm_mulVec_zero]
  change (hadFlag0Unitary n).1 *ᵥ ((permutationUnitary (cswapPerm n)).1 *ᵥ ((hadFlag0Unitary n).1 *ᵥ
    ((localAddrReg n 2).tensorState vOff (Pi.single (envOfMask n 0) (1 : ℂ)) + (localAddrReg n
    2).tensorState vDiag (Pi.single (envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) (1 :
    ℂ))))) = _; have hh0_in := hadFlag0_mulVec_tensorState vOff false false
  have hh2_in := hadFlag0_mulVec_tensorState vDiag false true
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add, show (2 + 1 : ℕ) = 3 from rfl, Fin.zero_eta]
    at hh0_in hh2_in; rw [Matrix.mulVec_add, hh0_in, hh2_in]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, cswapPerm_mulVec_tensorState]
  have hb0 : (0 : Fin (2 ^ 2)).val.testBit 0 = false := rfl
  have hb1 : (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)).val.testBit 0
    = true := by rfl
  have hb2 : (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)).val.testBit 0
    = false := by rfl
  have hb3 : (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)).val.testBit 0
    = true := by rfl
  rw [hb0, hb1, hb2, hb3]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hvDiag_swap : (fun u ↦ vDiag (swapAddrPerm n u)) = vDiag := by
    funext u; dsimp [vDiag]; by_cases hd : addrEquiv n 2 u s0 = addrEquiv n 2 u s1
    · rw [swapAddrPerm_eq_self_of_diag hd]
    · simp [hd, Ne.symm hd]
  rw [hvDiag_swap]; have hh00 := hadFlag0_mulVec_tensorState vOff false false
  have hh10 := hadFlag0_mulVec_tensorState (fun u ↦ vOff (swapAddrPerm n u)) true false
  have hh01 := hadFlag0_mulVec_tensorState vDiag false true
  have hh11 := hadFlag0_mulVec_tensorState vDiag true true
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add,
    show (2 + 1 : ℕ) = 3 from rfl, Fin.zero_eta] at hh00 hh10 hh01 hh11; rw [hh00, hh10, hh01, hh11]
  have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^
    2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^
    2)⟩} := by ext x; fin_cases x <;> simp
  rw [huniv4, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_singleton]
  have hsq2 : ((1 / √2 : ℝ) : ℂ) * ((1 / √2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
    norm_num
  have hsq2_neg : ((1 / √2 : ℝ) : ℂ) * ((-(1 / √2) : ℝ) : ℂ) = -(1 / 2 : ℂ) := by
    rw [Complex.ofReal_neg, mul_neg, hsq2]
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, QRegister.tensorState,
    show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
    show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
    show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
    show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
    show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
    show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp,
    ↓reduceIte, Pi.zero_apply, zero_mul, add_zero]
  dsimp only [vSym, vAnti]; have hhalf_c : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf_c]; let ez := ((localAddrReg n 2).basisSplitEquiv z).2
  let uz := (localAddrReg n 2).extractIndex z
  let eOf : Fin (2 ^ 2) → ((localAddrReg n 2).Environment → ZMod 2) → ℂ := fun o ↦ Pi.single
    (envOfMask n o) 1; change _ = _
  linear_combination (vOff uz * (eOf 0 ez + eOf ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ez) +
    vOff (swapAddrPerm n uz) * eOf 0 ez + vDiag uz * (2 * eOf ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2
    ^ 2)⟩ ez + eOf ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ ez)) * hsq2 + (vOff (swapAddrPerm n
    uz) * eOf ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ez + vDiag uz * eOf ⟨3,
    (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ ez) * hsq2_neg
/-! ## 4. Off-Diagonal 2D Grover Subspace & Reflection Diffuser (`A.card = 1`) -/
/-- Off-diagonal address-pair finset `{(x_0, x_1) | x_0 ≠ x_1}` on `2 * n` bits. -/
def offDiagSet (n : ℕ) : Finset (Fin (2 ^ (2 * n))) :=
  Finset.univ.filter fun u ↦ addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1
/-- Off-diagonal unmarked pair finset `offDiagSet n \ oddSet n 2 A`. -/
def offDiagUnmarkedSet (n : ℕ) (A : Finset (Fin (2 ^ n))) : Finset (Fin (2 ^ (2 * n))) :=
  offDiagSet n \ oddSet n 2 A
/-- 2D off-diagonal Grover plane vector `sin α |M_0⟩ + cos α |U_ne⟩`. -/
noncomputable def offDiagPlaneVec (n : ℕ) (A : Finset (Fin (2 ^ n))) (α : ℝ) :
    Fin (2 ^ (2 * n)) → ℂ :=
  (Real.sin α : ℂ) • unifSetVec (oddSet n 2 A) +
    (Real.cos α : ℂ) • unifSetVec (offDiagUnmarkedSet n A)
theorem mem_oddSet_two_iff {n : ℕ} {A : Finset (Fin (2 ^ n))} (u : Fin (2 ^ (2 * n))) : u ∈ oddSet n
  2 A ↔ (addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A) ∨ (addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2
  u s1 ∈ A) := by
  simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.prod_univ_two]
  change (if addrEquiv n 2 u s0 ∈ A then (-1 : ℤ) else 1) * (if addrEquiv n 2 u s1 ∈ A then (-1 : ℤ)
    else 1) = -1 ↔ _
  by_cases h0 : addrEquiv n 2 u s0 ∈ A <;> by_cases h1 : addrEquiv n 2 u s1 ∈ A <;> simp [h0, h1]
theorem oddSet_subset_offDiagSet {n : ℕ} {A : Finset (Fin (2 ^ n))} : oddSet n 2 A ⊆ offDiagSet n :=
  by
  intro u hu; rw [offDiagSet, Finset.mem_filter]; refine ⟨Finset.mem_univ u, fun heq ↦ ?_⟩
  rcases (mem_oddSet_two_iff u).1 hu with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact h1 (heq ▸ h0)
  · exact h0 (heq.symm ▸ h1)
theorem card_offDiagSet {n : ℕ} : (offDiagSet n).card = 2 ^ n * (2 ^ n - 1) := by
  have hcompl : (offDiagSet n)ᶜ = Finset.univ.image (fun x : Fin (2 ^ n) ↦ (addrEquiv n 2).symm (fun
    _ ↦ x)) := by
    ext u; simp only [offDiagSet, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not, Finset.mem_image]; constructor
    · intro heq; refine ⟨addrEquiv n 2 u s0, ?_⟩
      apply (addrEquiv n 2).injective; rw [Equiv.apply_symm_apply]; funext i
      rcases fin2_eq_s0_or_s1 i with rfl | rfl
      · rfl
      · exact heq
    · rintro ⟨x, rfl⟩; simp
  have hinj : Function.Injective (fun x : Fin (2 ^ n) ↦ (addrEquiv n 2).symm (fun _ ↦ x)) :=
    (by intro x y hxy; have h := congrFun (congrArg (addrEquiv n 2) hxy) s0; simpa using h)
  have hcard_c : (offDiagSet n)ᶜ.card = 2 ^ n :=
    (by rw [hcompl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin])
  have htot : (offDiagSet n).card + (offDiagSet n)ᶜ.card = 2 ^ (2 * n) := by
    have h := Finset.card_add_card_compl (offDiagSet n); rwa [Fintype.card_fin] at h
  have hpow : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := (by rw [Nat.mul_comm 2 n, pow_mul, sq]); have h1 : 1 ≤
    2 ^ n := Nat.one_le_two_pow; rw [Nat.mul_sub_left_distrib, mul_one]; omega
theorem card_oddSet_two_of_card_one {n : ℕ} {A : Finset (Fin (2 ^ n))} (hA1 : A.card = 1) : (oddSet
  n 2 A).card = 2 * (2 ^ n - 1) := by
  have hdiv := oddSet_card_div (m := 2) A; rw [hA1, oddFrac] at hdiv
  have hN_pos : (0 : ℝ) < 2 ^ n := (by positivity); have h2N_pos : (0 : ℝ) < 2 ^ (2 * n) :=
    (by positivity); have hpow : (2 ^ (2 * n) : ℝ) = (2 ^ n : ℝ) * (2 ^ n : ℝ) :=
    (by norm_cast; rw [Nat.mul_comm 2 n, pow_mul, sq])
  have hreal : ((oddSet n 2 A).card : ℝ) = 2 * ((2 ^ n : ℝ) - 1) := by
    have h1 := (div_eq_iff h2N_pos.ne').1 hdiv; rw [hpow] at h1; have h2 : (1 - (1 - 2 * (1 : ℝ) / 2
      ^ n) ^ 2) / 2 * (2 ^ n * 2 ^ n) = 2 * ((2 ^ n : ℝ) - 1) := (by field_simp [hN_pos.ne']; ring)
    linarith
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hcast : ((2 * (2 ^ n - 1) : ℕ) : ℝ) = 2 * ((2 ^ n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  exact Nat.cast_injective (hreal.trans hcast.symm)
theorem card_offDiagUnmarkedSet_of_card_one {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn2 : 2 ≤ n) (hA1 :
  A.card = 1) : (offDiagUnmarkedSet n A).card = (2 ^ n - 1) * (2 ^ n - 2) := by
  dsimp only [offDiagUnmarkedSet]; rw [Finset.card_sdiff_of_subset oddSet_subset_offDiagSet,
    card_offDiagSet, card_oddSet_two_of_card_one hA1]
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  zify [h4, show 1 ≤ 2 ^ n by omega, show 2 ≤ 2 ^ n by omega,
    show 2 * (2 ^ n - 1) ≤ 2 ^ n * (2 ^ n - 1) by nlinarith]
  ring
theorem dotProduct_unifSetVec_disjoint {n : ℕ} {S₁ S₂ : Finset (Fin (2 ^ n))} (hdisj : Disjoint S₁
  S₂) : star (unifSetVec S₁) ⬝ᵥ unifSetVec S₂ = 0 := by
  simp only [dotProduct, unifSetVec, Pi.star_apply]; refine Finset.sum_eq_zero fun u _ ↦ ?_
  by_cases h1 : u ∈ S₁
  · have h2 : u ∉ S₂ := Finset.disjoint_left.1 hdisj h1; simp [h1, h2]
  · simp [h1]
theorem dotProduct_offDiagPlaneVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn2 : 2 ≤ n) (hA1 : A.card =
  1) (α : ℝ) : star (offDiagPlaneVec n A α) ⬝ᵥ offDiagPlaneVec n A α = 1 := by
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have hM1 : 1 ≤ (oddSet n 2 A).card := (by rw [card_oddSet_two_of_card_one hA1]; omega)
  have hU1 : 1 ≤ (offDiagUnmarkedSet n A).card :=
    (by rw [card_offDiagUnmarkedSet_of_card_one hn2 hA1]; exact Nat.mul_pos (by omega) (by omega))
  have hdisj : Disjoint (oddSet n 2 A) (offDiagUnmarkedSet n A) := Finset.disjoint_sdiff
  have hdM := dotProduct_unifSetVec hM1; have hdU := dotProduct_unifSetVec hU1; have hdMU :=
    dotProduct_unifSetVec_disjoint hdisj; have hdUM := dotProduct_unifSetVec_disjoint hdisj.symm;
    dsimp only [offDiagPlaneVec]; simp only [star_add, star_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hdM, hdU, hdMU, hdUM, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add, RCLike.star_def, Complex.conj_ofReal]
  exact_mod_cast (by linear_combination Real.sin_sq_add_cos_sq α :
    Real.sin α * Real.sin α + Real.cos α * Real.cos α = 1)
theorem unifSetVec_offDiagSet_eq_plane {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn2 : 2 ≤ n) (hA1 :
  A.card = 1) : unifSetVec (offDiagSet n) = offDiagPlaneVec n A (halfAngleSet n 2) := by
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  set N : ℝ := (2 : ℝ) ^ n; have hN_cast : (2 ^ n : ℝ) = N := rfl; have h4R : (4 : ℝ) ≤ N :=
    (by rw [← hN_cast]; exact_mod_cast h4); have hN_pos : 0 < N := (by linarith); have hN1_pos : 0 <
    N - 1 := (by linarith); have hN2_pos : 0 < N - 2 := (by linarith); have h2N : (2 : ℝ) / N ≤ 1 :=
    (by rw [div_le_one hN_pos]; linarith)
  have hsin : Real.sin (halfAngleSet n 2) = √((2 : ℝ) / N) := by
    dsimp only [halfAngleSet]; rw [Nat.cast_ofNat, hN_cast]
    exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((2 : ℝ) / N)]) (Real.sqrt_le_one.2 h2N)
  have hcos : Real.cos (halfAngleSet n 2) = √((N - 2) / N) := by
    dsimp only [halfAngleSet]; rw [Nat.cast_ofNat, hN_cast, Real.cos_arcsin, Real.sq_sqrt
      (by positivity)]; congr 1; field_simp [hN_pos.ne']
  have hcO : ((offDiagSet n).card : ℝ) = N * (N - 1) := by
    rw [card_offDiagSet, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 ^ n), Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one]
  have hcM : ((oddSet n 2 A).card : ℝ) = 2 * (N - 1) := by
    rw [card_oddSet_two_of_card_one hA1, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub
      (by omega : 1 ≤ 2 ^ n), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hcU : ((offDiagUnmarkedSet n A).card : ℝ) = (N - 1) * (N - 2) := by
    rw [card_offDiagUnmarkedSet_of_card_one hn2 hA1, Nat.cast_mul, Nat.cast_sub
      (by omega : 1 ≤ 2 ^ n), Nat.cast_sub (by omega : 2 ≤ 2 ^ n), Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
  funext u; dsimp only [offDiagPlaneVec, unifSetVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsin, hcos, hcO, hcM, hcU]; by_cases huO : u ∈ offDiagSet n
  · by_cases huM : u ∈ oddSet n 2 A
    · have huU : u ∉ offDiagUnmarkedSet n A := fun h ↦ (Finset.mem_sdiff.1 h).2 huM; simp only [huO,
        huM, huU, ↓reduceIte, mul_zero, add_zero]
      have hreal : 1 / √(N * (N - 1)) = √((2 : ℝ) / N) * (1 / √(2 * (N - 1))) := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_mul hN_pos.le, Real.sqrt_mul
          (by positivity : (0 : ℝ) ≤ 2)]; field_simp [(Real.sqrt_pos.2 hN_pos).ne', (Real.sqrt_pos.2
          hN1_pos).ne', (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2)).ne']
      have hC := congrArg Complex.ofReal hreal; push_cast at hC ⊢; exact hC
    · have huU : u ∈ offDiagUnmarkedSet n A := Finset.mem_sdiff.2 ⟨huO, huM⟩; simp only [huO, huM,
        huU, ↓reduceIte, mul_zero, zero_add]
      have hreal : 1 / √(N * (N - 1)) = √((N - 2) / N) * (1 / √((N - 1) * (N - 2))) := by
        rw [Real.sqrt_div hN2_pos.le, Real.sqrt_mul hN_pos.le, Real.sqrt_mul hN1_pos.le]
        field_simp [(Real.sqrt_pos.2 hN_pos).ne', (Real.sqrt_pos.2 hN1_pos).ne', (Real.sqrt_pos.2
          hN2_pos).ne']
      have hC := congrArg Complex.ofReal hreal; push_cast at hC ⊢; exact hC
  · have huM : u ∉ oddSet n 2 A := fun h ↦ huO (oddSet_subset_offDiagSet h)
    have huU : u ∉ offDiagUnmarkedSet n A := fun h ↦ huO (Finset.mem_sdiff.1 h).1; simp [huO, huM,
      huU]
theorem dotProduct_unifSetVec_offDiagSet {n : ℕ} (hn1 : 1 ≤ n) : star (unifSetVec (offDiagSet n)) ⬝ᵥ
  unifSetVec (offDiagSet n) = 1 := by
  refine dotProduct_unifSetVec ?_; rw [card_offDiagSet]
  have h2 : 2 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn1 : 2 ^ 1 ≤ 2 ^ n)
  exact Nat.mul_pos (by omega) (by omega)
/-- Reflection diffuser `2 |offDiagSet n⟩⟨offDiagSet n| - I` on `2 * n` address wires (`n ≥
  1`). -/
noncomputable def offDiagDiffuserUnitary (n : ℕ) (hn1 : 1 ≤ n) : Unitary (2 ^ (2 * n)) :=
  unitReflectUnitary (unifSetVec (offDiagSet n)) (dotProduct_unifSetVec_offDiagSet hn1)
theorem isRealMatrix_offDiagDiffuserUnitary (n : ℕ) (hn1 : 1 ≤ n) : IsRealMatrix
  (offDiagDiffuserUnitary n hn1).1 :=
  isRealMatrix_unitReflectUnitary (dotProduct_unifSetVec_offDiagSet hn1) fun u ↦ by
    dsimp only [unifSetVec]; split_ifs <;> simp
/-- Flag-`0`-subspace reflection `2 |offDiagSet ⊗ 0⟩⟨offDiagSet ⊗ 0| - I` on `(n + 1) * 2`
  wires. -/
noncomputable def ctrlOffDiagDiffuserUnitary (n : ℕ) (hn1 : 1 ≤ n) :
    Unitary (2 ^ ((n + 1) * 2)) :=
  unitReflectUnitary
    ((localAddrReg n 2).tensorState (unifSetVec (offDiagSet n)) (Pi.single 0 1))
    (by rw [dotProduct_tensorState, dotProduct_unifSetVec_offDiagSet hn1, dotProduct_env_single,
          mul_one])
theorem isRealMatrix_ctrlOffDiagDiffuserUnitary (n : ℕ) (hn1 : 1 ≤ n) : IsRealMatrix
  (ctrlOffDiagDiffuserUnitary n hn1).1 := isRealMatrix_unitReflectUnitary _ fun z ↦ by
    dsimp only [QRegister.tensorState, unifSetVec]
    by_cases hE : ((localAddrReg n 2).basisSplitEquiv z).2 = 0
    · rw [hE, Pi.single_eq_same, mul_one]; split_ifs <;> simp
    · simp [Pi.single_eq_of_ne hE]
theorem offDiagDiffuser_lockSetKraus0_planeVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn2 : 2 ≤ n)
  (hA1 : A.card = 1) (s α : ℝ) :
    let θ := halfAngleSet n 2
    (offDiagDiffuserUnitary n (by omega)).1 *ᵥ (lockSetKraus0 (oddSet n 2 A) s *ᵥ offDiagPlaneVec
      n A α) = ((s * Real.cos (2 * θ) * Real.sin α + Real.sin (2 * θ) * Real.cos α : ℝ) : ℂ) •
      unifSetVec (oddSet n 2 A) + ((Real.cos (2 * θ) * Real.cos α - s * Real.sin (2 * θ) * Real.sin
      α : ℝ) : ℂ) • unifSetVec (offDiagUnmarkedSet n A) := by
  intro θ; have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have hM1 : 1 ≤ (oddSet n 2 A).card := (by rw [card_oddSet_two_of_card_one hA1]; omega)
  have hU1 : 1 ≤ (offDiagUnmarkedSet n A).card :=
    (by rw [card_offDiagUnmarkedSet_of_card_one hn2 hA1]; exact Nat.mul_pos (by omega) (by omega))
  have hdisj : Disjoint (oddSet n 2 A) (offDiagUnmarkedSet n A) := Finset.disjoint_sdiff
  have hkM : lockSetKraus0 (oddSet n 2 A) s *ᵥ unifSetVec (oddSet n 2 A) = ((-s : ℝ) : ℂ) •
    unifSetVec (oddSet n 2 A) := by
    funext u; simp only [lockSetKraus0, Matrix.mulVec_diagonal, unifSetVec, Pi.smul_apply,
      smul_eq_mul]
    split_ifs <;> { push_cast; ring }
  have hkU : lockSetKraus0 (oddSet n 2 A) s *ᵥ unifSetVec (offDiagUnmarkedSet n A) = unifSetVec
    (offDiagUnmarkedSet n A) := by
    funext u; simp only [lockSetKraus0, Matrix.mulVec_diagonal, unifSetVec]
    by_cases huM : u ∈ oddSet n 2 A
    · have huU : u ∉ offDiagUnmarkedSet n A := fun h ↦ (Finset.mem_sdiff.1 h).2 huM; simp [huM, huU]
    · simp [huM]
  set w := lockSetKraus0 (oddSet n 2 A) s *ᵥ offDiagPlaneVec n A α
  have hw_eq : w = ((-s * Real.sin α : ℝ) : ℂ) • unifSetVec (oddSet n 2 A) + (Real.cos α : ℂ) •
    unifSetVec (offDiagUnmarkedSet n A) := by
    dsimp only [w, offDiagPlaneVec]; rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hkM, hkU]; funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  rw [offDiagDiffuserUnitary, unitReflectUnitary_mulVec (dotProduct_unifSetVec_offDiagSet
    (by omega)), unifSetVec_offDiagSet_eq_plane hn2 hA1, hw_eq]
  have hdM := dotProduct_unifSetVec hM1; have hdU := dotProduct_unifSetVec hU1; have hdMU :=
    dotProduct_unifSetVec_disjoint hdisj; have hdUM := dotProduct_unifSetVec_disjoint hdisj.symm
  have hdot : star (offDiagPlaneVec n A θ) ⬝ᵥ (((-s * Real.sin α : ℝ) : ℂ) • unifSetVec (oddSet n 2
    A) + (Real.cos α : ℂ) • unifSetVec (offDiagUnmarkedSet n A)) = ((-s * Real.sin θ * Real.sin α +
    Real.cos θ * Real.cos α : ℝ) : ℂ) := by
    dsimp only [offDiagPlaneVec]; simp only [star_add, star_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, hdM, hdU, hdMU, hdUM, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add, RCLike.star_def, Complex.conj_ofReal]; push_cast; ring
  rw [hdot]; have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := Real.cos_two_mul' θ
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hcoeffM : 2 * (-s * Real.sin θ * Real.sin α + Real.cos θ * Real.cos α) * Real.sin θ - (-s *
    Real.sin α) = s * Real.cos (2 * θ) * Real.sin α + Real.sin (2 * θ) * Real.cos α := by
    rw [hs2, hc2]; linear_combination -s * Real.sin α * hsc
  have hcoeffU : 2 * (-s * Real.sin θ * Real.sin α + Real.cos θ * Real.cos α) * Real.cos θ -
    Real.cos α = Real.cos (2 * θ) * Real.cos α - s * Real.sin (2 * θ) * Real.sin α := by
    rw [hs2, hc2]; linear_combination Real.cos α * hsc
  have hM_c := congrArg Complex.ofReal hcoeffM; have hU_c := congrArg Complex.ofReal hcoeffU
  dsimp only [θ] at hM_c hU_c; simp only [Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] at hM_c hU_c ⊢; funext u
  dsimp only [offDiagPlaneVec]; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination unifSetVec (oddSet n 2 A) u * hM_c +
    unifSetVec (offDiagUnmarkedSet n A) u * hU_c
theorem offDiagGroverStep_planeVec {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hn2 : 2 ≤ n) (hA1 : A.card = 1) (α : ℝ) :
    (offDiagDiffuserUnitary n (by omega)).1 *ᵥ
        (setOracleMatrix (oddSet n 2 A) *ᵥ offDiagPlaneVec n A α) =
      offDiagPlaneVec n A (α + 2 * halfAngleSet n 2) := by
  have hkraus : setOracleMatrix (oddSet n 2 A) = lockSetKraus0 (oddSet n 2 A) 1 :=
    (by ext i j; simp [setOracleMatrix, lockSetKraus0]); rw [hkraus,
    offDiagDiffuser_lockSetKraus0_planeVec hn2 hA1 1 α]; dsimp only [offDiagPlaneVec]
  have hs : 1 * Real.cos (2 * halfAngleSet n 2) * Real.sin α + Real.sin (2 * halfAngleSet n 2) *
    Real.cos α = Real.sin (α + 2 * halfAngleSet n 2) := (by rw [Real.sin_add]; ring)
  have hc : Real.cos (2 * halfAngleSet n 2) * Real.cos α - 1 * Real.sin (2 * halfAngleSet n 2) *
    Real.sin α = Real.cos (α + 2 * halfAngleSet n 2) := (by rw [Real.cos_add]; ring); rw [hs, hc]
theorem ctrlOffDiagRound_locked {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn2 : 2 ≤ n) (hA1 : A.card = 1)
  {β : ℝ} (h2θ : 2 * halfAngleSet n 2 ≤ β) (hβ_lt : β < π / 2) :
    let θ := halfAngleSet n 2; let s := lockedRatio β θ; let α := lockedAlpha β θ
    let Ubody := ctrlOffDiagDiffuserUnitary n (by omega) * chordUnitary n 2 (by omega) s * flagConj
      n 2 * parallelMarkingOracle 2 A * flagConj n 2 * chordUnitary n 2 (by omega) s
    Ubody.1 *ᵥ (localAddrReg n 2).tensorState (offDiagPlaneVec n A β) (Pi.single 0 1) = (α : ℂ) •
      (localAddrReg n 2).tensorState (offDiagPlaneVec n A β) (Pi.single 0 1) + ((√(1 - α ^ 2) : ℝ) :
      ℂ) • (localAddrReg n 2).tensorState (unifSetVec (oddSet n 2 A)) (Pi.single 1 1) := by
  intro θ s α Ubody; have hθ_pos : 0 < θ := Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos
    (by norm_num) (by positivity)))
  obtain ⟨hs0, hs1, hα_pos, hα_sq_lt⟩ := lockedRatio_bounds hθ_pos h2θ hβ_lt
  have hmid : Ubody.1 = (ctrlOffDiagDiffuserUnitary n (by omega)).1 * ((chordMat n 2 (by omega) s *
    sDiagM n 2 A * chordMat n 2 (by omega) s)) := by
    have hpar : (flagConj n 2 * parallelMarkingOracle 2 A * flagConj n 2).1 = sDiagM n 2 A :=
      (by simp only [Submonoid.coe_mul, flagConj_mul_parallelMarkingOracle_mul_flagConj])
    dsimp only [Ubody]; simp only [Submonoid.coe_mul, chordUnitary]
    calc (ctrlOffDiagDiffuserUnitary n (by omega)).1 * chordMat n 2 (by omega) s * (flagConj n
          2).1 * (parallelMarkingOracle 2 A).1 * (flagConj n 2).1 * chordMat n 2 (by omega) s =
          (ctrlOffDiagDiffuserUnitary n (by omega)).1 * (chordMat n 2 (by omega) s * ((flagConj n
          2).1 * (parallelMarkingOracle 2 A).1 * (flagConj n 2).1) * chordMat n 2 (by omega)
          s) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← Submonoid.coe_mul, ← Submonoid.coe_mul, hpar]
  rw [hmid, ← Matrix.mulVec_mulVec, parityMat_mulVec_zero (by omega) A hs0 hs1]; set v0 :=
    lockSetKraus0 (oddSet n 2 A) s *ᵥ offDiagPlaneVec n A β
  set v1 := pinHitVec (oddSet n 2 A) s (offDiagPlaneVec n A β)
  -- Action of `ctrlOffDiagDiffuserUnitary` on `Pi.single 0 1` and `Pi.single 1 1`
  have h01_ne : (0 : (localAddrReg n 2).Environment → ZMod 2) ≠ 1 :=
    (by intro heq; exact zero_ne_one (congrFun heq (localFlagEnvWire n 2 s0)))
  have hc0 : (ctrlOffDiagDiffuserUnitary n (by omega)).1 *ᵥ (localAddrReg n 2).tensorState v0
    (Pi.single 0 1) = (localAddrReg n 2).tensorState ((offDiagDiffuserUnitary n (by omega)).1 *ᵥ v0)
    (Pi.single 0 1) := by
    rw [ctrlOffDiagDiffuserUnitary, unitReflectUnitary_mulVec, dotProduct_tensorState_pair,
      dotProduct_env_single, mul_one]; funext z; simp only [Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, QRegister.tensorState, offDiagDiffuserUnitary, unitReflectUnitary_mulVec]; ring
  have hc1 : (ctrlOffDiagDiffuserUnitary n (by omega)).1 *ᵥ (localAddrReg n 2).tensorState v1
    (Pi.single 1 1) = (localAddrReg n 2).tensorState (-v1) (Pi.single 1 1) := by
    rw [ctrlOffDiagDiffuserUnitary, unitReflectUnitary_mulVec, dotProduct_tensorState_pair]
    have henv0 : star (Pi.single (0 : (localAddrReg n 2).Environment → ZMod 2) (1 : ℂ)) ⬝ᵥ Pi.single
      1 1 = 0 := by
      rw [dotProduct, Finset.sum_eq_single 0]
      · rw [Pi.single_apply, ite_eq_right h01_ne, mul_zero]
      · intro x _ hx; rw [Pi.star_apply, Pi.single_eq_of_ne hx, star_zero, zero_mul]
      · intro habs; exact (habs (Finset.mem_univ 0)).elim
    rw [henv0, mul_zero, mul_zero, zero_smul, zero_sub]; funext z; simp [QRegister.tensorState]
  rw [Matrix.mulVec_add, hc0, hc1]
  -- Evaluate `(offDiagDiffuserUnitary *ᵥ v0)` via locked trig algebra
  have hsinβ_ne : Real.sin β ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [Real.pi_pos])).ne'; have hcos_sub : Real.cos (β - 2 * θ) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩).ne'
  have hssin : s * Real.sin β = α * Real.sin (β - 2 * θ) :=
    (by dsimp only [s, α, lockedRatio, lockedAlpha]; field_simp)
  have htrig1 : s * Real.cos (2 * θ) * Real.sin β + Real.sin (2 * θ) * Real.cos β = α * Real.sin β
    := by
    calc s * Real.cos (2 * θ) * Real.sin β + Real.sin (2 * θ) * Real.cos β = (s * Real.sin β) *
          Real.cos (2 * θ) + (α * Real.cos (β - 2 * θ)) * Real.sin (2 * θ) := by
            have hαc : α * Real.cos (β - 2 * θ) = Real.cos β := div_mul_cancel₀ _ hcos_sub
            rw [hαc]; ring
      _ = α * (Real.sin (β - 2 * θ) * Real.cos (2 * θ) +
            Real.cos (β - 2 * θ) * Real.sin (2 * θ)) := by rw [hssin]; ring
      _ = α * Real.sin β := by rw [← Real.sin_add, show β - 2 * θ + 2 * θ = β by ring]
  have htrig2 : Real.cos (2 * θ) * Real.cos β - s * Real.sin (2 * θ) * Real.sin β = α * Real.cos β
    := by
    calc Real.cos (2 * θ) * Real.cos β - s * Real.sin (2 * θ) * Real.sin β = (α * Real.cos (β - 2 *
          θ)) * Real.cos (2 * θ) - (s * Real.sin β) * Real.sin (2 * θ) := by
            have hαc : α * Real.cos (β - 2 * θ) = Real.cos β := div_mul_cancel₀ _ hcos_sub
            rw [hαc]; ring
      _ = α * (Real.cos (β - 2 * θ) * Real.cos (2 * θ) -
            Real.sin (β - 2 * θ) * Real.sin (2 * θ)) := by rw [hssin]; ring
      _ = α * Real.cos β := by rw [← Real.cos_add, show β - 2 * θ + 2 * θ = β by ring]
  have hv0_out : (offDiagDiffuserUnitary n (by omega)).1 *ᵥ v0 = (α : ℂ) • offDiagPlaneVec n A β
    := by
    dsimp only [v0]; rw [offDiagDiffuser_lockSetKraus0_planeVec hn2 hA1 s β, htrig1, htrig2]
    dsimp only [offDiagPlaneVec]; funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul];
      push_cast; ring
  have hv1_out : -v1 = ((2 * chordCos s * chordSin s * Real.sin β : ℝ) : ℂ) • unifSetVec (oddSet n 2
    A) := by
    funext u; dsimp only [v1, pinHitVec, offDiagPlaneVec, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]; by_cases huM : u ∈ oddSet n 2 A
    · have huU : u ∉ offDiagUnmarkedSet n A := fun h ↦ (Finset.mem_sdiff.1 h).2 huM
      have h0U : unifSetVec (offDiagUnmarkedSet n A) u = 0 := (by simp [unifSetVec, huU])
      rw [ite_eq_left huM, h0U, mul_zero, add_zero]; push_cast; ring
    · simp [huM, unifSetVec]
  rw [hv0_out, hv1_out, (localAddrReg n 2).tensorState_smul_left, (localAddrReg n
    2).tensorState_smul_left]
  set cHit : ℝ := 2 * chordCos s * chordSin s * Real.sin β
  have hcHit_nn : 0 ≤ cHit := by
    dsimp only [cHit, chordCos, chordSin]; have hsβ : 0 ≤ Real.sin β :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]); positivity
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have hM1 : 1 ≤ (oddSet n 2 A).card := (by rw [card_oddSet_two_of_card_one hA1]; omega)
  have hψ_in : star ((localAddrReg n 2).tensorState (offDiagPlaneVec n A β) (Pi.single 0 1)) ⬝ᵥ
    (localAddrReg n 2).tensorState (offDiagPlaneVec n A β) (Pi.single 0 1) = 1 := by
    rw [dotProduct_tensorState, dotProduct_offDiagPlaneVec hn2 hA1 β, dotProduct_env_single,
      mul_one]
  have hnorm_U := dotProduct_unitary_mulVec Ubody hψ_in; rw [hmid, ← Matrix.mulVec_mulVec,
    parityMat_mulVec_zero (by omega) A hs0 hs1, Matrix.mulVec_add, hc0, hc1, hv0_out, hv1_out,
    (localAddrReg n 2).tensorState_smul_left, (localAddrReg n 2).tensorState_smul_left] at hnorm_U
  have horth01 : star ((localAddrReg n 2).tensorState (offDiagPlaneVec n A β) (Pi.single 0 1)) ⬝ᵥ
    (localAddrReg n 2).tensorState (unifSetVec (oddSet n 2 A)) (Pi.single 1 1) = 0 := by
    rw [dotProduct_tensorState_pair]
    have he : star (Pi.single (0 : (localAddrReg n 2).Environment → ZMod 2) (1 : ℂ)) ⬝ᵥ Pi.single 1
      1 = 0 := by
      rw [dotProduct, Finset.sum_eq_single 0]
      · rw [Pi.single_apply, ite_eq_right h01_ne, mul_zero]
      · intro x _ hx; rw [Pi.star_apply, Pi.single_eq_of_ne hx, star_zero, zero_mul]
      · intro habs; exact (habs (Finset.mem_univ 0)).elim
    rw [he, mul_zero]
  have horth10 : star ((localAddrReg n 2).tensorState (unifSetVec (oddSet n 2 A)) (Pi.single 1 1))
    ⬝ᵥ (localAddrReg n 2).tensorState (offDiagPlaneVec n A β) (Pi.single 0 1) = 0 := by
    rw [dotProduct_tensorState_pair]
    have he : star (Pi.single (1 : (localAddrReg n 2).Environment → ZMod 2) (1 : ℂ)) ⬝ᵥ Pi.single 0
      1 = 0 := by
      rw [dotProduct, Finset.sum_eq_single 1]
      · rw [Pi.single_apply, ite_eq_right h01_ne.symm, mul_zero]
      · intro x _ hx; rw [Pi.star_apply, Pi.single_eq_of_ne hx, star_zero, zero_mul]
      · intro habs; exact (habs (Finset.mem_univ 1)).elim
    rw [he, mul_zero]
  have hψ_hit : star ((localAddrReg n 2).tensorState (unifSetVec (oddSet n 2 A)) (Pi.single 1 1)) ⬝ᵥ
    (localAddrReg n 2).tensorState (unifSetVec (oddSet n 2 A)) (Pi.single 1 1) = 1 :=
    (by rw [dotProduct_tensorState, dotProduct_unifSetVec hM1, dotProduct_env_single, mul_one])
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    hψ_in, hψ_hit, horth01, horth10, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add,
    RCLike.star_def, Complex.conj_ofReal] at hnorm_U
  have hsq_real : α ^ 2 + cHit ^ 2 = 1 := by
    have hc := Complex.ofReal_injective (by push_cast; exact hnorm_U :
      ((α * α + cHit * cHit : ℝ) : ℂ) = ((1 : ℝ) : ℂ))
    linarith [hc, sq α, sq cHit]
  have hcHit_eq : cHit = √(1 - α ^ 2) :=
    (by rw [show 1 - α ^ 2 = cHit ^ 2 by linarith, Real.sqrt_sq hcHit_nn]); rw [hcHit_eq]
/-! ## 5. Shared 1-Query Odd-Pair Target Extraction (`extractOddPairStage1Circuit`) -/
/-- Signed odd-parity uniform state `(sgn: ℂ)` on `(x*, y)` and `± 1` on `(y, x*)` (`y ∉
  A`). -/
noncomputable def signedOddVec (n : ℕ) (A : Finset (Fin (2 ^ n))) (anti : Bool)
    (u : Fin (2 ^ (2 * n))) : ℂ :=
  let c : ℝ := 1 / √(2 * ((2 ^ n : ℝ) - 1))
  if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A then
    if anti then ((-c : ℝ) : ℂ) else (c : ℂ)
  else if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A then
    (c : ℂ)
  else
    0
theorem signedOddVec_false_eq_unifSetVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hA1 : A.card = 1) :
  signedOddVec n A false = unifSetVec (oddSet n 2 A) := by
  funext u; dsimp only [signedOddVec, unifSetVec]; rw [card_oddSet_two_of_card_one hA1,
    Nat.cast_mul, Nat.cast_sub Nat.one_le_two_pow]; push_cast; by_cases hu : u ∈ oddSet n 2 A
  · rw [ite_eq_left hu]; rcases (mem_oddSet_two_iff u).1 hu with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0,
      h1]
  · rw [ite_eq_right hu]; have hnot := mt (mem_oddSet_two_iff u).2 hu; simp only [not_or, not_and,
      not_not] at hnot; by_cases h0 : addrEquiv n 2 u s0 ∈ A
    · have h1 := hnot.1 h0; simp [h0, h1]
    · by_cases h1 : addrEquiv n 2 u s1 ∈ A
      · exact (hnot.2 h0 h1).elim
      · simp [h0, h1]
theorem dotProduct_signedOddVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn2 : 2 ≤ n) (hA1 : A.card = 1)
  (anti : Bool) : star (signedOddVec n A anti) ⬝ᵥ signedOddVec n A anti = 1 := by
  have heq : star (signedOddVec n A anti) ⬝ᵥ signedOddVec n A anti = star (signedOddVec n A false)
    ⬝ᵥ signedOddVec n A false := by
    simp only [dotProduct, signedOddVec, Pi.star_apply]; refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases h01 : addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A
    · cases anti <;> simp [h01]
    · simp [h01]
  rw [heq, signedOddVec_false_eq_unifSetVec hA1]
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  refine dotProduct_unifSetVec ?_; rw [card_oddSet_two_of_card_one hA1]; omega
private theorem parallelMarkingOracle_mulVec_signedOddVec_aux {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (_hA1 : A.card = 1) (anti : Bool) : (parallelMarkingOracle 2 A).1 *ᵥ (localAddrReg n
    2).tensorState (signedOddVec n A anti) (Pi.single 0 1) = ∑ o : Fin (2 ^ 2), (localAddrReg n
    2).tensorState (if o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then fun u ↦ if addrEquiv n
    2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A then signedOddVec n A anti u else 0 else if o = ⟨2,
    (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then fun u ↦ if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2
    u s1 ∈ A then signedOddVec n A anti u else 0 else 0) (Pi.single (envOfMask n o) 1) := by
  have hexpand : (localAddrReg n 2).tensorState (signedOddVec n A anti) (Pi.single 0 1) = ∑ z : Fin
    (2 ^ ((n + 1) * 2)), ((localAddrReg n 2).tensorState (signedOddVec n A anti) (Pi.single 0 1) z)
    • Pi.single z (1 : ℂ) := (by funext w; simp [Finset.sum_apply, Pi.single_apply]); rw [hexpand,
    Matrix.mulVec_sum]; simp_rw [Matrix.mulVec_smul, parallelMarkingOracle_mulVec_single_local]
  -- `[x_i ∈ A]` into `localSlotFlag`
  have hfin2 : List.finRange 2 = [s0, s1] := rfl; simp_rw [hfin2]
  set markMap := localAppMark n 2 A [s0, s1]
  have haddr (z : Fin (2 ^ ((n + 1) * 2))) (i : Fin 2) : localSlotAddr n 2 (markMap z) i =
    localSlotAddr n 2 z i := by
    dsimp only [markMap, localAppMark, localSlotAddr]; rcases fin2_eq_s0_or_s1 i with rfl | rfl
    · rw [(localSlotReg n 2 s0).extractIndex_replaceIndex, extractIndex_localIdxReg_slotMarkPerm]
      rw [(localSlotReg n 2 s0).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s1)
        (localSlotReg_disjoint (by simp))]
    · rw [(localSlotReg n 2 s1).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s0)
        (localSlotReg_disjoint (by simp)), (localSlotReg n 2 s1).extractIndex_replaceIndex,
        extractIndex_localIdxReg_slotMarkPerm]
  have hexA (z : Fin (2 ^ ((n + 1) * 2))) : (localAddrReg n 2).extractIndex (markMap z) =
    (localAddrReg n 2).extractIndex z := by
    apply (addrEquiv n 2).injective; funext i; rw [addrEquiv_extractIndex_localAddrReg,
      addrEquiv_extractIndex_localAddrReg, haddr]
  have hflag (z : Fin (2 ^ ((n + 1) * 2))) (i : Fin 2) : basisBits 1 (localSlotFlag n 2 (markMap z)
    i) 0 = basisBits 1 (localSlotFlag n 2 z i) 0 + (if localSlotAddr n 2 z i ∈ A then 1 else 0)
    := by
    dsimp only [markMap, localAppMark, localSlotFlag, localSlotAddr]; have hmw : (localMarkerReg
      n).wires 0 = 0 := Fin.ext (by simp [localMarkerReg]); rcases fin2_eq_s0_or_s1 i with rfl | rfl
    · rw [(localMarkerReg n).basisBits_extractIndex, (localMarkerReg n).basisBits_extractIndex, hmw,
        (localSlotReg n 2 s0).extractIndex_replaceIndex, (localSlotReg n 2
        s0).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s1) (localSlotReg_disjoint
        (by simp)), basisBits_slotMarkPerm]
      by_cases hm : (localIdxReg n).extractIndex ((localSlotReg n 2 s0).extractIndex z) ∈ A <;> simp
        [hm]
    · rw [(localMarkerReg n).basisBits_extractIndex, (localMarkerReg n).basisBits_extractIndex, hmw,
        (localSlotReg n 2 s1).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s0)
        (localSlotReg_disjoint (by simp)), (localSlotReg n 2 s1).extractIndex_replaceIndex,
        basisBits_slotMarkPerm]; by_cases hm : (localIdxReg n).extractIndex ((localSlotReg n 2
        s1).extractIndex z) ∈ A <;> simp [hm]
  have hmark_inv (z : Fin (2 ^ ((n + 1) * 2))) : markMap (markMap z) = z := by
    apply (localAddrReg n 2).basisSplitEquiv.injective; ext1
    · rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst, hexA, hexA]
    · funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
      · rw [← basisBits_localSlotFlag, ← basisBits_localSlotFlag, hflag, hflag, haddr, add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
      · rw [← basisBits_localSlotFlag, ← basisBits_localSlotFlag, hflag, hflag, haddr, add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
  funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; rw [Finset.sum_eq_single
    (markMap w)]
  · rw [show markMap (markMap w) = w from hmark_inv w, Pi.single_eq_same, mul_one]
    have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2
      ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^
      2)⟩} := (by ext x; fin_cases x <;> simp); rw [huniv4, Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    dsimp only [QRegister.tensorState]; rw [hexA]; set u := (localAddrReg n 2).extractIndex w
    have h0_addr : localSlotAddr n 2 w s0 = addrEquiv n 2 u s0 :=
      (addrEquiv_extractIndex_localAddrReg n 2 w s0).symm; have h1_addr : localSlotAddr n 2 w s1 =
      addrEquiv n 2 u s1 := (addrEquiv_extractIndex_localAddrReg n 2 w s1).symm
    have henv_zero_iff : ((localAddrReg n 2).basisSplitEquiv (markMap w)).2 = 0 ↔ ∀ i : Fin 2,
      basisBits 1 (localSlotFlag n 2 w i) 0 = (if addrEquiv n 2 u i ∈ A then 1 else 0) := by
      constructor
      · intro h0 i; have hi := congrFun h0 (localFlagEnvWire n 2 i); rw [← basisBits_localSlotFlag,
          hflag, Pi.zero_apply] at hi
        have hadd := congrArg (· + if localSlotAddr n 2 w i ∈ A then 1 else 0) hi
        simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hadd
        rcases fin2_eq_s0_or_s1 i with rfl | rfl
        · rwa [h0_addr] at hadd
        · rwa [h1_addr] at hadd
      · intro hall; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
        · rw [← basisBits_localSlotFlag, hflag, hall s0, h0_addr, CharTwo.add_self_eq_zero]; rfl
        · rw [← basisBits_localSlotFlag, hflag, hall s1, h1_addr, CharTwo.add_self_eq_zero]; rfl
    simp only [
      show (0 : Fin (2 ^ 2)) ≠ ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
      show (0 : Fin (2 ^ 2)) ≠ ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp,
      show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
        (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
      show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
        (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
      show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
        (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp,
      ↓reduceIte, Pi.zero_apply, zero_mul, zero_add, add_zero]
    by_cases hc10 : addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A
    · have hc01 : ¬ (addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A) := fun h ↦ h.1 hc10.1
      rw [ite_eq_left hc10, ite_eq_right hc01, zero_mul, add_zero]
      have hm_eq : ((localAddrReg n 2).basisSplitEquiv (markMap w)).2 = 0 ↔ ((localAddrReg n
        2).basisSplitEquiv w).2 = envOfMask n ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ := by
        rw [henv_zero_iff]; constructor
        · intro hall; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
          · rw [← basisBits_localSlotFlag, hall s0, ite_eq_left hc10.1, envOfMask_s0]; simp
          · rw [← basisBits_localSlotFlag, hall s1, ite_eq_right hc10.2, envOfMask_s1]; simp
        · intro hwE i; rw [basisBits_localSlotFlag, hwE]; rcases fin2_eq_s0_or_s1 i with rfl | rfl
          · rw [envOfMask_s0, ite_eq_left hc10.1]; simp
          · rw [envOfMask_s1, ite_eq_right hc10.2]; simp
      congr 1; simp only [Pi.single_apply, hm_eq]
    · by_cases hc01 : addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A
      · rw [ite_eq_right hc10, ite_eq_left hc01, zero_mul, zero_add]
        have hm_eq : ((localAddrReg n 2).basisSplitEquiv (markMap w)).2 = 0 ↔ ((localAddrReg n
          2).basisSplitEquiv w).2 = envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ := by
          rw [henv_zero_iff]; constructor
          · intro hall; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
            · rw [← basisBits_localSlotFlag, hall s0, ite_eq_right hc01.1, envOfMask_s0]; simp
            · rw [← basisBits_localSlotFlag, hall s1, ite_eq_left hc01.2, envOfMask_s1]; simp
          · intro hwE i; rw [basisBits_localSlotFlag, hwE]; rcases fin2_eq_s0_or_s1 i with rfl | rfl
            · rw [envOfMask_s0, ite_eq_right hc01.1]; simp
            · rw [envOfMask_s1, ite_eq_left hc01.2]; simp
        congr 1; simp only [Pi.single_apply, hm_eq]
      · have hs0_zero : signedOddVec n A anti u = 0 :=
          (by dsimp only [signedOddVec]; rw [ite_eq_right hc10, ite_eq_right hc01])
        simp only [ite_eq_right hc10, ite_eq_right hc01, hs0_zero, zero_mul, add_zero]
  · intro z _ hzw; have hne : w ≠ markMap z := fun h ↦ hzw (by rw [h, hmark_inv])
    rw [Pi.single_eq_of_ne hne, mul_zero]
  · intro habs; exact (habs (Finset.mem_univ (markMap w))).elim
theorem parallelMarkingOracle_mulVec_signedOddVec {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (_hA1 : A.card = 1) (anti : Bool) :
    (parallelMarkingOracle 2 A).1 *ᵥ (localAddrReg n 2).tensorState (signedOddVec n A anti)
      (Pi.single 0 1) = ∑ o : Fin (2 ^ 2), (localAddrReg n 2).tensorState (if o = ⟨1, by decide⟩
      then fun u ↦ if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A then signedOddVec n A anti u
      else 0 else if o = ⟨2, by decide⟩ then fun u ↦ if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1
      ∈ A then signedOddVec n A anti u else 0 else 0) (Pi.single (envOfMask n o) 1) :=
      parallelMarkingOracle_mulVec_signedOddVec_aux _hA1 anti
/-! ## 6. Odd-Pair Extraction & Off-Diagonal Stationary-chord Loop (`m = 2, r = 1`) -/
theorem envOfMask_eq_iff_slotFlags {n : ℕ} (z : Fin (2 ^ ((n + 1) * 2))) (o : Fin (2 ^ 2)) :
  ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n o ↔ (localMarkerReg n).extractIndex
  ((localSlotReg n 2 s0).extractIndex z) = (if o.val.testBit 0 then 1 else 0) ∧ (localMarkerReg
  n).extractIndex ((localSlotReg n 2 s1).extractIndex z) = (if o.val.testBit 1 then 1 else 0) := by
  constructor
  · intro hE
    have hbit (i : Fin 2) : basisBits 1 (localSlotFlag n 2 z i) 0 = envOfMask n o (localFlagEnvWire
      n 2 i) := (by rw [basisBits_localSlotFlag, hE]); have h0 := hbit s0; have h1 := hbit s1
    simp only [envOfMask, ↓reduceIte, (localFlagEnvWire_ne n).symm] at h0 h1
    exact ⟨(basisBits_one_zero_eq_ite_iff _ _).1 h0, (basisBits_one_zero_eq_ite_iff _ _).1 h1⟩
  · rintro ⟨h0, h1⟩; funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
    · rw [← basisBits_localSlotFlag, envOfMask, ite_eq_left rfl]
      exact (basisBits_one_zero_eq_ite_iff _ _).2 h0
    · rw [← basisBits_localSlotFlag, envOfMask, ite_eq_right (localFlagEnvWire_ne n).symm]
      exact (basisBits_one_zero_eq_ite_iff _ _).2 h1
theorem prodSlotLocalVec_roundOut_one {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hn2 : 2 ≤ n) (hA1 : A.card = 1) (anti : Bool) :
    (localAddrReg n 2).tensorState
        (fun u ↦ if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A then
          signedOddVec n A anti u else 0)
        (Pi.single (envOfMask n ⟨1, by decide⟩) 1) =
      ((√(1 / 2) : ℝ) : ℂ) •
        ((if anti then (1 : ℂ) else -1) •
          prodSlotLocalVec (fun i : Fin 2 ↦ roundOutSlotVec A 0 ((1 : ℕ).testBit i.val))) := by
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have hN1_pos : (0 : ℝ) < (2 ^ n : ℝ) - 1 :=
    (by have : (4 : ℝ) ≤ 2 ^ n := (by exact_mod_cast h4); linarith)
  have hrad : √(1 / 2 : ℝ) * (1 / √((2 ^ n : ℝ) - 1)) = 1 / √(2 * ((2 ^ n : ℝ) - 1)) := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, one_div_mul_one_div, ← Real.sqrt_mul
      (by positivity : (0 : ℝ) ≤ 2)]
  funext z; dsimp only [QRegister.tensorState, prodSlotLocalVec, Pi.smul_apply, smul_eq_mul]
  rw [Fin.prod_univ_two]; change (if addrEquiv n 2 ((localAddrReg n 2).extractIndex z) s0 ∈ A ∧
    addrEquiv n 2 ((localAddrReg n 2).extractIndex z) s1 ∉ A then signedOddVec n A anti
    ((localAddrReg n 2).extractIndex z) else 0) * (Pi.single (envOfMask n ⟨1, (Nat.lt_of_sub_eq_succ
    rfl : 1 < 2 ^ 2)⟩) 1 : ((localAddrReg n 2).Environment → ZMod 2) → ℂ) ((localAddrReg n
    2).basisSplitEquiv z).2 = ((√(1 / 2) : ℝ) : ℂ) * ((if anti then (1 : ℂ) else -1) *
    (roundOutSlotVec A 0 ((1 : ℕ).testBit 0) ((localSlotReg n 2 s0).extractIndex z) *
    roundOutSlotVec A 0 ((1 : ℕ).testBit 1) ((localSlotReg n 2 s1).extractIndex z))); have hb0 : (1
    : ℕ).testBit 0 = true := rfl; have hb1 : (1 : ℕ).testBit 1 = false := rfl; have hb0' : (⟨1,
    (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)).val.testBit 0 = true := (by rfl)
  have hb1' : (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)).val.testBit 1 = false :=
    (by rfl); rw [hb0, hb1]; simp only [roundOutSlotVec, Bool.false_eq_true, ↓reduceIte,
    slotPairVec]
  have haddr0 : (localIdxReg n).extractIndex ((localSlotReg n 2 s0).extractIndex z) = addrEquiv n 2
    ((localAddrReg n 2).extractIndex z) s0 := (addrEquiv_extractIndex_localAddrReg n 2 z s0).symm
  have haddr1 : (localIdxReg n).extractIndex ((localSlotReg n 2 s1).extractIndex z) = addrEquiv n 2
    ((localAddrReg n 2).extractIndex z) s1 := (addrEquiv_extractIndex_localAddrReg n 2 z s1).symm
  rw [haddr0, haddr1]; by_cases hE : ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n ⟨1,
    (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
  · obtain ⟨hf0, hf1⟩ := (envOfMask_eq_iff_slotFlags z ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^
      2)⟩).1 hE
    rw [hb0'] at hf0; rw [hb1'] at hf1; simp only [Bool.false_eq_true, ↓reduceIte] at hf0 hf1
    rw [hE, hf0, hf1]; simp only [Pi.single_eq_same, mul_one, Pi.neg_apply, planeVec, Real.sin_zero,
      Real.cos_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul, zero_add,
      unifSetVec, unifComplVec, hA1, Nat.cast_one, Real.sqrt_one, div_one]; set u := (localAddrReg n
      2).extractIndex z; by_cases hc : addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A
    · rw [ite_eq_left hc, ite_eq_left hc.1, ite_eq_right hc.2]; dsimp only [signedOddVec]
      rw [ite_eq_left hc, ← hrad]; cases anti <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> {
        push_cast; ring }
    · rw [ite_eq_right hc]; by_cases h0 : addrEquiv n 2 u s0 ∈ A
      · have h1 : addrEquiv n 2 u s1 ∈ A := (by by_contra h1; exact hc ⟨h0, h1⟩); simp [h0, h1]
      · simp [h0]
  · rw [Pi.single_eq_of_ne hE, mul_zero]; have hnot := mt (envOfMask_eq_iff_slotFlags z ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩).2 hE
    rw [hb0', hb1'] at hnot; simp only [↓reduceIte] at hnot; by_cases hf0 : (localMarkerReg
      n).extractIndex ((localSlotReg n 2 s0).extractIndex z) = 1
    · have hf1 : (localMarkerReg n).extractIndex ((localSlotReg n 2 s1).extractIndex z) ≠ 0 := fun h
        ↦ hnot ⟨hf0, h⟩; simp [Pi.single_eq_of_ne hf1]
    · simp [Pi.single_eq_of_ne hf0]
theorem prodSlotLocalVec_roundOut_two {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hn2 : 2 ≤ n) (hA1 : A.card = 1) (anti : Bool) :
    (localAddrReg n 2).tensorState
        (fun u ↦ if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A then
          signedOddVec n A anti u else 0)
        (Pi.single (envOfMask n ⟨2, by decide⟩) 1) =
      ((√(1 / 2) : ℝ) : ℂ) •
        (-prodSlotLocalVec (fun i : Fin 2 ↦ roundOutSlotVec A 0 ((2 : ℕ).testBit i.val))) := by
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have hrad : √(1 / 2 : ℝ) * (1 / √((2 ^ n : ℝ) - 1)) = 1 / √(2 * ((2 ^ n : ℝ) - 1)) := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, one_div_mul_one_div, ← Real.sqrt_mul
      (by positivity : (0 : ℝ) ≤ 2)]
  funext z; dsimp only [QRegister.tensorState, prodSlotLocalVec, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul]; rw [Fin.prod_univ_two]; change (if addrEquiv n 2 ((localAddrReg n 2).extractIndex
    z) s0 ∉ A ∧ addrEquiv n 2 ((localAddrReg n 2).extractIndex z) s1 ∈ A then signedOddVec n A anti
    ((localAddrReg n 2).extractIndex z) else 0) * (Pi.single (envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ
    rfl : 2 < 2 ^ 2)⟩) 1 : ((localAddrReg n 2).Environment → ZMod 2) → ℂ) ((localAddrReg n
    2).basisSplitEquiv z).2 = ((√(1 / 2) : ℝ) : ℂ) * -(roundOutSlotVec A 0 ((2 : ℕ).testBit 0)
    ((localSlotReg n 2 s0).extractIndex z) * roundOutSlotVec A 0 ((2 : ℕ).testBit 1) ((localSlotReg
    n 2 s1).extractIndex z)); have hb0 : (2 : ℕ).testBit 0 = false := rfl; have hb1 : (2 :
    ℕ).testBit 1 = true := rfl; have hb0' : (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^
    2)).val.testBit 0 = false := (by rfl); have hb1' : (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩
    : Fin (2 ^ 2)).val.testBit 1 = true := (by rfl); rw [hb0, hb1]; simp only [roundOutSlotVec,
    Bool.false_eq_true, ↓reduceIte, slotPairVec]
  have haddr0 : (localIdxReg n).extractIndex ((localSlotReg n 2 s0).extractIndex z) = addrEquiv n 2
    ((localAddrReg n 2).extractIndex z) s0 := (addrEquiv_extractIndex_localAddrReg n 2 z s0).symm
  have haddr1 : (localIdxReg n).extractIndex ((localSlotReg n 2 s1).extractIndex z) = addrEquiv n 2
    ((localAddrReg n 2).extractIndex z) s1 := (addrEquiv_extractIndex_localAddrReg n 2 z s1).symm
  rw [haddr0, haddr1]; by_cases hE : ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n ⟨2,
    (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩
  · obtain ⟨hf0, hf1⟩ := (envOfMask_eq_iff_slotFlags z ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^
      2)⟩).1 hE; rw [hb0'] at hf0; rw [hb1'] at hf1; rw [hE, hf0, hf1]
    simp only [Pi.single_eq_same, mul_one, Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, planeVec,
      Real.sin_zero, Real.cos_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul,
      zero_add, unifSetVec, unifComplVec, hA1, Nat.cast_one, Real.sqrt_one, div_one]; set u :=
      (localAddrReg n 2).extractIndex z
    by_cases hc : addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A
    · have hc' : ¬ (addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A) := fun h ↦ hc.1 h.1
      rw [ite_eq_left hc, ite_eq_right hc.1, ite_eq_left hc.2]; dsimp only [signedOddVec]
      rw [ite_eq_right hc', ite_eq_left hc, ← hrad]; push_cast; ring
    · rw [ite_eq_right hc]; by_cases h0 : addrEquiv n 2 u s0 ∈ A
      · simp [h0]
      · have h1 : addrEquiv n 2 u s1 ∉ A := fun h1 ↦ hc ⟨h0, h1⟩; simp [h0, h1]
  · rw [Pi.single_eq_of_ne hE, mul_zero]; have hnot := mt (envOfMask_eq_iff_slotFlags z ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩).2 hE
    rw [hb0', hb1'] at hnot; simp only [Bool.false_eq_true, ↓reduceIte] at hnot
    by_cases hf0 : (localMarkerReg n).extractIndex ((localSlotReg n 2 s0).extractIndex z) = 0
    · have hf1 : (localMarkerReg n).extractIndex ((localSlotReg n 2 s1).extractIndex z) ≠ 1 := fun h
        ↦ hnot ⟨hf0, h⟩; simp [Pi.single_eq_of_ne hf1]
    · simp [Pi.single_eq_of_ne hf0]
/-- Shared 1-query terminal target extractor from `signedOddVec n (S \ T) anti` (`|S \ T| =
  1`):
  queries the deflated parallel marking oracle once, measures `allMarkersReg`, and extracts
  the
  unique clicked slot via `onHitStage1Circuit`. -/
noncomputable def extractOddPairStage1Circuit {Var : Type} (res : Var) (n k : ℕ)
    (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2) :=
  .seq (deflateCirc n 2 T (.oracle (oracleReg n 2 k)))
    (.seq (.measure res (allMarkersReg n 2 k))
      (dispBits res 2 0 fun oVal ↦
        let o : Fin (2 ^ 2) := ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩
        if o = 0 then .skip else onHitStage1Circuit res n k (by decide) T o))
theorem extractOddPairStage1_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn2 :
  2 ≤ n) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA1 : (S \ T).card = 1)
  (anti : Bool) {Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)} (hΔ : PureStateAt ((oracleReg n
    2
  k).tensorState ((localAddrReg n 2).tensorState (signedOddVec n (S \ T) anti) (Pi.single 0 1))
  (Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1)) Δ) :
    let prog :=
      (extractOddPairStage1Circuit res n k T).compile QProg.qAssign (parallelMarkingOracle 2 S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
  intro prog; set A := S \ T
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have hAN : A.card < 2 ^ n := (by omega)
  let oracleS := parallelMarkingOracle 2 S; let oracleA := parallelMarkingOracle 2 A
  let modelS := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleS
  let modelA := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleA
  let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ :=
    Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1
  let ψ_in := (oracleReg n 2 k).tensorState
    ((localAddrReg n 2).tensorState (signedOddVec n A anti) (Pi.single 0 1)) env0
  have hψ_in : star ψ_in ⬝ᵥ ψ_in = 1 := by
    dsimp only [ψ_in]
    rw [dotProduct_tensorState, dotProduct_tensorState, dotProduct_signedOddVec hn2 hA1 anti,
      dotProduct_env_single, dotProduct_env_single, mul_one, mul_one]
  -- Step 1: Deflated oracle query (`cost = 1`)
  have hcost_q : expectedCost modelS ((deflateCirc (Var := Var) n 2 T (.oracle (oracleReg n 2
    k))).compile QProg.qAssign oracleS) Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
    rw [congrFun (expectedCost_deflateCirc n 2 hTS (c := .oracle (oracleReg n 2 k)) trivial) Δ]
    simp only [OracleDynamicCircuit.compile_oracle, expectedCost_qAssign]
    have hex : ∃ r : QRegister ((n + 1) * 2) (findAllQubits n 2 k),
        (oracleReg n 2 k).embedUnitary oracleA = r.embedUnitary oracleA := ⟨oracleReg n 2 k, rfl⟩
    have h1 : modelA.unitaryCost ((oracleReg n 2 k).embedUnitary oracleA) = 1 := by
      simp [modelA, CostModel.ofEmbeddedOracle, hex]
    rw [h1]; simp
  set Δq := (interp ((deflateCirc (Var := Var) n 2 T (.oracle (oracleReg n 2 k))).compile
    QProg.qAssign oracleS)).toStateFun Δ
  have hΔq_eq : Δq = CQState.qAssign ((oracleReg n 2 k).embedUnitary oracleA) Δ := by
    dsimp only [Δq]
    rw [interp_deflateCirc n 2 hTS (.oracle (oracleReg n 2 k)), OracleDynamicCircuit.compile_oracle,
      interp_qAssign]; rfl
  obtain ⟨hPq, htr_q⟩ := pureStateAt_qAssign ((oracleReg n 2 k).embedUnitary oracleA) hψ_in hΔ
  rw [← hΔq_eq] at hPq htr_q; let ψ_q := ((oracleReg n 2 k).embedUnitary oracleA).1 *ᵥ ψ_in
  have hψ_q : star ψ_q ⬝ᵥ ψ_q = 1 :=
    dotProduct_unitary_mulVec ((oracleReg n 2 k).embedUnitary oracleA) hψ_in
  -- Step 2: Measure `allMarkersReg n 2 k` (`0` cost)
  let w : Fin (2 ^ 2) → ℝ := fun o ↦ if o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then 1 / 2
    else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then 1 / 2 else 0
  have hw_nn (o : Fin (2 ^ 2)) : 0 ≤ w o := (by dsimp only [w]; split_ifs <;> norm_num)
  let ψ_out : Fin (2 ^ 2) → Fin (2 ^ findAllQubits n 2 k) → ℂ := fun o ↦ if o = ⟨1,
    (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then (if anti then (1 : ℂ) else -1) • prodSlotState n 2
    k (fun i ↦ roundOutSlotVec A 0 ((1 : ℕ).testBit i.val)) else if o = ⟨2, (Nat.lt_of_sub_eq_succ
    rfl : 2 < 2 ^ 2)⟩ then -prodSlotState n 2 k (fun i ↦ roundOutSlotVec A 0 ((2 : ℕ).testBit
    i.val)) else ψ_in
  have hψ_out (o : Fin (2 ^ 2)) : star (ψ_out o) ⬝ᵥ ψ_out o = 1 := by
    dsimp only [ψ_out]; by_cases h1 : o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
    · rw [ite_eq_left h1]; have hn1 := dotProduct_prodSlotState (n := n) (m := 2) (k := k)
        (fun i ↦ dotProduct_roundOutSlotVec (by omega) hAN 0 ((1 : ℕ).testBit i.val))
      cases anti <;> simp [hn1]
    · rw [ite_eq_right h1]; by_cases h2 : o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩
      · rw [ite_eq_left h2]; have hn2' := dotProduct_prodSlotState (n := n) (m := 2) (k := k)
          (fun i ↦ dotProduct_roundOutSlotVec (by omega) hAN 0 ((2 : ℕ).testBit i.val))
        simpa using hn2'
      · rw [ite_eq_right h2]; exact hψ_in
  have hproj (o : Fin (2 ^ 2)) : (allMarkersReg n 2 k).basisOutcomeProjector o *ᵥ ψ_q = ((√(w o) :
    ℝ) : ℂ) • ψ_out o := by
    have hψq_expand : ψ_q = (oracleReg n 2 k).tensorState ((parallelMarkingOracle 2 A).1 *ᵥ
      (localAddrReg n 2).tensorState (signedOddVec n A anti) (Pi.single 0 1)) env0 := by
      dsimp only [ψ_q, ψ_in, oracleA]
      rw [QRegister.embedUnitary_val, (oracleReg n 2 k).embedMatrix_mulVec_tensorState]
    rw [hψq_expand, parallelMarkingOracle_mulVec_signedOddVec hA1 anti,
      basisOutcomeProjector_allMarkers_oracle_tensorState]
    have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3,
      (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ := by
      fin_cases o <;> simp
    rcases ho_cases with rfl | rfl | rfl | rfl
    · funext z; simp [w, QRegister.tensorState]
    · simp only [↓reduceIte, w, ψ_out]
      rw [prodSlotLocalVec_roundOut_one hn2 hA1 anti, (oracleReg n 2 k).tensorState_smul_left,
        (oracleReg n 2 k).tensorState_smul_left]; rfl
    · simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
        (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte,
        w, ψ_out]
      rw [prodSlotLocalVec_roundOut_two hn2 hA1 anti, (oracleReg n 2 k).tensorState_smul_left]
      congr 1; funext z; simp [prodSlotState, QRegister.tensorState]
    · funext z; simp [w, QRegister.tensorState]
  set Δm := (interp (QProg.measureRegister res (allMarkersReg n 2 k))).toStateFun Δq
  have hmeas := measure_sliceState_of_pureStateAt res (allMarkersReg n 2 k)
    hψ_q w hw_nn ψ_out hψ_out hproj hPq
  let branchCirc (o : Fin (2 ^ 2)) :=
    if o = 0 then OracleDynamicCircuit.skip else onHitStage1Circuit res n k (by omega) T o
  let Post : CQAssertion (Store Var) (2 ^ findAllQubits n 2 k) :=
    liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
  have hbranch (o : Fin (2 ^ 2)) :
      let fo := (branchCirc o).compile QProg.qAssign oracleS; let Ξ_o := sliceState res 0 2 o.val Δm
      𝔼[(interp fo).toStateFun Ξ_o, Post] = w o * Δ.trace ∧
        expectedCost modelS fo Ξ_o = 0 := by
    intro fo Ξ_o; obtain ⟨hPo, htro⟩ := hmeas o; rw [htr_q] at htro
    have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3,
      (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ := by
      fin_cases o <;> simp
    rcases ho_cases with rfl | rfl | rfl | rfl
    · have htr0 : Ξ_o.trace = 0 :=
        NNReal.coe_inj.mp (by push_cast; dsimp [Ξ_o, w] at htro ⊢; linarith)
      refine ⟨?_, ?_⟩
      · dsimp [fo, branchCirc, w]; simp only [zero_mul]
        exact expect_eq_zero_of_trace_eq_zero htr0 Post
      · dsimp [fo, branchCirc]
    · have hPo' : PureStateAt
          (prodSlotState n 2 k fun i ↦ roundOutSlotVec A 0 ((1 : ℕ).testBit i.val)) Ξ_o := by
        dsimp only [ψ_out] at hPo; simp only [↓reduceIte] at hPo; cases anti
        · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_smul] at hPo
          exact pureStateAt_neg.1 hPo
        · simpa using hPo
      obtain ⟨hexp_h, hcost_h⟩ := onHitStage1Circuit_transition res (by omega) hScard hTS hA1 hAN
        (fun _ ↦ 0) (o := ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) (by simp) hPo'
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte]; exact hexp_h.trans htro
      · dsimp only [fo, branchCirc]
        simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte]; exact hcost_h
    · have hPo' : PureStateAt
          (prodSlotState n 2 k fun i ↦ roundOutSlotVec A 0 ((2 : ℕ).testBit i.val)) Ξ_o := by
        dsimp only [ψ_out] at hPo
        simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
          (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte] at hPo
        exact pureStateAt_neg.1 hPo
      obtain ⟨hexp_h, hcost_h⟩ := onHitStage1Circuit_transition res (by omega) hScard hTS hA1 hAN
        (fun _ ↦ 0) (o := ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) (by simp) hPo'
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte]; exact hexp_h.trans htro
      · dsimp only [fo, branchCirc]
        simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte]; exact hcost_h
    · have hw3 : w ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ = 0 := (by simp [w])
      have htr0 : Ξ_o.trace = 0 := NNReal.coe_inj.mp (by push_cast; rw [htro, hw3, zero_mul])
      have hto0 : ((interp fo).toStateFun Ξ_o).trace = 0 :=
        nonpos_iff_eq_zero.mp (((interp fo).trace_toStateFun_le _).trans_eq htr0)
      obtain ⟨_, hcost_h⟩ := onHitStage1Circuit_transition res (by omega) hScard hTS hA1 hAN
        (fun _ ↦ 0) (o := ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩) (by simp)
        (pureStateAt_of_trace_zero _ htr0)
      refine ⟨?_, ?_⟩
      · rw [expect_eq_zero_of_trace_eq_zero hto0 Post, hw3, zero_mul]
      · dsimp only [fo, branchCirc]
        simp only [show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte]; exact hcost_h
  have hprog_unfold : prog = ((deflateCirc n 2 T (.oracle (oracleReg n 2 k))).compile QProg.qAssign
    oracleS ;; (QProg.measureRegister res (allMarkersReg n 2 k) ;; (dispBits res 2 0 fun oVal ↦
    branchCirc ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile QProg.qAssign oracleS)) := by
    dsimp only [prog, extractOddPairStage1Circuit]
    rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure]
  rw [hprog_unfold]; refine ⟨?_, ?_⟩
  · rw [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSeq, QMonad.Q.toStateFun_bind,
      expect_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hsum_eq :
        (∑ o : Fin (2 ^ 2),
          𝔼[(interp ((branchCirc ⟨o.val % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile
              QProg.qAssign oracleS)).toStateFun (sliceState res 0 2 o.val Δm), Post]) =
        ∑ o : Fin (2 ^ 2), w o * Δ.trace :=
      Finset.sum_congr rfl fun o _ ↦ by simpa only [fin_mk_mod_pow] using (hbranch o).1
    have hw_sum : ∑ o : Fin (2 ^ 2), w o = 1 := by
      have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 <
        2 ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 <
        2 ^ 2)⟩} := by ext x; fin_cases x <;> simp
      rw [huniv4, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_singleton]; dsimp only [w]; norm_num
    rw [hsum_eq, ← Finset.sum_mul, hw_sum, one_mul]
  · rw [expectedCost_qSeq, expectedCost_qSeq]
    have hm0 : expectedCost modelS (QProg.measureRegister res (allMarkersReg n 2 k)) Δq = 0 := by
      simp [QProg.measureRegister, modelS]
    rw [hm0, zero_add, expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]; have hdisp0 :
        (∑ o : Fin (2 ^ 2), expectedCost modelS
            ((branchCirc ⟨o.val % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile
              QProg.qAssign oracleS)
            (sliceState res 0 2 o.val Δm)) = 0 :=
      Finset.sum_eq_zero fun o _ ↦ by simpa only [fin_mk_mod_pow] using (hbranch o).2
    rw [hdisp0, add_zero]; exact hcost_q
/-- Single pure-unitary off-diagonal Grover step (`1` oracle query) on `oracleReg n 2 k`. -/
noncomputable def offDiagPrepStepCircuit {Var : Type} (n k : ℕ) (hn1 : 1 ≤ n) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2) :=
  rawPrePostOracleCircuit n 2 k (flagConj n 2)
    ((localAddrReg n 2).embedUnitary (offDiagDiffuserUnitary n hn1) * flagConj n 2)
/-- `K` deterministic deflated off-diagonal Grover steps advancing `α ↦ α + 2 * K * θ₂`. -/
noncomputable def offDiagPrepRec {Var : Type} (n k : ℕ) (hn1 : 1 ≤ n)
    (T : Finset (Fin (2 ^ n))) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2)
  | 0 => .skip
  | K + 1 =>
      .seq (deflateCirc n 2 T (offDiagPrepStepCircuit n k hn1))
        (offDiagPrepRec n k hn1 T K)
theorem offDiagPrepRec_pureStateAt {Var : Type} [DecidableEq Var] {n k : ℕ} (hn2 : 2 ≤ n) {S T :
  Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hA1 : (S \ T).card = 1) : ∀ (K : ℕ) (α : ℝ) {Δ : CQState
    (Store Var)
  (2 ^ findAllQubits n 2 k)}, PureStateAt ((oracleReg n 2 k).tensorState ((localAddrReg n
  2).tensorState (offDiagPlaneVec n (S \ T) α) (Pi.single 0 1)) (Pi.single ((oracleReg n 2
  k).basisSplitEquiv 0).2 1)) Δ →
      let prog := (offDiagPrepRec (Var := Var) n k (by omega) T K).compile QProg.qAssign
        (parallelMarkingOracle 2 S)
      PureStateAt ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState (offDiagPlaneVec n
        (S \ T) (α + 2 * (K : ℝ) * halfAngleSet n 2)) (Pi.single 0 1)) (Pi.single ((oracleReg n 2
        k).basisSplitEquiv 0).2 1)) ((interp prog).toStateFun Δ) ∧ ((interp prog).toStateFun
        Δ).trace = Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S))
        prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (K : ℝ) := by
  intro K; set A := S \ T
  let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ :=
    Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1
  have hpre_real : IsRealMatrix (flagConj n 2).1 := isRealMatrix_flagConj n 2
  have hpost_real : IsRealMatrix (((localAddrReg n 2).embedUnitary (offDiagDiffuserUnitary n
    (by omega)) * flagConj n 2)).1 := isRealMatrix_mul (isRealMatrix_embedMatrix _
    (isRealMatrix_offDiagDiffuserUnitary n (by omega))) hpre_real
  induction K with
  | zero => intro α Δ hΔ; simp [offDiagPrepRec, hΔ]
  | succ K ih =>
      intro α Δ hΔ; dsimp only [offDiagPrepRec]; rw [OracleDynamicCircuit.compile_seq, interp_qSeq,
        QMonad.Q.toStateFun_bind, expectedCost_qSeq, interp_deflateCirc n 2 hTS
        (offDiagPrepStepCircuit n k (by omega)), congrFun (expectedCost_deflateCirc n 2 hTS (c :=
        offDiagPrepStepCircuit n k (by omega)) (zeroStepCost_rawPrePostOracleCircuit hpre_real
        hpost_real)) Δ]
      have hcost1 : expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 A))
        ((offDiagPrepStepCircuit (Var := Var) n k (by omega)).compile QProg.qAssign
        (parallelMarkingOracle 2 A)) Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
        simpa [offDiagPrepStepCircuit, ENNReal.ofReal_one] using costBound_rawPrePostOracleCircuit
          (Var := Var) (k := k) hpre_real hpost_real A Δ
      set Δ1 := (interp ((offDiagPrepStepCircuit (Var := Var) n k (by omega)).compile QProg.qAssign
        (parallelMarkingOracle 2 A))).toStateFun Δ
      let Ustep := ((localAddrReg n 2).embedUnitary (offDiagDiffuserUnitary n (by omega)) *
        flagConj n 2) * parallelMarkingOracle 2 A * flagConj n 2
      have hΔ1_eq : Δ1 = CQState.qAssign ((oracleReg n 2 k).embedUnitary Ustep) Δ := by
        dsimp only [Δ1, offDiagPrepStepCircuit]; rw [interp_rawPrePostOracleCircuit, interp_qAssign]
        rfl
      have hψ_in : star ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState
        (offDiagPlaneVec n A α) (Pi.single 0 1)) env0) ⬝ᵥ (oracleReg n 2 k).tensorState
        ((localAddrReg n 2).tensorState (offDiagPlaneVec n A α) (Pi.single 0 1)) env0 = 1 := by
        rw [dotProduct_tensorState, dotProduct_tensorState, dotProduct_offDiagPlaneVec hn2 hA1 α,
          dotProduct_env_single, dotProduct_env_single, mul_one, mul_one]
      obtain ⟨hP1, htr1⟩ := pureStateAt_qAssign ((oracleReg n 2 k).embedUnitary Ustep) hψ_in hΔ
      rw [← hΔ1_eq] at hP1 htr1
      have hvec1 : (((oracleReg n 2 k).embedUnitary Ustep).1 *ᵥ (oracleReg n 2 k).tensorState
        ((localAddrReg n 2).tensorState (offDiagPlaneVec n A α) (Pi.single 0 1)) env0) = (oracleReg
        n 2 k).tensorState ((localAddrReg n 2).tensorState (offDiagPlaneVec n A (α + 2 *
        halfAngleSet n 2)) (Pi.single 0 1)) env0 := by
        rw [QRegister.embedUnitary_val, (oracleReg n 2 k).embedMatrix_mulVec_tensorState]; congr 1
        have hU_mat : Ustep.1 = ((localAddrReg n 2).embedUnitary (offDiagDiffuserUnitary n
          (by omega))).1 * sDiagM n 2 A := by
          dsimp only [Ustep]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]; have hf :=
            flagConj_mul_parallelMarkingOracle_mul_flagConj n 2 A
          simp only [Matrix.mul_assoc] at hf; rw [hf]
        rw [hU_mat, ← Matrix.mulVec_mulVec, sDiagM_mulVec_env_zero, QRegister.embedUnitary_val,
          (localAddrReg n 2).embedMatrix_mulVec_tensorState, offDiagGroverStep_planeVec hn2 hA1 α]
      rw [hvec1] at hP1; obtain ⟨hPK, htrK, hcostK⟩ := ih (α + 2 * halfAngleSet n 2) hP1
      have hmass1 : (Δ1.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr1
      rw [hmass1] at hcostK
      have hang_eq : (α + 2 * halfAngleSet n 2) + 2 * (K : ℝ) * halfAngleSet n 2 = α + 2 * ((K + 1 :
        ℕ) : ℝ) * halfAngleSet n 2 := (by push_cast; ring); rw [hang_eq] at hPK; refine ⟨hPK,
        htrK.trans htr1, ?_⟩
      calc _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 + (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (K : ℝ) :=
            add_le_add hcost1 hcostK
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (1 + (K : ℝ)) := by
            rw [← mul_add, ← ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg K)]
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K + 1 : ℕ) : ℝ) := by push_cast; ring_nf
/-- Stationary weak-measurement `.qWhile` loop on `offDiagPlaneVec n (S \ T) β`
  (`2 * θ₂ ≤ β < π / 2`)
  followed by flag reset (`flipPerm`) and `extractOddPairStage1Circuit`. -/
noncomputable def offDiagLockedLoopCircuit {Var : Type} (res : Var) (n k : ℕ) (hn1 : 1 ≤ n)
    (T : Finset (Fin (2 ^ n))) (β : ℝ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2) :=
  let s := lockedRatio β (halfAngleSet n 2)
  let Upre := flagConj n 2 * chordUnitary n 2 (by decide) s
  let Upost := ctrlOffDiagDiffuserUnitary n hn1 * chordUnitary n 2 (by decide) s * flagConj n 2
  let cCore := rawPrePostOracleCircuit (Var := Var) n 2 k Upre Upost
  let cLoop := OracleDynamicCircuit.seq (.measure res (allMarkersReg n 2 k))
    (.qWhile (loopGuard res 2) (.seq cCore (.measure res (allMarkersReg n 2 k))))
  .seq (deflateCirc n 2 T cLoop)
    (dispBits res 2 0 fun oVal ↦
      let o : Fin (2 ^ 2) := ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩
      if o = ⟨3, by decide⟩ then
        .seq (.step (phaseI ((oracleReg n 2 k).embedUnitary (permutationUnitary (flipPerm n 2)))))
          (extractOddPairStage1Circuit res n k T)
      else
        .skip)
theorem offDiagLockedLoop_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn2 : 2 ≤
  n) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA1 : (S \ T).card = 1) {β :
  ℝ} (h2θ : 2 * halfAngleSet n 2 ≤ β) (hβ_lt : β < π / 2) {Δ : CQState (Store Var) (2 ^
    findAllQubits n 2
  k)} (hΔ : PureStateAt ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState
  (offDiagPlaneVec n (S \ T) β) (Pi.single 0 1)) (Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2
  1)) Δ) :
    let prog := (offDiagLockedLoopCircuit res n k (by omega) T β).compile QProg.qAssign
      (parallelMarkingOracle 2 S); let α := lockedAlpha β (halfAngleSet n 2)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - α ^ 2)⁻¹ + 1) := by
  intro prog α; set A := S \ T; set θ := halfAngleSet n 2; set s := lockedRatio β θ
  have hθ_pos : 0 < θ := Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos (by norm_num) (by positivity)))
  obtain ⟨_, _, hα_pos, hα_sq_lt⟩ := lockedRatio_bounds hθ_pos h2θ hβ_lt
  have h1mq_pos : 0 < 1 - α ^ 2 := (by linarith); let oracleS := parallelMarkingOracle 2 S
  let oracleA := parallelMarkingOracle 2 A
  let modelS := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleS
  let modelA := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleA
  have horacleS := isRealMatrix_parallelMarkingOracle (m := 2) S
  let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ := Pi.single ((oracleReg n 2
    k).basisSplitEquiv 0).2 1; let Upre := flagConj n 2 * chordUnitary n 2 (by omega) s
  let Upost := ctrlOffDiagDiffuserUnitary n (by omega) *
    chordUnitary n 2 (by omega) s * flagConj n 2
  have hpre_real : IsRealMatrix Upre.1 := isRealMatrix_mul (isRealMatrix_flagConj n 2)
    (isRealMatrix_chordMat n 2 (by omega) s); have hpost_real : IsRealMatrix Upost.1 :=
    isRealMatrix_mul (isRealMatrix_mul (isRealMatrix_ctrlOffDiagDiffuserUnitary n (by omega))
    (isRealMatrix_chordMat n 2 (by omega) s)) (isRealMatrix_flagConj n 2)
  let cCore := rawPrePostOracleCircuit (Var := Var) n 2 k Upre Upost
  let cLoop := OracleDynamicCircuit.seq (.measure res (allMarkersReg n 2 k))
    (.qWhile (loopGuard res 2) (.seq cCore (.measure res (allMarkersReg n 2 k))))
  have hzc_loop : ZeroStepCost cLoop := ⟨trivial, ⟨zeroStepCost_rawPrePostOracleCircuit hpre_real
    hpost_real, trivial⟩⟩
  let ψ := (oracleReg n 2 k).tensorState
    ((localAddrReg n 2).tensorState (offDiagPlaneVec n A β) (Pi.single 0 1)) env0
  have hψ : star ψ ⬝ᵥ ψ = 1 := by
    dsimp only [ψ]; rw [dotProduct_tensorState, dotProduct_tensorState, dotProduct_offDiagPlaneVec
      hn2 hA1 β, dotProduct_env_single, dotProduct_env_single, mul_one, mul_one]
  let ψ_hit := (oracleReg n 2 k).tensorState
    ((localAddrReg n 2).tensorState (unifSetVec (oddSet n 2 A)) (Pi.single 1 1)) env0
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
  have hM1 : 1 ≤ (oddSet n 2 A).card := (by rw [card_oddSet_two_of_card_one hA1]; omega)
  have hψ_hit : star ψ_hit ⬝ᵥ ψ_hit = 1 := by
    dsimp only [ψ_hit]; rw [dotProduct_tensorState, dotProduct_tensorState, dotProduct_unifSetVec
      hM1, dotProduct_env_single, dotProduct_env_single, mul_one, mul_one]
  have hψ0 : (allMarkersReg n 2 k).basisOutcomeProjector 0 *ᵥ ψ = ψ := by
    let v0 : Fin (2 ^ 2) → Fin (2 ^ (2 * n)) → ℂ :=
      fun m ↦ if m = 0 then offDiagPlaneVec n A β else 0
    have hψ_sum : ψ = (oracleReg n 2 k).tensorState (∑ m : Fin (2 ^ 2), (localAddrReg n
      2).tensorState (v0 m) (Pi.single (envOfMask n m) 1)) env0 := by
      dsimp only [ψ, v0]; congr 1; rw [Finset.sum_eq_single 0]
      · simp
      · intro m _ hm; simp only [hm, ↓reduceIte]; funext z; simp [QRegister.tensorState]
      · intro habs; exact (habs (Finset.mem_univ 0)).elim
    nth_rw 1 [hψ_sum]; rw [basisOutcomeProjector_allMarkers_oracle_tensorState]; dsimp only [v0, ψ,
      env0]; simp
  let Ub := (oracleReg n 2 k).embedUnitary (Upost * oracleA * Upre)
  let w : Fin (2 ^ 2) → ℝ := fun o ↦ if o = 0 then α ^ 2 else if o = ⟨3, (Nat.lt_of_sub_eq_succ rfl
    : 3 < 2 ^ 2)⟩ then 1 - α ^ 2 else 0
  have hw_nn (o : Fin (2 ^ 2)) : 0 ≤ w o := by
    dsimp only [w]; split_ifs
    · exact sq_nonneg α
    · exact h1mq_pos.le
    · exact le_rfl
  let ψ_out : Fin (2 ^ 2) → Fin (2 ^ findAllQubits n 2 k) → ℂ :=
    fun o ↦ if o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ then ψ_hit else ψ
  have hψ_out (o : Fin (2 ^ 2)) : star (ψ_out o) ⬝ᵥ ψ_out o = 1 := by
    dsimp only [ψ_out]; split_ifs
    · exact hψ_hit
    · exact hψ
  have hproj (o : Fin (2 ^ 2)) : (allMarkersReg n 2 k).basisOutcomeProjector o *ᵥ (Ub.1 *ᵥ ψ) =
    ((√(w o) : ℝ) : ℂ) • ψ_out o := by
    have hUbody_eq : Upost * oracleA * Upre = ctrlOffDiagDiffuserUnitary n (by omega) * chordUnitary
      n 2 (by omega) s * flagConj n 2 * parallelMarkingOracle 2 A * flagConj n 2 * chordUnitary n 2
      (by omega) s := (by dsimp only [Upre, Upost, oracleA]; simp only [mul_assoc])
    have hUbψ : Ub.1 *ᵥ ψ = (oracleReg n 2 k).tensorState (∑ m : Fin (2 ^ 2), (localAddrReg n
      2).tensorState (if m = 0 then (α : ℂ) • offDiagPlaneVec n A β else if m = ⟨3,
      (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ then ((√(1 - α ^ 2) : ℝ) : ℂ) • unifSetVec (oddSet n
      2 A) else 0) (Pi.single (envOfMask n m) 1)) env0 := by
      dsimp only [Ub, ψ]; rw [hUbody_eq, QRegister.embedUnitary_val, (oracleReg n 2
        k).embedMatrix_mulVec_tensorState, ctrlOffDiagRound_locked hn2 hA1 h2θ hβ_lt]; congr 1
      have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 <
        2 ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 <
        2 ^ 2)⟩} := (by ext x; fin_cases x <;> simp); rw [huniv4, Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]; funext z
      simp only [
        show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨3,
          (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ by simp,
        show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨3,
          (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ by simp,
        show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        ↓reduceIte, envOfMask_zero, envOfMask_three, QRegister.tensorState,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, zero_add]
      dsimp only [α]; ring
    rw [hUbψ, basisOutcomeProjector_allMarkers_oracle_tensorState]; have ho_cases : o = 0 ∨ o = ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨
      o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ := (by fin_cases o <;> simp)
    rcases ho_cases with rfl | rfl | rfl | rfl
    · have hα_nn : 0 ≤ α := hα_pos.le
      simp only [↓reduceIte, show (0 : Fin (2 ^ 2)) ≠ ⟨3,
        (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ by simp,
        w, ψ_out, Real.sqrt_sq hα_nn, envOfMask_zero]
      rw [(localAddrReg n 2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
    · funext z; simp [w, QRegister.tensorState]
    · funext z; simp [w, QRegister.tensorState]
    · simp only [show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        ↓reduceIte,
        w, ψ_out, envOfMask_three]
      rw [(localAddrReg n 2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
  have hloopA := qWhile_sliceState_of_pureStateAt modelA res (allMarkersReg n 2 k) (cCore.compile
    QProg.qAssign oracleA) Ub 1 (wp_rawPrePostOracleCircuit n 2 k Upre Upost A)
    (costBound_rawPrePostOracleCircuit hpre_real hpost_real A) (fun Ξ ↦
    by simp [QProg.measureRegister, modelA]) hψ hψ0 hα_pos.le hα_sq_lt w hw_nn (by simp [w]; rfl)
    ψ_out hψ_out (by dsimp [ψ_out]) hproj hΔ; set Δloop := (interp ((deflateCirc n 2 T
    cLoop).compile QProg.qAssign oracleS)).toStateFun Δ
  have hΔloop_eq : Δloop = (interp (cLoop.compile QProg.qAssign oracleA)).toStateFun Δ :=
    (by dsimp only [Δloop]; rw [interp_deflateCirc n 2 hTS cLoop])
  have hcost_loop : expectedCost modelS ((deflateCirc n 2 T cLoop).compile QProg.qAssign oracleS) Δ
    ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - α ^ 2)⁻¹) := by
    rw [congrFun (expectedCost_deflateCirc n 2 hTS hzc_loop) Δ]; have hc1 := hloopA.1
    simpa [cLoop, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure,
      OracleDynamicCircuit.compile_qWhile, one_mul] using hc1
  have hloop_slices : (sliceState res 0 2 0 Δloop).trace = 0 ∧ ∀ o : Fin (2 ^ 2), o ≠ 0 →
    PureStateAt (ψ_out o) (sliceState res 0 2 o.val Δloop) ∧
    ((sliceState res 0 2 o.val Δloop).trace : ℝ) = (w o / (1 - α ^ 2)) * (Δ.trace : ℝ) := by
    rw [hΔloop_eq]; simpa [cLoop, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure, OracleDynamicCircuit.compile_qWhile] using hloopA.2
  -- Step 2: Dispatch on `o` (`o = 3` flips flags and runs `extractOddPairStage1Circuit`)
  let branchCirc (o : Fin (2 ^ 2)) := if o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ then
    OracleDynamicCircuit.seq (.step (phaseI ((oracleReg n 2 k).embedUnitary (permutationUnitary
    (flipPerm n 2))))) (extractOddPairStage1Circuit res n k T) else .skip
  let Post : CQAssertion (Store Var) (2 ^ findAllQubits n 2 k) :=
    liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
  have hbranch (o : Fin (2 ^ 2)) :
      let fo := (branchCirc o).compile QProg.qAssign oracleS
      let Ξ_o := sliceState res 0 2 o.val Δloop
      𝔼[(interp fo).toStateFun Ξ_o, Post] =
          (if o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ then (Δ.trace : ℝ) else 0) ∧
        expectedCost modelS fo Ξ_o ≤
          (if o = ⟨3,
            (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ then (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1
            else 0) := by
    intro fo Ξ_o; have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ :=
      (by fin_cases o <;> simp); rcases ho_cases with rfl | rfl | rfl | rfl
    · have htr0 : Ξ_o.trace = 0 := hloop_slices.1; refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (0 : Fin (2 ^ 2)) ≠ ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ by simp,
          ↓reduceIte,
          OracleDynamicCircuit.compile_skip, interp_skip, QMonad.Q.toStateFun_pure]
        exact expect_eq_zero_of_trace_eq_zero htr0 Post
      · dsimp only [fo, branchCirc]; simp
    · obtain ⟨_, htro⟩ := hloop_slices.2 ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ (by simp)
      have htr0 : Ξ_o.trace = 0 := NNReal.coe_inj.mp (by push_cast; simpa [w] using htro)
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨3,
          (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ by simp, ↓reduceIte,
          OracleDynamicCircuit.compile_skip, interp_skip, QMonad.Q.toStateFun_pure]
        exact expect_eq_zero_of_trace_eq_zero htr0 Post
      · dsimp only [fo, branchCirc]; simp
    · obtain ⟨_, htro⟩ := hloop_slices.2 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ (by simp)
      have htr0 : Ξ_o.trace = 0 := NNReal.coe_inj.mp (by push_cast; simpa [w] using htro)
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨3,
          (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ by simp, ↓reduceIte,
          OracleDynamicCircuit.compile_skip, interp_skip, QMonad.Q.toStateFun_pure]
        exact expect_eq_zero_of_trace_eq_zero htr0 Post
      · dsimp only [fo, branchCirc]; simp
    · obtain ⟨hP3, htr3⟩ := hloop_slices.2 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ (by simp)
      dsimp only [ψ_out] at hP3; simp only [↓reduceIte] at hP3
      have htr3_eq : Ξ_o.trace = Δ.trace := NNReal.coe_inj.mp <| by
        dsimp only [w] at htr3
        simp only [show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte] at htr3; rwa [div_self h1mq_pos.ne', one_mul] at htr3
      -- Apply `flipPerm n 2` (`0` cost) to turn `Pi.single 1 1` into `Pi.single 0 1`
      let Uflip := (oracleReg n 2 k).embedUnitary (permutationUnitary (flipPerm n 2))
      set Ξ_flip := (interp ((OracleDynamicCircuit.step (phaseI Uflip)).compile QProg.qAssign
        oracleS)).toStateFun Ξ_o
      have hΞ_flip_eq : Ξ_flip = CQState.qAssign Uflip Ξ_o := by
        dsimp only [Ξ_flip]; rw [OracleDynamicCircuit.compile_step, interp_qAssign]
        exact cqState_qAssign_phaseI Uflip Ξ_o
      obtain ⟨hP_flip, htr_flip⟩ := pureStateAt_qAssign Uflip hψ_hit hP3
      rw [← hΞ_flip_eq] at hP_flip htr_flip
      have hflip_vec : Uflip.1 *ᵥ ψ_hit = (oracleReg n 2 k).tensorState ((localAddrReg n
        2).tensorState (signedOddVec n A false) (Pi.single 0 1)) env0 := by
        dsimp only [Uflip, ψ_hit]; rw [QRegister.embedUnitary_val, (oracleReg n 2
          k).embedMatrix_mulVec_tensorState]; congr 1; change flipMat n 2 *ᵥ (localAddrReg n
          2).tensorState (unifSetVec (oddSet n 2 A)) (Pi.single 1 1) = _
        rw [flipMat_mulVec_tensorState, localEnv_one_add_one, signedOddVec_false_eq_unifSetVec hA1]
      rw [hflip_vec] at hP_flip
      obtain ⟨hexp_ext, hcost_ext⟩ := extractOddPairStage1_transition res hn2 hScard hTS hA1 false
        hP_flip; have hmass_flip : (Ξ_flip.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal (htr_flip.trans htr3_eq)
      rw [hmass_flip] at hcost_ext; refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]; simp only [↓reduceIte, OracleDynamicCircuit.compile_seq,
          interp_qSeq, QMonad.Q.toStateFun_bind]; rw [hexp_ext, htr_flip, htr3_eq]
      · dsimp only [fo, branchCirc]; simp only [↓reduceIte, OracleDynamicCircuit.compile_seq,
          expectedCost_qSeq]
        have hc_u : expectedCost modelS ((OracleDynamicCircuit.step (phaseI Uflip)).compile
          QProg.qAssign oracleS) Ξ_o = 0 := by
          dsimp only [Uflip, modelS]; rw [OracleDynamicCircuit.compile_step, expectedCost_qAssign,
            ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacleS (isRealMatrix_embedUnitary
            (oracleReg n 2 k) (isRealMatrix_permutationUnitary (flipPerm n 2)))]; simp
        have hst_u : (interp ((OracleDynamicCircuit.step (phaseI Uflip)).compile QProg.qAssign
          oracleS)).toStateFun Ξ_o = Ξ_flip := rfl; rw [hc_u, zero_add, hst_u]; exact hcost_ext
  have hprog_unfold : prog = ((deflateCirc n 2 T cLoop).compile QProg.qAssign oracleS ;; (dispBits
    res 2 0 fun oVal ↦ branchCirc ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile
    QProg.qAssign oracleS) :=
    (by dsimp [prog, offDiagLockedLoopCircuit, branchCirc, cLoop, cCore, Upre, Upost, s, θ])
  rw [hprog_unfold]; have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1,
    (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3,
    (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩} := (by ext x; fin_cases x <;> simp); refine ⟨?_, ?_⟩
  · rw [interp_qSeq, QMonad.Q.toStateFun_bind, expect_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hsum_eq :
        (∑ o : Fin (2 ^ 2),
          𝔼[(interp ((branchCirc ⟨o.val % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile
              QProg.qAssign oracleS)).toStateFun (sliceState res 0 2 o.val Δloop), Post]) =
        ∑ o : Fin (2 ^ 2), if o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ then (Δ.trace : ℝ)
          else 0 :=
      Finset.sum_congr rfl fun o _ ↦ by simpa only [fin_mk_mod_pow] using (hbranch o).1
    rw [hsum_eq, huniv4, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert
      (by simp), Finset.sum_singleton]; simp
  · rw [expectedCost_qSeq, expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hdisp_le : (∑ o : Fin (2 ^ 2), expectedCost modelS ((branchCirc ⟨o.val % 2 ^ 2, Nat.mod_lt
      _ (by positivity)⟩).compile QProg.qAssign oracleS) (sliceState res 0 2 o.val Δloop)) ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
      calc _ ≤ ∑ o : Fin (2 ^ 2),
                if o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ then (Δ.trace : ℝ≥0∞) *
                  ENNReal.ofReal 1 else 0 :=
              Finset.sum_le_sum fun o _ ↦ by simpa only [fin_mk_mod_pow] using (hbranch o).2
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
            rw [huniv4, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert
              (by simp), Finset.sum_singleton]; simp
    calc _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - α ^ 2)⁻¹) +
              (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 :=
          add_le_add hcost_loop hdisp_le
      _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - α ^ 2)⁻¹ + 1) := by
          rw [← mul_add, ← ENNReal.ofReal_add (inv_nonneg.2 h1mq_pos.le) zero_le_one]
/-! ## 7. Terminal `r = 1` CSWAP Warm Readout Circuit & Cost Bound (`m = 2`) -/
theorem planeVec_halfAngleSet_one_eq_const {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn1 : 1 ≤ n) (hA1 :
  A.card = 1) (x : Fin (2 ^ n)) : planeVec A (halfAngleSet n 1) x = ((1 / √(2 ^ n : ℝ) : ℝ) : ℂ) :=
  by
  have h1N : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega); have hN_pos : (0 : ℝ) < 2 ^ n :=
    (by positivity); have hSN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := Real.sqrt_pos.2 hN_pos
  have hN1_pos : (0 : ℝ) < (2 ^ n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ 2 ^ n := (by have h2 : 2 ≤ 2 ^ n := (by omega); exact_mod_cast h2); linarith
  have hsin := sqrt_dim_mul_sin_halfAngleSet (n := n) (r := 1) h1N.le; have hcos :=
    sqrt_dim_mul_cos_halfAngleSet n 1; simp only [Nat.cast_one, Real.sqrt_one] at hsin hcos
  simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hA1,
    Nat.cast_one, Real.sqrt_one, div_one]; by_cases hx : x ∈ A
  · simp only [hx, ↓reduceIte, Complex.ofReal_one, mul_one, mul_zero, add_zero]
    have hr : Real.sin (halfAngleSet n 1) = 1 / √(2 ^ n : ℝ) :=
      (by rw [eq_div_iff hSN_pos.ne', mul_comm]; exact hsin); have hC := congrArg Complex.ofReal hr;
      push_cast at hC ⊢; exact hC
  · simp only [hx, ↓reduceIte, mul_zero, zero_add]
    have hr : Real.cos (halfAngleSet n 1) * (1 / √((2 ^ n : ℝ) - 1)) = 1 / √(2 ^ n : ℝ) := by
      rw [mul_one_div, div_eq_div_iff (Real.sqrt_pos.2 hN1_pos).ne' hSN_pos.ne']; linarith [hcos]
    have hC := congrArg Complex.ofReal hr; push_cast at hC ⊢; exact hC
/-- Diagonal collision unit vector on `2 * n` address bits (`planeVec A γ x` on `(x, x)`). -/
noncomputable def diagNormVec (n : ℕ) (A : Finset (Fin (2 ^ n))) (γ : ℝ)
    (u : Fin (2 ^ (2 * n))) : ℂ :=
  if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then planeVec A γ (addrEquiv n 2 u s0) else 0
theorem dotProduct_diagNormVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn1 : 1 ≤ n) (hA1 : A.card = 1)
  (γ : ℝ) : star (diagNormVec n A γ) ⬝ᵥ diagNormVec n A γ = 1 := by
  have h1N : A.card < 2 ^ n := (by rw [hA1]; exact Nat.one_lt_two_pow (by omega)); have hplane :=
    dotProduct_planeVec (by omega : 1 ≤ A.card) h1N γ; simp only [dotProduct, diagNormVec,
    Pi.star_apply] at hplane ⊢; rw [← (addrEquiv n 2).symm.sum_comp]
  let pairEquiv : (Fin 2 → Fin (2 ^ n)) ≃ Fin (2 ^ n) × Fin (2 ^ n) :=
    { toFun := fun f ↦ (f s0, f s1)
      invFun := fun p i ↦ if i = s0 then p.1 else p.2
      left_inv := fun f ↦ by funext i; fin_cases i <;> rfl
      right_inv := fun p ↦ rfl }
  have hpair := pairEquiv.symm.sum_comp (fun f : Fin 2 → Fin (2 ^ n) ↦ star (if f s0 = f s1 then
    planeVec A γ (f s0) else 0) * if f s0 = f s1 then planeVec A γ (f s0) else 0)
  simp only [Equiv.apply_symm_apply]; rw [← hpair, Fintype.sum_prod_type]
  have hrow (x : Fin (2 ^ n)) : (∑ y : Fin (2 ^ n), star (if pairEquiv.symm (x, y) s0 =
    pairEquiv.symm (x, y) s1 then planeVec A γ (pairEquiv.symm (x, y) s0) else 0) * if
    pairEquiv.symm (x, y) s0 = pairEquiv.symm (x, y) s1 then planeVec A γ (pairEquiv.symm (x, y) s0)
    else 0) = star (planeVec A γ x) * planeVec A γ x := by
    rw [Finset.sum_eq_single x]
    · dsimp [pairEquiv]; simp
    · intro y _ hyx; have hne : pairEquiv.symm (x, y) s0 ≠ pairEquiv.symm (x, y) s1 := Ne.symm hyx
      simp [hne]
    · intro habs; exact (habs (Finset.mem_univ x)).elim
  simp_rw [hrow]; exact hplane
/-- Marked-pair amplitude of the symmetric CSWAP branch `vSym` (`m = 2, r = 1`). -/
noncomputable def cswapSymAmpM (n : ℕ) (γ : ℝ) : ℝ :=
  (Real.sin γ * √((2 ^ n : ℝ) - 1) + Real.cos γ) / √(2 * (2 ^ n : ℝ))
/-- Unmarked off-diagonal amplitude of the symmetric CSWAP branch `vSym` (`m = 2, r = 1`). -/
noncomputable def cswapSymAmpU (n : ℕ) (γ : ℝ) : ℝ :=
  Real.cos γ * √((2 ^ n : ℝ) - 2) / √(2 ^ n : ℝ)
/-- Post-CSWAP symmetric branch weight `a_M² + a_U²` (`= 1 - sin²(γ - θ₁)/2 - 1/2^n`). -/
noncomputable def cswapSymWeight (n : ℕ) (γ : ℝ) : ℝ :=
  cswapSymAmpM n γ ^ 2 + cswapSymAmpU n γ ^ 2
/-- Post-CSWAP symmetric off-diagonal Grover plane angle `arctan(a_M / a_U)`. -/
noncomputable def cswapSymAngle (n : ℕ) (γ : ℝ) : ℝ :=
  Real.arctan (cswapSymAmpM n γ / cswapSymAmpU n γ)
theorem cswapSymWeight_eq {n : ℕ} (hn1 : 1 ≤ n) (γ : ℝ) : cswapSymWeight n γ = 1 - Real.sin (γ -
  halfAngleSet n 1) ^ 2 / 2 - 1 / (2 ^ n : ℝ) := by
  have h1N : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega); set N : ℝ := (2 : ℝ) ^ n; have hN_cast : (2
    ^ n : ℝ) = N := rfl; have h2R : (2 : ℝ) ≤ N :=
    (by have h2 : 2 ≤ 2 ^ n := (by omega); rw [← hN_cast]; exact_mod_cast h2)
  have hN_pos : 0 < N := (by linarith); have h2N_pos : 0 < 2 * N := (by positivity)
  have hSN_pos : 0 < √N := Real.sqrt_pos.2 hN_pos; have hN1_nn : 0 ≤ N - 1 := (by linarith)
  have hN2_nn : 0 ≤ N - 2 := (by linarith); have hsin1 : √N * Real.sin (halfAngleSet n 1) = 1 :=
    (by have hs := sqrt_dim_mul_sin_halfAngleSet (n := n) (r := 1) h1N.le; simpa [hN_cast] using hs)
  have hcos1 : √N * Real.cos (halfAngleSet n 1) = √(N - 1) :=
    (by have hc := sqrt_dim_mul_cos_halfAngleSet n 1; simpa [hN_cast] using hc)
  have hsin_sub : Real.sin (γ - halfAngleSet n 1) = (Real.sin γ * √(N - 1) - Real.cos γ) / √N := by
    rw [Real.sin_sub, eq_div_iff hSN_pos.ne']
    linear_combination Real.sin γ * hcos1 - Real.cos γ * hsin1
  dsimp only [cswapSymWeight, cswapSymAmpM, cswapSymAmpU]; rw [hN_cast, hsin_sub, div_pow, div_pow,
    div_pow, mul_pow, Real.sq_sqrt h2N_pos.le, Real.sq_sqrt hN_pos.le, Real.sq_sqrt hN2_nn]
  have hA2 : (Real.sin γ * √(N - 1)) ^ 2 = Real.sin γ ^ 2 * (N - 1) :=
    (by rw [mul_pow, Real.sq_sqrt hN1_nn]); have hexp1 : (Real.sin γ * √(N - 1) + Real.cos γ) ^ 2 =
    Real.sin γ ^ 2 * (N - 1) + 2 * (Real.sin γ * √(N - 1)) * Real.cos γ + Real.cos γ ^ 2 :=
    (by linear_combination hA2)
  have hexp2 : (Real.sin γ * √(N - 1) - Real.cos γ) ^ 2 = Real.sin γ ^ 2 * (N - 1) - 2 * (Real.sin γ
    * √(N - 1)) * Real.cos γ + Real.cos γ ^ 2 := (by linear_combination hA2); rw [hexp1, hexp2]
  have hcos_sq : Real.cos γ ^ 2 = 1 - Real.sin γ ^ 2 := (by linarith [Real.sin_sq_add_cos_sq γ])
  rw [hcos_sq]; field_simp [hN_pos.ne']; ring
private theorem arctan_lt_arctan {x y : ℝ} (h : x < y) : Real.arctan x < Real.arctan y := by
  refine strictMono_of_deriv_pos (fun z ↦ ?_) h; rw [(Real.hasDerivAt_arctan z).deriv]; positivity
theorem cswapSymAngle_bounds {n : ℕ} (hn : 100 ≤ n) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ_hi : γ ≤ 4 / 5) : 0 <
  cswapSymAmpU n γ ∧ 0 ≤ cswapSymAmpM n γ ∧ 0 < cswapSymWeight n γ ∧ 0 ≤ cswapSymAngle n γ ∧
  cswapSymAngle n γ < π / 4 ∧ Real.arctan (Real.tan γ / √2) ≤ cswapSymAngle n γ ∧ cswapSymAmpM n γ =
  √(cswapSymWeight n γ) * Real.sin (cswapSymAngle n γ) ∧ cswapSymAmpU n γ = √(cswapSymWeight n γ) *
  Real.cos (cswapSymAngle n γ) := by
  set N : ℝ := (2 : ℝ) ^ n; have hN_cast : (2 ^ n : ℝ) = N := rfl
  have hN1000 : (1000 : ℝ) ≤ N := by
    have h10 : 1024 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) (by omega) : 2 ^ 10 ≤ 2 ^ n)
    have h10' : (1024 : ℝ) ≤ N := (by rw [← hN_cast]; exact_mod_cast h10); linarith
  have hN_pos : 0 < N := (by linarith); have hN1_pos : 0 < N - 1 := (by linarith)
  have hN2_pos : 0 < N - 2 := (by linarith); have h45_lt_pi2 : (4 / 5 : ℝ) < π / 2 :=
    (by linarith [Real.pi_gt_three])
  have hcos45_ge : 17 / 25 ≤ Real.cos (4 / 5) := by
    have h2 : (4 / 5 : ℝ) = 2 * (2 / 5) := (by ring); rw [h2, Real.cos_two_mul']
    have hs : Real.sin (2 / 5) ≤ 2 / 5 := Real.sin_le (by positivity); have hs0 : 0 ≤ Real.sin (2 /
      5) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_gt_three])
    have hsc := Real.sin_sq_add_cos_sq (2 / 5); nlinarith
  have hcos_γ : 17 / 25 ≤ Real.cos γ := hcos45_ge.trans (Real.cos_le_cos_of_nonneg_of_le_pi hγ0
    (by linarith [Real.pi_gt_three]) hγ_hi); have hcos_pos : 0 < Real.cos γ := (by linarith)
  have hsin_nn : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0
    (by linarith [Real.pi_gt_three])
  have hsin_le : Real.sin γ ≤ 4 / 5 := (Real.sin_le hγ0).trans hγ_hi
  have htan_le : Real.tan γ ≤ 20 / 17 :=
    (by rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos_pos]; linarith)
  have htan_nn : 0 ≤ Real.tan γ :=
    (by rw [Real.tan_eq_sin_div_cos]; exact div_nonneg hsin_nn hcos_pos.le)
  have haU_pos : 0 < cswapSymAmpU n γ := by
    dsimp only [cswapSymAmpU]; rw [hN_cast]; exact div_pos (mul_pos hcos_pos (Real.sqrt_pos.2
      hN2_pos)) (Real.sqrt_pos.2 hN_pos)
  have haM_nn : 0 ≤ cswapSymAmpM n γ := by
    dsimp only [cswapSymAmpM]; rw [hN_cast]; exact div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hw_pos : 0 < cswapSymWeight n γ := (by dsimp only [cswapSymWeight]; positivity)
  have hratio_eq : cswapSymAmpM n γ / cswapSymAmpU n γ = (Real.tan γ * √(N - 1) + 1) / (√2 * √(N -
    2)) := by
    dsimp only [cswapSymAmpM, cswapSymAmpU]; rw [hN_cast, Real.sqrt_mul
      (by positivity : (0 : ℝ) ≤ 2), Real.tan_eq_sin_div_cos]; have hSN : √N ≠ 0 := (Real.sqrt_pos.2
      hN_pos).ne'; have hSN2 : √(N - 2) ≠ 0 := (Real.sqrt_pos.2 hN2_pos).ne'
    have hs2 : (√2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'; field_simp [hcos_pos.ne', hSN,
      hSN2, hs2]
  have hratio_ge : Real.tan γ / √2 ≤ cswapSymAmpM n γ / cswapSymAmpU n γ := by
    rw [hratio_eq]; have hle_sqrt : √(N - 2) ≤ √(N - 1) := Real.sqrt_le_sqrt (by linarith)
    have hSN2_pos : 0 < √(N - 2) := Real.sqrt_pos.2 hN2_pos; have hs2_pos : (0 : ℝ) < √2 :=
      Real.sqrt_pos.2 (by positivity)
    calc Real.tan γ / √2
        = (Real.tan γ * √(N - 2)) / (√2 * √(N - 2)) := by field_simp [hs2_pos.ne', hSN2_pos.ne']
      _ ≤ (Real.tan γ * √(N - 1) + 1) / (√2 * √(N - 2)) := by
            refine div_le_div_of_nonneg_right ?_ (mul_pos hs2_pos hSN2_pos).le
            linarith [mul_le_mul_of_nonneg_left hle_sqrt htan_nn]
  have hratio_lt_one : cswapSymAmpM n γ / cswapSymAmpU n γ < 1 := by
    rw [hratio_eq, div_lt_one (mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_pos.2 hN2_pos))]
    have h31 : 31 ≤ √(N - 1) :=
      (by rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 31)]; exact Real.sqrt_le_sqrt (by linarith))
    have hnum_le : Real.tan γ * √(N - 1) + 1 ≤ (21 / 17) * √(N - 1) :=
      (by nlinarith [mul_le_mul_of_nonneg_right htan_le (Real.sqrt_nonneg (N - 1))])
    have hsq_lt : ((21 / 17 : ℝ) * √(N - 1)) ^ 2 < (√2 * √(N - 2)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hN1_pos.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2),
        Real.sq_sqrt hN2_pos.le]; linarith
    have hrhs_pos : 0 < √2 * √(N - 2) := mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_pos.2
      hN2_pos); have hlt2 : (21 / 17 : ℝ) * √(N - 1) < √2 * √(N - 2) :=
      (by nlinarith [sq_nonneg (√2 * √(N - 2) - (21 / 17) * √(N - 1))]); linarith
  have hang_nn : 0 ≤ cswapSymAngle n γ := Real.arctan_nonneg.2 (div_nonneg haM_nn haU_pos.le)
  have hang_lt : cswapSymAngle n γ < π / 4 :=
    (by rw [cswapSymAngle, ← Real.arctan_one]; exact arctan_lt_arctan hratio_lt_one)
  have hang_ge : Real.arctan (Real.tan γ / √2) ≤ cswapSymAngle n γ := Real.arctan_mono hratio_ge
  have h1_add_sq : 1 + (cswapSymAmpM n γ / cswapSymAmpU n γ) ^ 2 = cswapSymWeight n γ / cswapSymAmpU
    n γ ^ 2 := (by dsimp only [cswapSymWeight]; field_simp [haU_pos.ne']; ring)
  have hcos_ang : √(cswapSymWeight n γ) * Real.cos (cswapSymAngle n γ) = cswapSymAmpU n γ := by
    rw [cswapSymAngle, Real.cos_arctan, h1_add_sq, Real.sqrt_div hw_pos.le, Real.sqrt_sq haU_pos.le]
    field_simp [haU_pos.ne', (Real.sqrt_pos.2 hw_pos).ne']
  have hsin_ang : √(cswapSymWeight n γ) * Real.sin (cswapSymAngle n γ) = cswapSymAmpM n γ := by
    rw [cswapSymAngle, Real.sin_arctan, h1_add_sq, Real.sqrt_div hw_pos.le, Real.sqrt_sq haU_pos.le]
    field_simp [haU_pos.ne', (Real.sqrt_pos.2 hw_pos).ne']
  exact ⟨haU_pos, haM_nn, hw_pos, hang_nn, hang_lt, hang_ge, hsin_ang.symm, hcos_ang.symm⟩
theorem cswapFilter_twoSlot_outcomes {n : ℕ} {A : Finset (Fin (2 ^ n))} (hn : 100 ≤ n) (hA1 : A.card
  = 1) {v0 v1 : Fin (2 ^ n) → ℂ} {γ : ℝ} (hγ_lo : halfAngleSet n 1 ≤ γ) (hγ_hi : γ ≤ 4 / 5) (hslots
  : (v0 = planeVec A (halfAngleSet n 1) ∧ v1 = planeVec A γ) ∨ (v0 = planeVec A γ ∧ v1 = planeVec A
  (halfAngleSet n 1))) :
    let sgn : ℂ := if v0 = planeVec A (halfAngleSet n 1) ∧ v1 = planeVec A γ then 1 else -1
    let w : Fin (2 ^ 2) → ℝ := fun o ↦ if o = 0 then cswapSymWeight n γ else if o = ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then Real.sin (γ - halfAngleSet n 1) ^ 2 / 2 else if
      o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then 1 / (2 ^ n : ℝ) else 0
    (cswapFilterUnitary n).1 *ᵥ prodSlotLocalVec (![slotPairVec v0 (Pi.single 0 1), slotPairVec v1
      (Pi.single 0 1)]) = ∑ o : Fin (2 ^ 2), (localAddrReg n 2).tensorState (if o = 0 then ((√(w 0)
      : ℝ) : ℂ) • offDiagPlaneVec n A (cswapSymAngle n γ) else if o = ⟨1, (Nat.lt_of_sub_eq_succ rfl
      : 1 < 2 ^ 2)⟩ then ((√(w ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) : ℝ) : ℂ) • (sgn •
      signedOddVec n A true) else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then ((√(w ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) : ℝ) : ℂ) • diagNormVec n A γ else 0) (Pi.single
      (envOfMask n o) 1) := by
  intro sgn w; have hn1 : 1 ≤ n := (by omega); have hn2 : 2 ≤ n := (by omega)
  have h1N : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega); set N : ℝ := (2 : ℝ) ^ n; have hN_cast : (2
    ^ n : ℝ) = N := rfl
  have h4R : (4 : ℝ) ≤ N := by
    have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) hn2 : 2 ^ 2 ≤ 2 ^ n)
    rw [← hN_cast]; exact_mod_cast h4
  have hN_pos : 0 < N := (by linarith); have hSN_pos : 0 < √N := Real.sqrt_pos.2 hN_pos
  have hN1_pos : 0 < N - 1 := (by linarith); have hN2_pos : 0 < N - 2 := (by linarith)
  have hθ1_nn : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hγ0 : 0 ≤ γ := hθ1_nn.trans hγ_lo; obtain ⟨_, _, _, _, _, _, haM_eq, haU_eq⟩ :=
    cswapSymAngle_bounds hn hγ0 hγ_hi; rw [prodSlotLocalVec_zero_flags_eq_tensorState, ←
    envOfMask_zero n]; change (cswapFilterUnitary n).1 *ᵥ (localAddrReg n 2).tensorState (fun u ↦ v0
    (addrEquiv n 2 u s0) * v1 (addrEquiv n 2 u s1)) (Pi.single (envOfMask n 0) 1) = _
  rw [cswapFilterUnitary_mulVec_zero]; set vIn : Fin (2 ^ (2 * n)) → ℂ := fun u ↦ v0 (addrEquiv n 2
    u s0) * v1 (addrEquiv n 2 u s1)
  set vOff : Fin (2 ^ (2 * n)) → ℂ := fun u ↦ if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then 0 else
    vIn u
  set vDiag : Fin (2 ^ (2 * n)) → ℂ := fun u ↦ if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then vIn u
    else 0; set vSym : Fin (2 ^ (2 * n)) → ℂ := fun u ↦ ((1 / 2 : ℝ) : ℂ) * (vOff u + vOff
    (swapAddrPerm n u)); set vAnti : Fin (2 ^ (2 * n)) → ℂ := fun u ↦ ((1 / 2 : ℝ) : ℂ) * (vOff u -
    vOff (swapAddrPerm n u))
  -- 1. Evaluate `vDiag`
  have hvDiag_eq : vDiag = ((√(w ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) : ℝ) : ℂ) •
    diagNormVec n A γ := by
    have hw2 : √(w ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) = 1 / √N := by
      dsimp only [w]
      simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
          (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte]
      rw [hN_cast, Real.sqrt_div zero_le_one, Real.sqrt_one]
    rw [hw2]; funext u; dsimp only [vDiag, vIn, diagNormVec, Pi.smul_apply, smul_eq_mul]
    by_cases hd : addrEquiv n 2 u s0 = addrEquiv n 2 u s1
    · rw [ite_eq_left hd, ite_eq_left hd, ← hd]; rcases hslots with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [planeVec_halfAngleSet_one_eq_const hn1 hA1, hN_cast]
      · rw [planeVec_halfAngleSet_one_eq_const hn1 hA1, hN_cast, mul_comm]
    · simp [hd]
  -- 2. Evaluate `vSym`
  have hvSym_eq : vSym = ((√(w 0) : ℝ) : ℂ) • offDiagPlaneVec n A (cswapSymAngle n γ) := by
    have hw0 : w 0 = cswapSymWeight n γ := (by simp [w]); rw [hw0]; funext u; dsimp only [vSym,
      vOff, vIn, offDiagPlaneVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; have hsw0 :=
      addrEquiv_swapAddrPerm_s0 n u; have hsw1 := addrEquiv_swapAddrPerm_s1 n u
    by_cases hd : addrEquiv n 2 u s0 = addrEquiv n 2 u s1
    · have hd' : addrEquiv n 2 (swapAddrPerm n u) s0 = addrEquiv n 2 (swapAddrPerm n u) s1 :=
        (by rw [hsw0, hsw1, hd]); have hnotM : u ∉ oddSet n 2 A := fun hm ↦ (Finset.mem_filter.1
        (oddSet_subset_offDiagSet hm)).2 hd
      have hnotU : u ∉ offDiagUnmarkedSet n A := fun hu ↦ (Finset.mem_filter.1 (Finset.mem_sdiff.1
        hu).1).2 hd; simp [hd, hd', unifSetVec, hnotM, hnotU]
    · have hd' : addrEquiv n 2 (swapAddrPerm n u) s0 ≠ addrEquiv n 2 (swapAddrPerm n u) s1 :=
        (by rw [hsw0, hsw1]; exact Ne.symm hd); rw [ite_eq_right hd, ite_eq_right hd', hsw0, hsw1]
      have hsum_in : v0 (addrEquiv n 2 u s0) * v1 (addrEquiv n 2 u s1) + v0 (addrEquiv n 2 u s1) *
        v1 (addrEquiv n 2 u s0) = ((1 / √N : ℝ) : ℂ) * (planeVec A γ (addrEquiv n 2 u s0) + planeVec
        A γ (addrEquiv n 2 u s1)) := by
        rcases hslots with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [planeVec_halfAngleSet_one_eq_const hn1 hA1,
            planeVec_halfAngleSet_one_eq_const hn1 hA1, hN_cast]; ring
        · rw [planeVec_halfAngleSet_one_eq_const hn1 hA1,
            planeVec_halfAngleSet_one_eq_const hn1 hA1, hN_cast]; ring
      rw [hsum_in]; by_cases huM : u ∈ oddSet n 2 A
      · have huU : u ∉ offDiagUnmarkedSet n A := fun hu ↦ (Finset.mem_sdiff.1 hu).2 huM
        have hunifM : unifSetVec (oddSet n 2 A) u = ((1 / √(2 * (N - 1)) : ℝ) : ℂ) := by
          dsimp only [unifSetVec]; rw [ite_eq_left huM, card_oddSet_two_of_card_one hA1,
            Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow,
            Nat.cast_ofNat, Nat.cast_one]
        have hunifU : unifSetVec (offDiagUnmarkedSet n A) u = 0 := (by simp [unifSetVec, huU])
        rw [hunifM, hunifU, mul_zero, add_zero]
        have hp_sum : planeVec A γ (addrEquiv n 2 u s0) + planeVec A γ (addrEquiv n 2 u s1) =
          ((Real.sin γ + Real.cos γ / √(N - 1) : ℝ) : ℂ) := by
          rcases (mem_oddSet_two_iff u).1 huM with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              h0, h1, ↓reduceIte, hA1, Nat.cast_one, Real.sqrt_one]; push_cast; ring
          · simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              h0, h1, ↓reduceIte, hA1, Nat.cast_one, Real.sqrt_one]; push_cast; ring
        rw [hp_sum]; have hreal : (1 / 2 : ℝ) * ((1 / √N) * (Real.sin γ + Real.cos γ / √(N - 1))) =
          √(cswapSymWeight n γ) * Real.sin (cswapSymAngle n γ) * (1 / √(2 * (N - 1))) := by
          rw [← haM_eq]; dsimp only [cswapSymAmpM]; rw [hN_cast, Real.sqrt_mul
            (by positivity : (0 : ℝ) ≤ 2), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
          have hs2 : (√2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
          have hsN1 : √(N - 1) ≠ 0 := (Real.sqrt_pos.2 hN1_pos).ne'; field_simp [hSN_pos.ne', hs2,
            hsN1]; rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]; ring
        have hC := congrArg Complex.ofReal hreal; push_cast at hC ⊢; linear_combination hC
      · have huOff : u ∈ offDiagSet n := Finset.mem_filter.2 ⟨Finset.mem_univ u, hd⟩
        have huU : u ∈ offDiagUnmarkedSet n A := Finset.mem_sdiff.2 ⟨huOff, huM⟩
        have hboth_out : addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A := by
          have hnot := mt (mem_oddSet_two_iff u).2 huM; simp only [not_or, not_and, not_not] at hnot
          by_cases h0 : addrEquiv n 2 u s0 ∈ A
          · exfalso; have h1 : addrEquiv n 2 u s1 ∈ A := hnot.1 h0; exact hd (Finset.card_le_one.1
              hA1.le (addrEquiv n 2 u s0) h0 (addrEquiv n 2 u s1) h1)
          · exact ⟨h0, fun h1 ↦ hnot.2 h0 h1⟩
        have hunifM : unifSetVec (oddSet n 2 A) u = 0 := (by simp [unifSetVec, huM])
        have hunifU : unifSetVec (offDiagUnmarkedSet n A) u = ((1 / √((N - 1) * (N - 2)) : ℝ) : ℂ)
          := by
          dsimp only [unifSetVec]; rw [ite_eq_left huU, card_offDiagUnmarkedSet_of_card_one hn2 hA1,
            Nat.cast_mul, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_sub (show 2 ≤ 2 ^ n by omega),
            Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        rw [hunifM, hunifU, mul_zero, zero_add]
        have hp_sum : planeVec A γ (addrEquiv n 2 u s0) + planeVec A γ (addrEquiv n 2 u s1) = ((2 *
          Real.cos γ / √(N - 1) : ℝ) : ℂ) := by
          simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            hboth_out.1, hboth_out.2, ↓reduceIte, hA1, Nat.cast_one]; push_cast; ring
        rw [hp_sum]
        have hreal : (1 / 2 : ℝ) * ((1 / √N) * (2 * Real.cos γ / √(N - 1))) = √(cswapSymWeight n γ)
          * Real.cos (cswapSymAngle n γ) * (1 / √((N - 1) * (N - 2))) := by
          rw [← haU_eq]; dsimp only [cswapSymAmpU]; rw [hN_cast, Real.sqrt_mul hN1_pos.le]
          have hsN1 : √(N - 1) ≠ 0 := (Real.sqrt_pos.2 hN1_pos).ne'; have hsN2 : √(N - 2) ≠ 0 :=
            (Real.sqrt_pos.2 hN2_pos).ne'; field_simp [hSN_pos.ne', hsN1, hsN2]
        have hC := congrArg Complex.ofReal hreal; push_cast at hC ⊢; linear_combination hC
  -- 3. Evaluate `vAnti`
  have hvAnti_eq : vAnti = ((√(w ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) : ℝ) : ℂ) • (sgn •
    signedOddVec n A true) := by
    have hsin_diff_nn : 0 ≤ Real.sin (γ - halfAngleSet n 1) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_three])
    have hw1 : √(w ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) = Real.sin (γ - halfAngleSet n 1) /
      √2 := by
      dsimp only [w]
      simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        ↓reduceIte]; rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hsin_diff_nn]
    rw [hw1]
    have hsin1 : √N * Real.sin (halfAngleSet n 1) = 1 := by
      have hs := sqrt_dim_mul_sin_halfAngleSet (n := n) (r := 1) h1N.le; simpa [hN_cast] using hs
    have hcos1 : √N * Real.cos (halfAngleSet n 1) = √(N - 1) :=
      (by have hc := sqrt_dim_mul_cos_halfAngleSet n 1; simpa [hN_cast] using hc)
    have hsin_sub : Real.sin (γ - halfAngleSet n 1) = (Real.sin γ * √(N - 1) - Real.cos γ) / √N
      := by
      rw [Real.sin_sub, eq_div_iff hSN_pos.ne']
      linear_combination Real.sin γ * hcos1 - Real.cos γ * hsin1
    have hamp : (1 / 2 : ℝ) * ((1 / √N) * (Real.sin γ - Real.cos γ / √(N - 1))) = (Real.sin (γ -
      halfAngleSet n 1) / √2) * (1 / √(2 * (N - 1))) := by
      rw [hsin_sub, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]; have hs2 : (√2 : ℝ) ≠ 0 :=
        (Real.sqrt_pos.2 (by positivity)).ne'; have hsN1 : √(N - 1) ≠ 0 := (Real.sqrt_pos.2
        hN1_pos).ne'; field_simp [hSN_pos.ne', hs2, hsN1]; rw [Real.sq_sqrt
        (by positivity : (0 : ℝ) ≤ 2)]; ring
    funext u; dsimp only [vAnti, vOff, vIn, signedOddVec, Pi.smul_apply, smul_eq_mul]; rw [hN_cast]
    have hsw0 := addrEquiv_swapAddrPerm_s0 n u; have hsw1 := addrEquiv_swapAddrPerm_s1 n u
    by_cases hd : addrEquiv n 2 u s0 = addrEquiv n 2 u s1
    · have hd' : addrEquiv n 2 (swapAddrPerm n u) s0 = addrEquiv n 2 (swapAddrPerm n u) s1 :=
        (by rw [hsw0, hsw1, hd]); have hc10 : ¬ (addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A) :=
        fun h ↦ h.2 (hd ▸ h.1); have hc01 : ¬ (addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A) :=
        fun h ↦ h.1 (hd.symm ▸ h.2); rw [ite_eq_left hd, ite_eq_left hd', sub_zero, mul_zero,
        ite_eq_right hc10, ite_eq_right hc01, mul_zero, mul_zero]
    · have hd' : addrEquiv n 2 (swapAddrPerm n u) s0 ≠ addrEquiv n 2 (swapAddrPerm n u) s1 :=
        (by rw [hsw0, hsw1]; exact Ne.symm hd); rw [ite_eq_right hd, ite_eq_right hd', hsw0, hsw1]
      -- Note `sgn = 1` in Case A and `sgn = -1` in Case B
      have hdiff_in : v0 (addrEquiv n 2 u s0) * v1 (addrEquiv n 2 u s1) - v0 (addrEquiv n 2 u s1) *
        v1 (addrEquiv n 2 u s0) = sgn * (((1 / √N : ℝ) : ℂ) * (planeVec A γ (addrEquiv n 2 u s1) -
        planeVec A γ (addrEquiv n 2 u s0))) := by
        by_cases hcase : v0 = planeVec A (halfAngleSet n 1) ∧ v1 = planeVec A γ
        · obtain ⟨h0_eq, h1_eq⟩ := hcase; have hsgn1 : sgn = 1 := ite_eq_left ⟨h0_eq, h1_eq⟩
          rw [hsgn1, h0_eq, h1_eq, planeVec_halfAngleSet_one_eq_const hn1 hA1,
            planeVec_halfAngleSet_one_eq_const hn1 hA1, hN_cast]; ring
        · rcases hslots with hc | ⟨h0_eq, h1_eq⟩
          · exact (hcase hc).elim
          · have hsgn_neg : sgn = -1 := ite_eq_right hcase; rw [hsgn_neg, h0_eq, h1_eq,
              planeVec_halfAngleSet_one_eq_const hn1 hA1, planeVec_halfAngleSet_one_eq_const hn1
              hA1, hN_cast]; ring
      rw [hdiff_in]; by_cases hc10 : addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A
      · rw [ite_eq_left hc10]; simp only [↓reduceIte]
        have hp_diff : planeVec A γ (addrEquiv n 2 u s1) - planeVec A γ (addrEquiv n 2 u s0) =
          ((-(Real.sin γ - Real.cos γ / √(N - 1)) : ℝ) : ℂ) := by
          simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            hc10.1, hc10.2, ↓reduceIte, hA1, Nat.cast_one, Real.sqrt_one]; push_cast; ring
        rw [hp_diff]; have hC := congrArg Complex.ofReal hamp; push_cast at hC ⊢
        linear_combination -sgn * hC
      · rw [ite_eq_right hc10]; by_cases hc01 : addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A
        · rw [ite_eq_left hc01]
          have hp_diff : planeVec A γ (addrEquiv n 2 u s1) - planeVec A γ (addrEquiv n 2 u s0) =
            ((Real.sin γ - Real.cos γ / √(N - 1) : ℝ) : ℂ) := by
            simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              hc01.1, hc01.2, ↓reduceIte, hA1, Nat.cast_one, Real.sqrt_one]; push_cast; ring
          rw [hp_diff]; have hC := congrArg Complex.ofReal hamp; push_cast at hC ⊢
          linear_combination sgn * hC
        · rw [ite_eq_right hc01, mul_zero, mul_zero]
          have hboth_out : addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A := by
            by_cases h0 : addrEquiv n 2 u s0 ∈ A
            · exfalso; have h1 : addrEquiv n 2 u s1 ∈ A := (by by_contra h1; exact hc10 ⟨h0, h1⟩)
              exact hd (Finset.card_le_one.1 hA1.le (addrEquiv n 2 u s0) h0 (addrEquiv n 2 u s1) h1)
            · exact ⟨h0, fun h1 ↦ hc01 ⟨h0, h1⟩⟩
          have hp_eq : planeVec A γ (addrEquiv n 2 u s1) - planeVec A γ (addrEquiv n 2 u s0) = 0
            := by
            simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              hboth_out.1, hboth_out.2, ↓reduceIte, sub_self]
          rw [hp_eq, mul_zero, mul_zero, mul_zero]
  rw [hvSym_eq, hvAnti_eq, hvDiag_eq]
/-- Stage-`1` guard for CSWAP warm readout: one slot sits at `θ₁ = halfAngleSet n 1` and the
  peer
  slot sits in `[θ₁, 4 / 5]`. -/
noncomputable def cswapWarmGuard (n : ℕ) (betas : Fin 2 → ℝ) : Prop :=
  (betas s0 = halfAngleSet n 1 ∧ halfAngleSet n 1 ≤ betas s1 ∧ betas s1 ≤ 4 / 5) ∨
    (betas s1 = halfAngleSet n 1 ∧ halfAngleSet n 1 ≤ betas s0 ∧ betas s0 ≤ 4 / 5)
/-- Explicit elementary upper bound on the expected query cost of `cswapWarmR1Circuit`
  whenever the
  warm slot angle satisfies `0 ≤ γ_lo ≤ max (betas s0) (betas s1) ≤ 4 / 5` (`n ≥ 100`). -/
noncomputable def cswapR1CostUpper (n : ℕ) (γ_lo : ℝ) : ℝ :=
  ((1 - Real.sin γ_lo ^ 2 / 2) *
      ((π / 4 - Real.arctan (Real.tan γ_lo / √2)) / (2 * √2) + 1 / (4 * √2)) +
    1 / 1000000000000) * √((2 : ℝ) ^ n)
/-- Hybrid `r = 1` potential (`m = 2`) using `cswapR1CostUpper` under `cswapWarmGuard` and
  falling
  back to `PipeFuse.warmR1Cost1` otherwise. -/
noncomputable def cswapWarmR1Cost1 (n : ℕ) (betas : Fin 2 → ℝ) : ℝ :=
  open Classical in
  if cswapWarmGuard n betas then
    cswapR1CostUpper n (max (betas s0) (betas s1))
  else
    PipeFuse.warmR1Cost1 n 2 betas
theorem cswapR1CostUpper_nonneg (n : ℕ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ_hi : γ ≤ 4 / 5) : 0 ≤
  cswapR1CostUpper n γ := by
  dsimp only [cswapR1CostUpper]; have hs2 : Real.sin γ ^ 2 ≤ 1 :=
    (by nlinarith [Real.sin_sq_add_cos_sq γ, sq_nonneg (Real.cos γ)])
  have h1s : 0 ≤ 1 - Real.sin γ ^ 2 / 2 := (by linarith)
  have hcos45_ge : 17 / 25 ≤ Real.cos (4 / 5) := by
    have h2 : (4 / 5 : ℝ) = 2 * (2 / 5) := (by ring); rw [h2, Real.cos_two_mul']
    have hs : Real.sin (2 / 5) ≤ 2 / 5 := Real.sin_le (by positivity); have hs0 : 0 ≤ Real.sin (2 /
      5) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_gt_three])
    nlinarith [Real.sin_sq_add_cos_sq (2 / 5)]
  have hcos_γ : 17 / 25 ≤ Real.cos γ := hcos45_ge.trans (Real.cos_le_cos_of_nonneg_of_le_pi hγ0
    (by linarith [Real.pi_gt_three]) hγ_hi)
  have htan_le : Real.tan γ ≤ 20 / 17 := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]; linarith [(Real.sin_le hγ0).trans
      hγ_hi]
  have hdiv_lt1 : Real.tan γ / √2 ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.2 (by positivity))]; have hsq : (20 / 17 : ℝ) ^ 2 ≤ (√2) ^ 2 :=
      (by rw [Real.sq_sqrt (by positivity)]; norm_num); exact htan_le.trans (PipeFuse.sq_le_imp_le
      (by positivity) (Real.sqrt_nonneg _) hsq)
  have harc_le : Real.arctan (Real.tan γ / √2) ≤ π / 4 :=
    (by simpa [Real.arctan_one] using Real.arctan_mono hdiv_lt1); have hsub_nn : 0 ≤ π / 4 -
    Real.arctan (Real.tan γ / √2) := (by linarith); positivity
theorem cswapR1CostUpper_anti (n : ℕ) {γ₁ γ₂ : ℝ} (h1 : 0 ≤ γ₁) (h12 : γ₁ ≤ γ₂) (h2 : γ₂ ≤ 4 / 5) :
  cswapR1CostUpper n γ₂ ≤ cswapR1CostUpper n γ₁ := by
  dsimp only [cswapR1CostUpper]; refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine add_le_add_left ?_ (1 / 1000000000000 : ℝ); have hpi2 : (4 / 5 : ℝ) < π / 2 :=
    (by linarith [Real.pi_gt_three]); have hs_nn1 : 0 ≤ Real.sin γ₁ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith [Real.pi_gt_three])
  have hs_le : Real.sin γ₁ ≤ Real.sin γ₂ := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_gt_three]) (h2.trans hpi2.le) h12; have hs2_le1 : Real.sin γ₂ ^ 2 ≤ 1 :=
    (by nlinarith [Real.sin_sq_add_cos_sq γ₂, sq_nonneg (Real.cos γ₂)])
  have hf1_le : 1 - Real.sin γ₂ ^ 2 / 2 ≤ 1 - Real.sin γ₁ ^ 2 / 2 := (by nlinarith)
  have hf1_nn : 0 ≤ 1 - Real.sin γ₂ ^ 2 / 2 := (by linarith)
  have htan_le : Real.tan γ₁ ≤ Real.tan γ₂ := PipeFuse.tan_mono_nonneg h1 h12 (h2.trans_lt hpi2)
  have harc_le : Real.arctan (Real.tan γ₁ / √2) ≤ Real.arctan (Real.tan γ₂ / √2) := Real.arctan_mono
    (div_le_div_of_nonneg_right htan_le (Real.sqrt_nonneg _))
  have hcos45_ge : 17 / 25 ≤ Real.cos (4 / 5) := by
    have h2' : (4 / 5 : ℝ) = 2 * (2 / 5) := (by ring); rw [h2', Real.cos_two_mul']
    have hs : Real.sin (2 / 5) ≤ 2 / 5 := Real.sin_le (by positivity); have hs0 : 0 ≤ Real.sin (2 /
      5) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_gt_three])
    nlinarith [Real.sin_sq_add_cos_sq (2 / 5)]
  have hcos_γ2 : 17 / 25 ≤ Real.cos γ₂ := hcos45_ge.trans (Real.cos_le_cos_of_nonneg_of_le_pi
    (h1.trans h12) (by linarith [Real.pi_gt_three]) h2)
  have htan2_le : Real.tan γ₂ ≤ 20 / 17 := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]; linarith [(Real.sin_le (h1.trans
      h12)).trans h2]
  have hdiv_le1 : Real.tan γ₂ / √2 ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.2 (by positivity))]; have hsq : (20 / 17 : ℝ) ^ 2 ≤ (√2) ^ 2 :=
      (by rw [Real.sq_sqrt (by positivity)]; norm_num); exact htan2_le.trans (PipeFuse.sq_le_imp_le
      (by positivity) (Real.sqrt_nonneg _) hsq)
  have harc2_le : Real.arctan (Real.tan γ₂ / √2) ≤ π / 4 :=
    (by simpa [Real.arctan_one] using Real.arctan_mono hdiv_le1)
  have hf2_nn : 0 ≤ (π / 4 - Real.arctan (Real.tan γ₂ / √2)) / (2 * √2) + 1 / (4 * √2) :=
    (by have : 0 ≤ π / 4 - Real.arctan (Real.tan γ₂ / √2) := (by linarith); positivity)
  have hf2_le : (π / 4 - Real.arctan (Real.tan γ₂ / √2)) / (2 * √2) + 1 / (4 * √2) ≤ (π / 4 -
    Real.arctan (Real.tan γ₁ / √2)) / (2 * √2) + 1 / (4 * √2) := by
    have hsub : π / 4 - Real.arctan (Real.tan γ₂ / √2) ≤ π / 4 - Real.arctan (Real.tan γ₁ / √2) :=
      (by linarith); exact add_le_add_left (div_le_div_of_nonneg_right hsub (by positivity)) _
  exact mul_le_mul hf1_le hf2_le hf2_nn (hf1_nn.trans hf1_le)
theorem cswapWarmR1Cost1_nonneg (n : ℕ) (betas : Fin 2 → ℝ) : 0 ≤ cswapWarmR1Cost1 n betas := by
  dsimp only [cswapWarmR1Cost1]; split_ifs with hg
  · have hθ1_nn : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); rcases hg with
      ⟨h0, h1_lo, h1_hi⟩ | ⟨h1, h0_lo, h0_hi⟩
    · have hm_eq : max (betas s0) (betas s1) = betas s1 := (by rw [h0]; exact max_eq_right h1_lo)
      rw [hm_eq]; exact cswapR1CostUpper_nonneg n (hθ1_nn.trans h1_lo) h1_hi
    · have hm_eq : max (betas s0) (betas s1) = betas s0 := (by rw [h1]; exact max_eq_left h0_lo)
      rw [hm_eq]; exact cswapR1CostUpper_nonneg n (hθ1_nn.trans h0_lo) h0_hi
  · exact PipeFuse.warmR1Cost1_nonneg n 2 betas
/-- Terminal (`r = 1`, `m = 2`) CSWAP symmetry-filtered warm readout circuit with automatic
  fallback to `rawProjCheckStage1Circuit` outside `cswapWarmGuard`. -/
noncomputable def cswapWarmR1Circuit {Var : Type} (res : Var) (n k : ℕ)
    (T : Finset (Fin (2 ^ n))) (betas : Fin 2 → ℝ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2) :=
  open Classical in
  if hc : cswapWarmGuard n betas ∧ 100 ≤ n then
    let γ := max (betas s0) (betas s1)
    let γ_sym := cswapSymAngle n γ
    let θ₂ := halfAngleSet n 2
    let K := ⌈(π / 4 - γ_sym) / (2 * θ₂)⌉₊
    let β_end := γ_sym + 2 * (K : ℝ) * θ₂
    .seq (.step (phaseI ((oracleReg n 2 k).embedUnitary (cswapFilterUnitary n))))
      (.seq (.measure res (allMarkersReg n 2 k))
        (dispBits res 2 0 fun oVal ↦
          let o : Fin (2 ^ 2) := ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩
          if o = 0 then
            .seq (offDiagPrepRec n k (by omega) T K)
              (offDiagLockedLoopCircuit res n k (by omega) T β_end)
          else if o = ⟨1, by decide⟩ then
            .seq (.step (phaseI
                ((oracleReg n 2 k).embedUnitary (permutationUnitary (flipFlag0Perm n)))))
              (extractOddPairStage1Circuit res n k T)
          else if o = ⟨2, by decide⟩ then
            .seq (resetRegCircuit res (oracleReg n 2 k))
              (lockSingleFromSetCircuit res n 2 k T)
          else
            .skip))
  else
    rawProjCheckStage1Circuit res n k (by decide) T
theorem lockedAlpha_m2_r2_pi4_bound_100 {n : ℕ} (hn : 100 ≤ n) {β_end : ℝ} (hβ_ge_pi4 : π / 4 ≤
  β_end) (hβ_le_54 : β_end ≤ 5 / 4) : (1 - lockedAlpha β_end (halfAngleSet n 2) ^ 2)⁻¹ ≤ (1 / (4 *
  √2) + 1 / 2000000000000) * √((2 : ℝ) ^ n) := by
  set N : ℝ := (2 : ℝ) ^ n; have hN_cast : (2 ^ n : ℝ) = N := rfl; obtain ⟨hSN_ge, hN_ge⟩ :=
    PipeFuse.pow_two_bounds_100 hn; rw [hN_cast] at hSN_ge hN_ge; have hSN_pos : 0 < √N :=
    lt_of_lt_of_le (by positivity) hSN_ge
  have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge; obtain ⟨_, _, _, hcos2, hsin2_lo,
    hsin2_hi⟩ := PipeFuse.halfAngleSet_bounds_100 hn (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024)
  simp only [Nat.cast_ofNat] at hcos2 hsin2_lo hsin2_hi; rw [hN_cast] at hcos2 hsin2_lo hsin2_hi
  set θ₂ : ℝ := halfAngleSet n 2; obtain ⟨htan54, h54_lt⟩ := PipeFuse.tan_five_div_four_le_five
  have hβ_lt_pi2 : β_end < π / 2 := hβ_le_54.trans_lt h54_lt; have hcβ_end : 0 < Real.cos β_end :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos, hβ_ge_pi4], hβ_lt_pi2⟩
  have htan_lo : 1 ≤ Real.tan β_end := by
    rw [← Real.tan_pi_div_four]
    exact PipeFuse.tan_mono_nonneg (by linarith only [Real.pi_pos]) hβ_ge_pi4 hβ_lt_pi2
  have htan_hi : Real.tan β_end ≤ 5 := (PipeFuse.tan_mono_nonneg
    (by linarith only [Real.pi_pos, hβ_ge_pi4]) hβ_le_54 h54_lt).trans htan54
  have hs2_le2 : √(2 : ℝ) ≤ 2 := PipeFuse.sq_le_imp_le (Real.sqrt_nonneg _) (by norm_num)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num); set u_lock : ℝ := Real.tan β_end * Real.sin (2 *
    θ₂) - 2 * 2 / N
  have hu_lo : (9999999999989 / 10000000000000) * (2 * √(2 : ℝ) / √N) ≤ u_lock := by
    have hts : (999999999999 / 1000000000000) * (2 * √(2 : ℝ) / √N) ≤ Real.tan β_end * Real.sin (2 *
      θ₂) :=
      (by simpa using mul_le_mul htan_lo hsin2_lo (by positivity) (by linarith only [htan_lo]))
    have h4N : 2 * (2 : ℝ) / N ≤ (1 / 10000000000000) * (2 * √(2 : ℝ) / √N) := by
      have hfac : √(2 : ℝ) / √N ≤ 2 / 1000000000000000 := (div_le_div_of_nonneg_right hs2_le2
        hSN_pos.le).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)
      have hsq_eq : 2 * (2 : ℝ) / N = (√(2 : ℝ) / √N) * (2 * √(2 : ℝ) / √N) := by
        rw [div_mul_div_comm, Real.mul_self_sqrt hN_pos.le]; have hs2 : √(2 : ℝ) * (2 * √(2 : ℝ)) =
          2 * (√(2 : ℝ) * √(2 : ℝ)) := (by ring); rw [hs2, Real.mul_self_sqrt (by norm_num)]
      rw [hsq_eq]; exact mul_le_mul_of_nonneg_right (by linarith only [hfac]) (by positivity)
    have hpos_x : 0 ≤ 2 * √(2 : ℝ) / √N := (by positivity); have hsub : (9999999999989 /
      10000000000000) * (2 * √(2 : ℝ) / √N) ≤ (999999999999 / 1000000000000 - 1 / 10000000000000) *
      (2 * √(2 : ℝ) / √N) := mul_le_mul_of_nonneg_right (by norm_num) hpos_x
    have hsub' : (999999999999 / 1000000000000 - 1 / 10000000000000) * (2 * √(2 : ℝ) / √N) =
      (999999999999 / 1000000000000) * (2 * √(2 : ℝ) / √N) - (1 / 10000000000000) * (2 * √(2 : ℝ) /
      √N) := (by ring); dsimp only [u_lock]; linarith only [hts, h4N, hsub, hsub']
  have hu_pos : 0 < u_lock := lt_of_lt_of_le (by positivity) hu_lo
  have hu_hi : u_lock ≤ 1 / 10000000000000 := by
    have hs2_small : Real.sin (2 * θ₂) ≤ 4 / 1000000000000000 := hsin2_hi.trans
      ((div_le_div_of_nonneg_right (by linarith only [hs2_le2]) hSN_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)); dsimp only [u_lock]
    have h1 : Real.tan β_end * Real.sin (2 * θ₂) ≤ 5 * (4 / 1000000000000000) := mul_le_mul htan_hi
      hs2_small (le_trans (by positivity) hsin2_lo) (by positivity)
    have h2 : 0 ≤ 2 * (2 : ℝ) / N := (by positivity); linarith only [h1, h2]
  have hα_eq : lockedAlpha β_end θ₂ = 1 / (1 + u_lock) := by
    dsimp only [lockedAlpha, u_lock]; rw [Real.cos_sub, Real.tan_eq_sin_div_cos, hcos2]
    have h1u : 0 < 1 + (Real.sin β_end / Real.cos β_end * Real.sin (2 * θ₂) - 2 * 2 / N) :=
      (by rw [← Real.tan_eq_sin_div_cos]; change 0 < 1 + u_lock; linarith only [hu_pos])
    have hden_c : Real.cos β_end * (1 - 2 * 2 / N) + Real.sin β_end * Real.sin (2 * θ₂) = Real.cos
      β_end * (1 + (Real.sin β_end / Real.cos β_end * Real.sin (2 * θ₂) - 2 * 2 / N)) :=
      (by field_simp [hcβ_end.ne', hN_pos.ne']; ring); rw [hden_c]; field_simp [hcβ_end.ne',
      h1u.ne']
  have hlock_lo : 4 * 1 * (999999999998 / 1000000000000) * √(2 : ℝ) / √N ≤ 1 - lockedAlpha β_end θ₂
    ^ 2 := by
    have hclick_eq : 1 - lockedAlpha β_end θ₂ ^ 2 = (2 * u_lock + u_lock ^ 2) / (1 + u_lock) ^ 2 :=
      (by rw [hα_eq]; field_simp [(by linarith only [hu_pos] : (0 : ℝ) < 1 + u_lock).ne']; ring)
    rw [hclick_eq]
    have h1 : 2 * u_lock * (9999999999997 / 10000000000000) ≤ (2 * u_lock + u_lock ^ 2) / (1 +
      u_lock) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; have hu2 : u_lock ^ 2 ≤ (1 / 10000000000000) * u_lock :=
        (by rw [sq]; exact mul_le_mul_of_nonneg_right hu_hi hu_pos.le); have hu1 : u_lock ≤ 1 :=
        (by linarith only [hu_hi])
      have hu2_s : u_lock ^ 2 ≤ 1 / 10000000000000 := by
        calc u_lock ^ 2 = u_lock * u_lock := sq u_lock
          _ ≤ (1 / 10000000000000) * 1 := mul_le_mul hu_hi hu1 hu_pos.le (by positivity)
          _ = 1 / 10000000000000 := mul_one _
      have hu3 : u_lock ^ 2 * u_lock ≤ (1 / 10000000000000) * u_lock := mul_le_mul_of_nonneg_right
        hu2_s hu_pos.le
      have hexp : 2 * u_lock * (9999999999997 / 10000000000000) * (1 + u_lock) ^ 2 = (9999999999997
        / 5000000000000) * u_lock + (9999999999997 / 2500000000000) * u_lock ^ 2 + (9999999999997 /
        5000000000000) * (u_lock ^ 2 * u_lock) := (by ring); linarith only [hexp, hu2, hu3, hu_pos]
    have hm := mul_le_mul_of_nonneg_right hu_lo
      (by norm_num : (0 : ℝ) ≤ 2 * (9999999999997 / 10000000000000)); have hfac : 4 * (999999999998
      / 1000000000000 : ℝ) ≤ 2 * (9999999999989 / 10000000000000) * 2 * (9999999999997 /
      10000000000000) := (by norm_num); have hpos_s : 0 ≤ √(2 : ℝ) / √N := (by positivity)
    have h2 : 4 * 1 * (999999999998 / 1000000000000) * √(2 : ℝ) / √N ≤ 2 * u_lock * (9999999999997 /
      10000000000000) := by
      calc 4 * 1 * (999999999998 / 1000000000000) * √(2 : ℝ) / √N
          = (4 * (999999999998 / 1000000000000)) * (√(2 : ℝ) / √N) := by ring
        _ ≤ (2 * (9999999999989 / 10000000000000) * 2 * (9999999999997 / 10000000000000)) *
              (√(2 : ℝ) / √N) := mul_le_mul_of_nonneg_right hfac hpos_s
        _ = (9999999999989 / 10000000000000) * (2 * √(2 : ℝ) / √N) *
              (2 * (9999999999997 / 10000000000000)) := by ring
        _ ≤ u_lock * (2 * (9999999999997 / 10000000000000)) := hm
        _ = 2 * u_lock * (9999999999997 / 10000000000000) := by ring
    exact h2.trans h1
  have hlhs_pos : 0 < 4 * 1 * (999999999998 / 1000000000000) * √(2 : ℝ) / √N := (by positivity)
  have h1 : (1 - lockedAlpha β_end θ₂ ^ 2)⁻¹ ≤ (4 * 1 * (999999999998 / 1000000000000) * √(2 : ℝ) /
    √N)⁻¹ := inv_anti₀ hlhs_pos hlock_lo; refine h1.trans ?_; rw [inv_div]; have hden_pos : 0 < 4 *
    1 * (999999999998 / 1000000000000) * √(2 : ℝ) := (by positivity); rw [div_le_iff₀ hden_pos]
  have hs2_pos : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by positivity)
  have h25_lt : (4000000000000 / 999999999998 : ℝ) ≤ 4 * √2 := by
    refine PipeFuse.sq_le_imp_le (by norm_num) (by positivity) ?_; rw [mul_pow, Real.sq_sqrt
      (by positivity)]; norm_num
  have hprod_eq : (1 / (4 * √2) + 1 / 2000000000000) * √N * (4 * 1 * (999999999998 / 1000000000000)
    * √(2 : ℝ)) = √N * (999999999998 / 1000000000000 + (999999999998 / 2000000000000000000000000) *
    (4 * √2)) := (by field_simp [hs2_pos.ne']; ring); rw [hprod_eq]; have h1_le : (1 : ℝ) ≤
    999999999998 / 1000000000000 + (999999999998 / 2000000000000000000000000) * (4 * √2) :=
    (by linarith only [h25_lt]); simpa using mul_le_mul_of_nonneg_left h1_le hSN_pos.le
theorem cswapWarmR1_real_cost_le {n : ℕ} (hn : 100 ≤ n) {γ : ℝ} (hγ_lo : halfAngleSet n 1 ≤ γ)
  (hγ_hi : γ ≤ 4 / 5) :
    let γ_sym := cswapSymAngle n γ; let θ₂ := halfAngleSet n 2
    let K := ⌈(π / 4 - γ_sym) / (2 * θ₂)⌉₊; let β_end := γ_sym + 2 * (K : ℝ) * θ₂
    let α := lockedAlpha β_end θ₂
    let cCold := ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / 2)
    2 * θ₂ ≤ β_end ∧ β_end < π / 2 ∧ cswapSymWeight n γ * ((K : ℝ) + ((1 - α ^ 2)⁻¹ + 1)) +
      (Real.sin (γ - halfAngleSet n 1) ^ 2 / 2) * 1 + (1 / (2 ^ n : ℝ)) * cCold ≤ cswapR1CostUpper n
      γ := by
  intro γ_sym θ₂ K β_end α cCold; have hn1 : 1 ≤ n := (by omega)
  set N : ℝ := (2 : ℝ) ^ n; have hN_cast : (2 ^ n : ℝ) = N := rfl; obtain ⟨hSN_ge, hN_ge⟩ :=
    PipeFuse.pow_two_bounds_100 hn; rw [hN_cast] at hSN_ge hN_ge; have hSN_pos : 0 < √N :=
    lt_of_lt_of_le (by positivity) hSN_ge
  have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge; obtain ⟨hθ1_lo, _, hθ1_13, -⟩ :=
    PipeFuse.halfAngleSet_bounds_100 hn (by omega : 1 ≤ 1) (by omega : 1 ≤ 1024); obtain ⟨hθ2_lo, _,
    hθ2_13, -⟩ := PipeFuse.halfAngleSet_bounds_100 hn (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024)
  simp only [Nat.cast_one] at hθ1_lo; simp only [Nat.cast_ofNat] at hθ2_lo; have hθ1_nn : 0 ≤
    halfAngleSet n 1 := (by linarith [div_pos (Real.sqrt_pos.2 zero_lt_one) hSN_pos])
  have hθ2_pos : 0 < θ₂ := lt_of_lt_of_le (div_pos (Real.sqrt_pos.2 (by positivity)) hSN_pos) hθ2_lo
  have hγ0 : 0 ≤ γ := hθ1_nn.trans hγ_lo
  obtain ⟨_, _, hw0_pos, hγsym_nn, hγsym_lt, hγsym_ge, -, -⟩ := cswapSymAngle_bounds hn hγ0 hγ_hi
  -- 1. Bounds on `K` and `β_end`
  have hquot_pos : 0 < (π / 4 - γ_sym) / (2 * θ₂) := div_pos (by linarith) (by positivity)
  have hK_pos : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hquot_pos).ne'; have hK_ge : (π /
    4 - γ_sym) / (2 * θ₂) ≤ (K : ℝ) := Nat.le_ceil _; have hK_lt : (K : ℝ) < (π / 4 - γ_sym) / (2 *
    θ₂) + 1 := Nat.ceil_lt_add_one hquot_pos.le
  have hβ_ge_2θ : 2 * θ₂ ≤ β_end := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := (by exact_mod_cast hK_pos)
    calc 2 * θ₂ = 0 + 1 * (2 * θ₂) := by ring
      _ ≤ γ_sym + (K : ℝ) * (2 * θ₂) :=
          add_le_add hγsym_nn (mul_le_mul_of_nonneg_right hK1 (by positivity))
      _ = β_end := by dsimp [β_end]; ring
  have hβ_ge_pi4 : π / 4 ≤ β_end := by
    dsimp only [β_end]; have hmul := mul_le_mul_of_nonneg_right hK_ge (by positivity : 0 ≤ 2 * θ₂)
    rw [div_mul_cancel₀ _ (by positivity)] at hmul; linarith
  have hβ_lt_step : β_end < π / 4 + 2 * θ₂ := by
    dsimp only [β_end]; have hmul := mul_lt_mul_of_pos_right hK_lt (by positivity : 0 < 2 * θ₂)
    rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul] at hmul; linarith
  have hβ_le_54 : β_end ≤ 5 / 4 := (by linarith [hβ_lt_step, hθ2_13, Real.pi_lt_d4])
  obtain ⟨htan54, h54_lt⟩ := PipeFuse.tan_five_div_four_le_five; have hβ_lt_pi2 : β_end < π / 2 :=
    hβ_le_54.trans_lt h54_lt; refine ⟨hβ_ge_2θ, hβ_lt_pi2, ?_⟩
  -- 2. Upper bound on `(K: ℝ)`
  have hK_bound : (K : ℝ) ≤ ((π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * √2)) * √N + 1 := by
    have hnum_le : π / 4 - γ_sym ≤ π / 4 - Real.arctan (Real.tan γ / √2) := (by linarith)
    have h1 : (π / 4 - γ_sym) / (2 * θ₂) ≤ (π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * (√2 / √N))
      := by
      have hd1 : (π / 4 - γ_sym) / (2 * θ₂) ≤ (π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * θ₂) :=
        div_le_div_of_nonneg_right hnum_le (by positivity)
      refine hd1.trans (div_le_div_of_nonneg_left (by linarith) (by positivity) ?_)
      linarith [hθ2_lo]
    have hrew : (π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * (√2 / √N)) = ((π / 4 - Real.arctan
      (Real.tan γ / √2)) / (2 * √2)) * √N := by
      have hs2 : (√2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'; field_simp [hSN_pos.ne',
        hs2]
    linarith [hK_lt, h1, hrew]
  -- 3. Tight `n ≥ 100` upper bound on `(1 - α ^ 2)⁻¹`
  have hinv_le : (1 - α ^ 2)⁻¹ ≤ (1 / (4 * √2) + 1 / 2000000000000) * √N :=
    lockedAlpha_m2_r2_pi4_bound_100 hn hβ_ge_pi4 hβ_le_54
  -- 4. Bounds on `cswapSymWeight n γ` and `w 1`, `w 2`
  have hw0_eq := cswapSymWeight_eq hn1 γ; rw [hN_cast] at hw0_eq
  have hw0_le1 : cswapSymWeight n γ ≤ 1 := by
    rw [hw0_eq]; have hs_nn : 0 ≤ Real.sin (γ - halfAngleSet n 1) ^ 2 / 2 := (by positivity)
    have hN_inv : 0 ≤ 1 / N := (by positivity); linarith
  have hw0_approx : cswapSymWeight n γ ≤ 1 - Real.sin γ ^ 2 / 2 + 2 / √N := by
    rw [hw0_eq]
    have hsin1_eq : Real.sin (halfAngleSet n 1) = 1 / √N := by
      have hs := sqrt_dim_mul_sin_halfAngleSet (n := n) (r := 1) (Nat.one_lt_two_pow (by omega)).le
      simp only [Nat.cast_one, Real.sqrt_one, hN_cast] at hs; rw [eq_div_iff hSN_pos.ne', mul_comm]
      exact hs
    have hcos1_ge : 1 - 1 / N ≤ Real.cos (halfAngleSet n 1) := by
      have hc := sqrt_dim_mul_cos_halfAngleSet n 1; simp only [Nat.cast_one, hN_cast] at hc
      have hcos_eq : Real.cos (halfAngleSet n 1) = √(1 - 1 / N) := by
        have h1 : √((N - 1) / N) = √(N - 1) / √N := Real.sqrt_div (by linarith) N
        have h2 : (N - 1) / N = 1 - 1 / N := (by field_simp [hN_pos.ne']); rw [← h2, h1, eq_div_iff
          hSN_pos.ne', mul_comm]; exact hc
      rw [hcos_eq]; have h1N_le1 : 1 / N ≤ 1 := div_le_one_of_le₀ (by linarith) hN_pos.le
      have h1_sub_nn : 0 ≤ 1 - 1 / N := sub_nonneg.2 h1N_le1
      refine PipeFuse.sq_le_imp_le h1_sub_nn (Real.sqrt_nonneg _) ?_; rw [Real.sq_sqrt h1_sub_nn]
      have hsq1N : (1 / N) ^ 2 ≤ 1 / N :=
        (by rw [sq]; exact mul_le_of_le_one_left (by positivity) h1N_le1)
      have hexp1N : (1 - 1 / N) ^ 2 = 1 - 2 * (1 / N) + (1 / N) ^ 2 := (by ring)
      linarith only [hsq1N, hexp1N]
    have hsin_γ_nn : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0
      (by linarith [Real.pi_gt_three]); have hsin_γ_le1 : Real.sin γ ≤ 1 := Real.sin_le_one γ
    have hcos_γ_nn : 0 ≤ Real.cos γ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    have hcos_γ_le1 : Real.cos γ ≤ 1 := Real.cos_le_one γ
    have h1N_le_SN : 1 / N ≤ 1 / √N := by
      refine div_le_div_of_nonneg_left zero_le_one hSN_pos ?_
      calc √N ≤ √N * √N := le_mul_of_one_le_right hSN_pos.le (by linarith only [hSN_ge])
        _ = N := Real.mul_self_sqrt hN_pos.le
    have hsin_diff_ge : Real.sin γ - 2 / √N ≤ Real.sin (γ - halfAngleSet n 1) := by
      rw [Real.sin_sub, hsin1_eq]
      have h1 : Real.sin γ * (1 - 1 / N) ≤ Real.sin γ * Real.cos (halfAngleSet n 1) :=
        mul_le_mul_of_nonneg_left hcos1_ge hsin_γ_nn; have h2 : Real.cos γ * (1 / √N) ≤ 1 / √N :=
        mul_le_of_le_one_left (by positivity) hcos_γ_le1; have h3 : Real.sin γ * (1 / N) ≤ 1 / √N :=
        (mul_le_of_le_one_left (by positivity) hsin_γ_le1).trans h1N_le_SN
      have hdist : Real.sin γ * (1 - 1 / N) = Real.sin γ - Real.sin γ * (1 / N) := (by ring)
      have hdiv2 : 2 / √N = 2 * (1 / √N) := (by ring); linarith only [h1, h2, h3, hdist, hdiv2]
    have hsin_diff_nn : 0 ≤ Real.sin (γ - halfAngleSet n 1) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_three])
    have hsq_diff : Real.sin γ ^ 2 - 4 / √N ≤ Real.sin (γ - halfAngleSet n 1) ^ 2 := by
      by_cases hpos : 0 ≤ Real.sin γ - 2 / √N
      · have hsq : (Real.sin γ - 2 / √N) ^ 2 ≤ Real.sin (γ - halfAngleSet n 1) ^ 2 :=
          pow_le_pow_left₀ hpos hsin_diff_ge 2; have hm4 : (4 / √N) * Real.sin γ ≤ 4 / √N :=
          mul_le_of_le_one_right (by positivity) hsin_γ_le1; have hsq2 : 0 ≤ (2 / √N) ^ 2 :=
          sq_nonneg _
        have hexp : (Real.sin γ - 2 / √N) ^ 2 = Real.sin γ ^ 2 - (4 / √N) * Real.sin γ + (2 / √N) ^
          2 := (by ring); linarith only [hsq, hm4, hsq2, hexp]
      · have hpos' : Real.sin γ < 2 / √N := (by linarith only [hpos])
        have hle : Real.sin γ ^ 2 ≤ 4 / √N := by
          have h2 : Real.sin γ ≤ 2 / √N := hpos'.le
          have hmul : Real.sin γ ^ 2 ≤ 1 * (2 / √N) := by
            calc Real.sin γ ^ 2 = Real.sin γ * Real.sin γ := sq _
              _ ≤ 1 * (2 / √N) := mul_le_mul hsin_γ_le1 h2 hsin_γ_nn zero_le_one
          have hdpos : 0 < 2 / √N := div_pos (by norm_num) hSN_pos; have hdiv4 : 4 / √N = 2 * (2 /
            √N) := (by ring); linarith only [hmul, hdpos, hdiv4]
        have hsq_nn : 0 ≤ Real.sin (γ - halfAngleSet n 1) ^ 2 := sq_nonneg _; linarith only [hle,
          hsq_nn]
    have hhalf : Real.sin γ ^ 2 / 2 - 2 / √N ≤ Real.sin (γ - halfAngleSet n 1) ^ 2 / 2 :=
      (by have h42 : 4 / √N = 2 * (2 / √N) := (by ring); linarith only [hsq_diff, h42])
    have h1N_nn : 0 ≤ 1 / N := (by positivity); linarith only [hhalf, h1N_nn]
  -- 5. Combine all branch terms into `cswapR1CostUpper n γ`
  set C_main : ℝ := (π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * √2) + 1 / (4 * √2)
  have hC_main_nn : 0 ≤ C_main := by
    dsimp only [C_main]; have harc_le : Real.arctan (Real.tan γ / √2) ≤ π / 4 :=
      (by have h1 : Real.arctan (Real.tan γ / √2) ≤ cswapSymAngle n γ := hγsym_ge; linarith)
    have : 0 ≤ π / 4 - Real.arctan (Real.tan γ / √2) := (by linarith); positivity
  have hC_main_le1 : C_main ≤ 1 := by
    dsimp only [C_main]
    have harc_nn : 0 ≤ Real.arctan (Real.tan γ / √2) := by
      refine Real.arctan_nonneg.2 (div_nonneg ?_ (Real.sqrt_nonneg _)); rw [Real.tan_eq_sin_div_cos]
      exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hγ0 (by linarith [Real.pi_gt_three]))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three],
          by linarith [Real.pi_gt_three]⟩)
    have hs2_ge : (7 / 5 : ℝ) ≤ √2 := by
      refine PipeFuse.sq_le_imp_le (by norm_num) (Real.sqrt_nonneg _) ?_; rw [Real.sq_sqrt
        (by norm_num)]; norm_num
    have hd1 : (π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * √2) ≤ 1 / (2 * (7 / 5)) := by
      have h1 : (π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * √2) ≤ 1 / (2 * √2) :=
        div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d4, harc_nn]) (by positivity)
      exact h1.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith [hs2_ge]))
    have hd2 : (1 : ℝ) / (4 * √2) ≤ 1 / (4 * (7 / 5)) := div_le_div_of_nonneg_left zero_le_one
      (by norm_num) (by linarith only [hs2_ge]); linarith only [hd1, hd2]
  have hw0_term : cswapSymWeight n γ * ((K : ℝ) + ((1 - α ^ 2)⁻¹ + 1)) ≤ (1 - Real.sin γ ^ 2 / 2) *
    C_main * √N + (1 / 2000000000000) * √N + 4 := by
    have hsum_inner : (K : ℝ) + ((1 - α ^ 2)⁻¹ + 1) ≤ C_main * √N + (1 / 2000000000000) * √N + 2
      := by
      dsimp only [C_main]; have hadd_c : (((π / 4 - Real.arctan (Real.tan γ / √2)) / (2 * √2)) * √N
        + 1) + (((1 / (4 * √2) + 1 / 2000000000000) * √N) + 1) = ((π / 4 - Real.arctan (Real.tan γ /
        √2)) / (2 * √2) + 1 / (4 * √2)) * √N + (1 / 2000000000000) * √N + 2 := (by ring)
      linarith only [hK_bound, hinv_le, hadd_c]
    have hm1 := mul_le_mul_of_nonneg_left hsum_inner hw0_pos.le
    have hm2 : cswapSymWeight n γ * (C_main * √N) ≤ (1 - Real.sin γ ^ 2 / 2) * C_main * √N + 2 *
      C_main := by
      have hmul := mul_le_mul_of_nonneg_right hw0_approx (mul_nonneg hC_main_nn hSN_pos.le)
      have hcancel : (2 / √N) * (C_main * √N) = 2 * C_main := (by field_simp [hSN_pos.ne'])
      have hdist_c : (1 - Real.sin γ ^ 2 / 2 + 2 / √N) * (C_main * √N) = (1 - Real.sin γ ^ 2 / 2) *
        C_main * √N + (2 / √N) * (C_main * √N) := (by ring); linarith only [hmul, hcancel, hdist_c]
    have hm3 : cswapSymWeight n γ * ((1 / 2000000000000) * √N + 2) ≤ (1 / 2000000000000) * √N + 2 :=
      mul_le_of_le_one_left (by positivity) hw0_le1; have hdist_w0 : cswapSymWeight n γ * (C_main *
      √N + (1 / 2000000000000) * √N + 2) = cswapSymWeight n γ * (C_main * √N) + cswapSymWeight n γ *
      ((1 / 2000000000000) * √N + 2) := (by ring); linarith only [hm1, hm2, hm3, hC_main_le1,
      hdist_w0]
  have hw1_le : (Real.sin (γ - halfAngleSet n 1) ^ 2 / 2) * 1 ≤ 1 := by
    have hs2 : Real.sin (γ - halfAngleSet n 1) ^ 2 ≤ 1 := by
      have hsc := Real.sin_sq_add_cos_sq (γ - halfAngleSet n 1); have hc2 : 0 ≤ Real.cos (γ -
        halfAngleSet n 1) ^ 2 := sq_nonneg _; linarith only [hsc, hc2]
    linarith only [hs2]
  have hw2_le : (1 / (2 ^ n : ℝ)) * cCold ≤ 1 := by
    dsimp only [cCold]; rw [hN_cast]; have hrc : ((relCostLock : ℚ≥0) : ℝ) ≤ 1 :=
      (by unfold relCostLock; norm_num); have hpi4 : π / 4 ≤ 1 :=
      (by linarith only [Real.pi_lt_d4])
    have hsq_half : √(N / 2) ≤ √N := Real.sqrt_le_sqrt (by linarith only [hN_pos])
    have hcCold_le : ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √(N / 2) ≤ √N := by
      have hp1 : ((relCostLock : ℚ≥0) : ℝ) * (π / 4) ≤ 1 := (mul_le_of_le_one_left (by positivity)
        hrc).trans hpi4; exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) hp1).trans hsq_half
    have hprod : (1 / N) * √N ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hN_pos]
      calc √N ≤ √N * √N := le_mul_of_one_le_right hSN_pos.le (by linarith only [hSN_ge])
        _ = N := Real.mul_self_sqrt hN_pos.le
    exact (mul_le_mul_of_nonneg_left hcCold_le (by positivity)).trans hprod
  have h6_le : (6 : ℝ) ≤ (1 / 2000000000000) * √N := (by linarith only [hSN_ge])
  dsimp only [cswapR1CostUpper]
  change _ ≤ ((1 - Real.sin γ ^ 2 / 2) * C_main + 1 / 1000000000000) * √N; linarith only [hw0_term,
    hw1_le, hw2_le, h6_le]
theorem cswapWarmR1_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn : 100 ≤ n)
  (hk1024 : k ≤ 1024) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA1 : (S \
  T).card = 1) {betas : Fin 2 → ℝ} (hβ0 : ∀ i, 0 ≤ betas i) (hβ_lt : ∀ i, betas i < π / 2) {Δ :
  CQState (Store Var) (2 ^ findAllQubits n 2 k)} (hΔ : PureStateAt (prodSlotState n 2 k fun i ↦
    slotPairVec
  (planeVec (S \ T) (betas i)) (Pi.single 0 1)) Δ) :
    let prog := (cswapWarmR1Circuit res n k T betas).compile QProg.qAssign (parallelMarkingOracle 2
      S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (cswapWarmR1Cost1 n betas) := by
  intro prog; by_cases hg : cswapWarmGuard n betas
  · have hc : cswapWarmGuard n betas ∧ 100 ≤ n := ⟨hg, hn⟩; have hn1 : 1 ≤ n := (by omega)
    have hn2 : 2 ≤ n := (by omega); set A := S \ T; have hrem1 : k - T.card = 1 :=
      (by rw [← hScard, ← Finset.card_sdiff_of_subset hTS]; exact hA1)
    let oracleS := parallelMarkingOracle 2 S
    let modelS := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleS
    have horacleS := isRealMatrix_parallelMarkingOracle (m := 2) S
    let Post : CQAssertion (Store Var) (2 ^ findAllQubits n 2 k) :=
      liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
    let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ := Pi.single ((oracleReg n 2
      k).basisSplitEquiv 0).2 1; set γ := max (betas s0) (betas s1)
    have hslots_and_bds : halfAngleSet n 1 ≤ γ ∧ γ ≤ 4 / 5 ∧ ((planeVec A (betas s0) = planeVec A
      (halfAngleSet n 1) ∧ planeVec A (betas s1) = planeVec A γ) ∨ (planeVec A (betas s0) = planeVec
      A γ ∧ planeVec A (betas s1) = planeVec A (halfAngleSet n 1))) := by
      rcases hg with ⟨hb0, hb1_lo, hb1_hi⟩ | ⟨hb1, hb0_lo, hb0_hi⟩
      · have hmax : γ = betas s1 := (by dsimp only [γ]; rw [hb0]; exact max_eq_right hb1_lo)
        exact ⟨hmax ▸ hb1_lo, hmax ▸ hb1_hi, Or.inl ⟨hb0 ▸ rfl, hmax ▸ rfl⟩⟩
      · have hmax : γ = betas s0 := (by dsimp only [γ]; rw [hb1]; exact max_eq_left hb0_lo)
        exact ⟨hmax ▸ hb0_lo, hmax ▸ hb0_hi, Or.inr ⟨hmax ▸ rfl, hb1 ▸ rfl⟩⟩
    obtain ⟨hγ_lo, hγ_hi, hslots⟩ := hslots_and_bds; have hθ1_nn : 0 ≤ halfAngleSet n 1 :=
      Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); have hγ0 : 0 ≤ γ := hθ1_nn.trans hγ_lo; obtain ⟨_,
      _, hw0_pos, _, _, _, -, -⟩ := cswapSymAngle_bounds hn hγ0 hγ_hi
    set γ_sym := cswapSymAngle n γ; set θ₂ := halfAngleSet n 2; set K := ⌈(π / 4 - γ_sym) / (2 *
      θ₂)⌉₊; set β_end := γ_sym + 2 * (K : ℝ) * θ₂; set α := lockedAlpha β_end θ₂; set cCold :=
      ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / 2); obtain ⟨hβ_ge_2θ, hβ_lt_pi2,
      hreal_cost⟩ := cswapWarmR1_real_cost_le hn hγ_lo hγ_hi
    -- Step 1: Apply `cswapFilterUnitary n` (`0` oracle cost)
    let Ucswap := (oracleReg n 2 k).embedUnitary (cswapFilterUnitary n)
    have hAN : A.card < 2 ^ n := (by rw [hA1]; exact Nat.one_lt_two_pow (by omega))
    let ψ_in := prodSlotState n 2 k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
    have hψ_in : star ψ_in ⬝ᵥ ψ_in = 1 := dotProduct_prodSlotState fun i ↦ dotProduct_slotPairVec
      (dotProduct_planeVec (by omega) hAN _) (dotProduct_single_one 0); set Δu := (interp
      ((OracleDynamicCircuit.step (phaseI Ucswap)).compile QProg.qAssign oracleS)).toStateFun Δ
    have hΔu_eq : Δu = CQState.qAssign Ucswap Δ := by
      dsimp only [Δu]; rw [OracleDynamicCircuit.compile_step, interp_qAssign]
      exact cqState_qAssign_phaseI Ucswap Δ
    obtain ⟨hPu, htr_u⟩ := pureStateAt_qAssign Ucswap hψ_in hΔ; rw [← hΔu_eq] at hPu htr_u
    let ψ_u := Ucswap.1 *ᵥ ψ_in
    have hψ_u : star ψ_u ⬝ᵥ ψ_u = 1 := dotProduct_unitary_mulVec Ucswap hψ_in
    -- Step 2: Measure `allMarkersReg n 2 k` (`0` oracle cost)
    let sgn : ℂ := if planeVec A (betas s0) = planeVec A (halfAngleSet n 1) ∧ planeVec A (betas s1)
      = planeVec A γ then 1 else -1
    let w : Fin (2 ^ 2) → ℝ := fun o ↦ if o = 0 then cswapSymWeight n γ else if o = ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then Real.sin (γ - halfAngleSet n 1) ^ 2 / 2 else if
      o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then 1 / (2 ^ n : ℝ) else 0
    have hw_nn (o : Fin (2 ^ 2)) : 0 ≤ w o := by
      dsimp only [w]; split_ifs
      · exact hw0_pos.le
      · positivity
      · positivity
      · exact le_rfl
    have hw_sum : ∑ o : Fin (2 ^ 2), w o = 1 := by
      have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 <
        2 ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 <
        2 ^ 2)⟩} := (by ext x; fin_cases x <;> simp); rw [huniv4, Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
      dsimp only [w]
      simp only [↓reduceIte,
        show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
          (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
        show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
          (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
        show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
          (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp]; rw [cswapSymWeight_eq hn1 γ]; ring
    let ψ_out : Fin (2 ^ 2) → Fin (2 ^ findAllQubits n 2 k) → ℂ := fun o ↦ if o = 0 then (oracleReg
      n 2 k).tensorState ((localAddrReg n 2).tensorState (offDiagPlaneVec n A γ_sym) (Pi.single 0
      1)) env0 else if o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then (oracleReg n 2
      k).tensorState ((localAddrReg n 2).tensorState (sgn • signedOddVec n A true) (Pi.single
      (envOfMask n ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) 1)) env0 else if o = ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then (oracleReg n 2 k).tensorState ((localAddrReg n
      2).tensorState (diagNormVec n A γ) (Pi.single (envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2
      < 2 ^ 2)⟩) 1)) env0 else ψ_in
    have hψ_out (o : Fin (2 ^ 2)) : star (ψ_out o) ⬝ᵥ ψ_out o = 1 := by
      dsimp only [ψ_out]; by_cases h0 : o = 0
      · rw [ite_eq_left h0, dotProduct_tensorState, dotProduct_tensorState,
          dotProduct_offDiagPlaneVec hn2 hA1 γ_sym, dotProduct_env_single, dotProduct_env_single,
          mul_one, mul_one]
      · rw [ite_eq_right h0]; by_cases h1 : o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
        · rw [ite_eq_left h1, dotProduct_tensorState, dotProduct_tensorState, dotProduct_env_single,
            dotProduct_env_single, mul_one, mul_one]
          have hodd := dotProduct_signedOddVec hn2 hA1 true; dsimp only [sgn]
          split_ifs <;> simp [hodd]
        · rw [ite_eq_right h1]; by_cases h2 : o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩
          · rw [ite_eq_left h2, dotProduct_tensorState, dotProduct_tensorState,
              dotProduct_diagNormVec hn1 hA1 γ, dotProduct_env_single, dotProduct_env_single,
              mul_one, mul_one]
          · rw [ite_eq_right h2]; exact hψ_in
    have hproj (o : Fin (2 ^ 2)) : (allMarkersReg n 2 k).basisOutcomeProjector o *ᵥ ψ_u = ((√(w o) :
      ℝ) : ℂ) • ψ_out o := by
      have hslot_fn : (fun i : Fin 2 ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)) =
        ![slotPairVec (planeVec A (betas s0)) (Pi.single 0 1), slotPairVec (planeVec A (betas s1))
        (Pi.single 0 1)] := (by funext i; fin_cases i <;> rfl)
      have hψu_eq : ψ_u = (oracleReg n 2 k).tensorState ((cswapFilterUnitary n).1 *ᵥ
        prodSlotLocalVec ![slotPairVec (planeVec A (betas s0)) (Pi.single 0 1), slotPairVec
        (planeVec A (betas s1)) (Pi.single 0 1)]) env0 := by
        dsimp only [ψ_u, Ucswap, ψ_in, prodSlotState]; rw [hslot_fn, QRegister.embedUnitary_val,
          (oracleReg n 2 k).embedMatrix_mulVec_tensorState]
      rw [hψu_eq, cswapFilter_twoSlot_outcomes hn hA1 hγ_lo hγ_hi hslots,
        basisOutcomeProjector_allMarkers_oracle_tensorState]
      have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
        (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩
        := (by fin_cases o <;> simp); rcases ho_cases with rfl | rfl | rfl | rfl
      · simp only [↓reduceIte, w, ψ_out, envOfMask_zero]; rw [(localAddrReg n
          2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
      · simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte, w, ψ_out]
        rw [(localAddrReg n 2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
      · simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte, w, ψ_out]
        rw [(localAddrReg n 2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
      · simp only [show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
          show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
            (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp, ↓reduceIte, w,
          Real.sqrt_zero, Complex.ofReal_zero, zero_smul]; funext z; simp [QRegister.tensorState]
    set Δm := (interp (QProg.measureRegister res (allMarkersReg n 2 k))).toStateFun Δu
    have hmeas := measure_sliceState_of_pureStateAt res (allMarkersReg n 2 k) hψ_u w hw_nn ψ_out
      hψ_out hproj hPu
    -- Step 3: Dispatch on `o`
    let branchCirc (o : Fin (2 ^ 2)) := if o = 0 then OracleDynamicCircuit.seq (offDiagPrepRec n k
      hn1 T K) (offDiagLockedLoopCircuit res n k hn1 T β_end) else if o = ⟨1, (Nat.lt_of_sub_eq_succ
      rfl : 1 < 2 ^ 2)⟩ then .seq (.step (phaseI ((oracleReg n 2 k).embedUnitary (permutationUnitary
      (flipFlag0Perm n))))) (extractOddPairStage1Circuit res n k T) else if o = ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then .seq (resetRegCircuit res (oracleReg n 2 k))
      (lockSingleFromSetCircuit res n 2 k T) else .skip
    let branchVal (o : Fin (2 ^ 2)) : ℝ := if o = 0 then (K : ℝ) + ((1 - α ^ 2)⁻¹ + 1) else if o =
      ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then 1 else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl
      : 2 < 2 ^ 2)⟩ then cCold else 0
    have h1mq_pos : 0 < 1 - α ^ 2 := by
      have hθ2_pos : 0 < θ₂ := Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos (by norm_num)
        (by positivity))); obtain ⟨_, _, _, hsq⟩ := lockedRatio_bounds hθ2_pos hβ_ge_2θ hβ_lt_pi2;
        linarith
    have hcCold_nn : 0 ≤ cCold :=
      (by dsimp only [cCold]; have : 0 ≤ π / 4 := (by linarith [Real.pi_pos]); positivity)
    have hbranchVal_nn (o : Fin (2 ^ 2)) : 0 ≤ branchVal o := by
      dsimp only [branchVal]; split_ifs
      · positivity
      · norm_num
      · exact hcCold_nn
      · exact le_rfl
    have hbranch (o : Fin (2 ^ 2)) :
        let fo := (branchCirc o).compile QProg.qAssign oracleS
        let Ξ_o := sliceState res 0 2 o.val Δm
        𝔼[(interp fo).toStateFun Ξ_o, Post] = w o * Δ.trace ∧
          expectedCost modelS fo Ξ_o ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w o * branchVal o) := by
      intro fo Ξ_o; obtain ⟨hPo, htro⟩ := hmeas o; rw [htr_u] at htro
      have hmass_o : (Ξ_o.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w o) := by
        nth_rw 1 [← ENNReal.ofReal_coe_nnreal]
        rw [htro, mul_comm (w o), ENNReal.ofReal_mul Δ.trace.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
        (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩
        := (by fin_cases o <;> simp); rcases ho_cases with rfl | rfl | rfl | rfl
      · -- `o = 0`: `offDiagPrepRec` + `offDiagLockedLoopCircuit`
        dsimp only [ψ_out] at hPo; simp only [↓reduceIte] at hPo; obtain ⟨hP_prep, htr_prep,
          hcost_prep⟩ := offDiagPrepRec_pureStateAt hn2 hTS hA1 K γ_sym hPo; set Ξ_prep := (interp
          ((offDiagPrepRec n k hn1 T K).compile QProg.qAssign oracleS)).toStateFun Ξ_o
        obtain ⟨hexp_loop, hcost_loop⟩ := offDiagLockedLoop_transition res hn2 hScard hTS hA1
          hβ_ge_2θ hβ_lt_pi2 hP_prep
        have hmass_prep : (Ξ_prep.trace : ℝ≥0∞) = (Ξ_o.trace : ℝ≥0∞) :=
          congrArg ENNReal.ofNNReal htr_prep
        rw [hmass_prep] at hcost_loop; refine ⟨?_, ?_⟩
        · dsimp only [fo, branchCirc]; simp only [↓reduceIte, OracleDynamicCircuit.compile_seq,
            interp_qSeq, QMonad.Q.toStateFun_bind]; rw [hexp_loop, htr_prep, htro]
        · dsimp only [fo, branchCirc, branchVal]; simp only [↓reduceIte,
            OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
          calc _ ≤ (Ξ_o.trace : ℝ≥0∞) * ENNReal.ofReal (K : ℝ) + (Ξ_o.trace : ℝ≥0∞) *
                ENNReal.ofReal ((1 - α ^ 2)⁻¹ + 1) := add_le_add hcost_prep hcost_loop
            _ = (Ξ_o.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + ((1 - α ^ 2)⁻¹ + 1)) := by
                rw [← mul_add, ← ENNReal.ofReal_add (Nat.cast_nonneg K) (by positivity)]
            _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w 0 * ((K : ℝ) + ((1 - α ^ 2)⁻¹ + 1))) := by
                rw [hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn 0)]
      · -- `o = 1`: `flipFlag0Perm` + `extractOddPairStage1Circuit`
        dsimp only [ψ_out] at hPo
        simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte] at hPo
        let Uf0 := (oracleReg n 2 k).embedUnitary (permutationUnitary (flipFlag0Perm n))
        set Ξ_f0 := (interp ((OracleDynamicCircuit.step (phaseI Uf0)).compile QProg.qAssign
          oracleS)).toStateFun Ξ_o
        have hΞ_f0_eq : Ξ_f0 = CQState.qAssign Uf0 Ξ_o := by
          dsimp only [Ξ_f0]; rw [OracleDynamicCircuit.compile_step, interp_qAssign]
          exact cqState_qAssign_phaseI Uf0 Ξ_o
        have hψ1_norm := hψ_out ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
        dsimp only [ψ_out] at hψ1_norm
        simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte] at hψ1_norm; obtain ⟨hPf0, htr_f0⟩ := pureStateAt_qAssign Uf0 hψ1_norm hPo
        rw [← hΞ_f0_eq] at hPf0 htr_f0
        have hf0_vec : Uf0.1 *ᵥ ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState (sgn
          • signedOddVec n A true) (Pi.single (envOfMask n ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^
          2)⟩) 1)) env0) = sgn • (oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState
          (signedOddVec n A true) (Pi.single 0 1)) env0 := by
          dsimp only [Uf0]; rw [QRegister.embedUnitary_val, (oracleReg n 2
            k).embedMatrix_mulVec_tensorState, flipFlag0Perm_mulVec_one, (localAddrReg n
            2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
        rw [hf0_vec] at hPf0
        have hPf0_clean : PureStateAt ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState
          (signedOddVec n A true) (Pi.single 0 1)) env0) Ξ_f0 := by
          dsimp only [sgn] at hPf0; split_ifs at hPf0 with hs
          · simpa using hPf0
          · rw [neg_one_smul] at hPf0; exact pureStateAt_neg.1 hPf0
        obtain ⟨hexp_ext, hcost_ext⟩ := extractOddPairStage1_transition res hn2 hScard hTS hA1 true
          hPf0_clean; have hmass_f0 : (Ξ_f0.trace : ℝ≥0∞) = (Ξ_o.trace : ℝ≥0∞) :=
          congrArg ENNReal.ofNNReal htr_f0
        rw [hmass_f0] at hcost_ext; refine ⟨?_, ?_⟩
        · dsimp only [fo, branchCirc]
          simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            ↓reduceIte,
            OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
          rw [hexp_ext, htr_f0, htro]
        · dsimp only [fo, branchCirc, branchVal]
          simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            ↓reduceIte,
            OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
            expectedCost_qSeq, expectedCost_qAssign]
          have hc0 := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacleS
            (isRealMatrix_embedUnitary (oracleReg n 2 k) (isRealMatrix_permutationUnitary
            (flipFlag0Perm n))); have hstep0 : (Ξ_o.trace : ℝ≥0∞) * ↑(modelS.unitaryCost
            (phaseI Uf0)) = 0 := (by dsimp [Uf0]; rw [hc0]; simp); rw [hstep0, zero_add]
          calc _ ≤ (Ξ_o.trace : ℝ≥0∞) * ENNReal.ofReal 1 := hcost_ext
            _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w ⟨1,
              (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ * 1) := by
                rw [hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn ⟨1, (Nat.lt_of_sub_eq_succ rfl :
                  1 < 2 ^ 2)⟩)]
      · -- `o = 2`: `resetRegCircuit` + `lockSingleFromSetCircuit`
        dsimp only [ψ_out] at hPo
        simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte] at hPo
        let v_diag := (localAddrReg n 2).tensorState (diagNormVec n A γ)
          (Pi.single (envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) 1)
        have hv_diag : star v_diag ⬝ᵥ v_diag = 1 := by
          dsimp only [v_diag]; rw [dotProduct_tensorState, dotProduct_diagNormVec hn1 hA1 γ,
            dotProduct_env_single, mul_one]
        have hϕ0 : star ((oracleReg n 2 k).tensorState (Pi.single 0 1) env0) ⬝ᵥ (oracleReg n 2
          k).tensorState (Pi.single 0 1) env0 = 1 :=
          (by rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_env_single, mul_one])
        obtain ⟨hPrst, htr_rst⟩ := resetRegCircuit_pureStateAt oracleS res (oracleReg n 2 k) hv_diag
          hϕ0 hPo; set Ξ_rst := (interp ((resetRegCircuit res (oracleReg n 2 k)).compile
          QProg.qAssign oracleS)).toStateFun Ξ_o
        have hPrst0 : PureStateAt (Pi.single 0 1) Ξ_rst := by
          have hz_eq : (oracleReg n 2 k).tensorState (Pi.single 0 1) env0 = Pi.single 0 1 :=
            (by rw [← prodSlotLocalVec_single_zero n 2]; exact prodSlotState_single_zero n 2 k)
          rwa [hz_eq] at hPrst
        have hsupp0 := supportedOn_of_pureStateAt
          (pred := (· = (0 : Fin (2 ^ findAllQubits n 2 k))))
          (fun z hz ↦ Pi.single_eq_of_ne hz 1) hPrst0
        obtain ⟨hexp_b, hcost_b⟩ := lockSingleFromSet_transition res hn (by omega) (by omega)
          hk1024 hScard hTS hrem1 hsupp0; have hmass_rst : (Ξ_rst.trace : ℝ≥0∞) = (Ξ_o.trace :
          ℝ≥0∞) := congrArg ENNReal.ofNNReal htr_rst; refine ⟨?_, ?_⟩
        · dsimp only [fo, branchCirc]
          simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
              (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte,
            OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
          rw [hexp_b, htr_rst, htro]
        · dsimp only [fo, branchCirc, branchVal]
          simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
              (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte,
            OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
          rw [expectedCost_resetRegCircuit_eq_zero res _ horacleS, zero_add]
          calc _ ≤ (Ξ_rst.trace : ℝ≥0∞) * ENNReal.ofReal cCold := hcost_b
            _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w ⟨2,
              (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ * cCold) := by
                rw [hmass_rst, hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn ⟨2,
                  (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩)]
      · -- `o = 3`: `.skip` (`w 3 = 0`)
        have htr0 : Ξ_o.trace = 0 := NNReal.coe_inj.mp (by push_cast; simpa [w] using htro)
        refine ⟨?_, ?_⟩
        · dsimp only [fo, branchCirc]
          simp only [show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
              (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
            show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
              (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp, ↓reduceIte,
            OracleDynamicCircuit.compile_skip, interp_skip, QMonad.Q.toStateFun_pure, w, zero_mul]
          exact expect_eq_zero_of_trace_eq_zero htr0 Post
        · dsimp only [fo, branchCirc, branchVal]; simp [w]
    -- Step 4: Assemble `prog` expectation and cost
    have hprog_unfold : prog = ((OracleDynamicCircuit.step (phaseI Ucswap)).compile QProg.qAssign
      oracleS ;; (QProg.measureRegister res (allMarkersReg n 2 k) ;; (dispBits res 2 0 fun oVal ↦
      branchCirc ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile QProg.qAssign oracleS)) := by
      dsimp [prog, cswapWarmR1Circuit, Ucswap, branchCirc, γ, γ_sym, θ₂, K, β_end]
      rw [dite_eq_left hc, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_measure]; rfl
    rw [hprog_unfold]; have hcost_eq : cswapWarmR1Cost1 n betas = cswapR1CostUpper n γ :=
      (by dsimp only [cswapWarmR1Cost1, γ]; exact ite_eq_left hg); rw [hcost_eq]; refine ⟨?_, ?_⟩
    · rw [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSeq, QMonad.Q.toStateFun_bind,
        expect_dispBits, ← Fin.sum_univ_eq_sum_range]
      have hsum_eq :
          (∑ o : Fin (2 ^ 2),
            𝔼[(interp ((branchCirc ⟨o.val % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile
                QProg.qAssign oracleS)).toStateFun (sliceState res 0 2 o.val Δm), Post]) =
          ∑ o : Fin (2 ^ 2), w o * Δ.trace :=
        Finset.sum_congr rfl fun o _ ↦ by simpa only [fin_mk_mod_pow] using (hbranch o).1
      rw [hsum_eq, ← Finset.sum_mul, hw_sum, one_mul]
    · rw [expectedCost_qSeq, expectedCost_qSeq]
      have hc_u : expectedCost modelS ((OracleDynamicCircuit.step (phaseI Ucswap)).compile
        QProg.qAssign oracleS) Δ = 0 := by
        dsimp [Ucswap]; rw [ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacleS
          (isRealMatrix_embedUnitary (oracleReg n 2 k) (isRealMatrix_cswapFilterUnitary n))]; simp
      have hc_m : expectedCost modelS (QProg.measureRegister res (allMarkersReg n 2 k)) Δu = 0 :=
        (by simp [QProg.measureRegister, modelS]); rw [hc_u, zero_add, hc_m, zero_add,
        expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]
      calc _ ≤ ∑ o : Fin (2 ^ 2), (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w o * branchVal o) :=
              Finset.sum_le_sum fun o _ ↦ by simpa only [fin_mk_mod_pow] using (hbranch o).2
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (∑ o : Fin (2 ^ 2), w o * branchVal o) := by
            rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun o _ ↦ mul_nonneg (hw_nn o)
              (hbranchVal_nn o))]
        _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (cswapR1CostUpper n γ) := by
            refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
            have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl
              : 1 < 2 ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3,
              (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩} := (by ext x; fin_cases x <;> simp)
            rw [huniv4, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert
              (by simp), Finset.sum_singleton]; dsimp [w, branchVal, γ_sym, θ₂, K, β_end, α, cCold];
              simp only [mul_zero, add_zero]; linarith [hreal_cost]
  · -- Fallback outside `cswapWarmGuard`: reduces to `rawProjCheckStage1Circuit`
    have hnc : ¬ (cswapWarmGuard n betas ∧ 100 ≤ n) := fun h ↦ hg h.1; have hprog_eq : prog =
      (rawProjCheckStage1Circuit res n k (by omega) T).compile QProg.qAssign (parallelMarkingOracle
      2 S) := (by dsimp [prog, cswapWarmR1Circuit]; rw [dite_eq_right hnc])
    have hcost_eq : cswapWarmR1Cost1 n betas = PipeFuse.warmR1Cost1 n 2 betas :=
      (by dsimp only [cswapWarmR1Cost1]; exact ite_eq_right hg); rw [hprog_eq, hcost_eq]
    exact rawProjCheckStage1_transition res hn (by omega) (by omega) hk1024 hScard hTS hA1 hβ0 hβ_lt
      hΔ
theorem fuseNextAngle_two_five_div_four_le_four_div_five {n : ℕ} (hn : 100 ≤ n) : fuseNextAngle n 2
  (5 / 4) ≤ 4 / 5 := by
  set N : ℝ := (2 : ℝ) ^ n; have hN_cast : (2 ^ n : ℝ) = N := rfl; obtain ⟨_, hN_ge⟩ :=
    PipeFuse.pow_two_bounds_100 hn; have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge
  obtain ⟨_, _, hθ1_13, -⟩ := PipeFuse.halfAngleSet_bounds_100 hn (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 1024)
  obtain ⟨_, _, hθ2_13, -⟩ := PipeFuse.halfAngleSet_bounds_100 hn (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 1024)
  have hθ2_nn : 0 ≤ halfAngleSet n 2 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have h2N : 2 < 2 ^ n := by
    have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by positivity) (by omega) : 2 ^ 2 ≤ 2 ^ n); omega
  have hlam_sq : fuseLamFin n 2 ^ 2 ≤ 501 / 1000 := by
    rw [fuseLamFin_sq (by omega : 2 ≤ 2) h2N, hN_cast]; have hden_pos : (0 : ℝ) < (2 : ℕ) * (N - (2
      : ℕ)) := (by push_cast; linarith); rw [div_le_iff₀ hden_pos]; push_cast; linarith [hN_ge]
  have hcos_54 : (7 : ℝ) / 32 ≤ Real.cos (5 / 4) := by
    have hs_nn : 0 ≤ Real.sin ((5 : ℝ) / 8) := Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
      (by linarith [Real.pi_gt_three]); have hs_le : Real.sin ((5 : ℝ) / 8) ≤ (5 : ℝ) / 8 :=
      Real.sin_le (by norm_num)
    have hcos_2 : Real.cos ((5 : ℝ) / 4) = 1 - 2 * Real.sin ((5 : ℝ) / 8) ^ 2 := by
      rw [show ((5 : ℝ) / 4) = 2 * ((5 : ℝ) / 8) by norm_num, Real.cos_two_mul]
      linarith [Real.sin_sq_add_cos_sq ((5 : ℝ) / 8)]
    nlinarith
  have hsin_54_sq : Real.sin (5 / 4) ^ 2 ≤ 975 / 1024 :=
    (by have hsc := Real.sin_sq_add_cos_sq (5 / 4); nlinarith); have h54_lt : (5 / 4 : ℝ) < π / 2 :=
    (PipeFuse.tan_five_div_four_le_five).2
  have hsin_sub_le : Real.sin (5 / 4 - halfAngleSet n 2) ≤ Real.sin (5 / 4) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three]) h54_lt.le (by linarith)
  have hsin_sub_nn : 0 ≤ Real.sin (5 / 4 - halfAngleSet n 2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_three]); obtain ⟨hlam_pos, _⟩ :=
    fuseLamFin_pos_and_lt_one (by omega : 2 ≤ 2) (PipeFuse.two_mul_le_pow_100 hn (by omega))
  have hprod_sq : (fuseLamFin n 2 * Real.sin (5 / 4 - halfAngleSet n 2)) ^ 2 ≤ 1 / 2 := by
    rw [mul_pow]; have hs2 : Real.sin (5 / 4 - halfAngleSet n 2) ^ 2 ≤ 975 / 1024 :=
      (pow_le_pow_left₀ hsin_sub_nn hsin_sub_le 2).trans hsin_54_sq
    calc fuseLamFin n 2 ^ 2 * Real.sin (5 / 4 - halfAngleSet n 2) ^ 2 ≤ (501 / 1000) * (975 / 1024)
          := mul_le_mul hlam_sq hs2 (sq_nonneg _) (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have hprod_le_sin : fuseLamFin n 2 * Real.sin (5 / 4 - halfAngleSet n 2) ≤ Real.sin (π / 4) := by
    rw [Real.sin_pi_div_four]
    refine PipeFuse.sq_le_imp_le (mul_nonneg hlam_pos.le hsin_sub_nn) (by positivity) ?_
    rw [div_pow, Real.sq_sqrt (by norm_num)]; linarith
  have harc_le : Real.arcsin (fuseLamFin n 2 * Real.sin (5 / 4 - halfAngleSet n 2)) ≤ π / 4 := by
    have h := Real.arcsin_le_arcsin hprod_le_sin
    rwa [Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])] at h
  dsimp only [fuseNextAngle]; change halfAngleSet n 1 + Real.arcsin (fuseLamFin n 2 * Real.sin (5 /
    4 - halfAngleSet n 2)) ≤ _; linarith [hθ1_13, harc_le, Real.pi_lt_d4]
theorem cswapWarmGuard_nextStageFuseBetas {n : ℕ} (hn : 100 ≤ n)
    {postBetas : Fin 2 → ℝ} (hpost : ValidStageBetas n 2 (5 / 4) postBetas) :
    (cswapWarmGuard n (nextStageFuseBetas n 2 ⟨1, by decide⟩ postBetas) ∧
      max (nextStageFuseBetas n 2 ⟨1, by decide⟩ postBetas s0)
        (nextStageFuseBetas n 2 ⟨1, by decide⟩ postBetas s1) =
          fuseNextAngle n 2 (postBetas s1)) ∧
    (cswapWarmGuard n (nextStageFuseBetas n 2 ⟨2, by decide⟩ postBetas) ∧
      max (nextStageFuseBetas n 2 ⟨2, by decide⟩ postBetas s0)
        (nextStageFuseBetas n 2 ⟨2, by decide⟩ postBetas s1) =
          fuseNextAngle n 2 (postBetas s0)) ∧
    (cswapWarmGuard n (nextStageFuseBetas n 2 ⟨3, by decide⟩ postBetas) ∧
      max (nextStageFuseBetas n 2 ⟨3, by decide⟩ postBetas s0)
        (nextStageFuseBetas n 2 ⟨3, by decide⟩ postBetas s1) =
          halfAngleSet n 1) := by
  have h2r : 2 * 2 ≤ 2 ^ n := PipeFuse.two_mul_le_pow_100 hn (by omega); have h54_lt : (5 / 4 : ℝ) <
    π / 2 := (PipeFuse.tan_five_div_four_le_five).2; have hf_hi :=
    fuseNextAngle_two_five_div_four_le_four_div_five hn; obtain ⟨_, _, hθ1_13, -⟩ :=
    PipeFuse.halfAngleSet_bounds_100 hn (by omega : 1 ≤ 1) (by omega : 1 ≤ 1024); have hf_bds (i :
    Fin 2) : halfAngleSet n 1 ≤ fuseNextAngle n 2 (postBetas i) ∧ fuseNextAngle n 2 (postBetas i) ≤
    4 / 5 := ⟨halfAngleSet_le_fuseNextAngle (by omega) h2r (hpost i).1 ((hpost i).2.trans
    h54_lt.le), (fuseNextAngle_mono (by omega) h2r (hpost i).1 (hpost i).2 h54_lt.le).trans hf_hi⟩
  refine ⟨?_, ?_, ?_⟩
  · have hb0 : nextStageFuseBetas n 2 ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas s0 =
      halfAngleSet n 1 := by
      dsimp only [nextStageFuseBetas, s0]; rw [show (1 : ℕ).testBit (0 : Fin 2).val = true from rfl]
      simp
    have hb1 : nextStageFuseBetas n 2 ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas s1 =
      fuseNextAngle n 2 (postBetas s1) := by
      dsimp only [nextStageFuseBetas, s1]; rw [show (1 : ℕ).testBit (1 : Fin 2).val = false from
        rfl]; simp
    exact ⟨Or.inl ⟨hb0, hb1 ▸ (hf_bds s1).1, hb1 ▸ (hf_bds s1).2⟩,
      by rw [hb0, hb1]; exact max_eq_right (hf_bds s1).1⟩
  · have hb0 : nextStageFuseBetas n 2 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas s0 =
      fuseNextAngle n 2 (postBetas s0) := by
      dsimp only [nextStageFuseBetas, s0]; rw [show (2 : ℕ).testBit (0 : Fin 2).val = false from
        rfl]; simp
    have hb1 : nextStageFuseBetas n 2 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas s1 =
      halfAngleSet n 1 := by
      dsimp only [nextStageFuseBetas, s1]; rw [show (2 : ℕ).testBit (1 : Fin 2).val = true from rfl]
      simp
    exact ⟨Or.inr ⟨hb1, hb0 ▸ (hf_bds s0).1, hb0 ▸ (hf_bds s0).2⟩,
      by rw [hb0, hb1]; exact max_eq_left (hf_bds s0).1⟩
  · have hb0 : nextStageFuseBetas n 2 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postBetas s0 =
      halfAngleSet n 1 := by
      dsimp only [nextStageFuseBetas, s0]; rw [show (3 : ℕ).testBit (0 : Fin 2).val = true from rfl]
      simp
    have hb1 : nextStageFuseBetas n 2 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postBetas s1 =
      halfAngleSet n 1 := by
      dsimp only [nextStageFuseBetas, s1]; rw [show (3 : ℕ).testBit (1 : Fin 2).val = true from rfl]
      simp
    exact ⟨Or.inl ⟨hb0, hb1 ▸ le_rfl, hb1 ▸ by linarith⟩, by rw [hb0, hb1, max_self]⟩
/-! ## 8. Multi-Stage `m = 2` Coherent Peer-Fusion Harvester with Terminal CSWAP Warm Readout -/
/-- Bellman potential specification for `m = 2` coherent peer fusion terminating in
  `cswapWarmR1Circuit` at `r = 1`. -/
structure ValidCswapWarmM2Potential (phiFn ubFn : ℕ → ℝ) (n k : ℕ)
    (Φ : ℕ → (Fin 2 → ℝ) → ℝ) : Prop where
  nonneg : ∀ r, 1 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas → 0 ≤ Φ r betas
  phi_lb : ∀ r, 2 ≤ r → r ≤ k → 2 * halfAngleSet n r ≤ phiFn r
  ub_lb : ∀ r, 1 ≤ r → r ≤ k →
    (if r = 1 then halfAngleSet n 1 else phiFn r + 2 * halfAngleSet n r) ≤ ubFn r
  ub_lt : ∀ r, 1 ≤ r → r ≤ k → ubFn r < π / 2
  ub_fuse : ∀ r, 2 ≤ r → r ≤ k → fuseNextAngle n r (ubFn r) ≤ ubFn (r - 1)
  base1_le : 1 ≤ k → ∀ betas, ValidStageBetas n 1 (ubFn 1) betas →
    cswapWarmR1Cost1 n betas ≤ Φ 1 betas
  step_le : ∀ r, 2 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas →
    1 + stepWeight n r (phiFn r) betas 0 * Φ r (nextBetasRamp n r (phiFn r) betas) +
      (∑ o ∈ Finset.univ.erase 0,
        stepWeight n r (phiFn r) betas o *
          expOnHitFuse Φ n r o (nextBetasRamp n r (phiFn r) betas)) ≤
      Φ r betas
/-- Stage-by-stage `m = 2` coherent peer-fusion harvester (`r ≥ 2`) terminating in
  `cswapWarmR1Circuit` at `rem = 0` (`r = 1`). -/
noncomputable def cswapWarmM2StageRec {Var : Type} (res : Var) (phiFn : ℕ → ℝ) (n k : ℕ) :
    ℕ → Finset (Fin (2 ^ n)) → (Fin 2 → ℝ) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
        (findAllQubits n 2 k) ((n + 1) * 2)
  | 0, T, betas =>
      cswapWarmR1Circuit res n k T betas
  | rem + 1, T, betas =>
      let r := rem + 2
      stageRampRec res n k T r (phiFn r)
        (fun postBetas o ↦
          onHitFuseCircuit res n k (by decide) r o postBetas fun xStar ↦
            cswapWarmM2StageRec res phiFn n k rem (insert xStar T)
              (nextStageFuseBetas n r o postBetas))
        (maxRemSteps n r (phiFn r) betas) betas
theorem cswapWarmM2StageRec_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn :
  100 ≤ n) (hk1024 : k ≤ 1024) {phiFn ubFn : ℕ → ℝ} {Φ : ℕ → (Fin 2 → ℝ) → ℝ} (hΦ :
  ValidCswapWarmM2Potential phiFn ubFn n k Φ) {S : Finset (Fin (2 ^ n))} (hScard : S.card = k) : ∀
  rem : ℕ, rem + 1 ≤ k → ∀ T : Finset (Fin (2 ^ n)), T ⊆ S → (S \ T).card = rem + 1 → ∀ betas : Fin
  2 → ℝ, ValidStageBetas n (rem + 1) (ubFn (rem + 1)) betas → ∀ Δ : CQState (Store Var) (2 ^
    findAllQubits n
  2 k), PureStateAt (prodSlotState n 2 k fun i ↦ slotPairVec (planeVec (S \ T) (betas i)) (Pi.single
  0 1)) Δ →
        let prog := (cswapWarmM2StageRec res phiFn n k rem T betas).compile QProg.qAssign
          (parallelMarkingOracle 2 S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (Φ (rem + 1) betas) := by
  have h2k : 2 * k ≤ 2 ^ n := PipeFuse.two_mul_le_pow_100 hn hk1024; intro rem
  induction rem with
  | zero =>
    intro h1k T hTS hAr betas hbetas Δ hΔ
    have hθ0 : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
    have hβ0 : ∀ i : Fin 2, 0 ≤ betas i := fun i ↦ hθ0.trans (hbetas i).1; have hβ_lt : ∀ i : Fin 2,
      betas i < π / 2 := fun i ↦ lt_of_le_of_lt (hbetas i).2 (hΦ.ub_lt 1 le_rfl h1k); obtain ⟨hexp,
      hcost⟩ := cswapWarmR1_transition res hn hk1024 hScard hTS hAr hβ0 hβ_lt hΔ; refine ⟨hexp,
      hcost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hΦ.base1_le h1k betas
      hbetas)) zero_le)⟩
  | succ rem ih =>
    intro hrk T hTS hAr betas hbetas Δ hΔ; set r := rem + 2; have hr2 : 2 ≤ r := (by omega)
    have hr1 : 1 ≤ r := (by omega); have h2r : 2 * r ≤ 2 ^ n := (by omega); have hrN : r < 2 ^ n :=
      (by omega); have hprev1 : 1 ≤ r - 1 := (by omega); have hprev_k : r - 1 ≤ k := (by omega)
    have hθ_prev : halfAngleSet n (r - 1) ≤ ubFn (r - 1) := by
      have hub := hΦ.ub_lb (r - 1) hprev1 hprev_k; by_cases hp1 : r - 1 = 1
      · simpa [hp1] using hub
      · have hp2 : 2 ≤ r - 1 := (by omega); have h1 := hΦ.phi_lb (r - 1) hp2 hprev_k; have h0 : 0 ≤
          halfAngleSet n (r - 1) := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); simp only [hp1,
          ↓reduceIte] at hub; linarith
    have hr_ne1 : r ≠ 1 := (by omega); have hub_r : phiFn r + 2 * halfAngleSet n r ≤ ubFn r :=
      (by simpa [hr_ne1] using hΦ.ub_lb r hr1 hrk)
    have hH_nn : ∀ postBetas, ValidStageBetas n r (ubFn r) postBetas → ∀ o : Fin (2 ^ 2), o ≠ 0 → 0
      ≤ expOnHitFuse Φ n r o postBetas := by
      intro postBetas hpost o _; simp only [expOnHitFuse, hr2, ↓reduceIte]
      exact hΦ.nonneg (r - 1) hprev1 hprev_k _ (validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt
        r hr1 hrk) (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost)
    exact stageRampRec_transition res (by omega) hTS hAr hr1 hrN
      (hΦ.phi_lb r hr2 hrk) hub_r (hΦ.ub_lt r hr1 hrk)
      (Φ r) (hΦ.nonneg r hr1 hrk)
      (fun postBetas o ↦ expOnHitFuse Φ n r o postBetas) hH_nn
      (hΦ.step_le r hr2 hrk)
      (fun postBetas o ↦
        onHitFuseCircuit res n k (by omega) r o postBetas fun xStar ↦
          cswapWarmM2StageRec res phiFn n k rem (insert xStar T)
            (nextStageFuseBetas n r o postBetas))
      (fun postBetas hpost o ho Ξ hΞ ↦
        onHitFuseCircuit_transition res (by omega) hTS hAr hr2 h2r (hΦ.ub_lt r hr1 hrk) hpost
          ho Φ
          (hΦ.nonneg (r - 1) hprev1 hprev_k _
            (validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr1 hrk)
              (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost))
          _
          (fun xStar hxStar Υ hΥ ↦ by
            have hT'_sub : insert xStar T ⊆ S := Finset.insert_subset (Finset.mem_sdiff.1 hxStar).1
              hTS
            have hcard_T' : (S \ insert xStar T).card = rem + 1 := by
              have hsdiff_eq : S \ insert xStar T = (S \ T) \ {xStar} := by
                ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
              rw [hsdiff_eq, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hxStar),
                Finset.card_singleton, hAr]; omega
            have hvalid_next : ValidStageBetas n (rem + 1) (ubFn (rem + 1)) (nextStageFuseBetas n r
              o postBetas) := validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr1 hrk)
              (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost
            exact ih hprev_k (insert xStar T) hT'_sub hcard_T' _ hvalid_next Υ hΥ)
          hΞ)
      (maxRemSteps n r (phiFn r) betas) betas hbetas le_rfl Δ hΔ
/-- Top-level `m = 2` coherent peer-fusion `FindAll` circuit with terminal CSWAP warm
  readout. -/
noncomputable def cswapWarmM2FindAllCircuit {Var : Type} (res : Var)
    (phiFn : ℕ → ℝ) (n k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2) :=
  if k = 0 then
    writeFinsetCircuit res n 2 k ∅
  else
    .seq (prepSlotsListCircuit res n 2 k (fun _ ↦ true) (List.finRange 2))
      (cswapWarmM2StageRec res phiFn n k (k - 1) ∅ (fun _ ↦ halfAngleSet n k))
theorem cswapWarmM2FindAllProgram_correctness_and_costBound {Var : Type} [DecidableEq Var] {n k : ℕ}
  (res : Var) (hn : 100 ≤ n) (hk1 : 1 ≤ k) (hk1024 : k ≤ 1024) {phiFn ubFn : ℕ → ℝ} {Φ : ℕ → (Fin 2
  → ℝ) → ℝ} (hΦ : ValidCswapWarmM2Potential phiFn ubFn n k Φ) {S : Finset (Fin (2 ^ n))} (hScard :
  S.card = k) {B : ℝ≥0} (hB : Φ k (fun _ ↦ halfAngleSet n k) ≤ B) :
    let prog := QProg.qSet ;; (cswapWarmM2FindAllCircuit (Var := Var) res phiFn n k).compile
      QProg.qAssign (parallelMarkingOracle 2 S)
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n 2 k)) ⦄ prog ⦃ liftPureProp (fun σ ↦
      decodeTargetsLocal n k (σ res) = S) ⦄ ∧ CostBound (CostModel.ofEmbeddedOracle
      (parallelMarkingOracle 2 S)) prog B := by
  intro prog; have hk_ne0 : k ≠ 0 := (by omega); have hk_sub : k - 1 + 1 = k := (by omega)
  have h2k : 2 * k ≤ 2 ^ n := PipeFuse.two_mul_le_pow_100 hn hk1024; have hkN : k < 2 ^ n :=
    (by omega)
  let oracle := parallelMarkingOracle 2 S
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracle
  have horacle := isRealMatrix_parallelMarkingOracle (m := 2) S; have hS1 : 1 ≤ (S \ ∅).card :=
    (by simp [hScard, hk1]); have hSN : (S \ ∅).card < 2 ^ n := (by simp [hScard, hkN])
  have hvalid_init : ValidStageBetas n (k - 1 + 1) (ubFn (k - 1 + 1)) (fun _ : Fin 2 ↦ halfAngleSet
    n k) := by
    rw [hk_sub]; intro _; have hub := hΦ.ub_lb k hk1 le_rfl; by_cases hk_eq1 : k = 1
    · subst hk_eq1; exact ⟨le_rfl, by simpa using hub⟩
    · have hk2 : 2 ≤ k := (by omega)
      have h0 : 0 ≤ halfAngleSet n k := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); have h1 :=
        hΦ.phi_lb k hk2 le_rfl; simp only [hk_eq1, ↓reduceIte] at hub; exact ⟨le_rfl, by linarith⟩
  have hmain (Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)) : 𝔼[(interp prog).toStateFun Δ,
    liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S)] = Δ.trace ∧ expectedCost model prog Δ
    ≤ (Δ.trace : ℝ≥0∞) * B := by
    dsimp only [prog, cswapWarmM2FindAllCircuit]; simp only [hk_ne0, ↓reduceIte,
      OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet,
      QMonad.Q.toStateFun_qSet, expectedCost_qSeq]
    have hqset : expectedCost model QProg.qSet Δ = 0 := (by simp [model]); rw [hqset, zero_add,
      expectedCost_prepSlotsListCircuit_eq_zero res n 2 k _ _ horacle, zero_add]
    have hPqset : PureStateAt (prodSlotState n 2 k fun _ ↦ Pi.single 0 1) Δ.qSet :=
      (by rw [prodSlotState_single_zero]; exact pureStateAt_qSet Δ)
    obtain ⟨hPprep, htr_prep⟩ := prepSlotsListCircuit_pureStateAt oracle res (fun _ ↦ true)
      (List.finRange 2) (List.nodup_finRange 2) hS1 hSN (fun _ ↦ dotProduct_single_one 0) hPqset
    set Ξ_prep := (interp ((prepSlotsListCircuit res n 2 k (fun _ ↦ true) (List.finRange 2)).compile
      QProg.qAssign oracle)).toStateFun Δ.qSet
    have hPprep' : PureStateAt (prodSlotState n 2 k fun _ ↦ slotPairVec (planeVec (S \ ∅)
      (halfAngleSet n k)) (Pi.single 0 1)) Ξ_prep := by
      convert hPprep using 2
      funext _; simp [List.mem_finRange, hScard]
    obtain ⟨hexp, hcost⟩ := cswapWarmM2StageRec_transition res hn hk1024 hΦ hScard (k - 1)
      (by omega) ∅ (Finset.empty_subset S) (by simp [hScard]; omega) (fun _ : Fin 2 ↦ halfAngleSet n
      k) hvalid_init Ξ_prep hPprep'; refine ⟨?_, ?_⟩
    · rw [hexp, htr_prep, CQState.trace_qSet]
    · rw [hk_sub] at hcost; have hmass : (Ξ_prep.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal (htr_prep.trans (CQState.trace_qSet Δ))
      rw [hmass] at hcost; refine hcost.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hB
  refine ⟨fun Δ ↦ ?_, fun Δ ↦ (hmain Δ).2⟩; rw [expect_top, (hmain Δ).1]
theorem cswapWarmM2StageRec_rMax_transition {Var : Type} [DecidableEq Var] {n k rMax : ℕ} (res :
  Var) (hn : 100 ≤ n) (hk1024 : k ≤ 1024) (hrMax1024 : rMax ≤ 1024) {phiFn ubFn : ℕ → ℝ} {Φ : ℕ →
  (Fin 2 → ℝ) → ℝ} (hΦ : ValidCswapWarmM2Potential phiFn ubFn n rMax Φ) {S : Finset (Fin (2 ^ n))}
  (hScard : S.card = k) : ∀ rem : ℕ, rem + 1 ≤ rMax → ∀ T : Finset (Fin (2 ^ n)), T ⊆ S → (S \
  T).card = rem + 1 → ∀ betas : Fin 2 → ℝ, ValidStageBetas n (rem + 1) (ubFn (rem + 1)) betas → ∀ Δ
  : CQState (Store Var) (2 ^ findAllQubits n 2 k), PureStateAt (prodSlotState n 2 k fun i ↦
    slotPairVec
  (planeVec (S \ T) (betas i)) (Pi.single 0 1)) Δ →
        let prog := (cswapWarmM2StageRec res phiFn n k rem T betas).compile QProg.qAssign
          (parallelMarkingOracle 2 S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (Φ (rem + 1) betas) := by
  have h2k : 2 * rMax ≤ 2 ^ n := PipeFuse.two_mul_le_pow_100 hn hrMax1024; intro rem
  induction rem with
  | zero =>
    intro h1k T hTS hAr betas hbetas Δ hΔ
    have hθ0 : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
    have hβ0 : ∀ i : Fin 2, 0 ≤ betas i := fun i ↦ hθ0.trans (hbetas i).1; have hβ_lt : ∀ i : Fin 2,
      betas i < π / 2 := fun i ↦ lt_of_le_of_lt (hbetas i).2 (hΦ.ub_lt 1 le_rfl h1k); obtain ⟨hexp,
      hcost⟩ := cswapWarmR1_transition res hn hk1024 hScard hTS hAr hβ0 hβ_lt hΔ; refine ⟨hexp,
      hcost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hΦ.base1_le h1k betas
      hbetas)) zero_le)⟩
  | succ rem ih =>
    intro hrk T hTS hAr betas hbetas Δ hΔ; set r := rem + 2; have hr2 : 2 ≤ r := (by omega)
    have hr1 : 1 ≤ r := (by omega); have h2r : 2 * r ≤ 2 ^ n := (by omega); have hrN : r < 2 ^ n :=
      (by omega); have hprev1 : 1 ≤ r - 1 := (by omega); have hprev_k : r - 1 ≤ rMax := (by omega)
    have hθ_prev : halfAngleSet n (r - 1) ≤ ubFn (r - 1) := by
      have hub := hΦ.ub_lb (r - 1) hprev1 hprev_k; by_cases hp1 : r - 1 = 1
      · simpa [hp1] using hub
      · have hp2 : 2 ≤ r - 1 := (by omega); have h1 := hΦ.phi_lb (r - 1) hp2 hprev_k; have h0 : 0 ≤
          halfAngleSet n (r - 1) := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); simp only [hp1,
          ↓reduceIte] at hub; linarith
    have hr_ne1 : r ≠ 1 := (by omega); have hub_r : phiFn r + 2 * halfAngleSet n r ≤ ubFn r :=
      (by simpa [hr_ne1] using hΦ.ub_lb r hr1 hrk)
    have hH_nn : ∀ postBetas, ValidStageBetas n r (ubFn r) postBetas → ∀ o : Fin (2 ^ 2), o ≠ 0 → 0
      ≤ expOnHitFuse Φ n r o postBetas := by
      intro postBetas hpost o _; simp only [expOnHitFuse, hr2, ↓reduceIte]
      exact hΦ.nonneg (r - 1) hprev1 hprev_k _ (validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt
        r hr1 hrk) (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost)
    exact stageRampRec_transition res (by omega) hTS hAr hr1 hrN
      (hΦ.phi_lb r hr2 hrk) hub_r (hΦ.ub_lt r hr1 hrk)
      (Φ r) (hΦ.nonneg r hr1 hrk)
      (fun postBetas o ↦ expOnHitFuse Φ n r o postBetas) hH_nn
      (hΦ.step_le r hr2 hrk)
      (fun postBetas o ↦
        onHitFuseCircuit res n k (by omega) r o postBetas fun xStar ↦
          cswapWarmM2StageRec res phiFn n k rem (insert xStar T)
            (nextStageFuseBetas n r o postBetas))
      (fun postBetas hpost o ho Ξ hΞ ↦
        onHitFuseCircuit_transition res (by omega) hTS hAr hr2 h2r (hΦ.ub_lt r hr1 hrk) hpost
          ho Φ
          (hΦ.nonneg (r - 1) hprev1 hprev_k _
            (validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr1 hrk)
              (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost))
          _
          (fun xStar hxStar Υ hΥ ↦ by
            have hT'_sub : insert xStar T ⊆ S := Finset.insert_subset (Finset.mem_sdiff.1 hxStar).1
              hTS
            have hcard_T' : (S \ insert xStar T).card = rem + 1 := by
              have hsdiff_eq : S \ insert xStar T = (S \ T) \ {xStar} := by
                ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
              rw [hsdiff_eq, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hxStar),
                Finset.card_singleton, hAr]; omega
            have hvalid_next : ValidStageBetas n (rem + 1) (ubFn (rem + 1)) (nextStageFuseBetas n r
              o postBetas) := validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr1 hrk)
              (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost
            exact ih hprev_k (insert xStar T) hT'_sub hcard_T' _ hvalid_next Υ hΥ)
          hΞ)
      (maxRemSteps n r (phiFn r) betas) betas hbetas le_rfl Δ hΔ
end QuantumComputation.Specs.GroverFindAll.Warm2
