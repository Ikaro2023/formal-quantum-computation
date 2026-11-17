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
public import Mathlib.Data.Fintype.CardEmbedding
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.WeakDickeCore
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingZoomK2Base
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomEval
/-
# Middle-`p` Collision-Zoom Bounds, Fibers, QHL, & Multi-Collision Deflated QHL
-/
section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
private lemma qhlQSet_val {Var : Type} {d : ℕ} [NeZero d]
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qSet σ).1.1 =
      (θ σ).1.1 0 0 • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qSet_apply_mat θ σ
end

section GHMidPZoomBounds
namespace QuantumComputation.Specs.DickeSol
open Real Complex
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
@[expose] public section
/- ## 1. Middle-`p` Schedule Types, Compilation, & 1-D Multi-Collision Model (`3 ≤ r ≤ 16`) -/
/-- Compiled Gaussian-Hamming probe `(phases, rotTop, kNext)` for `3 ≤ r ≤ 16`. -/
structure GHMidPProbe where
  phases : List GaussPyth
  rotTop : PythPair
  kNext : ℕ
  deriving DecidableEq, Repr
/-- Compiled row schedule `(kInit, probes, kZoom)` for `3 ≤ r ≤ 16` middle-`p`
  Collision-Zoom. -/
abbrev GHMidPSpec : Type := Option (ℕ × List GHMidPProbe × ℕ)
/-- Subcube-dimension-parameterized pass function (`subN` -> `r` -> `GHMidPSpec`). -/
abbrev GHMidPPassFn : Type := ℕ → ℕ → GHMidPSpec
/-- Worst-case parallel oracle queries consumed prior to `wt = r - 1` collision zoom. -/
def ghMidPPreMaxQueries (kInit : ℕ) (probes : List GHMidPProbe) : ℕ :=
  (kInit + 1) + (probes.map fun pr ↦ pr.kNext + 2).sum
/-- Worst-case parallel oracle queries including `wt = r - 1` collision zoom (`kZoom + 1`). -/
def ghMidPMaxQueries (kInit : ℕ) (probes : List GHMidPProbe) (kZoom : ℕ) : ℕ :=
  ghMidPPreMaxQueries kInit probes + (kZoom + 1)
/-- General integer-dimension Grover step count `⌊(aNum / aDen) / (2 * arcsin(1 / √D))⌋₊`. -/
noncomputable def wdMidPStepCount (D aNum aDen : ℕ) : ℕ :=
  Nat.floor (((aNum : ℝ) / (aDen : ℝ)) / (2 * Real.arcsin (1 / √(D : ℝ))))
theorem wdMidPStepCount_pow_eq (aNum aDen subN : ℕ) :
    wdMidPStepCount (2 ^ subN) aNum aDen = wdStepCount aNum aDen subN := by
  unfold wdMidPStepCount wdStepCount; push_cast; rfl
/-- Compiles one `MidPPhaseSpec` into `Option GaussPyth`. -/
def compileMidPPhase (ph : MidPPhaseSpec) : Option GaussPyth :=
  if h : 0 < ph.gd ∧ ph.ga ^ 2 + ph.gb ^ 2 = (ph.gd : ℤ) ^ 2 then
    some ⟨ph.ga, ph.gb, ph.gd, h.1, h.2⟩
  else
    none
/-- Compiles a `List MidPPhaseSpec` into `Option (List GaussPyth)`. -/
def compileMidPPhases : List MidPPhaseSpec → Option (List GaussPyth)
  | [] => some []
  | ph :: rest =>
      match compileMidPPhase ph, compileMidPPhases rest with
      | some g, some tl => some (g :: tl)
      | _, _ => none
/-- Compiles one `MidPProbeSpec` at subcube dimension `subN` (`len = r`). -/
noncomputable def compileMidPProbe (r : ℕ) (p : MidPProbeSpec) (subN : ℕ) : Option GHMidPProbe :=
  if h : p.phases.length = r ∧ 0 < p.daDen ∧ 0 < p.cDen ∧
      p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 = (p.cDen : ℤ) ^ 2 then
    match compileMidPPhases p.phases with
    | some gs =>
        some ⟨gs, ⟨p.cNum, p.sNum, p.cDen, h.2.2.1, h.2.2.2⟩,
          wdStepCount p.daNum p.daDen subN⟩
    | none => none
  else
    none
/-- Compiles a `List MidPProbeSpec` at subcube dimension `subN`. -/
noncomputable def compileMidPProbes (r : ℕ) :
    List MidPProbeSpec → ℕ → Option (List GHMidPProbe)
  | [], _ => some []
  | p :: rest, subN =>
      match compileMidPProbe r p subN, compileMidPProbes r rest subN with
      | some pr, some tl => some (pr :: tl)
      | _, _ => none
/-- Compiles a `MidPRowSpec` for `(m, r)` at subcube dimension `subN`. -/
noncomputable def compileMidPRow (m r : ℕ) (spec : MidPRowSpec) (subN : ℕ) : GHMidPSpec :=
  let p := Stage2CertInternals.gridExp m
  if 0 < spec.a0Den ∧ 0 < spec.kzDen then
    match compileMidPProbes r spec.probes subN with
    | some probes =>
        some (wdStepCount spec.a0Num spec.a0Den subN, probes,
          wdMidPStepCount ((r - 1) * 2 ^ (subN - p)) spec.kzNum spec.kzDen)
    | none => none
  else
    none
/-- Initial `deg`-singleton complex Dicke amplitude after `kInit` Grover steps + marking. -/
noncomputable def ghMidPInitAmp (deg : ℕ) (θ : ℝ) (kInit : ℕ) : ℕ → ℂ :=
  dickeStep deg (Real.cos ((2 * (kInit : ℝ) + 1) * θ) : ℂ)
    (Real.sin ((2 * (kInit : ℝ) + 1) * θ) : ℂ)
    (fun b ↦ if b = 0 then 1 else 0)
/-- No-click injective-fiber damping on `0.. r` under `pr: GHMidPProbe`. -/
noncomputable def ghMidPDampAmp (r : ℕ) (pr : GHMidPProbe) (u : ℕ → ℂ) (b : ℕ) : ℂ :=
  if b = 0 then u 0
  else if b < r then (pr.phases.getD (b - 1) gaussOne).val * u b
  else if b = r then (pr.rotTop.cVal : ℂ) * (pr.phases.getD (r - 1) gaussOne).val * u r
  else 0
/-- Next injective-fiber complex Dicke amplitude on no-click after one `GHMidPProbe`. -/
noncomputable def ghMidPProbeNextAmp (r : ℕ) (θ₁ : ℝ) (pr : GHMidPProbe) (u : ℕ → ℂ) : ℕ → ℂ :=
  dickeStep r (Real.cos (2 * (pr.kNext : ℝ) * θ₁) : ℂ)
    (Real.sin (2 * (pr.kNext : ℝ) * θ₁) : ℂ)
    (ghMidPDampAmp r pr u)
/-- Final injective-fiber complex Dicke amplitude across `probes`. -/
noncomputable def ghMidPChainFinalAmp (r : ℕ) (θ₁ : ℝ) : List GHMidPProbe → (ℕ → ℂ) → (ℕ → ℂ)
  | [], u => u
  | pr :: rest, u => ghMidPChainFinalAmp r θ₁ rest (ghMidPProbeNextAmp r θ₁ pr u)
/-- Expected extra parallel oracle queries along `probes` on an injective `r`-fiber. -/
noncomputable def ghMidPChainExtraQueries (r : ℕ) (θ₁ : ℝ) : List GHMidPProbe → (ℕ → ℂ) → ℝ
  | [], _ => 0
  | pr :: rest, u =>
      let uD := ghMidPDampAmp r pr u
      (∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) * Complex.normSq (uD w)) *
          ((pr.kNext + 2 : ℕ) : ℝ) +
        ghMidPChainExtraQueries r θ₁ rest (ghMidPProbeNextAmp r θ₁ pr u)
/-- Initial coupled `2`-row `[c, 1 ^ deg1]` amplitude (`SinglePair` at `r - 2`,
  `SingleTriple` at
  `r - 3`). -/
noncomputable def ghMidPInit2Row (deg1 : ℕ) (θ₁ θC : ℝ) (kInit : ℕ) : (ℕ → ℂ) × (ℕ → ℂ) :=
  let uSing := ghMidPInitAmp deg1 θ₁ kInit
  let cC : ℂ := Real.cos ((2 * (kInit : ℝ) + 1) * θC)
  let sC : ℂ := Real.sin ((2 * (kInit : ℝ) + 1) * θC)
  (fun w₁ ↦ cC * uSing w₁, fun w₁ ↦ sC * uSing w₁)
/-- Phase-damped row-`0` (`wdHitCount = w₁`) on `0.. deg1`. -/
noncomputable def ghMidPDamp2Row0 (deg1 : ℕ) (pr : GHMidPProbe) (z0 : ℕ → ℂ) (w₁ : ℕ) : ℂ :=
  if w₁ = 0 then z0 0
  else if w₁ ≤ deg1 then (pr.phases.getD (w₁ - 1) gaussOne).val * z0 w₁
  else 0
/-- Phase-damped row-`1` (`wdHitCount = w₁ + 1`) on `0.. deg1`. -/
noncomputable def ghMidPDamp2Row1 (deg1 : ℕ) (pr : GHMidPProbe) (z1 : ℕ → ℂ) (w₁ : ℕ) : ℂ :=
  if w₁ ≤ deg1 then (pr.phases.getD w₁ gaussOne).val * z1 w₁
  else 0
/-- Next coupled `2`-row `[c, 1 ^ deg1]` amplitude after one `GHMidPProbe` (`w₁ + 1 ≤ r -
  1`, so
  `rotTop` at weight `r` never fires on `deg1 ≤ r - 2`). -/
noncomputable def ghMidPProbeNext2Row (deg1 : ℕ) (θ₁ θC : ℝ) (pr : GHMidPProbe)
    (z : (ℕ → ℂ) × (ℕ → ℂ)) : (ℕ → ℂ) × (ℕ → ℂ) :=
  let c₁ : ℂ := Real.cos (2 * (pr.kNext : ℝ) * θ₁)
  let s₁ : ℂ := Real.sin (2 * (pr.kNext : ℝ) * θ₁)
  let cC : ℂ := Real.cos (2 * (pr.kNext : ℝ) * θC)
  let sC : ℂ := Real.sin (2 * (pr.kNext : ℝ) * θC)
  let m0 := dickeStep deg1 c₁ s₁ (ghMidPDamp2Row0 deg1 pr z.1)
  let m1 := dickeStep deg1 c₁ s₁ (ghMidPDamp2Row1 deg1 pr z.2)
  (fun w₁ ↦ cC * m0 w₁ - sC * m1 w₁, fun w₁ ↦ sC * m0 w₁ + cC * m1 w₁)
/-- Final coupled `2`-row `[c, 1 ^ deg1]` amplitude across `probes`. -/
noncomputable def ghMidPChainFinal2Row (deg1 : ℕ) (θ₁ θC : ℝ) :
    List GHMidPProbe → ((ℕ → ℂ) × (ℕ → ℂ)) → ((ℕ → ℂ) × (ℕ → ℂ))
  | [], z => z
  | pr :: rest, z => ghMidPChainFinal2Row deg1 θ₁ θC rest (ghMidPProbeNext2Row deg1 θ₁ θC pr z)
/-- Initial `TwoPair` `[2, 2, 1 ^ deg1]` `3`-row amplitude (`deg1 = r - 4`, `r ≥ 4`). -/
noncomputable def ghMidPInitTwoPair (deg1 : ℕ) (θ₁ θ₂ : ℝ) (kInit : ℕ) :
    (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ) :=
  let uSing := ghMidPInitAmp deg1 θ₁ kInit
  let uP2 := ghMidPInitAmp 2 θ₂ kInit
  (fun w₁ ↦ uP2 0 * uSing w₁, fun w₁ ↦ uP2 1 * uSing w₁, fun w₁ ↦ uP2 2 * uSing w₁)
/-- Phase-damped row-`2` (`wdHitCount = w₁ + 2`) on `0.. deg1` (`deg1 = r - 4`, so
  `w₁ + 2 ≤ r - 2 < r`). -/
noncomputable def ghMidPDampTwoPair2 (deg1 : ℕ) (pr : GHMidPProbe) (z2 : ℕ → ℂ) (w₁ : ℕ) : ℂ :=
  if w₁ ≤ deg1 then (pr.phases.getD (w₁ + 1) gaussOne).val * z2 w₁
  else 0
/-- Next `TwoPair` `[2, 2, 1 ^ deg1]` `3`-row amplitude after one `GHMidPProbe`. -/
noncomputable def ghMidPProbeNextTwoPair (deg1 : ℕ) (θ₁ θ₂ : ℝ) (pr : GHMidPProbe)
    (z : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ)) : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ) :=
  let c₁ : ℂ := Real.cos (2 * (pr.kNext : ℝ) * θ₁)
  let s₁ : ℂ := Real.sin (2 * (pr.kNext : ℝ) * θ₁)
  let c₂ : ℂ := Real.cos (2 * (pr.kNext : ℝ) * θ₂)
  let s₂ : ℂ := Real.sin (2 * (pr.kNext : ℝ) * θ₂)
  let m0 := dickeStep deg1 c₁ s₁ (ghMidPDamp2Row0 deg1 pr z.1)
  let m1 := dickeStep deg1 c₁ s₁ (ghMidPDamp2Row1 deg1 pr z.2.1)
  let m2 := dickeStep deg1 c₁ s₁ (ghMidPDampTwoPair2 deg1 pr z.2.2)
  let col (w₁ j : ℕ) : ℂ :=
    match j with
    | 0 => m0 w₁
    | 1 => m1 w₁
    | _ => m2 w₁
  (fun w₁ ↦ dickeStep 2 c₂ s₂ (col w₁) 0,
    fun w₁ ↦ dickeStep 2 c₂ s₂ (col w₁) 1,
    fun w₁ ↦ dickeStep 2 c₂ s₂ (col w₁) 2)
/-- Final `TwoPair` `[2, 2, 1 ^ deg1]` `3`-row amplitude across `probes`. -/
noncomputable def ghMidPChainFinalTwoPair (deg1 : ℕ) (θ₁ θ₂ : ℝ) :
    List GHMidPProbe → ((ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ)) → ((ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ))
  | [], z => z
  | pr :: rest, z =>
      ghMidPChainFinalTwoPair deg1 θ₁ θ₂ rest (ghMidPProbeNextTwoPair deg1 θ₁ θ₂ pr z)
/-- Exact `rm2` 1-pass Bellman upper bound for `3 ≤ r ≤ 16` middle-`p` unpadded `wt = r - 1`
  Collision-Zoom (`Inj`, `SinglePair`, `TwoPair`, `SingleTriple`, and residual fibers). -/
noncomputable def ghMidPOneDimUpper (subN p m : ℕ) (spec : GHMidPSpec) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0
  else
    match spec with
    | none => f r
    | some (kInit, probes, kZoom) =>
        if 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ m = 2 ^ p then
          let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
          let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
          let θ₃ := Real.arcsin (√3 / √(2 ^ subN : ℝ))
          let θZoom := Real.arcsin (1 / √(((r - 1) * 2 ^ (subN - p) : ℕ) : ℝ))
          let pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2
          let qZoom := ((kZoom + 1 : ℕ) : ℝ)
          let u₀ := ghMidPInitAmp r θ₁ kInit
          let uf := ghMidPChainFinalAmp r θ₁ probes u₀
          let qDist := ((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQueries r θ₁ probes u₀
          let remDist := ∑ w ∈ Finset.range r, (r.choose w : ℝ) * Complex.normSq (uf w) * (if w + 1
            = r then qZoom + f 1 else f (r - w))
          let qColl := (ghMidPPreMaxQueries kInit probes : ℝ)
          let sp₀ := ghMidPInit2Row (r - 2) θ₁ θ₂ kInit
          let spf := ghMidPChainFinal2Row (r - 2) θ₁ θ₂ probes sp₀
          let remSp0 := ∑ w₁ ∈ Finset.range (r - 1),
            ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.1 w₁) * f (r - w₁)
          let remSp1 := ∑ w₁ ∈ Finset.range (r - 1), ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.2
            w₁) * (if w₁ + 2 = r then qZoom + (1 - pZoom) * f 1 else f (r - 1 - w₁))
          let st₀ := ghMidPInit2Row (r - 3) θ₁ θ₃ kInit
          let stf := ghMidPChainFinal2Row (r - 3) θ₁ θ₃ probes st₀
          let remSt := ∑ w₁ ∈ Finset.range (r - 2),
            (((r - 3).choose w₁ : ℝ) * Complex.normSq (stf.1 w₁) * f (r - w₁) +
              ((r - 3).choose w₁ : ℝ) * Complex.normSq (stf.2 w₁) * f (r - (w₁ + 1)))
          let tp₀ := ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit
          let tpf := ghMidPChainFinalTwoPair (r - 4) θ₁ θ₂ probes tp₀
          let remTp := if 4 ≤ r then ∑ w₁ ∈ Finset.range (r - 3), (((r - 4).choose w₁ : ℝ) *
            Complex.normSq (tpf.1 w₁) * f (r - w₁) + (2 * (r - 4).choose w₁ : ℝ) * Complex.normSq
            (tpf.2.1 w₁) * f (r - (w₁ + 1)) + ((r - 4).choose w₁ : ℝ) * Complex.normSq (tpf.2.2
            w₁) * f (r - (w₁ + 2))) else 0
          let nInj : ℕ := m.descFactorial r
          let nSp : ℕ := r.choose 2 * m.descFactorial (r - 1)
          let nTp : ℕ := if 4 ≤ r then 3 * r.choose 4 * m.descFactorial (r - 2) else 0
          let nSt : ℕ := r.choose 3 * m.descFactorial (r - 2)
          let nRem : ℕ := m ^ r - (nInj + nSp + nTp + nSt)
          ((nInj : ℝ) * (qDist + remDist) +
            (nSp : ℝ) * (qColl + remSp0 + remSp1) +
            (nTp : ℝ) * (qColl + remTp) +
            (nSt : ℝ) * (qColl + remSt) +
            (nRem : ℝ) * (qColl + f r)) / ((m ^ r : ℕ) : ℝ)
        else f r
/- ## 2. Outward `sqrt(1..16)` & `subN ≥ 200` `arcsin` Ratio Enclosures (`0` `decide`) -/
private lemma wdScaleR_pos : 0 < wdScaleR := by unfold wdScaleR wdScale; norm_num
private lemma midP_arcsin_le_add_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.arcsin x ≤ x + x ^ 2 := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have h3 : x * (1 + x) ^ 3 ≤ 2 := by
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x) (by linarith : 1 + x ≤ 3 / 2) 3]
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
    ⟨by nlinarith [Real.pi_gt_three], by nlinarith [Real.pi_gt_three]⟩]
  nlinarith [Real.sin_gt_sub_cube (by positivity : 0 < x + x ^ 2),
    mul_le_mul_of_nonneg_left h3 (sq_nonneg x)]
private lemma midP_four_div_pi_le : (4 : ℝ) / π ≤ (wdPi4InvHi : ℝ) / wdScaleR := by
  have hpi : (3141592653589793 : ℝ) / 1000000000000000 < π := (by linarith [Real.pi_gt_d20])
  rw [div_le_iff₀ Real.pi_pos]; have h1 : (4 : ℝ) ≤ ((wdPi4InvHi : ℝ) / wdScaleR) *
      ((3141592653589793 : ℝ) / 1000000000000000) := by
    unfold wdPi4InvHi wdScaleR wdScale; norm_num
  exact h1.trans
    (mul_le_mul_of_nonneg_left hpi.le (by unfold wdPi4InvHi wdScaleR wdScale; positivity))
/-- General outward `subN ≥ 200` enclosure for `arcsin(√w / √(2 ^ subN)) / arcsin(1 / √(2 ^
  subN))`
  from integer square bounds `lo ^ 2 ≤ w * 10 ^ 30 ≤ hi ^ 2` (`1 ≤ w ≤ 16`). -/
theorem ghZoom_subN_sqrtW_ratio_bounds {w subN : ℕ} {lo hi : ℤ} (hsub : 200 ≤ subN) (hlo1 : 1 ≤ lo)
    (hhi_nn : 0 ≤ hi) (hhi4 : hi ≤ 4 * (wdScale : ℤ)) (hsq_lo : lo ^ 2 ≤ (w : ℤ) * (wdScale : ℤ) ^
    2) (hsq_hi : (w : ℤ) * (wdScale : ℤ) ^ 2 ≤ hi ^ 2) : wdMem (Real.arcsin (√(w : ℝ) / √(2 ^ subN :
    ℝ)) / Real.arcsin (1 / √(2 ^ subN : ℝ))) (lo - 1, hi + 1) := by
  have hB : 0 < wdScaleR := wdScaleR_pos; have hBeq : wdScaleR = (wdScale : ℝ) := rfl
  set D : ℝ := (2 ^ subN : ℝ)
  have hD_ge : (2 ^ 200 : ℝ) ≤ D := pow_le_pow_right₀ (by norm_num) hsub
  have hsqrtD_ge : (2 ^ 100 : ℝ) ≤ √D :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 ^ 100 : ℝ) ^ 2) ≤ 2 ^ 200).trans hD_ge)
  have hsqrtD_pos : 0 < √D := lt_of_lt_of_le (by norm_num) hsqrtD_ge; set x₁ : ℝ := 1 / √D
  have hx₁_pos : 0 < x₁ := div_pos one_pos hsqrtD_pos
  have hx₁_le : x₁ ≤ 1 / 2 ^ 100 := one_div_le_one_div_of_le (by norm_num) hsqrtD_ge
  set θ₁ : ℝ := Real.arcsin x₁
  have hx₁_θ₁ : x₁ ≤ θ₁ := self_le_arcsin hx₁_pos.le (hx₁_le.trans (by norm_num))
  have hθ₁_pos : 0 < θ₁ := hx₁_pos.trans_le hx₁_θ₁
  have hθ₁_hi : θ₁ ≤ (1 + 1 / 2 ^ 100) * x₁ := by
    have h := midP_arcsin_le_add_sq hx₁_pos.le (hx₁_le.trans (by norm_num))
    have hsq : x₁ ^ 2 ≤ (1 / 2 ^ 100) * x₁ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hx₁_le hx₁_pos.le
    linarith
  have hlo_sqrt : (lo : ℝ) / wdScaleR ≤ √(w : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [div_pow, div_le_iff₀ (pow_pos hB 2), hBeq]; exact_mod_cast hsq_lo
  have hsqrt_hi : √(w : ℝ) ≤ (hi : ℝ) / wdScaleR := by
    rw [Real.sqrt_le_iff]; refine ⟨div_nonneg (by exact_mod_cast hhi_nn) hB.le, ?_⟩
    rw [div_pow, le_div_iff₀ (pow_pos hB 2), hBeq]; exact_mod_cast hsq_hi
  have hhi4_r : (hi : ℝ) / wdScaleR ≤ 4 := (by rw [div_le_iff₀ hB, hBeq]; exact_mod_cast hhi4)
  set xw : ℝ := √(w : ℝ) / √D
  have hxw_eq : xw = √(w : ℝ) * x₁ := (by dsimp only [xw, x₁]; rw [div_eq_mul_one_div])
  have hxw_nn : 0 ≤ xw := div_nonneg (Real.sqrt_nonneg _) hsqrtD_pos.le
  have hxw_le : xw ≤ 4 / 2 ^ 100 := by
    rw [hxw_eq]
    exact (mul_le_mul (hsqrt_hi.trans hhi4_r) hx₁_le hx₁_pos.le (by norm_num)).trans (by norm_num)
  set θw : ℝ := Real.arcsin xw
  have hxw_θw : xw ≤ θw := self_le_arcsin hxw_nn (hxw_le.trans (by norm_num))
  have hθw_hi : θw ≤ (1 + 4 / 2 ^ 100) * xw := by
    have h := midP_arcsin_le_add_sq hxw_nn (hxw_le.trans (by norm_num))
    have hsq : xw ^ 2 ≤ (4 / 2 ^ 100) * xw := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hxw_le hxw_nn
    linarith
  have hlo_le_hi : lo ≤ hi := (by have hsq : lo ^ 2 ≤ hi ^ 2 := hsq_lo.trans hsq_hi; nlinarith)
  have hlo_bound : (lo : ℝ) ≤ 4 * 1000000000000000 := by
    have h4 : lo ≤ 4 * 1000000000000000 := (by unfold wdScale at hhi4; omega); exact_mod_cast h4
  have hhi_bound : (hi : ℝ) ≤ 4 * 1000000000000000 := by
    have h4 : hi ≤ 4 * 1000000000000000 := (by unfold wdScale at hhi4; omega); exact_mod_cast h4
  have hlo1_r : (1 : ℝ) ≤ (lo : ℝ) := (by exact_mod_cast hlo1); unfold wdMem; constructor
  · rw [le_div_iff₀ hθ₁_pos]
    have hcoef : (((lo - 1 : ℤ) : ℝ) / wdScaleR) * (1 + 1 / 2 ^ 100) ≤ (lo : ℝ) / wdScaleR := by
      have hnum : ((lo - 1 : ℤ) : ℝ) * (1 + 1 / 2 ^ 100) ≤ (lo : ℝ) := (by push_cast; linarith)
      calc (((lo - 1 : ℤ) : ℝ) / wdScaleR) * (1 + 1 / 2 ^ 100)
          = (((lo - 1 : ℤ) : ℝ) * (1 + 1 / 2 ^ 100)) / wdScaleR := by ring
        _ ≤ (lo : ℝ) / wdScaleR := div_le_div_of_nonneg_right hnum hB.le
    have hlo_m1_nn : 0 ≤ ((lo - 1 : ℤ) : ℝ) / wdScaleR := div_nonneg (by push_cast; linarith) hB.le
    calc (((lo - 1 : ℤ) : ℝ) / wdScaleR) * θ₁ ≤ (((lo - 1 : ℤ) : ℝ) / wdScaleR) * ((1 + 1 / 2 ^
          100) * x₁) := mul_le_mul_of_nonneg_left hθ₁_hi hlo_m1_nn
      _ = ((((lo - 1 : ℤ) : ℝ) / wdScaleR) * (1 + 1 / 2 ^ 100)) * x₁ := by ring
      _ ≤ ((lo : ℝ) / wdScaleR) * x₁ := mul_le_mul_of_nonneg_right hcoef hx₁_pos.le
      _ ≤ √(w : ℝ) * x₁ := mul_le_mul_of_nonneg_right hlo_sqrt hx₁_pos.le
      _ = xw := hxw_eq.symm
      _ ≤ θw := hxw_θw
  · rw [div_le_iff₀ hθ₁_pos]
    have hcoef : (1 + 4 / 2 ^ 100) * ((hi : ℝ) / wdScaleR) ≤ ((hi + 1 : ℤ) : ℝ) / wdScaleR := by
      have hnum : (1 + 4 / 2 ^ 100) * (hi : ℝ) ≤ ((hi + 1 : ℤ) : ℝ) := (by push_cast; linarith)
      calc (1 + 4 / 2 ^ 100) * ((hi : ℝ) / wdScaleR)
          = ((1 + 4 / 2 ^ 100) * (hi : ℝ)) / wdScaleR := by ring
        _ ≤ ((hi + 1 : ℤ) : ℝ) / wdScaleR := div_le_div_of_nonneg_right hnum hB.le
    have hhi_div_nn : 0 ≤ (hi : ℝ) / wdScaleR := div_nonneg (by exact_mod_cast hhi_nn) hB.le
    calc θw
        ≤ (1 + 4 / 2 ^ 100) * (√(w : ℝ) * x₁) := by rw [← hxw_eq]; exact hθw_hi
      _ ≤ (1 + 4 / 2 ^ 100) * (((hi : ℝ) / wdScaleR) * θ₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hsqrt_hi hx₁_θ₁ hx₁_pos.le hhi_div_nn) (by norm_num)
      _ = ((1 + 4 / 2 ^ 100) * ((hi : ℝ) / wdScaleR)) * θ₁ := by ring
      _ ≤ (((hi + 1 : ℤ) : ℝ) / wdScaleR) * θ₁ := mul_le_mul_of_nonneg_right hcoef hθ₁_pos.le
/-- Certified outward enclosure `wdMem (θ_w / θ_1) (midPSqrtRatioIv w)` for all `1 ≤ w ≤ 16`
  and `200 ≤ subN` (`0` `decide`). -/
theorem midPSqrtRatioIv_mem {w subN : ℕ} (hw1 : 1 ≤ w) (hw16 : w ≤ 16) (hsub : 200 ≤ subN) :
    wdMem (Real.arcsin (√(w : ℝ) / √(2 ^ subN : ℝ)) / Real.arcsin (1 / √(2 ^ subN : ℝ)))
      (midPSqrtRatioIv w) := by
  have htab : 1 ≤ (midPSqrtEntry w).lo ∧ 0 ≤ (midPSqrtEntry w).hi ∧ (midPSqrtEntry w).hi ≤ 4 *
    (wdScale : ℤ) ∧ (midPSqrtEntry w).lo ^ 2 ≤ (w : ℤ) * (wdScale : ℤ) ^ 2 ∧ (w : ℤ) * (wdScale : ℤ)
    ^ 2 ≤ (midPSqrtEntry w).hi ^ 2 := by
    interval_cases w <;> norm_num [midPSqrtEntry, midPSqrtTable16, wdScale]
  unfold midPSqrtRatioIv; change wdMem _ ((midPSqrtEntry w).lo - 1, (midPSqrtEntry w).hi + 1)
  exact ghZoom_subN_sqrtW_ratio_bounds hsub htab.1 htab.2.1 htab.2.2.1 htab.2.2.2.1 htab.2.2.2.2
/- ## 3. General Real-Dimension Step-Count & Unpadded `wt = r - 1` Zoom Bounds -/
/-- General angle & query bound for `wdMidPStepCount D aNum aDen` whenever `2 ^ 200 ≤ D`. -/
theorem ghRealDimStepCount_bounds {D aNum aDen : ℕ} (hD : 2 ^ 200 ≤ D) (hden : 0 < aDen) (c : ℕ) :
    let Dr : ℝ := (D : ℝ); let θ : ℝ := Real.arcsin (1 / √Dr)
    let scale15 : ℝ := ((π / 4) * √Dr) / wdScaleR; let aIV : WDIVal := wdRat (aNum : ℤ) aDen
    let K : ℕ := wdMidPStepCount D aNum aDen
    let qHi : ℤ := wdDivCeil ((aIV.2 + 2 * (c : ℤ)) * wdPi4InvHi) (2 * (wdScale : ℤ))
    wdMem ((2 * (K : ℝ) + 1) * θ) (max 0 (aIV.1 - 1), aIV.2 + 1) ∧ wdMem (2 * (K : ℝ) * θ) (max 0
      (aIV.1 - 2), aIV.2) ∧ 0 ≤ qHi ∧ ((K + c : ℕ) : ℝ) ≤ (qHi : ℝ) * scale15 := by
  intro Dr θ scale15 aIV K qHi; have hB : 0 < wdScaleR := wdScaleR_pos
  have h2BZ : (0 : ℤ) < 2 * (wdScale : ℤ) := (by unfold wdScale; norm_num)
  have hD_cast : ((2 ^ 200 : ℕ) : ℝ) ≤ Dr := Nat.cast_le.mpr hD
  have hsqrtD_ge : (2 ^ 100 : ℝ) ≤ √Dr :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 ^ 100 : ℝ) ^ 2) ≤ ((2 ^ 200 : ℕ) : ℝ)).trans hD_cast)
  have hsqrtD_pos : 0 < √Dr := lt_of_lt_of_le (by norm_num) hsqrtD_ge
  have hsqrtD_nn : 0 ≤ √Dr := hsqrtD_pos.le; set x₁ : ℝ := 1 / √Dr
  have hx₁_pos : 0 < x₁ := div_pos one_pos hsqrtD_pos
  have hx₁_le : x₁ ≤ 1 / 2 ^ 100 := one_div_le_one_div_of_le (by norm_num) hsqrtD_ge
  have hx₁_θ : x₁ ≤ θ := self_le_arcsin hx₁_pos.le (hx₁_le.trans (by norm_num))
  have hθ_pos : 0 < θ := hx₁_pos.trans_le hx₁_θ
  have hθ_scale : θ ≤ 1 / wdScaleR := by
    have h1 : θ ≤ x₁ + x₁ ^ 2 := midP_arcsin_le_add_sq hx₁_pos.le (hx₁_le.trans (by norm_num))
    have hsq : x₁ ^ 2 ≤ (1 / 2 ^ 100) * x₁ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hx₁_le hx₁_pos.le
    have h2 : θ ≤ (1 + 1 / 2 ^ 100) * (1 / 2 ^ 100) := (by nlinarith); refine h2.trans ?_
    unfold wdScaleR wdScale; norm_num
  have hone_le : (1 : ℝ) ≤ (1 / wdScaleR) * √Dr := by
    have hBs : wdScaleR ≤ 2 ^ 100 := (by unfold wdScaleR wdScale; norm_num)
    rw [one_div, inv_mul_eq_div, one_le_div hB]; exact hBs.trans hsqrtD_ge
  set a : ℝ := (aNum : ℝ) / (aDen : ℝ); have ha_nn : 0 ≤ a := (by positivity)
  have ha_mem : wdMem a aIV := (by simpa [a, aIV] using wdMem_rat (num := (aNum : ℤ)) hden)
  have h2θ_pos : 0 < 2 * θ := (by linarith)
  have hK_le : (K : ℝ) ≤ a / (2 * θ) := Nat.floor_le (div_nonneg ha_nn h2θ_pos.le)
  have hK_gt : a / (2 * θ) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2K_hi : 2 * (K : ℝ) * θ ≤ a := (by have h := (le_div_iff₀ h2θ_pos).mp hK_le; linarith)
  have h2K_lo : a - 2 * θ ≤ 2 * (K : ℝ) * θ := by have h := (div_lt_iff₀ h2θ_pos).mp hK_gt; linarith
  have h2θ_sc : 2 * θ ≤ 2 / wdScaleR := by
    rw [show (2 : ℝ) / wdScaleR = 2 * (1 / wdScaleR) by ring]; linarith [hθ_scale]
  have hm1 : wdMem ((2 * (K : ℝ) + 1) * θ) (max 0 (aIV.1 - 1), aIV.2 + 1) := by
    unfold wdMem; constructor
    · push_cast; rw [div_le_iff₀ hB]; refine max_le (by positivity) ?_
      rw [← div_le_iff₀ hB, sub_div]; linarith [ha_mem.1, h2K_lo, hθ_scale]
    · push_cast; rw [add_div]; linarith [ha_mem.2, h2K_hi, hθ_scale]
  have hm2 : wdMem (2 * (K : ℝ) * θ) (max 0 (aIV.1 - 2), aIV.2) := by
    unfold wdMem; constructor
    · push_cast; rw [div_le_iff₀ hB]; refine max_le (by positivity) ?_
      rw [← div_le_iff₀ hB, sub_div]; linarith [ha_mem.1, h2K_lo, h2θ_sc]
    · linarith [ha_mem.2, h2K_hi]
  have haIV2_nn : 0 ≤ aIV.2 := by
    dsimp only [aIV, wdRat]
    exact wdDivCeil_nonneg (mul_nonneg (Nat.cast_nonneg _) (by unfold wdScale; norm_num))
      (by exact_mod_cast hden)
  have hqHi_nn : 0 ≤ qHi := by
    dsimp only [qHi]; refine wdDivCeil_nonneg ?_ h2BZ
    exact mul_nonneg (by linarith) (by unfold wdPi4InvHi; norm_num)
  have hK_sqrt : (K : ℝ) ≤ (a / 2) * √Dr := by
    have hinv : 1 / (2 * θ) ≤ √Dr / 2 := by
      rw [div_le_div_iff₀ h2θ_pos (by norm_num)]
      have h1 := mul_le_mul_of_nonneg_right hx₁_θ hsqrtD_nn
      rw [one_div_mul_cancel hsqrtD_pos.ne'] at h1; linarith
    calc (K : ℝ) ≤ a * (1 / (2 * θ)) := by rw [← div_eq_mul_one_div]; exact hK_le
      _ ≤ a * (√Dr / 2) := mul_le_mul_of_nonneg_left hinv ha_nn
      _ = (a / 2) * √Dr := by ring
  have hc_sqrt : (c : ℝ) ≤ ((c : ℝ) / wdScaleR) * √Dr := by
    have h := mul_le_mul_of_nonneg_left hone_le (Nat.cast_nonneg c)
    linarith [show (c : ℝ) * ((1 / wdScaleR) * √Dr) = ((c : ℝ) / wdScaleR) * √Dr by ring]
  have hKc_sqrt : ((K + c : ℕ) : ℝ) ≤ (((aIV.2 + 2 * (c : ℤ) : ℤ) : ℝ) / (2 * wdScaleR)) * √Dr := by
    push_cast
    have hcoef : a / 2 + (c : ℝ) / wdScaleR ≤ ((aIV.2 : ℝ) + 2 * (c : ℝ)) / (2 * wdScaleR) := by
      have h2B : 0 < 2 * wdScaleR := (by linarith); rw [le_div_iff₀ h2B]
      have ha2 : a * wdScaleR ≤ (aIV.2 : ℝ) := (le_div_iff₀ hB).mp ha_mem.2
      have hcancel : (a / 2 + (c : ℝ) / wdScaleR) * (2 * wdScaleR) =
          a * wdScaleR + 2 * (c : ℝ) := by field_simp [hB.ne']
      linarith
    calc (K : ℝ) + (c : ℝ)
        ≤ (a / 2 + (c : ℝ) / wdScaleR) * √Dr := by linarith
      _ ≤ (((aIV.2 : ℝ) + 2 * (c : ℝ)) / (2 * wdScaleR)) * √Dr :=
          mul_le_mul_of_nonneg_right hcoef hsqrtD_nn
  have hpi_conv : √Dr ≤ ((wdPi4InvHi : ℝ) / wdScaleR) * ((π / 4) * √Dr) := by
    have h4pi := midP_four_div_pi_le
    have h1 : (1 : ℝ) ≤ ((wdPi4InvHi : ℝ) / wdScaleR) * (π / 4) := by
      have hp := Real.pi_pos; have hm := mul_le_mul_of_nonneg_right h4pi (by positivity : 0 ≤ π / 4)
      have heq : (4 / π) * (π / 4) = 1 := (by field_simp [hp.ne']); linarith
    have hm_d := mul_le_mul_of_nonneg_right h1 hsqrtD_nn; linarith
  have hqHi_bound : ((K + c : ℕ) : ℝ) ≤ (qHi : ℝ) * scale15 := by
    have hcoef_nn : 0 ≤ ((aIV.2 + 2 * (c : ℤ) : ℤ) : ℝ) / (2 * wdScaleR) := by
      refine div_nonneg ?_ (by linarith)
      exact_mod_cast (show 0 ≤ aIV.2 + 2 * (c : ℤ) by positivity)
    have hceil := le_wdDivCeil (a := (aIV.2 + 2 * (c : ℤ)) * wdPi4InvHi) h2BZ
    calc ((K + c : ℕ) : ℝ) ≤ (((aIV.2 + 2 * (c : ℤ) : ℤ) : ℝ) / (2 * wdScaleR)) * (((wdPi4InvHi : ℝ)
          / wdScaleR) * ((π / 4) * √Dr)) := hKc_sqrt.trans (mul_le_mul_of_nonneg_left hpi_conv
          hcoef_nn)
      _ = ((((aIV.2 + 2 * (c : ℤ)) * wdPi4InvHi : ℤ) : ℝ) /
            ((2 * (wdScale : ℤ) : ℤ) : ℝ)) * scale15 := by
          dsimp only [scale15, wdScaleR]; push_cast; ring
      _ ≤ (qHi : ℝ) * scale15 :=
          mul_le_mul_of_nonneg_right hceil (div_nonneg (by positivity [Real.pi_pos]) hB.le)
  exact ⟨hm1, hm2, hqHi_nn, hqHi_bound⟩
/-- Newton integer-isqrt invariant `n < (midPIsqrtLoop fuel g n + 1) ^ 2` for every `fuel`. -/
theorem midPIsqrtLoop_lt_succ_sq :
    ∀ (fuel g n : ℕ), n < (g + 1) ^ 2 → n < (midPIsqrtLoop fuel g n + 1) ^ 2
  | 0, g, _, h => h
  | fuel + 1, g, n, h => by
      unfold midPIsqrtLoop
      cases hg0 : (g == 0)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hg_pos : 0 < g := by
          have hne : g ≠ 0 := beq_eq_false_iff_ne.mp hg0; omega
        cases hble : Nat.ble g ((g + n / g) / 2)
        · simp only [Bool.false_eq_true, ↓reduceIte]; set q := n / g; set g1 := (g + q) / 2
          refine midPIsqrtLoop_lt_succ_sq fuel g1 n ?_
          have hdiv : g * q + n % g = n := Nat.div_add_mod n g
          have hmod : n % g < g := Nat.mod_lt n hg_pos
          have hg1_div : 2 * g1 + (g + q) % 2 = g + q := Nat.div_add_mod (g + q) 2
          have hg1_mod : (g + q) % 2 < 2 := Nat.mod_lt (g + q) (by omega)
          have h2g1 : g + (q + 1) ≤ 2 * (g1 + 1) := (by omega)
          have h4n : 4 * n < 4 * g * (q + 1) := (by nlinarith)
          have hamgm : 4 * g * (q + 1) ≤ (g + (q + 1)) ^ 2 := by
            apply Int.ofNat_le.mp; push_cast; nlinarith [sq_nonneg ((g : ℤ) - ((q : ℤ) + 1))]
          have hsq_le : (g + (q + 1)) ^ 2 ≤ (2 * (g1 + 1)) ^ 2 := Nat.pow_le_pow_left h2g1 2
          nlinarith
        · simp only [↓reduceIte]; exact h
      · have hg_eq : g = 0 := beq_iff_eq.mp hg0; subst hg_eq; have hn0 : n = 0 := (by omega)
        subst hn0; simp
theorem midPUnpaddedZoomScaleHi15_nonneg (wt m : ℕ) : 0 ≤ midPUnpaddedZoomScaleHi15 wt m := by
  unfold midPUnpaddedZoomScaleHi15; by_cases hm : (m == 0) = true
  · rw [ite_eq_left hm]
  · rw [ite_eq_right hm]; simp only [midPLitNat_eq, Int.ofNat_eq_natCast]; exact Nat.cast_nonneg _
/-- Unconditional outward square bound `(wt: ℤ) * 10 ^ 30 ≤ (m: ℤ) * u ^ 2` for `wt ≤ m` and
  `0 < m` (holds with or without the optional `Nat.ble` fallback branch). -/
theorem midPUnpaddedZoomScaleHi15_sq_le {wt m : ℕ} (hwt_le : wt ≤ m) (hm_pos : 0 < m) :
    (wt : ℤ) * (wdScale : ℤ) ^ 2 ≤ (m : ℤ) * (midPUnpaddedZoomScaleHi15 wt m) ^ 2 := by
  unfold midPUnpaddedZoomScaleHi15
  have hm0 : (m == 0) = false := beq_eq_false_iff_ne.mpr hm_pos.ne'; rw [hm0]
  simp only [Bool.false_eq_true, ↓reduceIte, midPLitNat_eq]; set S : ℕ := 1000000000000000
  set num : ℕ := wt * S * S; set n : ℕ := num / m
  have hnum_le : num ≤ m * (S * S) := by
    dsimp only [num]; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right (S * S) hwt_le
  have hn_le : n ≤ S * S := Nat.div_le_of_le_mul (by linarith)
  have hn_lt_S1 : n < (S + 1) ^ 2 := (by nlinarith); set g : ℕ := midPIsqrtLoop 64 S n
  have hg_lt : n < (g + 1) ^ 2 := midPIsqrtLoop_lt_succ_sq 64 S n hn_lt_S1
  set isq : ℕ := if Nat.ble (g * g) n then g else g - 1; set uCand : ℕ := isq + 1
  have hn_lt_uCand : n < uCand * uCand := by
    dsimp only [uCand, isq]; by_cases hgg : Nat.ble (g * g) n
    · simp only [hgg, ↓reduceIte]; nlinarith
    · simp only [hgg, Bool.false_eq_true, ↓reduceIte]
      have hgt : n < g * g := (by rw [Nat.ble_eq] at hgg; omega)
      have hg1 : 1 ≤ g := (by nlinarith); have hsub : g - 1 + 1 = g := (by omega); rw [hsub]
      exact hgt
  have hdiv : m * n + num % m = num := Nat.div_add_mod num m
  have hmod : num % m < m := Nat.mod_lt num hm_pos
  have hnum_cand : num ≤ m * (uCand * uCand) := by
    have hn1 : n + 1 ≤ uCand * uCand := (by omega)
    have hm1 : m * (n + 1) ≤ m * (uCand * uCand) := Nat.mul_le_mul_left m hn1; nlinarith
  have hnum_n1 : num ≤ m * ((n + 1) * (n + 1)) := by
    have hn1 : n + 1 ≤ (n + 1) * (n + 1) := (by nlinarith)
    have hm1 : m * (n + 1) ≤ m * ((n + 1) * (n + 1)) := Nat.mul_le_mul_left m hn1; nlinarith
  have hwdS : (wdScale : ℤ) ^ 2 = ((S * S : ℕ) : ℤ) := (by unfold wdScale; dsimp only [S]; norm_num)
  have hnumZ : (wt : ℤ) * (wdScale : ℤ) ^ 2 = (num : ℤ) := by
    rw [hwdS]; dsimp only [num]; push_cast; ring
  rw [hnumZ]; split_ifs
  · change (num : ℤ) ≤ (m : ℤ) * ((uCand : ℤ) ^ 2); rw [sq]; exact_mod_cast hnum_cand
  · change (num : ℤ) ≤ (m : ℤ) * (((n + 1 : ℕ) : ℤ) ^ 2); rw [sq]; exact_mod_cast hnum_n1
/-- Unpadded zoom scale conversion `√((wt * 2 ^ (subN - p))) ≤ (uScale / 10 ^ 15) * √(2 ^
  subN)`. -/
theorem scale15_midPZoom_le {wt m p subN : ℕ} (hwt_le : wt ≤ m) (hm_pos : 0 < m) (hm : m = 2 ^ p)
    (hp : p ≤ subN) : (((π / 4) * √(((wt * 2 ^ (subN - p) : ℕ) : ℝ))) / wdScaleR) ≤
    ((midPUnpaddedZoomScaleHi15 wt m : ℝ) / wdScaleR) * (((π / 4) * √(2 ^ subN : ℝ)) /
    wdScaleR) := by
  have hB : 0 < wdScaleR := wdScaleR_pos; have hBeq : wdScaleR = (wdScale : ℝ) := rfl
  set u := midPUnpaddedZoomScaleHi15 wt m
  have hu_nn : 0 ≤ u := midPUnpaddedZoomScaleHi15_nonneg wt m
  have hsq_le := midPUnpaddedZoomScaleHi15_sq_le hwt_le hm_pos
  have hm_posR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hratio : √((wt : ℝ) / (m : ℝ)) ≤ (u : ℝ) / wdScaleR := by
    rw [Real.sqrt_le_iff]; refine ⟨div_nonneg (by exact_mod_cast hu_nn) hB.le, ?_⟩
    rw [div_pow, div_le_div_iff₀ hm_posR (pow_pos hB 2), hBeq, mul_comm ((u : ℝ) ^ 2) (m : ℝ)]
    dsimp only [u]; exact_mod_cast hsq_le
  have hpow_eq : ((wt * 2 ^ (subN - p) : ℕ) : ℝ) = ((wt : ℝ) / (m : ℝ)) * (2 ^ subN : ℝ) := by
    have hpow_nat : 2 ^ subN = 2 ^ p * 2 ^ (subN - p) := (by rw [← pow_add, Nat.add_sub_of_le hp])
    have hsub : (2 ^ subN : ℝ) = (m : ℝ) * (2 ^ (subN - p) : ℝ) := by
      rw [hm]; exact_mod_cast hpow_nat
    rw [hsub]; push_cast; field_simp [hm_posR.ne']
  have hsqrt_eq : √(((wt * 2 ^ (subN - p) : ℕ) : ℝ)) = √((wt : ℝ) / (m : ℝ)) * √(2 ^ subN : ℝ) := by
    rw [hpow_eq, Real.sqrt_mul (by positivity)]
  have hfac_nn : 0 ≤ ((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR :=
    div_nonneg (by positivity [Real.pi_pos]) hB.le
  calc (((π / 4) * √(((wt * 2 ^ (subN - p) : ℕ) : ℝ))) / wdScaleR)
      = √((wt : ℝ) / (m : ℝ)) * (((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR) := by rw [hsqrt_eq]; ring
    _ ≤ ((u : ℝ) / wdScaleR) * (((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR) :=
          mul_le_mul_of_nonneg_right hratio hfac_nn
/-- Full unpadded `wt = r - 1` zoom step-count angle enclosure and -normalized query bound
  for `210 ≤ subN` (`p ≤ 10`, `1 ≤ wt ≤ m`). -/
theorem ghMidPZoomStepCount_bounds {wt m p subN kzNum kzDen : ℕ} (hwt1 : 1 ≤ wt) (hwt_le : wt ≤ m)
    (hm_pos : 0 < m) (hm : m = 2 ^ p) (hp10 : p ≤ 10) (hsub : 210 ≤ subN) (hkzDen : 0 < kzDen) :
    let Dz : ℕ := wt * 2 ^ (subN - p); let θZoom : ℝ := Real.arcsin (1 / √(Dz : ℝ))
    let kZoom : ℕ := wdMidPStepCount Dz kzNum kzDen; let kzIV : WDIVal := wdRat (kzNum : ℤ) kzDen
    let qzSub : ℤ := wdDivCeil ((kzIV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
    let uScale : ℤ := midPUnpaddedZoomScaleHi15 wt m
    let qZoomHi : ℤ := wdDivCeil (qzSub * uScale) (wdScale : ℤ)
    let scale15 : ℝ := ((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR
    wdMem ((2 * (kZoom : ℝ) + 1) * θZoom) (max 0 (kzIV.1 - 1), kzIV.2 + 1) ∧ 0 ≤ qZoomHi ∧ ((kZoom +
      1 : ℕ) : ℝ) ≤ (qZoomHi : ℝ) * scale15 := by
  intro Dz θZoom kZoom kzIV qzSub uScale qZoomHi scale15; have hB : 0 < wdScaleR := wdScaleR_pos
  have hBZ : (0 : ℤ) < (wdScale : ℤ) := (by unfold wdScale; norm_num)
  have hsub_z : 200 ≤ subN - p := (by omega)
  have hDz : 2 ^ 200 ≤ Dz := by
    calc 2 ^ 200 ≤ 2 ^ (subN - p) := Nat.pow_le_pow_right (by omega) hsub_z
      _ = 1 * 2 ^ (subN - p) := (Nat.one_mul _).symm
      _ ≤ wt * 2 ^ (subN - p) := Nat.mul_le_mul_right _ hwt1
  obtain ⟨hmem, _, hqz_nn, hqz_bound⟩ :=
    ghRealDimStepCount_bounds (D := Dz) (aNum := kzNum) hDz hkzDen 1
  have hp_le : p ≤ subN := (by omega); have hsc_z := scale15_midPZoom_le hwt_le hm_pos hm hp_le
  have hu_nn : 0 ≤ uScale := midPUnpaddedZoomScaleHi15_nonneg wt m
  have hqzHi_nn : 0 ≤ qZoomHi := wdDivCeil_nonneg (mul_nonneg hqz_nn hu_nn) hBZ
  have hceil := le_wdDivCeil (a := qzSub * uScale) hBZ
  have hs15_nn : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
  refine ⟨hmem, hqzHi_nn, ?_⟩
  calc ((kZoom + 1 : ℕ) : ℝ)
      ≤ (qzSub : ℝ) * (((π / 4) * √(Dz : ℝ)) / wdScaleR) := by simpa using hqz_bound
    _ ≤ (qzSub : ℝ) * (((uScale : ℝ) / wdScaleR) * scale15) :=
          mul_le_mul_of_nonneg_left hsc_z (by exact_mod_cast hqz_nn)
    _ = (((qzSub * uScale : ℤ) : ℝ) / ((wdScale : ℤ) : ℝ)) * scale15 := by
          dsimp only [wdScaleR]; push_cast; ring
    _ ≤ (qZoomHi : ℝ) * scale15 := mul_le_mul_of_nonneg_right hceil hs15_nn
/- ## 4. `.getD`-Free CPS Tensor Zipper Soundness (`midPFast*` Enclosures) -/
private lemma wdMul_nonneg_and_hi_mono {x y z : WDIVal} (hx1 : 0 ≤ x.1) (hx12 : x.1 ≤ x.2) (hy1 : 0
    ≤ y.1) (hy12 : y.1 ≤ y.2) (hyz : y.2 ≤ z.2) : 0 ≤ (ghMulIV x y).1 ∧ (ghMulIV x y).2 ≤ (ghMulIV x
    z).2 := by
  have hx2 : 0 ≤ x.2 := hx1.trans hx12; have hy2 : 0 ≤ y.2 := hy1.trans hy12
  have hBZ : (0 : ℤ) < (wdScale : ℤ) := (by unfold wdScale; norm_num); rw [ghMulIV_eq, ghMulIV_eq]
  unfold wdMul; dsimp only; constructor
  · refine wdDivFloor_nonneg ?_ hBZ
    refine le_min (le_min (mul_nonneg hx1 hy1) (mul_nonneg hx1 hy2))
      (le_min (mul_nonneg hx2 hy1) (mul_nonneg hx2 hy2))
  · have hmax_xy : max (max (x.1 * y.1) (x.1 * y.2)) (max (x.2 * y.1) (x.2 * y.2)) ≤ x.2 * z.2 := by
      have h11 : x.1 * y.1 ≤ x.2 * y.2 := mul_le_mul hx12 hy12 hy1 hx2
      have h12 : x.1 * y.2 ≤ x.2 * y.2 := mul_le_mul_of_nonneg_right hx12 hy2
      have h21 : x.2 * y.1 ≤ x.2 * y.2 := mul_le_mul_of_nonneg_left hy12 hx2
      have h22 : x.2 * y.2 ≤ x.2 * z.2 := mul_le_mul_of_nonneg_left hyz hx2
      exact max_le (max_le (h11.trans h22) (h12.trans h22)) (max_le (h21.trans h22) h22)
    have hxz_le : x.2 * z.2 ≤ max (max (x.1 * z.1) (x.1 * z.2)) (max (x.2 * z.1) (x.2 * z.2)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hm := hmax_xy.trans hxz_le; unfold wdDivCeil
    exact neg_le_neg (Int.ediv_le_ediv hBZ (neg_le_neg hm))
private lemma wdMem_lo_le_hi {r : ℝ} {iv : WDIVal} (h : wdMem r iv) : iv.1 ≤ iv.2 := by
  have hB : 0 < wdScaleR := wdScaleR_pos
  have hle : (iv.1 : ℝ) / wdScaleR ≤ (iv.2 : ℝ) / wdScaleR := h.1.trans h.2
  have h1 : (iv.1 : ℝ) ≤ (iv.2 : ℝ) := (div_le_div_iff_of_pos_right hB).mp hle; exact_mod_cast h1
theorem midPFastDickeStepVec_mem (deg : ℕ) {c s : ℝ} {cIV sIV : WDIVal} (hc : wdMem c cIV) (hs :
    wdMem s sIV) {u : ℕ → ℂ} {uList : List WDCVal} (hu : ∀ w, wdCMem (u w) (uList.getD w wdCZero)) :
    ∀ w', wdCMem (dickeStep deg (c : ℂ) (s : ℂ) u w') ((midPFastDickeStepVec deg cIV sIV uList).getD
    w' wdCZero) := by
  intro w'; rw [midPFastDickeStepVec_eq]; exact dickeStepCIVVec_mem deg hc hs hu w'
theorem midPOneHot0_mem (deg : ℕ) : ∀ w, wdCMem (if w = 0 then (1 : ℂ) else 0) ((midPOneHot0 (deg +
    1)).getD w wdCZero) := by
  intro w
  cases w with
  | zero => simp only [↓reduceIte, midPOneHot0, List.getD_cons_zero]; exact wdCMem_one
  | succ w' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, midPOneHot0, List.getD_cons_succ]
      by_cases hw : w' < deg
      · simp [List.getD_eq_getElem?_getD, hw, wdCMem_zero]
      · simp [List.getD_eq_getElem?_getD, hw, wdCMem_zero]
private lemma midPUnconsC1_eq {α : Type*} (gs : List WDCVal) (k : WDCVal → List WDCVal → α) :
    midPUnconsC1 gs k = k (gs.headD wdCOne) gs.tail := by cases gs <;> rfl
theorem midPZipRotSub_mem :
    ∀ (n : ℕ) {c s : ℝ} {cIV sIV : WDIVal}, wdMem c cIV → wdMem s sIV →
      ∀ {u0 u1 : ℕ → ℂ} {m0 m1 : List WDCVal},
        (∀ w < n, wdCMem (u0 w) (m0.getD w wdCZero)) →
        (∀ w < n, wdCMem (u1 w) (m1.getD w wdCZero)) →
        ∀ w < n, wdCMem ((c : ℂ) * u0 w - (s : ℂ) * u1 w)
          ((midPZipRotSub n cIV sIV m0 m1).getD w wdCZero)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, hw => by omega
  | n + 1, c, s, cIV, sIV, hc, hs, u0, u1, m0, m1, h0, h1, w, hw => by
      simp only [midPZipRotSub, midPUnconsC_eq]
      cases w with
      | zero =>
          rw [List.getD_cons_zero, midPFastCSub_eq, midPFastCRMul_eq, midPFastCRMul_eq,
            midPList_headD_eq_getD_zero, midPList_headD_eq_getD_zero]
          exact wdCMem_sub (wdCMem_rmul hc (h0 0 (by omega)))
            (wdCMem_rmul hs (h1 0 (by omega)))
      | succ w' =>
          rw [List.getD_cons_succ]
          exact midPZipRotSub_mem n hc hs
            (u0 := fun j ↦ u0 (j + 1)) (u1 := fun j ↦ u1 (j + 1))
            (m0 := m0.tail) (m1 := m1.tail)
            (fun j hj ↦ by rw [midPList_tail_getD]; exact h0 (j + 1) (by omega))
            (fun j hj ↦ by rw [midPList_tail_getD]; exact h1 (j + 1) (by omega))
            w' (by omega)
theorem midPZipRotAdd_mem :
    ∀ (n : ℕ) {c s : ℝ} {cIV sIV : WDIVal}, wdMem c cIV → wdMem s sIV →
      ∀ {u0 u1 : ℕ → ℂ} {m0 m1 : List WDCVal},
        (∀ w < n, wdCMem (u0 w) (m0.getD w wdCZero)) →
        (∀ w < n, wdCMem (u1 w) (m1.getD w wdCZero)) →
        ∀ w < n, wdCMem ((s : ℂ) * u0 w + (c : ℂ) * u1 w)
          ((midPZipRotAdd n cIV sIV m0 m1).getD w wdCZero)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, hw => by omega
  | n + 1, c, s, cIV, sIV, hc, hs, u0, u1, m0, m1, h0, h1, w, hw => by
      simp only [midPZipRotAdd, midPUnconsC_eq]
      cases w with
      | zero =>
          rw [List.getD_cons_zero, midPFastCAdd_eq, midPFastCRMul_eq, midPFastCRMul_eq,
            midPList_headD_eq_getD_zero, midPList_headD_eq_getD_zero]
          exact wdCMem_add (wdCMem_rmul hs (h0 0 (by omega)))
            (wdCMem_rmul hc (h1 0 (by omega)))
      | succ w' =>
          rw [List.getD_cons_succ]
          exact midPZipRotAdd_mem n hc hs
            (u0 := fun j ↦ u0 (j + 1)) (u1 := fun j ↦ u1 (j + 1))
            (m0 := m0.tail) (m1 := m1.tail)
            (fun j hj ↦ by rw [midPList_tail_getD]; exact h0 (j + 1) (by omega))
            (fun j hj ↦ by rw [midPList_tail_getD]; exact h1 (j + 1) (by omega))
            w' (by omega)
theorem midPDampShift0Aux_mem :
    ∀ (k : ℕ) {phs : List GaussPyth} {gs : List WDCVal},
      (∀ i, wdCMem (phs.getD i gaussOne).val (gs.getD i wdCOne)) →
      ∀ {z : ℕ → ℂ} {xs : List WDCVal},
        (∀ w < k, wdCMem (z w) (xs.getD w wdCZero)) →
        ∀ w, wdCMem (if w < k then (phs.getD w gaussOne).val * z w else 0)
          ((midPDampShift0Aux k gs xs).getD w wdCZero)
  | 0, _, _, _, _, _, _, w => by
      simp [midPDampShift0Aux, wdCMem_zero]
  | k + 1, phs, gs, hgs, z, xs, hxs, w => by
      simp only [midPDampShift0Aux, midPUnconsC1_eq, midPUnconsC_eq]
      cases w with
      | zero =>
          have hlt : 0 < k + 1 := by omega
          rw [ite_eq_left hlt, List.getD_cons_zero, midPFastCMul_eq, midPList_headD_eq_getD_zero,
            midPList_headD_eq_getD_zero]; exact wdCMem_mul (hgs 0) (hxs 0 hlt)
      | succ w' =>
          have hiff : (w' + 1 < k + 1) ↔ (w' < k) := (by omega)
          have hite : (if w' + 1 < k + 1 then (phs.getD (w' + 1) gaussOne).val * z (w' + 1) else 0)
            = (if w' < k then (phs.tail.getD w' gaussOne).val * z (w' + 1) else 0) := by
            by_cases hw' : w' < k
            · rw [ite_eq_left (hiff.mpr hw'), ite_eq_left hw', midPList_tail_getD]
            · rw [ite_eq_right (mt hiff.mp hw'), ite_eq_right hw']
          rw [hite, List.getD_cons_succ]
          exact midPDampShift0Aux_mem k (phs := phs.tail) (gs := gs.tail)
            (fun i ↦ by rw [midPList_tail_getD, midPList_tail_getD]; exact hgs (i + 1))
            (z := fun j ↦ z (j + 1)) (xs := xs.tail)
            (fun j hj ↦ by rw [midPList_tail_getD]; exact hxs (j + 1) (by omega)) w'
theorem midPFastDamp2Row0_mem (deg1 : ℕ) {pr : GHMidPProbe} {gIVs : List WDCVal} (hg : ∀ i, wdCMem
    (pr.phases.getD i gaussOne).val (gIVs.getD i wdCOne)) {z0 : ℕ → ℂ} {r0 : List WDCVal} (hr0 : ∀
    w₁ ≤ deg1, wdCMem (z0 w₁) (r0.getD w₁ wdCZero)) : ∀ w₁, wdCMem (ghMidPDamp2Row0 deg1 pr z0 w₁)
    ((midPFastDamp2Row0 deg1 gIVs r0).getD w₁ wdCZero) := by
  intro w₁; simp only [midPFastDamp2Row0, midPUnconsC_eq]
  cases w₁ with
  | zero =>
      simp only [ghMidPDamp2Row0, ↓reduceIte]; rw [List.getD_cons_zero, midPList_headD_eq_getD_zero]
      exact hr0 0 (Nat.zero_le _)
  | succ w' =>
      have hd : ghMidPDamp2Row0 deg1 pr z0 (w' + 1) =
          (if w' < deg1 then (pr.phases.getD w' gaussOne).val * z0 (w' + 1) else 0) := by
        unfold ghMidPDamp2Row0; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        by_cases hw : w' < deg1
        · rw [ite_eq_left (by omega : w' + 1 ≤ deg1), ite_eq_left hw]
        · rw [ite_eq_right (by omega : ¬(w' + 1 ≤ deg1)), ite_eq_right hw]
      rw [hd, List.getD_cons_succ]
      exact midPDampShift0Aux_mem deg1 (phs := pr.phases) (gs := gIVs) hg (z := fun j ↦ z0 (j + 1))
        (xs := r0.tail) (fun j hj ↦ by rw [midPList_tail_getD]; exact hr0 (j + 1) (by omega)) w'
theorem midPFastDamp2Row1_mem (deg1 : ℕ) {pr : GHMidPProbe} {gIVs : List WDCVal} (hg : ∀ i, wdCMem
    (pr.phases.getD i gaussOne).val (gIVs.getD i wdCOne)) {z1 : ℕ → ℂ} {r1 : List WDCVal} (hr1 : ∀
    w₁ ≤ deg1, wdCMem (z1 w₁) (r1.getD w₁ wdCZero)) : ∀ w₁, wdCMem (ghMidPDamp2Row1 deg1 pr z1 w₁)
    ((midPFastDamp2Row1 deg1 gIVs r1).getD w₁ wdCZero) := by
  intro w₁; have hd : ghMidPDamp2Row1 deg1 pr z1 w₁ =
      (if w₁ < deg1 + 1 then (pr.phases.getD w₁ gaussOne).val * z1 w₁ else 0) := by
    unfold ghMidPDamp2Row1; by_cases hw : w₁ ≤ deg1
    · rw [ite_eq_left hw, ite_eq_left (by omega : w₁ < deg1 + 1)]
    · rw [ite_eq_right hw, ite_eq_right (by omega : ¬(w₁ < deg1 + 1))]
  rw [hd]; unfold midPFastDamp2Row1; have hn : Nat.add deg1 1 = deg1 + 1 := rfl; rw [hn]
  exact midPDampShift0Aux_mem (deg1 + 1) hg (fun j hj ↦ hr1 j (by omega)) w₁
theorem midPFastDampTwoPair2_mem (deg1 : ℕ) {pr : GHMidPProbe} {gIVs : List WDCVal} (hg : ∀ i,
    wdCMem (pr.phases.getD i gaussOne).val (gIVs.getD i wdCOne)) {z2 : ℕ → ℂ} {r2 : List WDCVal}
    (hr2 : ∀ w₁ ≤ deg1, wdCMem (z2 w₁) (r2.getD w₁ wdCZero)) : ∀ w₁, wdCMem (ghMidPDampTwoPair2 deg1
    pr z2 w₁) ((midPFastDamp2Row1 deg1 gIVs.tail r2).getD w₁ wdCZero) := by
  intro w₁; have hd : ghMidPDampTwoPair2 deg1 pr z2 w₁ =
      (if w₁ < deg1 + 1 then (pr.phases.tail.getD w₁ gaussOne).val * z2 w₁ else 0) := by
    unfold ghMidPDampTwoPair2; rw [midPList_tail_getD]; by_cases hw : w₁ ≤ deg1
    · rw [ite_eq_left hw, ite_eq_left (by omega : w₁ < deg1 + 1)]
    · rw [ite_eq_right hw, ite_eq_right (by omega : ¬(w₁ < deg1 + 1))]
  rw [hd]; unfold midPFastDamp2Row1; have hn : Nat.add deg1 1 = deg1 + 1 := rfl; rw [hn]
  exact midPDampShift0Aux_mem (deg1 + 1) (phs := pr.phases.tail)
    (fun i ↦ by rw [midPList_tail_getD, midPList_tail_getD]; exact hg (i + 1))
    (fun j hj ↦ hr2 j (by omega)) w₁
theorem midPFastDampUTail_mem :
    ∀ (k : ℕ) {c : ℝ} {cTop : WDIVal}, wdMem c cTop →
      ∀ {phs : List GaussPyth} {gs : List WDCVal},
        (∀ i, wdCMem (phs.getD i gaussOne).val (gs.getD i wdCOne)) →
        ∀ {z : ℕ → ℂ} {xs : List WDCVal},
          (∀ w ≤ k, wdCMem (z w) (xs.getD w wdCZero)) →
          ∀ w, wdCMem
            (if w < k then (phs.getD w gaussOne).val * z w
             else if w = k then (c : ℂ) * (phs.getD w gaussOne).val * z w
             else 0)
            ((midPFastDampUTail k cTop gs xs).getD w wdCZero)
  | 0, c, cTop, hc, phs, gs, hgs, z, xs, hxs, w => by
      simp only [midPFastDampUTail, midPUnconsC1_eq, midPUnconsC_eq]
      cases w with
      | zero =>
          simp only [lt_self_iff_false, ↓reduceIte]
          have hmul : (c : ℂ) * (phs.getD 0 gaussOne).val * z 0 =
              (c : ℂ) * ((phs.getD 0 gaussOne).val * z 0) := by ring
          rw [hmul, List.getD_cons_zero, midPFastCRMul_eq, midPFastCMul_eq,
            midPList_headD_eq_getD_zero, midPList_headD_eq_getD_zero]
          exact wdCMem_rmul hc (wdCMem_mul (hgs 0) (hxs 0 le_rfl))
      | succ w' =>
          have h1 : ¬(w' + 1 < 0) := (by omega); have h2 : ¬(w' + 1 = 0) := (by omega)
          rw [ite_eq_right h1, ite_eq_right h2, List.getD_cons_succ, List.getD_nil]
          exact wdCMem_zero
  | k + 1, c, cTop, hc, phs, gs, hgs, z, xs, hxs, w => by
      simp only [midPFastDampUTail, midPUnconsC1_eq, midPUnconsC_eq]
      cases w with
      | zero =>
          have hlt : 0 < k + 1 := (by omega)
          rw [ite_eq_left hlt, List.getD_cons_zero, midPFastCMul_eq, midPList_headD_eq_getD_zero,
            midPList_headD_eq_getD_zero]; exact wdCMem_mul (hgs 0) (hxs 0 (Nat.zero_le _))
      | succ w' =>
          have hite : (if w' + 1 < k + 1 then (phs.getD (w' + 1) gaussOne).val * z (w' + 1) else if
            w' + 1 = k + 1 then (c : ℂ) * (phs.getD (w' + 1) gaussOne).val * z (w' + 1) else 0) =
            (if w' < k then (phs.tail.getD w' gaussOne).val * z (w' + 1) else if w' = k then (c :
            ℂ) * (phs.tail.getD w' gaussOne).val * z (w' + 1) else 0) := by
            rw [midPList_tail_getD]; by_cases h1 : w' < k
            · rw [ite_eq_left (by omega : w' + 1 < k + 1), ite_eq_left h1]
            · rw [ite_eq_right (by omega : ¬(w' + 1 < k + 1)), ite_eq_right h1]
              by_cases h2 : w' = k
              · rw [ite_eq_left (by omega : w' + 1 = k + 1), ite_eq_left h2]
              · rw [ite_eq_right (by omega : ¬(w' + 1 = k + 1)), ite_eq_right h2]
          rw [hite, List.getD_cons_succ]
          exact midPFastDampUTail_mem k hc (phs := phs.tail) (gs := gs.tail)
            (fun i ↦ by rw [midPList_tail_getD, midPList_tail_getD]; exact hgs (i + 1))
            (z := fun j ↦ z (j + 1)) (xs := xs.tail)
            (fun j hj ↦ by rw [midPList_tail_getD]; exact hxs (j + 1) (by omega)) w'
theorem midPFastDampUAux_mem :
    ∀ (k : ℕ) {c : ℝ} {cTop : WDIVal}, wdMem c cTop →
      ∀ {phs : List GaussPyth} {gs : List WDCVal},
        (∀ i, wdCMem (phs.getD i gaussOne).val (gs.getD i wdCOne)) →
        ∀ {z : ℕ → ℂ} {xs : List WDCVal},
          (∀ w < k, wdCMem (z w) (xs.getD w wdCZero)) →
          ∀ w, wdCMem
            (if w + 1 < k then (phs.getD w gaussOne).val * z w
             else if w + 1 = k then (c : ℂ) * (phs.getD w gaussOne).val * z w
             else 0)
            ((midPFastDampUAux k cTop gs xs).getD w wdCZero)
  | 0, _, _, _, _, _, _, _, _, _, w => by
      have h1 : ¬(w + 1 < 0) := by omega
      have h2 : ¬(w + 1 = 0) := (by omega); rw [ite_eq_right h1, ite_eq_right h2]
      simp [midPFastDampUAux, wdCMem_zero]
  | k + 1, c, cTop, hc, phs, gs, hgs, z, xs, hxs, w => by
      have hite : (if w + 1 < k + 1 then (phs.getD w gaussOne).val * z w else if w + 1 = k + 1 then
        (c : ℂ) * (phs.getD w gaussOne).val * z w else 0) = (if w < k then (phs.getD w
        gaussOne).val * z w else if w = k then (c : ℂ) * (phs.getD w gaussOne).val * z w else
        0) := by
        by_cases h1 : w < k
        · rw [ite_eq_left (by omega : w + 1 < k + 1), ite_eq_left h1]
        · rw [ite_eq_right (by omega : ¬(w + 1 < k + 1)), ite_eq_right h1]; by_cases h2 : w = k
          · rw [ite_eq_left (by omega : w + 1 = k + 1), ite_eq_left h2]
          · rw [ite_eq_right (by omega : ¬(w + 1 = k + 1)), ite_eq_right h2]
      rw [hite]; unfold midPFastDampUAux
      exact midPFastDampUTail_mem k hc hgs (fun j hj ↦ hxs j (by omega)) w
theorem midPFastDampU_mem (r : ℕ) {pr : GHMidPProbe} {gIVs : List WDCVal} {cTop : WDIVal} (hc :
    wdMem pr.rotTop.cVal cTop) (hg : ∀ i, wdCMem (pr.phases.getD i gaussOne).val (gIVs.getD i
    wdCOne)) {u : ℕ → ℂ} {uVec : List WDCVal} (hu : ∀ w ≤ r, wdCMem (u w) (uVec.getD w wdCZero)) : ∀
    w, wdCMem (ghMidPDampAmp r pr u w) ((midPFastDampU r gIVs cTop uVec).getD w wdCZero) := by
  intro w; simp only [midPFastDampU, midPUnconsC_eq]
  cases w with
  | zero =>
      simp only [ghMidPDampAmp, ↓reduceIte]; rw [List.getD_cons_zero, midPList_headD_eq_getD_zero]
      exact hu 0 (Nat.zero_le _)
  | succ w' =>
      have hd : ghMidPDampAmp r pr u (w' + 1) = (if w' + 1 < r then (pr.phases.getD w'
        gaussOne).val * u (w' + 1) else if w' + 1 = r then (pr.rotTop.cVal : ℂ) * (pr.phases.getD w'
        gaussOne).val * u (w' + 1) else 0) := by
        unfold ghMidPDampAmp; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        by_cases h1 : w' + 1 < r
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1]; by_cases h2 : w' + 1 = r
          · subst h2; simp
          · rw [ite_eq_right h2, ite_eq_right h2]
      rw [hd, List.getD_cons_succ]
      exact midPFastDampUAux_mem r hc (phs := pr.phases) (gs := gIVs) hg (z := fun j ↦ u (j + 1))
        (xs := uVec.tail) (fun j hj ↦ by rw [midPList_tail_getD]; exact hu (j + 1) (by omega)) w'
theorem midPFastStep2RowCPS_mem {α : Type*} (deg1 : ℕ) {θ₁ θC : ℝ} {pr : GHMidPProbe} {gIVs : List
    WDCVal} {c1 s1 cC sC : WDIVal} (hc1 : wdMem (Real.cos (2 * (pr.kNext : ℝ) * θ₁)) c1) (hs1 :
    wdMem (Real.sin (2 * (pr.kNext : ℝ) * θ₁)) s1) (hcC : wdMem (Real.cos (2 * (pr.kNext : ℝ) * θC))
    cC) (hsC : wdMem (Real.sin (2 * (pr.kNext : ℝ) * θC)) sC) (hg : ∀ i, wdCMem (pr.phases.getD i
    gaussOne).val (gIVs.getD i wdCOne)) {z : (ℕ → ℂ) × (ℕ → ℂ)} {r0 r1 : List WDCVal} (hz0 : ∀ w₁ ≤
    deg1, wdCMem (z.1 w₁) (r0.getD w₁ wdCZero)) (hz1 : ∀ w₁ ≤ deg1, wdCMem (z.2 w₁) (r1.getD w₁
    wdCZero)) (k : List WDCVal → List WDCVal → α) : ∃ n0 n1 : List WDCVal, midPFastStep2RowCPS deg1
    gIVs c1 s1 cC sC r0 r1 k = k n0 n1 ∧ (∀ w₁ ≤ deg1, wdCMem ((ghMidPProbeNext2Row deg1 θ₁ θC pr
    z).1 w₁) (n0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ deg1, wdCMem ((ghMidPProbeNext2Row deg1 θ₁ θC pr z).2
    w₁) (n1.getD w₁ wdCZero)) := by
  unfold midPFastStep2RowCPS; simp only [midPSeqCIVList_eq]
  set d0 := midPFastDamp2Row0 deg1 gIVs r0; set d1 := midPFastDamp2Row1 deg1 gIVs r1
  set m0 := midPFastDickeStepVec deg1 c1 s1 d0; set m1 := midPFastDickeStepVec deg1 c1 s1 d1
  have hn : Nat.add deg1 1 = deg1 + 1 := rfl; set n0 := midPZipRotSub (Nat.add deg1 1) cC sC m0 m1
  set n1 := midPZipRotAdd (Nat.add deg1 1) cC sC m0 m1
  have hd0 := midPFastDamp2Row0_mem deg1 hg hz0; have hd1 := midPFastDamp2Row1_mem deg1 hg hz1
  have hm0 := midPFastDickeStepVec_mem deg1 hc1 hs1 hd0
  have hm1 := midPFastDickeStepVec_mem deg1 hc1 hs1 hd1
  refine ⟨n0, n1, rfl, fun w₁ hw₁ ↦ ?_, fun w₁ hw₁ ↦ ?_⟩
  · dsimp only [n0]; rw [hn]
    exact midPZipRotSub_mem (deg1 + 1) hcC hsC (fun j _ ↦ hm0 j) (fun j _ ↦ hm1 j) w₁ (by omega)
  · dsimp only [n1]; rw [hn]
    exact midPZipRotAdd_mem (deg1 + 1) hcC hsC (fun j _ ↦ hm0 j) (fun j _ ↦ hm1 j) w₁ (by omega)
theorem midPDicke2Cols_mem : ∀ (n : ℕ) {c s : ℝ} {c2 s2 : WDIVal}, wdMem c c2 → wdMem s s2 → ∀ {f0
    f1 f2 : ℕ → ℂ} {r0 r1 r2 : List WDCVal}, (∀ w < n, wdCMem (f0 w) (r0.getD w wdCZero)) → (∀ w <
    n, wdCMem (f1 w) (r1.getD w wdCZero)) → (∀ w < n, wdCMem (f2 w) (r2.getD w wdCZero)) →
        let cols := midPDicke2Cols n c2 s2 r0 r1 r2
        let col (w j : ℕ) : ℂ := match j with | 0 => f0 w | 1 => f1 w | _ => f2 w
        (∀ w < n, wdCMem (dickeStep 2 (c : ℂ) (s : ℂ) (col w) 0) (cols.1.getD w wdCZero)) ∧
        (∀ w < n, wdCMem (dickeStep 2 (c : ℂ) (s : ℂ) (col w) 1) (cols.2.1.getD w wdCZero)) ∧
        (∀ w < n, wdCMem (dickeStep 2 (c : ℂ) (s : ℂ) (col w) 2) (cols.2.2.getD w wdCZero))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨fun _ h ↦ by omega, fun _ h ↦ by omega, fun _ h ↦ by omega⟩
  | n + 1, c, s, c2, s2, hc, hs, f0, f1, f2, r0, r1, r2, h0, h1, h2 => by
      have ha : wdCMem (f0 0) (r0.headD wdCZero) := by
        rw [midPList_headD_eq_getD_zero]; exact h0 0 (by omega)
      have hb : wdCMem (f1 0) (r1.headD wdCZero) := by
        rw [midPList_headD_eq_getD_zero]; exact h1 0 (by omega)
      have hd : wdCMem (f2 0) (r2.headD wdCZero) := by
        rw [midPList_headD_eq_getD_zero]; exact h2 0 (by omega)
      let col0 (j : ℕ) : ℂ := match j with | 0 => f0 0 | 1 => f1 0 | _ => f2 0
      have hd2_0 : dickeStep 2 (c : ℂ) (s : ℂ) col0 0 = (c : ℂ) * ((c : ℂ) * f0 0 - (s : ℂ) * f1
        0) - (s : ℂ) * ((c : ℂ) * f1 0 - (s : ℂ) * f2 0) := by
        simp [dickeStep, col0]
      have hd2_1 : dickeStep 2 (c : ℂ) (s : ℂ) col0 1 = (c : ℂ) * ((s : ℂ) * f0 0 + (c : ℂ) * f1
        0) - (s : ℂ) * ((s : ℂ) * f1 0 + (c : ℂ) * f2 0) := by
        simp [dickeStep, col0]
      have hd2_2 : dickeStep 2 (c : ℂ) (s : ℂ) col0 2 = (s : ℂ) * ((s : ℂ) * f0 0 + (c : ℂ) * f1
        0) + (c : ℂ) * ((s : ℂ) * f1 0 + (c : ℂ) * f2 0) := by
        simp [dickeStep, col0]
      set aIV := r0.headD wdCZero; set bIV := r1.headD wdCZero; set dIV := r2.headD wdCZero
      set m00 := midPFastCSub (midPFastCRMul c2 aIV) (midPFastCRMul s2 bIV)
      set m01 := midPFastCAdd (midPFastCRMul s2 aIV) (midPFastCRMul c2 bIV)
      set m10 := midPFastCSub (midPFastCRMul c2 bIV) (midPFastCRMul s2 dIV)
      set m11 := midPFastCAdd (midPFastCRMul s2 bIV) (midPFastCRMul c2 dIV)
      have hm00 : wdCMem ((c : ℂ) * f0 0 - (s : ℂ) * f1 0) m00 := by
        dsimp only [m00]; rw [midPFastCSub_eq, midPFastCRMul_eq, midPFastCRMul_eq]
        exact wdCMem_sub (wdCMem_rmul hc ha) (wdCMem_rmul hs hb)
      have hm01 : wdCMem ((s : ℂ) * f0 0 + (c : ℂ) * f1 0) m01 := by
        dsimp only [m01]; rw [midPFastCAdd_eq, midPFastCRMul_eq, midPFastCRMul_eq]
        exact wdCMem_add (wdCMem_rmul hs ha) (wdCMem_rmul hc hb)
      have hm10 : wdCMem ((c : ℂ) * f1 0 - (s : ℂ) * f2 0) m10 := by
        dsimp only [m10]; rw [midPFastCSub_eq, midPFastCRMul_eq, midPFastCRMul_eq]
        exact wdCMem_sub (wdCMem_rmul hc hb) (wdCMem_rmul hs hd)
      have hm11 : wdCMem ((s : ℂ) * f1 0 + (c : ℂ) * f2 0) m11 := by
        dsimp only [m11]; rw [midPFastCAdd_eq, midPFastCRMul_eq, midPFastCRMul_eq]
        exact wdCMem_add (wdCMem_rmul hs hb) (wdCMem_rmul hc hd)
      have hy0 : wdCMem (dickeStep 2 (c : ℂ) (s : ℂ) col0 0)
          (midPFastCSub (midPFastCRMul c2 m00) (midPFastCRMul s2 m10)) := by
        rw [hd2_0, midPFastCSub_eq, midPFastCRMul_eq, midPFastCRMul_eq]
        exact wdCMem_sub (wdCMem_rmul hc hm00) (wdCMem_rmul hs hm10)
      have hy1 : wdCMem (dickeStep 2 (c : ℂ) (s : ℂ) col0 1)
          (midPFastCSub (midPFastCRMul c2 m01) (midPFastCRMul s2 m11)) := by
        rw [hd2_1, midPFastCSub_eq, midPFastCRMul_eq, midPFastCRMul_eq]
        exact wdCMem_sub (wdCMem_rmul hc hm01) (wdCMem_rmul hs hm11)
      have hy2 : wdCMem (dickeStep 2 (c : ℂ) (s : ℂ) col0 2)
          (midPFastCAdd (midPFastCRMul s2 m01) (midPFastCRMul c2 m11)) := by
        rw [hd2_2, midPFastCAdd_eq, midPFastCRMul_eq, midPFastCRMul_eq]
        exact wdCMem_add (wdCMem_rmul hs hm01) (wdCMem_rmul hc hm11)
      have ih := midPDicke2Cols_mem n hc hs
        (f0 := fun j ↦ f0 (j + 1)) (f1 := fun j ↦ f1 (j + 1)) (f2 := fun j ↦ f2 (j + 1))
        (r0 := r0.tail) (r1 := r1.tail) (r2 := r2.tail)
        (fun j hj ↦ by rw [midPList_tail_getD]; exact h0 (j + 1) (by omega))
        (fun j hj ↦ by rw [midPList_tail_getD]; exact h1 (j + 1) (by omega))
        (fun j hj ↦ by rw [midPList_tail_getD]; exact h2 (j + 1) (by omega))
      have hcols : midPDicke2Cols (n + 1) c2 s2 r0 r1 r2 = (midPFastCSub (midPFastCRMul c2 m00)
        (midPFastCRMul s2 m10) :: (midPDicke2Cols n c2 s2 r0.tail r1.tail r2.tail).1, midPFastCSub
        (midPFastCRMul c2 m01) (midPFastCRMul s2 m11) :: (midPDicke2Cols n c2 s2 r0.tail r1.tail
        r2.tail).2.1, midPFastCAdd (midPFastCRMul s2 m01) (midPFastCRMul c2 m11) :: (midPDicke2Cols
        n c2 s2 r0.tail r1.tail r2.tail).2.2) := by
        cases r0 <;> cases r1 <;> cases r2
        all_goals
          simp only [midPDicke2Cols, midPUnconsC, midPSeqCIV_eq, List.headD, List.tail,
            aIV, bIV, dIV, m00, m01, m10, m11]
      dsimp only; rw [hcols]; refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · cases w with
        | zero => simpa [List.getD_cons_zero] using hy0
        | succ w' => simpa [List.getD_cons_succ] using ih.1 w' (by omega)
      · cases w with
        | zero => simpa [List.getD_cons_zero] using hy1
        | succ w' => simpa [List.getD_cons_succ] using ih.2.1 w' (by omega)
      · cases w with
        | zero => simpa [List.getD_cons_zero] using hy2
        | succ w' => simpa [List.getD_cons_succ] using ih.2.2 w' (by omega)
theorem midPFastStepTwoPairCPS_mem {α : Type*} (deg1 : ℕ) {θ₁ θ₂ : ℝ} {pr : GHMidPProbe} {gIVs :
    List WDCVal} {c1 s1 c2 s2 : WDIVal} (hc1 : wdMem (Real.cos (2 * (pr.kNext : ℝ) * θ₁)) c1) (hs1 :
    wdMem (Real.sin (2 * (pr.kNext : ℝ) * θ₁)) s1) (hc2 : wdMem (Real.cos (2 * (pr.kNext : ℝ) * θ₂))
    c2) (hs2 : wdMem (Real.sin (2 * (pr.kNext : ℝ) * θ₂)) s2) (hg : ∀ i, wdCMem (pr.phases.getD i
    gaussOne).val (gIVs.getD i wdCOne)) {z : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ)} {tp0 tp1 tp2 : List
    WDCVal} (hz0 : ∀ w₁ ≤ deg1, wdCMem (z.1 w₁) (tp0.getD w₁ wdCZero)) (hz1 : ∀ w₁ ≤ deg1, wdCMem
    (z.2.1 w₁) (tp1.getD w₁ wdCZero)) (hz2 : ∀ w₁ ≤ deg1, wdCMem (z.2.2 w₁) (tp2.getD w₁ wdCZero))
    (k : List WDCVal → List WDCVal → List WDCVal → α) : ∃ n0 n1 n2 : List WDCVal,
    midPFastStepTwoPairCPS deg1 gIVs c1 s1 c2 s2 tp0 tp1 tp2 k = k n0 n1 n2 ∧ (∀ w₁ ≤ deg1, wdCMem
    ((ghMidPProbeNextTwoPair deg1 θ₁ θ₂ pr z).1 w₁) (n0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ deg1, wdCMem
    ((ghMidPProbeNextTwoPair deg1 θ₁ θ₂ pr z).2.1 w₁) (n1.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ deg1, wdCMem
    ((ghMidPProbeNextTwoPair deg1 θ₁ θ₂ pr z).2.2 w₁) (n2.getD w₁ wdCZero)) := by
  unfold midPFastStepTwoPairCPS; simp only [midPSeqCIVList_eq]
  set d0 := midPFastDamp2Row0 deg1 gIVs tp0; set d1 := midPFastDamp2Row1 deg1 gIVs tp1
  set d2 := midPFastDamp2Row1 deg1 gIVs.tail tp2; set m0 := midPFastDickeStepVec deg1 c1 s1 d0
  set m1 := midPFastDickeStepVec deg1 c1 s1 d1; set m2 := midPFastDickeStepVec deg1 c1 s1 d2
  have hn : Nat.add deg1 1 = deg1 + 1 := rfl; have hd0 := midPFastDamp2Row0_mem deg1 hg hz0
  have hd1 := midPFastDamp2Row1_mem deg1 hg hz1; have hd2 := midPFastDampTwoPair2_mem deg1 hg hz2
  have hm0 := midPFastDickeStepVec_mem deg1 hc1 hs1 hd0
  have hm1 := midPFastDickeStepVec_mem deg1 hc1 hs1 hd1
  have hm2 := midPFastDickeStepVec_mem deg1 hc1 hs1 hd2
  have hcols := midPDicke2Cols_mem (deg1 + 1) hc2 hs2
    (fun j _ ↦ hm0 j) (fun j _ ↦ hm1 j) (fun j _ ↦ hm2 j)
  rcases hpair : midPDicke2Cols (Nat.add deg1 1) c2 s2 m0 m1 m2 with ⟨n0, n1, n2⟩; rw [hn] at hpair
  refine ⟨n0, n1, n2, rfl, fun w₁ hw₁ ↦ ?_, fun w₁ hw₁ ↦ ?_, fun w₁ hw₁ ↦ ?_⟩
  · have h := hcols.1 w₁ (by omega); rwa [hpair] at h
  · have h := hcols.2.1 w₁ (by omega); rwa [hpair] at h
  · have h := hcols.2.2 w₁ (by omega); rwa [hpair] at h
/- ## 5. Weight-Collapse Re-Indexing & Interval Norm-Squared Bounds -/
private lemma wdCMem_zero_iff {z : ℂ} (h : wdCMem z wdCZero) : z = 0 := by
  rcases h with ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩
  simp only [wdCZero, Int.cast_zero, zero_div] at hr1 hr2 hi1 hi2
  exact Complex.ext (by simp only [Complex.zero_re]; linarith)
    (by simp only [Complex.zero_im]; linarith)
private lemma list_map_wdCAbs2Hi_getD (xs : List WDCVal) (i : ℕ) : (xs.map wdCAbs2Hi).getD i 0 = if
    i < xs.length then wdCAbs2Hi (xs.getD i wdCZero) else 0 := by
  by_cases hi : i < xs.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]
private lemma normSq_le_map_wdCAbs2Hi_getD {z : ℂ} {xs : List WDCVal} {i : ℕ} (hz : wdCMem z
    (xs.getD i wdCZero)) : Complex.normSq z ≤ ((xs.map wdCAbs2Hi).getD i 0 : ℝ) / wdScaleR := by
  rw [list_map_wdCAbs2Hi_getD]; by_cases hi : i < xs.length
  · rw [ite_eq_left hi]; exact normSq_le_wdCAbs2Hi hz
  · rw [ite_eq_right hi]
    have hnil : xs.getD i wdCZero = wdCZero := (by simp [List.getD_eq_getElem?_getD, hi])
    rw [hnil] at hz; rw [wdCMem_zero_iff hz]; simp
private lemma map_wdCAbs2Hi_getD_nonneg (xs : List WDCVal) (i : ℕ) :
    0 ≤ (xs.map wdCAbs2Hi).getD i 0 := by
  rw [list_map_wdCAbs2Hi_getD]; split_ifs
  · exact wdCAbs2Hi_nonneg _
  · exact le_rfl
theorem midPCollapse2RowWt_bound (deg1 r : ℕ) {z : (ℕ → ℂ) × (ℕ → ℂ)} {r0 r1 : List WDCVal} (hz0 : ∀
    w₁ ≤ deg1, wdCMem (z.1 w₁) (r0.getD w₁ wdCZero)) (hz1 : ∀ w₁ ≤ deg1, wdCMem (z.2 w₁) (r1.getD w₁
    wdCZero)) : ∀ wt ≤ r, 0 ≤ (midPCollapse2RowWt deg1 r r0 r1).getD wt 0 ∧ ((if wt ≤ deg1 then
    (deg1.choose wt : ℝ) * Complex.normSq (z.1 wt) else 0) + (if 1 ≤ wt ∧ wt - 1 ≤ deg1 then
    (deg1.choose (wt - 1) : ℝ) * Complex.normSq (z.2 (wt - 1)) else 0)) ≤ ((midPCollapse2RowWt deg1
    r r0 r1).getD wt 0 : ℝ) / wdScaleR := by
  intro wt hwt; unfold midPCollapse2RowWt; simp only [midPSeqZList_eq]
  have hr1 : Nat.add r 1 = r + 1 := rfl
  rw [hr1, ghListMapRange_getD, ite_eq_left (by omega : wt < r + 1), midPForceInt_eq]
  have ha0_nn (i : ℕ) : 0 ≤ (r0.map wdCAbs2Hi).getD i 0 := map_wdCAbs2Hi_getD_nonneg r0 i
  have ha1_nn (i : ℕ) : 0 ≤ (r1.map wdCAbs2Hi).getD i 0 := map_wdCAbs2Hi_getD_nonneg r1 i
  set t0 : ℤ := if Nat.ble wt deg1 then Int.mul (Int.ofNat (ghBinom deg1 wt)) ((r0.map
    wdCAbs2Hi).getD wt 0) else 0
  set t1 : ℤ := if Nat.ble 1 wt && Nat.ble (wt - 1) deg1 then Int.mul (Int.ofNat (ghBinom deg1 (wt -
    1))) ((r1.map wdCAbs2Hi).getD (wt - 1) 0) else 0
  have ht0_nn : 0 ≤ t0 := by
    dsimp only [t0]; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (ha0_nn _)
    · exact le_rfl
  have ht1_nn : 0 ≤ t1 := by
    dsimp only [t1]; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (ha1_nn _)
    · exact le_rfl
  have hadd_eq : Int.add t0 t1 = t0 + t1 := rfl; rw [hadd_eq]; refine ⟨add_nonneg ht0_nn ht1_nn, ?_⟩
  push_cast; rw [add_div]; refine add_le_add ?_ ?_
  · dsimp only [t0]; by_cases hc0 : wt ≤ deg1
    · have hble : Nat.ble wt deg1 = true := Nat.ble_eq.mpr hc0; rw [ite_eq_left hc0, hble]
      simp only [↓reduceIte]
      have hmul : Int.mul (Int.ofNat (ghBinom deg1 wt)) ((r0.map wdCAbs2Hi).getD wt 0) =
          (deg1.choose wt : ℤ) * ((r0.map wdCAbs2Hi).getD wt 0) := by
        rw [← ghBinom_eq]; rfl
      rw [hmul]; push_cast; rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (normSq_le_map_wdCAbs2Hi_getD (hz0 wt hc0))
        (Nat.cast_nonneg _)
    · have hble : Nat.ble wt deg1 = false := by
        cases h : Nat.ble wt deg1
        · rfl
        · exfalso; exact hc0 (Nat.ble_eq.mp h)
      rw [ite_eq_right hc0, hble]; simp
  · dsimp only [t1]; by_cases hc1 : 1 ≤ wt ∧ wt - 1 ≤ deg1
    · have hble : (Nat.ble 1 wt && Nat.ble (wt - 1) deg1) = true := by
        simp [Nat.ble_eq, hc1.1, hc1.2]
      rw [ite_eq_left hc1, hble]; simp only [↓reduceIte]
      have hmul : Int.mul (Int.ofNat (ghBinom deg1 (wt - 1))) ((r1.map wdCAbs2Hi).getD (wt - 1) 0) =
        (deg1.choose (wt - 1) : ℤ) * ((r1.map wdCAbs2Hi).getD (wt - 1) 0) := by
        rw [← ghBinom_eq]; rfl
      rw [hmul]; push_cast; rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (normSq_le_map_wdCAbs2Hi_getD (hz1 (wt - 1) hc1.2))
        (Nat.cast_nonneg _)
    · have hble : (Nat.ble 1 wt && Nat.ble (wt - 1) deg1) = false := by
        cases h : Nat.ble 1 wt && Nat.ble (wt - 1) deg1
        · rfl
        · exfalso; simp only [Bool.and_eq_true, Nat.ble_eq] at h; exact hc1 h
      rw [ite_eq_right hc1, hble]; simp
theorem midPCollapseTwoPairWt_bound (deg1 r : ℕ) {z : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ)} {tp0 tp1 tp2 :
    List WDCVal} (hz0 : ∀ w₁ ≤ deg1, wdCMem (z.1 w₁) (tp0.getD w₁ wdCZero)) (hz1 : ∀ w₁ ≤ deg1,
    wdCMem (z.2.1 w₁) (tp1.getD w₁ wdCZero)) (hz2 : ∀ w₁ ≤ deg1, wdCMem (z.2.2 w₁) (tp2.getD w₁
    wdCZero)) : ∀ wt ≤ r, 0 ≤ (midPCollapseTwoPairWt deg1 r tp0 tp1 tp2).getD wt 0 ∧ ((if wt ≤ deg1
    then (deg1.choose wt : ℝ) * Complex.normSq (z.1 wt) else 0) + (if 1 ≤ wt ∧ wt - 1 ≤ deg1 then
    (2 * deg1.choose (wt - 1) : ℝ) * Complex.normSq (z.2.1 (wt - 1)) else 0) + (if 2 ≤ wt ∧ wt - 2 ≤
    deg1 then (deg1.choose (wt - 2) : ℝ) * Complex.normSq (z.2.2 (wt - 2)) else 0)) ≤
    ((midPCollapseTwoPairWt deg1 r tp0 tp1 tp2).getD wt 0 : ℝ) / wdScaleR := by
  intro wt hwt; unfold midPCollapseTwoPairWt; simp only [midPSeqZList_eq]
  have hr1 : Nat.add r 1 = r + 1 := rfl
  rw [hr1, ghListMapRange_getD, ite_eq_left (by omega : wt < r + 1), midPForceInt_eq]
  set t0 : ℤ := if Nat.ble wt deg1 then Int.mul (Int.ofNat (ghBinom deg1 wt)) ((tp0.map
    wdCAbs2Hi).getD wt 0) else 0
  set t1 : ℤ := if Nat.ble 1 wt && Nat.ble (wt - 1) deg1 then Int.mul (Int.ofNat (2 * ghBinom deg1
    (wt - 1))) ((tp1.map wdCAbs2Hi).getD (wt - 1) 0) else 0
  set t2 : ℤ := if Nat.ble 2 wt && Nat.ble (wt - 2) deg1 then Int.mul (Int.ofNat (ghBinom deg1 (wt -
    2))) ((tp2.map wdCAbs2Hi).getD (wt - 2) 0) else 0
  have ht0_nn : 0 ≤ t0 := by
    dsimp only [t0]; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (map_wdCAbs2Hi_getD_nonneg _ _)
    · exact le_rfl
  have ht1_nn : 0 ≤ t1 := by
    dsimp only [t1]; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (map_wdCAbs2Hi_getD_nonneg _ _)
    · exact le_rfl
  have ht2_nn : 0 ≤ t2 := by
    dsimp only [t2]; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (map_wdCAbs2Hi_getD_nonneg _ _)
    · exact le_rfl
  have hadd_eq : Int.add (Int.add t0 t1) t2 = t0 + t1 + t2 := rfl; rw [hadd_eq]
  refine ⟨add_nonneg (add_nonneg ht0_nn ht1_nn) ht2_nn, ?_⟩
  push_cast; rw [add_div, add_div]; refine add_le_add (add_le_add ?_ ?_) ?_
  · dsimp only [t0]; by_cases hc0 : wt ≤ deg1
    · have hble : Nat.ble wt deg1 = true := Nat.ble_eq.mpr hc0
      rw [ite_eq_left hc0, hble]; simp only [↓reduceIte]
      have hmul : Int.mul (Int.ofNat (ghBinom deg1 wt)) ((tp0.map wdCAbs2Hi).getD wt 0) =
          (deg1.choose wt : ℤ) * ((tp0.map wdCAbs2Hi).getD wt 0) := by
        rw [← ghBinom_eq]; rfl
      rw [hmul]; push_cast; rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (normSq_le_map_wdCAbs2Hi_getD (hz0 wt hc0))
        (Nat.cast_nonneg _)
    · have hble : Nat.ble wt deg1 = false := by
        cases h : Nat.ble wt deg1
        · rfl
        · exfalso; exact hc0 (Nat.ble_eq.mp h)
      rw [ite_eq_right hc0, hble]; simp
  · dsimp only [t1]; by_cases hc1 : 1 ≤ wt ∧ wt - 1 ≤ deg1
    · have hble : (Nat.ble 1 wt && Nat.ble (wt - 1) deg1) = true := by
        simp [Nat.ble_eq, hc1.1, hc1.2]
      rw [ite_eq_left hc1, hble]; simp only [↓reduceIte]
      have hmul : Int.mul (Int.ofNat (2 * ghBinom deg1 (wt - 1))) ((tp1.map wdCAbs2Hi).getD (wt - 1)
        0) = ((2 * deg1.choose (wt - 1) : ℕ) : ℤ) * ((tp1.map wdCAbs2Hi).getD (wt - 1) 0) := by
        rw [← ghBinom_eq]; rfl
      rw [hmul]; push_cast; rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (normSq_le_map_wdCAbs2Hi_getD (hz1 (wt - 1) hc1.2))
        (by positivity)
    · have hble : (Nat.ble 1 wt && Nat.ble (wt - 1) deg1) = false := by
        cases h : Nat.ble 1 wt && Nat.ble (wt - 1) deg1
        · rfl
        · exfalso; simp only [Bool.and_eq_true, Nat.ble_eq] at h; exact hc1 h
      rw [ite_eq_right hc1, hble]; simp
  · dsimp only [t2]; by_cases hc2 : 2 ≤ wt ∧ wt - 2 ≤ deg1
    · have hble : (Nat.ble 2 wt && Nat.ble (wt - 2) deg1) = true := by
        simp [Nat.ble_eq, hc2.1, hc2.2]
      rw [ite_eq_left hc2, hble]; simp only [↓reduceIte]
      have hmul : Int.mul (Int.ofNat (ghBinom deg1 (wt - 2))) ((tp2.map wdCAbs2Hi).getD (wt - 2) 0)
        = (deg1.choose (wt - 2) : ℤ) * ((tp2.map wdCAbs2Hi).getD (wt - 2) 0) := by
        rw [← ghBinom_eq]; rfl
      rw [hmul]; push_cast; rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (normSq_le_map_wdCAbs2Hi_getD (hz2 (wt - 2) hc2.2))
        (Nat.cast_nonneg _)
    · have hble : (Nat.ble 2 wt && Nat.ble (wt - 2) deg1) = false := by
        cases h : Nat.ble 2 wt && Nat.ble (wt - 2) deg1
        · rfl
        · exfalso; simp only [Bool.and_eq_true, Nat.ble_eq] at h; exact hc2 h
      rw [ite_eq_right hc2, hble]; simp
/-- Re-indexes the `SingleTriple` `[3, 1 ^ (r - 3)]` `w₁`-sum by total click weight `wt ≤ r
  - 2`. -/
theorem sum_singleTriple_by_wt {r : ℕ} (hr3 : 3 ≤ r) (a0 a1 f : ℕ → ℝ) : (∑ w₁ ∈ Finset.range (r -
    2), (a0 w₁ * f (r - w₁) + a1 w₁ * f (r - (w₁ + 1)))) = ∑ wt ∈ Finset.range (r - 1), ((if wt ≤
    r - 3 then a0 wt else 0) + (if 1 ≤ wt ∧ wt - 1 ≤ r - 3 then a1 (wt - 1) else 0)) * f (r -
    wt) := by
  set d := r - 3; have hr2 : r - 2 = d + 1 := (by omega); have hr1 : r - 1 = d + 2 := (by omega)
  rw [hr2, hr1, Finset.sum_add_distrib]; simp_rw [add_mul]; rw [Finset.sum_add_distrib]; congr 1
  · symm
    rw [Finset.sum_range_succ, ite_eq_right (by omega : ¬(d + 1 ≤ d)), zero_mul, add_zero]
    refine Finset.sum_congr rfl fun w₁ hw₁ ↦ ?_
    have hle : w₁ ≤ d := (by rw [Finset.mem_range] at hw₁; omega); rw [ite_eq_left hle]
  · symm
    rw [Finset.sum_range_succ', ite_eq_right (by omega : ¬(1 ≤ 0 ∧ 0 - 1 ≤ d)), zero_mul, add_zero]
    refine Finset.sum_congr rfl fun w₁ hw₁ ↦ ?_
    have hle : 1 ≤ w₁ + 1 ∧ (w₁ + 1) - 1 ≤ d := (by rw [Finset.mem_range] at hw₁; omega)
    rw [ite_eq_left hle, Nat.add_sub_cancel]
/-- Re-indexes the `TwoPair` `[2, 2, 1 ^ (r - 4)]` `w₁`-sum by total click weight `wt ≤ r -
  2`. -/
theorem sum_twoPair_by_wt {r : ℕ} (hr4 : 4 ≤ r) (a0 a1 a2 f : ℕ → ℝ) : (∑ w₁ ∈ Finset.range (r - 3),
    (a0 w₁ * f (r - w₁) + a1 w₁ * f (r - (w₁ + 1)) + a2 w₁ * f (r - (w₁ + 2)))) = ∑ wt ∈
    Finset.range (r - 1), ((if wt ≤ r - 4 then a0 wt else 0) + (if 1 ≤ wt ∧ wt - 1 ≤ r - 4 then a1
    (wt - 1) else 0) + (if 2 ≤ wt ∧ wt - 2 ≤ r - 4 then a2 (wt - 2) else 0)) * f (r - wt) := by
  set d := r - 4; have hr3 : r - 3 = d + 1 := (by omega); have hr1 : r - 1 = d + 3 := (by omega)
  rw [hr3, hr1, Finset.sum_add_distrib, Finset.sum_add_distrib]; simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; congr 1
  · congr 1
    · symm
      rw [Finset.sum_range_succ, ite_eq_right (by omega : ¬(d + 2 ≤ d)), zero_mul, add_zero,
        Finset.sum_range_succ, ite_eq_right (by omega : ¬(d + 1 ≤ d)), zero_mul, add_zero]
      refine Finset.sum_congr rfl fun w₁ hw₁ ↦ ?_
      have hle : w₁ ≤ d := (by rw [Finset.mem_range] at hw₁; omega); rw [ite_eq_left hle]
    · symm
      rw [Finset.sum_range_succ, ite_eq_right (by omega : ¬(1 ≤ d + 2 ∧ d + 2 - 1 ≤ d)),
        zero_mul, add_zero, Finset.sum_range_succ',
        ite_eq_right (by omega : ¬(1 ≤ 0 ∧ 0 - 1 ≤ d)), zero_mul, add_zero]
      refine Finset.sum_congr rfl fun w₁ hw₁ ↦ ?_
      have hle : 1 ≤ w₁ + 1 ∧ (w₁ + 1) - 1 ≤ d := (by rw [Finset.mem_range] at hw₁; omega)
      rw [ite_eq_left hle, Nat.add_sub_cancel]
  · symm
    rw [Finset.sum_range_succ', ite_eq_right (by omega : ¬(2 ≤ 0 ∧ 0 - 2 ≤ d)), zero_mul, add_zero,
      Finset.sum_range_succ', ite_eq_right (by omega : ¬(2 ≤ 0 + 1 ∧ (0 + 1) - 2 ≤ d)),
      zero_mul, add_zero]
    refine Finset.sum_congr rfl fun w₁ hw₁ ↦ ?_
    have hle : 2 ≤ w₁ + 1 + 1 ∧ (w₁ + 1 + 1) - 2 ≤ d := (by rw [Finset.mem_range] at hw₁; omega)
    rw [ite_eq_left hle]; have hsub : (w₁ + 1 + 1) - 2 = w₁ := (by omega)
    have hrw : r - (w₁ + 1 + 1) = r - (w₁ + 2) := (by omega); rw [hsub, hrw]
/- ## 6. Probe-Chain, Row-Summary, & Bellman-Step Soundness (`rm2`, `includeRm3 = false`) -/
private lemma evalMidPPhaseIV_sound {ph : MidPPhaseSpec} {gIV : WDCVal} (h : evalMidPPhaseIV ph =
    some gIV) : ∃ g : GaussPyth, compileMidPPhase ph = some g ∧ wdCMem g.val gIV := by
  unfold evalMidPPhaseIV at h; by_cases hcond : 0 < ph.gd ∧ ph.ga ^ 2 + ph.gb ^ 2 = (ph.gd : ℤ) ^ 2
  · rw [ite_eq_left hcond, midPSeqCIV_eq] at h
    injection h with hgIV
    subst hgIV; refine ⟨⟨ph.ga, ph.gb, ph.gd, hcond.1, hcond.2⟩, ?_, ?_⟩
    · simp [compileMidPPhase, hcond]
    · exact wdCMem_gaussPyth ⟨ph.ga, ph.gb, ph.gd, hcond.1, hcond.2⟩
  · rw [ite_eq_right hcond] at h
    cases h
private lemma evalMidPPhasesIV_sound :
    ∀ {phs : List MidPPhaseSpec} {gIVs : List WDCVal},
      evalMidPPhasesIV phs = some gIVs →
      ∃ gs : List GaussPyth,
        compileMidPPhases phs = some gs ∧
        gs.length = phs.length ∧
        gIVs.length = phs.length ∧
        ∀ i, wdCMem (gs.getD i gaussOne).val (gIVs.getD i wdCOne)
  | [], _, h => by
      simp only [evalMidPPhasesIV, Option.some.injEq] at h
      subst h
      refine ⟨[], rfl, rfl, rfl, fun i ↦ ?_⟩
      simp [gaussOne_val, wdCMem_one]
  | ph :: rest, _, h => by
      unfold evalMidPPhasesIV at h
      cases h1 : evalMidPPhaseIV ph with
      | none => rw [h1] at h; cases h
      | some gIV =>
          cases h2 : evalMidPPhasesIV rest with
          | none => rw [h1, h2] at h; cases h
          | some tlIV =>
              rw [h1, h2] at h
              injection h with hcons
              subst hcons
              obtain ⟨g, hcg, hmem_g⟩ := evalMidPPhaseIV_sound h1
              obtain ⟨gsTl, hcTl, hlen_gs, hlen_iv, hmem_tl⟩ := evalMidPPhasesIV_sound h2
              refine ⟨g :: gsTl, ?_, by simp [hlen_gs], by simp [hlen_iv], fun i ↦ ?_⟩
              · simp [compileMidPPhases, hcg, hcTl]
              · cases i with
                | zero => simpa using hmem_g
                | succ i' => simpa using hmem_tl i'
private lemma midPSumRangeZ_eq (N : ℕ) (f : ℕ → ℤ) :
    midPSumRangeZ N f = ∑ w ∈ Finset.range N, f w := by
  unfold midPSumRangeZ; rw [midPSumRangeZAux_eq, zero_add]
private lemma map_midPFastCRMul_mem {r : ℝ} {rIV : WDIVal} (hr : wdMem r rIV) {u : ℕ → ℂ} {xs : List
    WDCVal} {w : ℕ} (hu : wdCMem (u w) (xs.getD w wdCZero)) : wdCMem ((r : ℂ) * u w) ((xs.map
    (midPFastCRMul rIV)).getD w wdCZero) := by
  by_cases hw : w < xs.length
  · have hget : (xs.map (midPFastCRMul rIV)).getD w wdCZero =
        midPFastCRMul rIV (xs.getD w wdCZero) := by
      simp [List.getD_eq_getElem?_getD, hw]
    rw [hget, midPFastCRMul_eq]; exact wdCMem_rmul hr hu
  · have hnil1 : (xs.map (midPFastCRMul rIV)).getD w wdCZero = wdCZero := by
      simp [List.getD_eq_getElem?_getD, hw]
    have hnil2 : xs.getD w wdCZero = wdCZero := (by simp [List.getD_eq_getElem?_getD, hw])
    rw [hnil2] at hu; rw [hnil1, wdCMem_zero_iff hu, mul_zero]; exact wdCMem_zero
private lemma map_midPFastCMul_mem {p : ℂ} {pIV : WDCVal} (hp : wdCMem p pIV) {u : ℕ → ℂ} {xs : List
    WDCVal} {w : ℕ} (hu : wdCMem (u w) (xs.getD w wdCZero)) : wdCMem (p * u w) ((xs.map
    (midPFastCMul pIV)).getD w wdCZero) := by
  by_cases hw : w < xs.length
  · have hget : (xs.map (midPFastCMul pIV)).getD w wdCZero =
        midPFastCMul pIV (xs.getD w wdCZero) := by
      simp [List.getD_eq_getElem?_getD, hw]
    rw [hget, midPFastCMul_eq]; exact wdCMem_mul hp hu
  · have hnil1 : (xs.map (midPFastCMul pIV)).getD w wdCZero = wdCZero := by
      simp [List.getD_eq_getElem?_getD, hw]
    have hnil2 : xs.getD w wdCZero = wdCZero := (by simp [List.getD_eq_getElem?_getD, hw])
    rw [hnil2] at hu; rw [hnil1, wdCMem_zero_iff hu, mul_zero]; exact wdCMem_zero
private lemma midP_phi123_trig_mem {subN : ℕ} (hsub : 200 ≤ subN) {c : ℝ} {phi1 : WDIVal} (hm1 :
    wdMem (c * Real.arcsin (1 / √(2 ^ subN : ℝ))) phi1) (hang : (midPBleZ 0 phi1.1 && midPBleZ
    (midPFastMulIV phi1 (midPSqrtRatioIv 4)).2 (Int.mul 1024 midPScaleZ)) = true) :
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ)); let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    let θ₃ := Real.arcsin (√3 / √(2 ^ subN : ℝ)); let phi2 := midPFastMulIV phi1 (midPSqrtRatioIv 2)
    let phi3 := midPFastMulIV phi1 (midPSqrtRatioIv 3)
    (wdMem (Real.cos (c * θ₁)) (wdTrig phi1).1 ∧ wdMem (Real.sin (c * θ₁)) (wdTrig phi1).2) ∧
    (wdMem (Real.cos (c * θ₂)) (wdTrig phi2).1 ∧ wdMem (Real.sin (c * θ₂)) (wdTrig phi2).2) ∧
    (wdMem (Real.cos (c * θ₃)) (wdTrig phi3).1 ∧ wdMem (Real.sin (c * θ₃)) (wdTrig phi3).2) := by
  intro θ₁ θ₂ θ₃ phi2 phi3; set phi4 := midPFastMulIV phi1 (midPSqrtRatioIv 4)
  simp only [Bool.and_eq_true, midPBleZ_iff] at hang
  have hmaxAng_eq : Int.mul 1024 midPScaleZ = 1024 * (wdScale : ℤ) := rfl
  have hr2_mem := midPSqrtRatioIv_mem (by omega : 1 ≤ 2) (by omega : 2 ≤ 16) hsub
  have hr3_mem := midPSqrtRatioIv_mem (by omega : 1 ≤ 3) (by omega : 3 ≤ 16) hsub
  obtain ⟨⟨hθ₁_pos, _, _⟩, _, _⟩ := ghZoom_subN_angle_bounds hsub
  have hθ₁_ne : θ₁ ≠ 0 := hθ₁_pos.ne'
  have hm2 : wdMem (c * θ₂) phi2 := by
    have heq : c * θ₂ = (c * θ₁) * (θ₂ / θ₁) := (by rw [mul_assoc, mul_div_cancel₀ _ hθ₁_ne])
    dsimp only [phi2]; rw [heq, midPFastMulIV_eq, ghMulIV_eq]
    exact wdMem_mul hm1 (by simpa [θ₁, θ₂] using hr2_mem)
  have hm3 : wdMem (c * θ₃) phi3 := by
    have heq : c * θ₃ = (c * θ₁) * (θ₃ / θ₁) := (by rw [mul_assoc, mul_div_cancel₀ _ hθ₁_ne])
    dsimp only [phi3]; rw [heq, midPFastMulIV_eq, ghMulIV_eq]
    exact wdMem_mul hm1 (by simpa [θ₁, θ₃] using hr3_mem)
  have hd1_ord := wdMem_lo_le_hi hm1; have hr2_ord := wdMem_lo_le_hi hr2_mem
  have hr3_ord := wdMem_lo_le_hi hr3_mem
  have hr2_nn : 0 ≤ (midPSqrtRatioIv 2).1 := by
    change 0 ≤ (midPSqrtEntry 2).lo - 1; norm_num [midPSqrtEntry, midPSqrtTable16]
  have hr3_nn : 0 ≤ (midPSqrtRatioIv 3).1 := by
    change 0 ≤ (midPSqrtEntry 3).lo - 1; norm_num [midPSqrtEntry, midPSqrtTable16]
  have hr24 : (midPSqrtRatioIv 2).2 ≤ (midPSqrtRatioIv 4).2 := by
    norm_num [midPSqrtRatioIv, midPSqrtEntry, midPSqrtTable16]
  have hr34 : (midPSqrtRatioIv 3).2 ≤ (midPSqrtRatioIv 4).2 := by
    norm_num [midPSqrtRatioIv, midPSqrtEntry, midPSqrtTable16]
  have hphi2_bds : 0 ≤ phi2.1 ∧ phi2.2 ≤ 1024 * (wdScale : ℤ) := by
    dsimp only [phi2, phi4] at hang ⊢; rw [midPFastMulIV_eq] at hang ⊢
    have hb := wdMul_nonneg_and_hi_mono hang.1 hd1_ord hr2_nn hr2_ord hr24
    exact ⟨hb.1, hb.2.trans (hmaxAng_eq ▸ hang.2)⟩
  have hphi3_bds : 0 ≤ phi3.1 ∧ phi3.2 ≤ 1024 * (wdScale : ℤ) := by
    dsimp only [phi3, phi4] at hang ⊢; rw [midPFastMulIV_eq] at hang ⊢
    have hb := wdMul_nonneg_and_hi_mono hang.1 hd1_ord hr3_nn hr3_ord hr34
    exact ⟨hb.1, hb.2.trans (hmaxAng_eq ▸ hang.2)⟩
  have hphi1_hi : phi1.2 ≤ 1024 * (wdScale : ℤ) := by
    have hle4 : phi1.2 ≤ phi4.2 := by
      dsimp only [phi4]; rw [midPFastMulIV_eq, ghMulIV_eq]; unfold wdMul wdDivCeil wdDivFloor
      dsimp only
      have hmx : phi1.2 * (midPSqrtRatioIv 4).2 ≤ max (max (phi1.1 * (midPSqrtRatioIv 4).1)
        (phi1.1 * (midPSqrtRatioIv 4).2)) (max (phi1.2 * (midPSqrtRatioIv 4).1) (phi1.2 *
        (midPSqrtRatioIv 4).2)) := le_trans (le_max_right _ _) (le_max_right _ _)
      have h19 : phi1.2 * 1000000000000000 ≤ phi1.2 * (midPSqrtRatioIv 4).2 :=
        mul_le_mul_of_nonneg_left (by norm_num [midPSqrtRatioIv, midPSqrtEntry, midPSqrtTable16])
        (hang.1.trans hd1_ord)
      have htr := h19.trans hmx; unfold wdScale; omega
    exact hle4.trans (hmaxAng_eq ▸ hang.2)
  exact ⟨wdTrig_mem hang.1 hphi1_hi hm1, wdTrig_mem hphi2_bds.1 hphi2_bds.2 hm2, wdTrig_mem
    hphi3_bds.1 hphi3_bds.2 hm3⟩
private lemma midP_phi123_trigCPS_elim (α : Type*) {subN : ℕ} (hsub : 200 ≤ subN) {c : ℝ} {phi1 :
    WDIVal} (hm1 : wdMem (c * Real.arcsin (1 / √(2 ^ subN : ℝ))) phi1) (hang : (midPBleZ 0 phi1.1 &&
    midPBleZ (midPFastMulIV phi1 (midPSqrtRatioIv 4)).2 (Int.mul 1024 midPScaleZ)) = true) :
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ)); let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    let θ₃ := Real.arcsin (√3 / √(2 ^ subN : ℝ))
    ∃ c1 s1 c2 s2 c3 s3 : WDIVal, (∀ k : WDIVal → WDIVal → α, midPTrigCPS phi1 k = k c1 s1) ∧ (∀ k :
      WDIVal → WDIVal → α, midPTrigCPS (midPFastMulIV phi1 (midPSqrtRatioIv 2)) k = k c2 s2) ∧ (∀ k
      : WDIVal → WDIVal → α, midPTrigCPS (midPFastMulIV phi1 (midPSqrtRatioIv 3)) k = k c3 s3) ∧
      (wdMem (Real.cos (c * θ₁)) c1 ∧ wdMem (Real.sin (c * θ₁)) s1) ∧ (wdMem (Real.cos (c * θ₂)) c2
      ∧ wdMem (Real.sin (c * θ₂)) s2) ∧ (wdMem (Real.cos (c * θ₃)) c3 ∧ wdMem (Real.sin (c * θ₃))
      s3) := by
  intro θ₁ θ₂ θ₃; obtain ⟨ht1, ht2, ht3⟩ := midP_phi123_trig_mem hsub hm1 hang
  exact ⟨(wdTrig phi1).1, (wdTrig phi1).2, (wdTrig (midPFastMulIV phi1 (midPSqrtRatioIv 2))).1,
    (wdTrig (midPFastMulIV phi1 (midPSqrtRatioIv 2))).2, (wdTrig (midPFastMulIV phi1
    (midPSqrtRatioIv 3))).1, (wdTrig (midPFastMulIV phi1 (midPSqrtRatioIv 3))).2, fun k ↦
    midPTrigCPS_eq _ k, fun k ↦ midPTrigCPS_eq _ k, fun k ↦ midPTrigCPS_eq _ k, ht1, ht2, ht3⟩
private lemma midPTrigCPS_sin_elim (α : Type*) {θ : ℝ} {azIV : WDIVal} (hm : wdMem θ azIV) (haz :
    (midPBleZ 0 azIV.1 && midPBleZ azIV.2 (Int.mul 1024 midPScaleZ)) = true) : ∃ cAz sAz : WDIVal,
    (∀ k : WDIVal → WDIVal → α, midPTrigCPS azIV k = k cAz sAz) ∧ wdMem (Real.sin θ) sAz := by
  have haz' := haz; simp only [Bool.and_eq_true, midPBleZ_iff] at haz'
  have hmax : Int.mul 1024 midPScaleZ = 1024 * (wdScale : ℤ) := rfl
  exact ⟨(wdTrig azIV).1, (wdTrig azIV).2, fun k ↦ midPTrigCPS_eq azIV k,
    (wdTrig_mem haz'.1 (hmax ▸ haz'.2) hm).2⟩
private lemma midPSeqCIVList_elim (α : Type*) (xs : List WDCVal) {P : List WDCVal → Prop} (hP : P
    xs) : ∃ ys : List WDCVal, (∀ k : List WDCVal → α, midPSeqCIVList xs k = k ys) ∧ P ys :=
  ⟨xs, fun k ↦ midPSeqCIVList_eq xs k, hP⟩
private lemma midP_probe_step_sound {r subN : ℕ} (hsub : 200 ≤ subN) {p : MidPProbeSpec} {st st' :
    MidPProbeState} (hstep : evalMidPProbeStep r false p st = some st') {u : ℕ → ℂ} {sp stp : (ℕ →
    ℂ) × (ℕ → ℂ)} {tp : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ)} (hu : ∀ w ≤ r, wdCMem (u w) (st.uVec.getD w
    wdCZero)) (hsp0 : ∀ w₁ ≤ r - 2, wdCMem (sp.1 w₁) (st.sp0.getD w₁ wdCZero)) (hsp1 : ∀ w₁ ≤ r - 2,
    wdCMem (sp.2 w₁) (st.sp1.getD w₁ wdCZero)) (hst0 : ∀ w₁ ≤ r - 3, wdCMem (stp.1 w₁) (st.st0.getD
    w₁ wdCZero)) (hst1 : ∀ w₁ ≤ r - 3, wdCMem (stp.2 w₁) (st.st1.getD w₁ wdCZero)) (htp : 4 ≤ r → (∀
    w₁ ≤ r - 4, wdCMem (tp.1 w₁) (st.tp0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 4, wdCMem (tp.2.1 w₁)
    (st.tp1.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 4, wdCMem (tp.2.2 w₁) (st.tp2.getD w₁ wdCZero))) :
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ)); let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    let θ₃ := Real.arcsin (√3 / √(2 ^ subN : ℝ))
    let scale15 := ((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR
    ∃ pr : GHMidPProbe, compileMidPProbe r p subN = some pr ∧ 0 ≤ st'.qExtraHi - st.qExtraHi ∧ 0 ≤
      st'.qCollAddHi - st.qCollAddHi ∧ (∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) *
      Complex.normSq (ghMidPDampAmp r pr u w)) * ((pr.kNext + 2 : ℕ) : ℝ) ≤ ((st'.qExtraHi -
      st.qExtraHi : ℤ) : ℝ) * scale15 ∧ ((pr.kNext + 2 : ℕ) : ℝ) ≤ ((st'.qCollAddHi - st.qCollAddHi
      : ℤ) : ℝ) * scale15 ∧ (∀ w ≤ r, wdCMem (ghMidPProbeNextAmp r θ₁ pr u w) (st'.uVec.getD w
      wdCZero)) ∧ (∀ w₁ ≤ r - 2, wdCMem ((ghMidPProbeNext2Row (r - 2) θ₁ θ₂ pr sp).1 w₁)
      (st'.sp0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 2, wdCMem ((ghMidPProbeNext2Row (r - 2) θ₁ θ₂ pr
      sp).2 w₁) (st'.sp1.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 3, wdCMem ((ghMidPProbeNext2Row (r - 3) θ₁
      θ₃ pr stp).1 w₁) (st'.st0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 3, wdCMem ((ghMidPProbeNext2Row (r -
      3) θ₁ θ₃ pr stp).2 w₁) (st'.st1.getD w₁ wdCZero)) ∧ (4 ≤ r → (∀ w₁ ≤ r - 4, wdCMem
      ((ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr tp).1 w₁) (st'.tp0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r -
      4, wdCMem ((ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr tp).2.1 w₁) (st'.tp1.getD w₁ wdCZero)) ∧
      (∀ w₁ ≤ r - 4, wdCMem ((ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr tp).2.2 w₁) (st'.tp2.getD w₁
      wdCZero))) := by
  intro θ₁ θ₂ θ₃ scale15; have hB : 0 < wdScaleR := wdScaleR_pos
  have hBZ : (0 : ℤ) < (wdScale : ℤ) := (by unfold wdScale; norm_num)
  have hs15_nn : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
  unfold evalMidPProbeStep at hstep
  by_cases hpcond : p.phases.length = r ∧ 0 < p.daDen ∧ 0 < p.cDen ∧
      p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 = (p.cDen : ℤ) ^ 2
  · rw [ite_eq_left hpcond] at hstep
    cases hphs : evalMidPPhasesIV p.phases with
    | none => rw [hphs] at hstep; cases hstep
    | some gIVs =>
        rw [hphs] at hstep; dsimp only at hstep; set daIV := wdRat (p.daNum : ℤ) p.daDen
        set dphi1 := (ghMaxZ 0 (Int.sub daIV.1 2), daIV.2)
        by_cases hang : (midPBleZ 0 dphi1.1 &&
            midPBleZ (midPFastMulIV dphi1 (midPSqrtRatioIv 4)).2 (Int.mul 1024 midPScaleZ)) = true
        · rw [ite_eq_left hang] at hstep
          obtain ⟨gs, hcgs, _, _, hmem_gs⟩ := evalMidPPhasesIV_sound hphs
          let pr : GHMidPProbe := ⟨gs, ⟨p.cNum, p.sNum, p.cDen, hpcond.2.2.1, hpcond.2.2.2⟩,
            wdStepCount p.daNum p.daDen subN⟩
          have hcpr : compileMidPProbe r p subN = some pr := by
            unfold compileMidPProbe; rw [dite_eq_left hpcond, hcgs]
          obtain ⟨_, hdphi1_mem, hqda_nn, hqda_bound⟩ :=
            ghZoomStepCount_bounds (aNum := p.daNum) hpcond.2.1 hsub 2
          have hdphi1_eq : dphi1 = (max 0 (daIV.1 - 2), daIV.2) := by
            dsimp only [dphi1]; rw [ghMaxZ_eq]; rfl
          have hm_phi1 : wdMem (2 * (pr.kNext : ℝ) * θ₁) dphi1 := by
            rw [hdphi1_eq]; exact hdphi1_mem
          obtain ⟨c1, s1, c2, s2, c3, s3, htc1, htc2, htc3, htrig1, htrig2, htrig3⟩ :=
            midP_phi123_trigCPS_elim (Option MidPProbeState) hsub
              (c := 2 * (pr.kNext : ℝ)) hm_phi1 hang
          have hcTop_mem : wdMem pr.rotTop.cVal (wdRat p.cNum p.cDen) := wdMem_rat hpcond.2.2.1
          obtain ⟨uD, huD_eq, huD_mem⟩ := midPSeqCIVList_elim (Option MidPProbeState) (midPFastDampU
            r gIVs (wdRat p.cNum p.cDen) st.uVec) (P := fun ys ↦ ∀ w, wdCMem (ghMidPDampAmp r pr u
            w) (ys.getD w wdCZero)) (midPFastDampU_mem r hcTop_mem hmem_gs hu)
          rw [huD_eq] at hstep; clear huD_eq
          set sHi := midPSumRangeZ (Nat.add r 1) fun w ↦
            Int.mul (Int.ofNat (ghBinom r w)) (wdCAbs2Hi (uD.getD w wdCZero))
          set qdaHi := wdDivCeil (Int.mul (Int.add daIV.2 4) wdPi4InvHi) (Int.mul 2 midPScaleZ)
          set stepQ := wdDivCeil (Int.mul sHi qdaHi) midPScaleZ
          have hqda_eq : qdaHi = wdDivCeil ((daIV.2 + 2 * (2 : ℤ)) * wdPi4InvHi)
              (2 * (wdScale : ℤ)) := rfl
          have hsHi_nn : 0 ≤ sHi := by
            dsimp only [sHi]; rw [midPSumRangeZ_eq]; refine Finset.sum_nonneg fun w _ ↦ ?_
            exact mul_nonneg (Nat.cast_nonneg _) (wdCAbs2Hi_nonneg _)
          have hsHi_bound : (∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) * Complex.normSq
            (ghMidPDampAmp r pr u w)) ≤ (sHi : ℝ) / wdScaleR := by
            dsimp only [sHi]; have hr1_eq : Nat.add r 1 = r + 1 := rfl
            rw [midPSumRangeZ_eq, hr1_eq]; push_cast; rw [Finset.sum_div]
            refine Finset.sum_le_sum fun w _ ↦ ?_
            have hmul_eq : Int.mul (Int.ofNat (ghBinom r w)) (wdCAbs2Hi (uD.getD w wdCZero)) =
              (r.choose w : ℤ) * wdCAbs2Hi (uD.getD w wdCZero) := by
              rw [← ghBinom_eq]; rfl
            rw [hmul_eq]; push_cast; rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (normSq_le_wdCAbs2Hi (huD_mem w)) (Nat.cast_nonneg _)
          have hstepQ_nn : 0 ≤ stepQ :=
            wdDivCeil_nonneg (mul_nonneg hsHi_nn (hqda_eq ▸ hqda_nn)) hBZ
          have hstepQ_bound : (∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) * Complex.normSq
            (ghMidPDampAmp r pr u w)) * ((pr.kNext + 2 : ℕ) : ℝ) ≤ (stepQ : ℝ) * scale15 := by
            have hceil := le_wdDivCeil (a := sHi * qdaHi) hBZ
            calc (∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) * Complex.normSq (ghMidPDampAmp r pr
                  u w)) * ((pr.kNext + 2 : ℕ) : ℝ) ≤ ((sHi : ℝ) / wdScaleR) * ((qdaHi : ℝ) *
                  scale15) := mul_le_mul hsHi_bound (hqda_eq ▸ hqda_bound) (Nat.cast_nonneg _)
                  (div_nonneg (by exact_mod_cast hsHi_nn) hB.le)
              _ = (((sHi * qdaHi : ℤ) : ℝ) / ((wdScale : ℤ) : ℝ)) * scale15 := by
                  dsimp only [wdScaleR]; push_cast; ring
              _ ≤ (stepQ : ℝ) * scale15 := mul_le_mul_of_nonneg_right hceil hs15_nn
          have hqda_nn' : 0 ≤ qdaHi := hqda_eq ▸ hqda_nn
          have hqda_bd' : ((pr.kNext + 2 : ℕ) : ℝ) ≤ (qdaHi : ℝ) * scale15 := hqda_eq ▸ hqda_bound
          rw [midPSeqInt_eq] at hstep; rw [midPSeqInt_eq] at hstep; rw [htc1, htc2, htc3] at hstep
          clear htc1 htc2 htc3
          clear_value stepQ qdaHi sHi dphi1 daIV
          obtain ⟨uNext, huN_eq, huNext⟩ := midPSeqCIVList_elim (Option MidPProbeState)
            (midPFastDickeStepVec r c1 s1 uD) (P := fun ys ↦ ∀ w, wdCMem (ghMidPProbeNextAmp r θ₁ pr
            u w) (ys.getD w wdCZero)) (midPFastDickeStepVec_mem r htrig1.1 htrig1.2 huD_mem)
          rw [huN_eq] at hstep; clear huN_eq
          let kStep2 (sp0N sp1N st0N st1N : List WDCVal) : Option MidPProbeState := if Nat.ble 4 r
            then midPFastStepTwoPairCPS (r - 4) gIVs c1 s1 c2 s2 st.tp0 st.tp1 st.tp2 fun tp0N tp1N
            tp2N ↦ if (false : Bool) then midPTrigCPS (midPFastMulIV dphi1 (midPSqrtRatioIv 4)) fun
            c4 s4 ↦ midPFastStep2RowCPS (r - 4) gIVs c1 s1 c4 s4 st.q10 st.q11 fun q10N q11N ↦ some
            (MidPProbeState.mk (Int.add st.qExtraHi stepQ) (Int.add st.qCollAddHi qdaHi) uNext sp0N
            sp1N st0N st1N tp0N tp1N tp2N q10N q11N) else some (MidPProbeState.mk (Int.add
            st.qExtraHi stepQ) (Int.add st.qCollAddHi qdaHi) uNext sp0N sp1N st0N st1N tp0N tp1N
            tp2N [] []) else some (MidPProbeState.mk (Int.add st.qExtraHi stepQ) (Int.add
            st.qCollAddHi qdaHi) uNext sp0N sp1N st0N st1N [] [] [] [] [])
          change (midPFastStep2RowCPS (r - 2) gIVs c1 s1 c2 s2 st.sp0 st.sp1 fun sp0N sp1N ↦
            midPFastStep2RowCPS (r - 3) gIVs c1 s1 c3 s3 st.st0 st.st1 fun st0N st1N ↦ kStep2 sp0N
            sp1N st0N st1N) = some st' at hstep
          obtain ⟨sp0N, sp1N, hsp_eq, hsp0N, hsp1N⟩ := midPFastStep2RowCPS_mem (α := Option
            MidPProbeState) (r - 2) htrig1.1 htrig1.2 htrig2.1 htrig2.2 hmem_gs hsp0 hsp1 (fun sp0N
            sp1N ↦ midPFastStep2RowCPS (r - 3) gIVs c1 s1 c3 s3 st.st0 st.st1 fun st0N st1N ↦ kStep2
            sp0N sp1N st0N st1N)
          rw [hsp_eq] at hstep
          obtain ⟨st0N, st1N, hst_eq, hst0N, hst1N⟩ := midPFastStep2RowCPS_mem (α := Option
            MidPProbeState) (r - 3) htrig1.1 htrig1.2 htrig3.1 htrig3.2 hmem_gs hst0 hst1 (fun st0N
            st1N ↦ kStep2 sp0N sp1N st0N st1N)
          rw [hst_eq] at hstep; dsimp only [kStep2] at hstep
          have htp_step : ∃ tp0N tp1N tp2N : List WDCVal, st' = MidPProbeState.mk (Int.add
            st.qExtraHi stepQ) (Int.add st.qCollAddHi qdaHi) uNext sp0N sp1N st0N st1N tp0N tp1N
            tp2N [] [] ∧ (4 ≤ r → (∀ w₁ ≤ r - 4, wdCMem ((ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr
            tp).1 w₁) (tp0N.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 4, wdCMem ((ghMidPProbeNextTwoPair (r -
            4) θ₁ θ₂ pr tp).2.1 w₁) (tp1N.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 4, wdCMem
            ((ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr tp).2.2 w₁) (tp2N.getD w₁ wdCZero))) := by
            by_cases hr4 : 4 ≤ r
            · have hble4 : Nat.ble 4 r = true := Nat.ble_eq.mpr hr4
              conv at hstep => lhs; rw [ite_eq_left hble4]
              obtain ⟨htp0, htp1, htp2⟩ := htp hr4
              obtain ⟨tp0N, tp1N, tp2N, htp_eq, htp0N, htp1N, htp2N⟩ := midPFastStepTwoPairCPS_mem
                (α := Option MidPProbeState) (r - 4) htrig1.1 htrig1.2 htrig2.1 htrig2.2 hmem_gs
                htp0 htp1 htp2 (fun tp0N tp1N tp2N ↦ if (false : Bool) then midPTrigCPS
                (midPFastMulIV dphi1 (midPSqrtRatioIv 4)) fun c4 s4 ↦ midPFastStep2RowCPS (r - 4)
                gIVs c1 s1 c4 s4 st.q10 st.q11 fun q10N q11N ↦ some (MidPProbeState.mk (Int.add
                st.qExtraHi stepQ) (Int.add st.qCollAddHi qdaHi) uNext sp0N sp1N st0N st1N tp0N tp1N
                tp2N q10N q11N) else some (MidPProbeState.mk (Int.add st.qExtraHi stepQ) (Int.add
                st.qCollAddHi qdaHi) uNext sp0N sp1N st0N st1N tp0N tp1N tp2N [] []))
              rw [htp_eq] at hstep
              conv at hstep => lhs; rw [ite_eq_right Bool.noConfusion]
              injection hstep with hst_eq'
              exact ⟨tp0N, tp1N, tp2N, hst_eq'.symm, fun _ ↦ ⟨htp0N, htp1N, htp2N⟩⟩
            · have hnot_ble4 : ¬(Nat.ble 4 r = true) := (by rw [Nat.ble_eq]; exact hr4)
              conv at hstep => lhs; rw [ite_eq_right hnot_ble4]
              injection hstep with hst_eq'
              exact ⟨[], [], [], hst_eq'.symm, fun h4 ↦ absurd h4 hr4⟩
          obtain ⟨tp0N, tp1N, tp2N, hst'_eq, htpN⟩ := htp_step; rw [hst'_eq]; dsimp only
          have hqEx_sub : Int.add st.qExtraHi stepQ - st.qExtraHi = stepQ := by
            change (st.qExtraHi + stepQ) - st.qExtraHi = stepQ
            exact add_sub_cancel_left st.qExtraHi stepQ
          have hqColl_sub : Int.add st.qCollAddHi qdaHi - st.qCollAddHi = qdaHi := by
            change (st.qCollAddHi + qdaHi) - st.qCollAddHi = qdaHi
            exact add_sub_cancel_left st.qCollAddHi qdaHi
          rw [hqEx_sub, hqColl_sub]
          exact ⟨pr, hcpr, hstepQ_nn, hqda_nn', hstepQ_bound, hqda_bd',
            fun w _ ↦ huNext w, hsp0N, hsp1N, hst0N, hst1N, htpN⟩
        · rw [ite_eq_right hang] at hstep; cases hstep
  · rw [ite_eq_right hpcond] at hstep; cases hstep
private lemma midP_probes_chain_sound {r subN : ℕ} (hsub : 200 ≤ subN) :
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ)); let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    let θ₃ := Real.arcsin (√3 / √(2 ^ subN : ℝ))
    let scale15 := ((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR
    ∀ (ps : List MidPProbeSpec) (st : MidPProbeState) (fin : MidPProbeState), evalMidPProbes r false
      ps st = some fin → ∀ (u : ℕ → ℂ) (sp stp : (ℕ → ℂ) × (ℕ → ℂ)) (tp : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ →
      ℂ)), (∀ w ≤ r, wdCMem (u w) (st.uVec.getD w wdCZero)) → (∀ w₁ ≤ r - 2, wdCMem (sp.1 w₁)
      (st.sp0.getD w₁ wdCZero)) → (∀ w₁ ≤ r - 2, wdCMem (sp.2 w₁) (st.sp1.getD w₁ wdCZero)) → (∀ w₁
      ≤ r - 3, wdCMem (stp.1 w₁) (st.st0.getD w₁ wdCZero)) → (∀ w₁ ≤ r - 3, wdCMem (stp.2 w₁)
      (st.st1.getD w₁ wdCZero)) → (4 ≤ r → (∀ w₁ ≤ r - 4, wdCMem (tp.1 w₁) (st.tp0.getD w₁ wdCZero))
      ∧ (∀ w₁ ≤ r - 4, wdCMem (tp.2.1 w₁) (st.tp1.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 4, wdCMem (tp.2.2
      w₁) (st.tp2.getD w₁ wdCZero))) → ∃ prs : List GHMidPProbe, compileMidPProbes r ps subN = some
      prs ∧ 0 ≤ fin.qExtraHi - st.qExtraHi ∧ 0 ≤ fin.qCollAddHi - st.qCollAddHi ∧
      ghMidPChainExtraQueries r θ₁ prs u ≤ ((fin.qExtraHi - st.qExtraHi : ℤ) : ℝ) * scale15 ∧
      (((prs.map fun pr ↦ pr.kNext + 2).sum : ℕ) : ℝ) ≤ ((fin.qCollAddHi - st.qCollAddHi : ℤ) : ℝ) *
      scale15 ∧ (∀ w ≤ r, wdCMem (ghMidPChainFinalAmp r θ₁ prs u w) (fin.uVec.getD w wdCZero)) ∧ (∀
      w₁ ≤ r - 2, wdCMem ((ghMidPChainFinal2Row (r - 2) θ₁ θ₂ prs sp).1 w₁) (fin.sp0.getD w₁
      wdCZero)) ∧ (∀ w₁ ≤ r - 2, wdCMem ((ghMidPChainFinal2Row (r - 2) θ₁ θ₂ prs sp).2 w₁)
      (fin.sp1.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 3, wdCMem ((ghMidPChainFinal2Row (r - 3) θ₁ θ₃ prs
      stp).1 w₁) (fin.st0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 3, wdCMem ((ghMidPChainFinal2Row (r - 3)
      θ₁ θ₃ prs stp).2 w₁) (fin.st1.getD w₁ wdCZero)) ∧ (4 ≤ r → (∀ w₁ ≤ r - 4, wdCMem
      ((ghMidPChainFinalTwoPair (r - 4) θ₁ θ₂ prs tp).1 w₁) (fin.tp0.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r -
      4, wdCMem ((ghMidPChainFinalTwoPair (r - 4) θ₁ θ₂ prs tp).2.1 w₁) (fin.tp1.getD w₁ wdCZero)) ∧
      (∀ w₁ ≤ r - 4, wdCMem ((ghMidPChainFinalTwoPair (r - 4) θ₁ θ₂ prs tp).2.2 w₁) (fin.tp2.getD w₁
      wdCZero))) := by
  intro θ₁ θ₂ θ₃ scale15 ps
  induction ps with
  | nil =>
      intro st fin hev u sp stp tp hu hsp0 hsp1 hst0 hst1 htp
      simp only [evalMidPProbes, Option.some.injEq] at hev; subst hev
      refine ⟨[], rfl, (sub_self _).ge, (sub_self _).ge, ?_, ?_, hu, hsp0, hsp1, hst0, hst1, htp⟩
      · simp [ghMidPChainExtraQueries]
      · simp
  | cons p rest ih =>
      intro st fin hev u sp stp tp hu hsp0 hsp1 hst0 hst1 htp; simp only [evalMidPProbes] at hev
      cases hstep : evalMidPProbeStep r false p st with
      | none => rw [hstep] at hev; cases hev
      | some st' =>
          rw [hstep] at hev
          obtain ⟨pr, hcpr, hqEx1_nn, hqColl1_nn, hqEx1_bd, hqColl1_bd, hu1, hsp01, hsp11, hst01,
            hst11, htp1⟩ := midP_probe_step_sound hsub hstep hu hsp0 hsp1 hst0 hst1 htp
          obtain ⟨prsTl, hcTl, hqEx_nn, hqColl_nn, hqEx_tl, hqColl_tl, hu_tl, hsp0_tl, hsp1_tl,
            hst0_tl, hst1_tl, htp_tl⟩ := ih st' fin hev (ghMidPProbeNextAmp r θ₁ pr u)
            (ghMidPProbeNext2Row (r - 2) θ₁ θ₂ pr sp) (ghMidPProbeNext2Row (r - 3) θ₁ θ₃ pr stp)
            (ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr tp) hu1 hsp01 hsp11 hst01 hst11 htp1
          refine ⟨pr :: prsTl, ?_, ?_, ?_, ?_, ?_,
            hu_tl, hsp0_tl, hsp1_tl, hst0_tl, hst1_tl, htp_tl⟩
          · simp [compileMidPProbes, hcpr, hcTl]
          · have hadd := add_nonneg hqEx1_nn hqEx_nn
            have heq : (st'.qExtraHi - st.qExtraHi) + (fin.qExtraHi - st'.qExtraHi) =
                fin.qExtraHi - st.qExtraHi := by ring
            rwa [heq] at hadd
          · have hadd := add_nonneg hqColl1_nn hqColl_nn
            have heq : (st'.qCollAddHi - st.qCollAddHi) + (fin.qCollAddHi - st'.qCollAddHi) =
                fin.qCollAddHi - st.qCollAddHi := by ring
            rwa [heq] at hadd
          · dsimp only [ghMidPChainExtraQueries]
            have hsplit : ((fin.qExtraHi - st.qExtraHi : ℤ) : ℝ) * scale15 =
                ((st'.qExtraHi - st.qExtraHi : ℤ) : ℝ) * scale15 +
                  ((fin.qExtraHi - st'.qExtraHi : ℤ) : ℝ) * scale15 := by
              push_cast; ring
            rw [hsplit]; exact add_le_add hqEx1_bd hqEx_tl
          · rw [List.map_cons, List.sum_cons, Nat.cast_add]
            have hsplit : ((fin.qCollAddHi - st.qCollAddHi : ℤ) : ℝ) * scale15 =
                ((st'.qCollAddHi - st.qCollAddHi : ℤ) : ℝ) * scale15 +
                  ((fin.qCollAddHi - st'.qCollAddHi : ℤ) : ℝ) * scale15 := by
              push_cast; ring
            rw [hsplit]; exact add_le_add hqColl1_bd hqColl_tl
/-- Soundness of `evalMidPRowSummary` (`includeRm3 = false`) for `210 ≤ subN`: compiles
  `spec`
  to `(kInit, probes, kZoom)` and certifies all query bounds, zoom hit probability, and
  final fiber
  weight enclosures stored in `s: MidPSummary`. -/
theorem evalMidPRowSummary_sound {m r subN : ℕ} {spec : MidPRowSpec} {s : MidPSummary}
    (hsum : evalMidPRowSummary m r false spec = some s) (hsub : 210 ≤ subN) :
    let p := Stage2CertInternals.gridExp m; let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ)); let θ₃ := Real.arcsin (√3 / √(2 ^ subN : ℝ))
    let θZoom := Real.arcsin (1 / √(((r - 1) * 2 ^ (subN - p) : ℕ) : ℝ))
    let scale15 := ((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR
    (3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ m = 2 ^ p) ∧ ∃ kInit probes kZoom, compileMidPRow m r spec subN =
      some (kInit, probes, kZoom) ∧ ((ghMidPMaxQueries kInit probes kZoom : ℕ) : ℝ) ≤ 12 * ((π /
      4) * √(2 ^ subN : ℝ)) ∧ 0 ≤ s.qDistHi ∧ 0 ≤ s.qCollHi ∧ 0 ≤ s.qZoomHi ∧ ((kInit + 1 : ℕ) :
      ℝ) + ghMidPChainExtraQueries r θ₁ probes (ghMidPInitAmp r θ₁ kInit) ≤ (s.qDistHi : ℝ) *
      scale15 ∧ (ghMidPPreMaxQueries kInit probes : ℝ) ≤ (s.qCollHi : ℝ) * scale15 ∧ ((kZoom + 1 :
      ℕ) : ℝ) ≤ (s.qZoomHi : ℝ) * scale15 ∧ (s.zHitLo : ℝ) / wdScaleR ≤ Real.sin ((2 * (kZoom : ℝ) +
      1) * θZoom) ^ 2 ∧ (∀ w ≤ r, 0 ≤ s.uAbs2Hi.getD w 0 ∧ Complex.normSq (ghMidPChainFinalAmp r θ₁
      probes (ghMidPInitAmp r θ₁ kInit) w) ≤ (s.uAbs2Hi.getD w 0 : ℝ) / wdScaleR) ∧ (∀ w₁ ≤ r - 2, 0
      ≤ s.z0Abs2Hi.getD w₁ 0 ∧ Complex.normSq ((ghMidPChainFinal2Row (r - 2) θ₁ θ₂ probes
      (ghMidPInit2Row (r - 2) θ₁ θ₂ kInit)).1 w₁) ≤ (s.z0Abs2Hi.getD w₁ 0 : ℝ) / wdScaleR) ∧ (∀ w₁ ≤
      r - 2, 0 ≤ s.z1Abs2Hi.getD w₁ 0 ∧ Complex.normSq ((ghMidPChainFinal2Row (r - 2) θ₁ θ₂ probes
      (ghMidPInit2Row (r - 2) θ₁ θ₂ kInit)).2 w₁) ≤ (s.z1Abs2Hi.getD w₁ 0 : ℝ) / wdScaleR) ∧ (∀ wt ≤
      r, 0 ≤ s.stWtHi.getD wt 0 ∧ ((if wt ≤ r - 3 then ((r - 3).choose wt : ℝ) * Complex.normSq
      ((ghMidPChainFinal2Row (r - 3) θ₁ θ₃ probes (ghMidPInit2Row (r - 3) θ₁ θ₃ kInit)).1 wt) else
      0) + (if 1 ≤ wt ∧ wt - 1 ≤ r - 3 then ((r - 3).choose (wt - 1) : ℝ) * Complex.normSq
      ((ghMidPChainFinal2Row (r - 3) θ₁ θ₃ probes (ghMidPInit2Row (r - 3) θ₁ θ₃ kInit)).2 (wt - 1))
      else 0)) ≤ (s.stWtHi.getD wt 0 : ℝ) / wdScaleR) ∧ (4 ≤ r → ∀ wt ≤ r, 0 ≤ s.tpWtHi.getD wt 0 ∧
      ((if wt ≤ r - 4 then ((r - 4).choose wt : ℝ) * Complex.normSq ((ghMidPChainFinalTwoPair (r -
      4) θ₁ θ₂ probes (ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit)).1 wt) else 0) + (if 1 ≤ wt ∧ wt - 1 ≤
      r - 4 then (2 * (r - 4).choose (wt - 1) : ℝ) * Complex.normSq ((ghMidPChainFinalTwoPair (r -
      4) θ₁ θ₂ probes (ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit)).2.1 (wt - 1)) else 0) + (if 2 ≤ wt ∧
      wt - 2 ≤ r - 4 then ((r - 4).choose (wt - 2) : ℝ) * Complex.normSq ((ghMidPChainFinalTwoPair
      (r - 4) θ₁ θ₂ probes (ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit)).2.2 (wt - 2)) else 0)) ≤
      (s.tpWtHi.getD wt 0 : ℝ) / wdScaleR) := by
  intro p θ₁ θ₂ θ₃ θZoom scale15; have hB : 0 < wdScaleR := wdScaleR_pos
  have hs15_nn : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
  have hsub200 : 200 ≤ subN := (by omega); unfold evalMidPRowSummary at hsum
  dsimp only [p] at hsum ⊢
  by_cases hhdr : 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ 2 ≤ p ∧ p ≤ 10 ∧ m = 2 ^ p ∧
      0 < spec.a0Den ∧ 0 < spec.kzDen
  · rw [ite_eq_left hhdr] at hsum
    rcases hhdr with ⟨hr3, hr16, hrm, _, hp10, hm_pow, ha0Den, hkzDen⟩
    set a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den
    set phi01 := (ghMaxZ 0 (Int.sub a0IV.1 1), Int.add a0IV.2 1)
    by_cases hang0 : (midPBleZ 0 phi01.1 &&
        midPBleZ (midPFastMulIV phi01 (midPSqrtRatioIv 4)).2 (Int.mul 1024 midPScaleZ)) = true
    · rw [ite_eq_left hang0] at hsum; set kInit := wdStepCount spec.a0Num spec.a0Den subN
      set kZoom := wdMidPStepCount ((r - 1) * 2 ^ (subN - p)) spec.kzNum spec.kzDen
      obtain ⟨hphi01_mem0, _, hq0_nn, hq0_bound⟩ :=
        ghZoomStepCount_bounds (aNum := spec.a0Num) ha0Den hsub200 1
      have hphi01_eq : phi01 = (max 0 (a0IV.1 - 1), a0IV.2 + 1) := by
        dsimp only [phi01]; rw [ghMaxZ_eq]; rfl
      have hphi01_mem : wdMem ((2 * (kInit : ℝ) + 1) * θ₁) phi01 := by
        rw [hphi01_eq]; exact hphi01_mem0
      obtain ⟨c01, s01, c02, s02, c03, s03, htc01, htc02, htc03, htrig01, htrig02, htrig03⟩ :=
        midP_phi123_trigCPS_elim (Option MidPSummary) hsub200
          (c := 2 * (kInit : ℝ) + 1) hphi01_mem hang0
      rw [htc01, htc02, htc03] at hsum; clear htc01 htc02 htc03
      clear_value phi01
      have hu0_raw : ∀ w ≤ r, wdCMem (ghMidPInitAmp r θ₁ kInit w)
          ((midPFastDickeStepVec r c01 s01 (midPOneHot0 (Nat.add r 1))).getD w wdCZero) := by
        intro w _; have hr1_eq : Nat.add r 1 = r + 1 := rfl; rw [hr1_eq]
        exact midPFastDickeStepVec_mem r htrig01.1 htrig01.2 (midPOneHot0_mem r) w
      obtain ⟨u0, hu0_eq, hu0_mem⟩ := midPSeqCIVList_elim (Option MidPSummary) (midPFastDickeStepVec
        r c01 s01 (midPOneHot0 (Nat.add r 1))) (P := fun ys ↦ ∀ w ≤ r, wdCMem (ghMidPInitAmp r θ₁
        kInit w) (ys.getD w wdCZero)) hu0_raw
      rw [hu0_eq] at hsum; clear hu0_eq hu0_raw
      have huRm2_raw : ∀ w, wdCMem (ghMidPInitAmp (r - 2) θ₁ kInit w)
          ((midPFastDickeStepVec (r - 2) c01 s01 (midPOneHot0 (r - 1))).getD w wdCZero) := by
        intro w; have h_eq : r - 1 = (r - 2) + 1 := (by omega); rw [h_eq]
        exact midPFastDickeStepVec_mem (r - 2) htrig01.1 htrig01.2 (midPOneHot0_mem (r - 2)) w
      obtain ⟨uRm2, huRm2_eq, huRm2_mem⟩ := midPSeqCIVList_elim (Option MidPSummary)
        (midPFastDickeStepVec (r - 2) c01 s01 (midPOneHot0 (r - 1))) (P := fun ys ↦ ∀ w, wdCMem
        (ghMidPInitAmp (r - 2) θ₁ kInit w) (ys.getD w wdCZero)) huRm2_raw
      rw [huRm2_eq] at hsum; clear huRm2_eq huRm2_raw
      obtain ⟨sp0Init, hsp0_eq, hsp0_init⟩ := midPSeqCIVList_elim (Option MidPSummary) (uRm2.map
        (midPFastCRMul c02)) (P := fun ys ↦ ∀ w₁ ≤ r - 2, wdCMem ((ghMidPInit2Row (r - 2) θ₁ θ₂
        kInit).1 w₁) (ys.getD w₁ wdCZero)) (fun w₁ _ ↦ map_midPFastCRMul_mem htrig02.1 (huRm2_mem
        w₁))
      rw [hsp0_eq] at hsum; clear hsp0_eq
      obtain ⟨sp1Init, hsp1_eq, hsp1_init⟩ := midPSeqCIVList_elim (Option MidPSummary) (uRm2.map
        (midPFastCRMul s02)) (P := fun ys ↦ ∀ w₁ ≤ r - 2, wdCMem ((ghMidPInit2Row (r - 2) θ₁ θ₂
        kInit).2 w₁) (ys.getD w₁ wdCZero)) (fun w₁ _ ↦ map_midPFastCRMul_mem htrig02.2 (huRm2_mem
        w₁))
      rw [hsp1_eq] at hsum; clear hsp1_eq
      have huRm3_raw : ∀ w, wdCMem (ghMidPInitAmp (r - 3) θ₁ kInit w)
          ((midPFastDickeStepVec (r - 3) c01 s01 (midPOneHot0 (r - 2))).getD w wdCZero) := by
        intro w; have h_eq : r - 2 = (r - 3) + 1 := (by omega); rw [h_eq]
        exact midPFastDickeStepVec_mem (r - 3) htrig01.1 htrig01.2 (midPOneHot0_mem (r - 3)) w
      obtain ⟨uRm3, huRm3_eq, huRm3_mem⟩ := midPSeqCIVList_elim (Option MidPSummary)
        (midPFastDickeStepVec (r - 3) c01 s01 (midPOneHot0 (r - 2))) (P := fun ys ↦ ∀ w, wdCMem
        (ghMidPInitAmp (r - 3) θ₁ kInit w) (ys.getD w wdCZero)) huRm3_raw
      rw [huRm3_eq] at hsum; clear huRm3_eq huRm3_raw
      obtain ⟨st0Init, hst0_eq, hst0_init⟩ := midPSeqCIVList_elim (Option MidPSummary) (uRm3.map
        (midPFastCRMul c03)) (P := fun ys ↦ ∀ w₁ ≤ r - 3, wdCMem ((ghMidPInit2Row (r - 3) θ₁ θ₃
        kInit).1 w₁) (ys.getD w₁ wdCZero)) (fun w₁ _ ↦ map_midPFastCRMul_mem htrig03.1 (huRm3_mem
        w₁))
      rw [hst0_eq] at hsum; clear hst0_eq
      obtain ⟨st1Init, hst1_eq, hst1_init⟩ := midPSeqCIVList_elim (Option MidPSummary) (uRm3.map
        (midPFastCRMul s03)) (P := fun ys ↦ ∀ w₁ ≤ r - 3, wdCMem ((ghMidPInit2Row (r - 3) θ₁ θ₃
        kInit).2 w₁) (ys.getD w₁ wdCZero)) (fun w₁ _ ↦ map_midPFastCRMul_mem htrig03.2 (huRm3_mem
        w₁))
      rw [hst1_eq] at hsum; clear hst1_eq
      let runChain (tp0I tp1I tp2I q10I q11I : List WDCVal) : Option MidPSummary :=
        let stInit : MidPProbeState :=
          ⟨0, 0, u0, sp0Init, sp1Init, st0Init, st1Init, tp0I, tp1I, tp2I, q10I, q11I⟩
        match evalMidPProbes r false spec.probes stInit with
        | none => none
        | some fin =>
            let q0Hi := wdDivCeil (Int.mul (Int.add a0IV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
            let qDistHi := Int.add q0Hi fin.qExtraHi; let qCollHi := Int.add q0Hi fin.qCollAddHi
            let kzIV := wdRat (spec.kzNum : ℤ) spec.kzDen
            let azIV : WDIVal := (ghMaxZ 0 (Int.sub kzIV.1 1), Int.add kzIV.2 1)
            if midPBleZ 0 azIV.1 && midPBleZ azIV.2 (Int.mul 1024 midPScaleZ) then
              midPTrigCPS azIV fun _ sAz ↦
              let zHitLo := (ghSqIV sAz).1
              let qzSub := wdDivCeil (Int.mul (Int.add kzIV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
              let uScale := midPUnpaddedZoomScaleHi15 (r - 1) m
              let qZoomHi := wdDivCeil (Int.mul qzSub uScale) midPScaleZ
              if midPBleZ 0 zHitLo && midPBleZ zHitLo midPScaleZ &&
                  midPBleZ (Int.add qCollHi qZoomHi) (Int.mul 12 midPScaleZ) then
                midPSeqInt qDistHi fun qdF ↦
                midPSeqInt qCollHi fun qcF ↦
                midPSeqInt qZoomHi fun qzF ↦
                midPSeqInt zHitLo fun zhF ↦
                midPSeqZList (fin.uVec.map wdCAbs2Hi) fun uAbs ↦
                midPSeqZList (fin.sp0.map wdCAbs2Hi) fun z0Abs ↦
                midPSeqZList (fin.sp1.map wdCAbs2Hi) fun z1Abs ↦
                let tpWt := if Nat.ble 4 r then midPCollapseTwoPairWt (r - 4) r fin.tp0 fin.tp1
                  fin.tp2 else List.replicate (Nat.add r 1) 0
                let stWt := midPCollapse2RowWt (r - 3) r fin.st0 fin.st1
                let q1Wt := if Nat.ble 4 r && false then midPCollapse2RowWt (r - 4) r fin.q10
                  fin.q11 else List.replicate (Nat.add r 1) 0
                midPSeqZList tpWt fun tpF ↦
                midPSeqZList stWt fun stF ↦
                midPSeqZList q1Wt fun q1F ↦
                  some ⟨qdF, qcF, qzF, zhF, uAbs, z0Abs, z1Abs, tpF, stF, q1F⟩
              else none
            else none
      have htp_ex : ∃ tp0I tp1I tp2I : List WDCVal, (4 ≤ r → (∀ w₁ ≤ r - 4, wdCMem
        ((ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit).1 w₁) (tp0I.getD w₁ wdCZero)) ∧ (∀ w₁ ≤ r - 4,
        wdCMem ((ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit).2.1 w₁) (tp1I.getD w₁ wdCZero)) ∧ (∀ w₁ ≤
        r - 4, wdCMem ((ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit).2.2 w₁) (tp2I.getD w₁ wdCZero))) ∧
        runChain tp0I tp1I tp2I [] [] = some s := by
        by_cases hr4 : 4 ≤ r
        · have hble4 : Nat.ble 4 r = true := Nat.ble_eq.mpr hr4
          conv at hsum => lhs; rw [ite_eq_left hble4]
          have huRm4_raw : ∀ w, wdCMem (ghMidPInitAmp (r - 4) θ₁ kInit w)
              ((midPFastDickeStepVec (r - 4) c01 s01 (midPOneHot0 (r - 3))).getD w wdCZero) := by
            intro w; have h_eq : r - 3 = (r - 4) + 1 := (by omega); rw [h_eq]
            exact midPFastDickeStepVec_mem (r - 4) htrig01.1 htrig01.2 (midPOneHot0_mem (r - 4)) w
          obtain ⟨uRm4, huRm4_eq, huRm4⟩ := midPSeqCIVList_elim (Option MidPSummary)
            (midPFastDickeStepVec (r - 4) c01 s01 (midPOneHot0 (r - 3))) (P := fun ys ↦ ∀ w, wdCMem
            (ghMidPInitAmp (r - 4) θ₁ kInit w) (ys.getD w wdCZero)) huRm4_raw
          rw [huRm4_eq] at hsum; clear huRm4_eq huRm4_raw
          obtain ⟨uP2, huP2_eq, huP2⟩ := midPSeqCIVList_elim (Option MidPSummary)
            (midPFastDickeStepVec 2 c02 s02 (midPOneHot0 3))
            (P := fun ys ↦ ∀ j, wdCMem (ghMidPInitAmp 2 θ₂ kInit j) (ys.getD j wdCZero))
            (midPFastDickeStepVec_mem 2 htrig02.1 htrig02.2 (midPOneHot0_mem 2))
          rw [huP2_eq] at hsum; clear huP2_eq
          obtain ⟨tp0I, htp0_eq, htp0⟩ := midPSeqCIVList_elim (Option MidPSummary) (uRm4.map
            (midPFastCMul (uP2.getD 0 wdCZero))) (P := fun ys ↦ ∀ w₁ ≤ r - 4, wdCMem
            ((ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit).1 w₁) (ys.getD w₁ wdCZero)) (fun w₁ _ ↦
            map_midPFastCMul_mem (huP2 0) (huRm4 w₁))
          rw [htp0_eq] at hsum; clear htp0_eq
          obtain ⟨tp1I, htp1_eq, htp1⟩ := midPSeqCIVList_elim (Option MidPSummary) (uRm4.map
            (midPFastCMul (uP2.getD 1 wdCZero))) (P := fun ys ↦ ∀ w₁ ≤ r - 4, wdCMem
            ((ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit).2.1 w₁) (ys.getD w₁ wdCZero)) (fun w₁ _ ↦
            map_midPFastCMul_mem (huP2 1) (huRm4 w₁))
          rw [htp1_eq] at hsum; clear htp1_eq
          obtain ⟨tp2I, htp2_eq, htp2⟩ := midPSeqCIVList_elim (Option MidPSummary) (uRm4.map
            (midPFastCMul (uP2.getD 2 wdCZero))) (P := fun ys ↦ ∀ w₁ ≤ r - 4, wdCMem
            ((ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit).2.2 w₁) (ys.getD w₁ wdCZero)) (fun w₁ _ ↦
            map_midPFastCMul_mem (huP2 2) (huRm4 w₁))
          rw [htp2_eq] at hsum; clear htp2_eq
          conv at hsum => lhs; rw [ite_eq_right Bool.noConfusion]
          exact ⟨tp0I, tp1I, tp2I, fun _ ↦ ⟨htp0, htp1, htp2⟩, hsum⟩
        · have hnot_ble4 : ¬(Nat.ble 4 r = true) := (by rw [Nat.ble_eq]; exact hr4)
          conv at hsum => lhs; rw [ite_eq_right hnot_ble4]
          exact ⟨[], [], [], fun h4 ↦ absurd h4 hr4, hsum⟩
      obtain ⟨tp0I, tp1I, tp2I, htp_init, hsum_rc⟩ := htp_ex; clear hsum
      dsimp only [runChain] at hsum_rc
      set stInit : MidPProbeState :=
        ⟨0, 0, u0, sp0Init, sp1Init, st0Init, st1Init, tp0I, tp1I, tp2I, [], []⟩
      cases hpr : evalMidPProbes r false spec.probes stInit with
      | none => rw [hpr] at hsum_rc; cases hsum_rc
      | some fin =>
          rw [hpr] at hsum_rc; dsimp only at hsum_rc
          set q0Hi := wdDivCeil (Int.mul (Int.add a0IV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
          set qDistHi := Int.add q0Hi fin.qExtraHi; set qCollHi := Int.add q0Hi fin.qCollAddHi
          set kzIV := wdRat (spec.kzNum : ℤ) spec.kzDen
          set azIV := (ghMaxZ 0 (Int.sub kzIV.1 1), Int.add kzIV.2 1)
          by_cases haz : (midPBleZ 0 azIV.1 && midPBleZ azIV.2 (Int.mul 1024 midPScaleZ)) = true
          · rw [ite_eq_left haz] at hsum_rc; have hm_pos : 0 < m := (by rw [hm_pow]; positivity)
            obtain ⟨haz_mem0, hqz_nn0, hqz_bd0⟩ :=
              ghMidPZoomStepCount_bounds (wt := r - 1) (by omega) (by omega) hm_pos hm_pow
                hp10 hsub hkzDen (kzNum := spec.kzNum)
            have haz_eq : azIV = (max 0 (kzIV.1 - 1), kzIV.2 + 1) := by
              dsimp only [azIV]; rw [ghMaxZ_eq]; rfl
            have haz_mem : wdMem ((2 * (kZoom : ℝ) + 1) * θZoom) azIV := by
              rw [haz_eq]; exact haz_mem0
            obtain ⟨_, sAz, htcAz, hsAz_mem⟩ :=
              midPTrigCPS_sin_elim (Option MidPSummary) haz_mem haz
            rw [htcAz] at hsum_rc; clear htcAz
            clear_value azIV
            set zHitLo := (ghSqIV sAz).1
            set qzSub := wdDivCeil (Int.mul (Int.add kzIV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
            set uScale := midPUnpaddedZoomScaleHi15 (r - 1) m
            set qZoomHi := wdDivCeil (Int.mul qzSub uScale) midPScaleZ
            by_cases hzg : (midPBleZ 0 zHitLo && midPBleZ zHitLo midPScaleZ &&
                midPBleZ (Int.add qCollHi qZoomHi) (Int.mul 12 midPScaleZ)) = true
            · rw [ite_eq_left hzg] at hsum_rc; rw [midPSeqInt_eq] at hsum_rc
              rw [midPSeqInt_eq] at hsum_rc; rw [midPSeqInt_eq] at hsum_rc
              rw [midPSeqInt_eq] at hsum_rc; rw [midPSeqZList_eq] at hsum_rc
              rw [midPSeqZList_eq] at hsum_rc; rw [midPSeqZList_eq] at hsum_rc
              rw [midPSeqZList_eq] at hsum_rc; rw [midPSeqZList_eq] at hsum_rc
              rw [midPSeqZList_eq] at hsum_rc
              injection hsum_rc with hs_eq
              subst hs_eq
              obtain ⟨probes, hcProbes, hqEx_nn, hqColl_nn, hqEx_bd, hqColl_bd, huf, hspf0, hspf1,
                hstf0, hstf1, htpf⟩ := midP_probes_chain_sound hsub200 spec.probes stInit fin hpr
                (ghMidPInitAmp r θ₁ kInit) (ghMidPInit2Row (r - 2) θ₁ θ₂ kInit) (ghMidPInit2Row (r -
                3) θ₁ θ₃ kInit) (ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit) hu0_mem hsp0_init hsp1_init
                hst0_init hst1_init htp_init
              simp only [Bool.and_eq_true, midPBleZ_iff] at hzg
              have hzHit_lo : (zHitLo : ℝ) / wdScaleR ≤
                  Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2 := by
                dsimp only [zHitLo]; rw [ghSqIV_eq]; exact (wdMem_sq hsAz_mem).1
              have hq0_eq : q0Hi = wdDivCeil ((a0IV.2 + 2 * (1 : ℤ)) * wdPi4InvHi)
                  (2 * (wdScale : ℤ)) := rfl
              have hqz_eq : qZoomHi = wdDivCeil (wdDivCeil ((kzIV.2 + 2) * wdPi4InvHi) (2 * (wdScale
                : ℤ)) * uScale) (wdScale : ℤ) := rfl
              have hqd_eq : qDistHi = q0Hi + fin.qExtraHi := rfl
              have hqc_eq : qCollHi = q0Hi + fin.qCollAddHi := rfl
              dsimp only [stInit] at hqEx_nn hqColl_nn hqEx_bd hqColl_bd
              rw [sub_zero] at hqEx_nn hqColl_nn hqEx_bd hqColl_bd
              have hq0_nn' : 0 ≤ q0Hi := hq0_eq ▸ hq0_nn
              have hq0_bd' : ((kInit + 1 : ℕ) : ℝ) ≤ (q0Hi : ℝ) * scale15 := hq0_eq ▸ hq0_bound
              have hqz_nn' : 0 ≤ qZoomHi := hqz_eq ▸ hqz_nn0
              have hqz_bd' : ((kZoom + 1 : ℕ) : ℝ) ≤ (qZoomHi : ℝ) * scale15 := hqz_eq ▸ hqz_bd0
              have hqd_nn : 0 ≤ qDistHi := hqd_eq ▸ add_nonneg hq0_nn' hqEx_nn
              have hqc_nn : 0 ≤ qCollHi := hqc_eq ▸ add_nonneg hq0_nn' hqColl_nn
              clear_value qZoomHi uScale qzSub zHitLo qDistHi qCollHi q0Hi kzIV a0IV
              have hqDist_bd : ((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQueries r θ₁ probes
                (ghMidPInitAmp r θ₁ kInit) ≤ (qDistHi : ℝ) * scale15 := by
                rw [hqd_eq, Int.cast_add, add_mul]; exact add_le_add hq0_bd' hqEx_bd
              have hqColl_bd' :
                  (ghMidPPreMaxQueries kInit probes : ℝ) ≤ (qCollHi : ℝ) * scale15 := by
                unfold ghMidPPreMaxQueries; rw [hqc_eq, Nat.cast_add, Int.cast_add, add_mul]
                exact add_le_add hq0_bd' hqColl_bd
              have hqMax_bd : ((ghMidPMaxQueries kInit probes kZoom : ℕ) : ℝ) ≤ 12 * ((π / 4) * √(2
                ^ subN : ℝ)) := by
                have hsum_q : ((ghMidPMaxQueries kInit probes kZoom : ℕ) : ℝ) ≤
                    ((qCollHi + qZoomHi : ℤ) : ℝ) * scale15 := by
                  unfold ghMidPMaxQueries; rw [Nat.cast_add, Int.cast_add, add_mul]
                  exact add_le_add hqColl_bd' hqz_bd'
                have h12Z : qCollHi + qZoomHi ≤ 12 * (wdScale : ℤ) := hzg.2
                have h12R : ((qCollHi + qZoomHi : ℤ) : ℝ) ≤ 12 * wdScaleR := by
                  unfold wdScaleR; exact_mod_cast h12Z
                calc ((ghMidPMaxQueries kInit probes kZoom : ℕ) : ℝ)
                    ≤ ((qCollHi + qZoomHi : ℤ) : ℝ) * scale15 := hsum_q
                  _ ≤ (12 * wdScaleR) * scale15 := mul_le_mul_of_nonneg_right h12R hs15_nn
                  _ = 12 * ((π / 4) * √(2 ^ subN : ℝ)) := by
                      dsimp only [scale15]; rw [mul_assoc, mul_div_cancel₀ _ hB.ne']
              have hcomp : compileMidPRow m r spec subN = some (kInit, probes, kZoom) := by
                unfold compileMidPRow; dsimp only; rw [ite_eq_left ⟨ha0Den, hkzDen⟩, hcProbes]
              refine ⟨⟨hr3, hr16, hrm, hm_pow⟩, kInit, probes, kZoom, hcomp, hqMax_bd, hqd_nn,
                hqc_nn, hqz_nn', hqDist_bd, hqColl_bd', hqz_bd', hzHit_lo, ?_, ?_, ?_, ?_, ?_⟩
              · intro w hw
                exact ⟨map_wdCAbs2Hi_getD_nonneg _ _, normSq_le_map_wdCAbs2Hi_getD (huf w hw)⟩
              · intro w₁ hw₁
                exact ⟨map_wdCAbs2Hi_getD_nonneg _ _, normSq_le_map_wdCAbs2Hi_getD (hspf0 w₁ hw₁)⟩
              · intro w₁ hw₁
                exact ⟨map_wdCAbs2Hi_getD_nonneg _ _, normSq_le_map_wdCAbs2Hi_getD (hspf1 w₁ hw₁)⟩
              · exact midPCollapse2RowWt_bound (r - 3) r hstf0 hstf1
              · intro hr4; have hble4 : Nat.ble 4 r = true := Nat.ble_eq.mpr hr4
                simp only [hble4, ↓reduceIte]; obtain ⟨ht0, ht1, ht2⟩ := htpf hr4
                exact midPCollapseTwoPairWt_bound (r - 4) r ht0 ht1 ht2
            · rw [ite_eq_right hzg] at hsum_rc; cases hsum_rc
          · rw [ite_eq_right haz] at hsum_rc; cases hsum_rc
    · rw [ite_eq_right hang0] at hsum; cases hsum
  · rw [ite_eq_right hhdr] at hsum; cases hsum
/-- Worst-case query bound `≤ 12 * ((π / 4) * √(2 ^ subN))` extracted from
  `evalMidPRowSummary`. -/
theorem evalMidPRowSummary_qBound {m r subN kInit kZoom : ℕ} {spec : MidPRowSpec} {s : MidPSummary}
    {probes : List GHMidPProbe} (hsum : evalMidPRowSummary m r false spec = some s) (hsub : 210 ≤
    subN) (hcomp : compileMidPRow m r spec subN = some (kInit, probes, kZoom)) : ((ghMidPMaxQueries
    kInit probes kZoom : ℕ) : ℝ) ≤ 12 * ((π / 4) * √(2 ^ subN : ℝ)) := by
  obtain ⟨_, kI, prs, kZ, hc, hq, _⟩ := evalMidPRowSummary_sound hsum hsub; rw [hcomp] at hc
  injection hc with htri
  rcases Prod.mk.inj htri with ⟨rfl, hrest⟩; rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩; exact hq
private lemma midP_divCeil_scale15_bound {pReal cReal scale15 : ℝ} {pHi cHi : ℤ} (hs15 : 0 ≤
    scale15) (hp0 : 0 ≤ pReal) (hp : pReal ≤ (pHi : ℝ) / wdScaleR) (hc0 : 0 ≤ cReal) (hc : cReal ≤
    (cHi : ℝ) * scale15) : pReal * cReal ≤ (wdDivCeil (Int.mul pHi cHi) midPScaleZ : ℝ) *
    scale15 := by
  have hBZ : (0 : ℤ) < midPScaleZ := (by unfold midPScaleZ; norm_num)
  have hm := mul_le_mul hp hc hc0 (hp0.trans hp)
  have heq : ((pHi : ℝ) / wdScaleR) * ((cHi : ℝ) * scale15) =
      (((Int.mul pHi cHi : ℤ) : ℝ) / (midPScaleZ : ℝ)) * scale15 := by
    change ((pHi : ℝ) / wdScaleR) * ((cHi : ℝ) * scale15) =
      (((pHi * cHi : ℤ) : ℝ) / (midPScaleZ : ℝ)) * scale15
    unfold midPScaleZ wdScaleR wdScale; push_cast; ring
  have hceil := le_wdDivCeil (a := Int.mul pHi cHi) hBZ
  exact (hm.trans_eq heq).trans (mul_le_mul_of_nonneg_right hceil hs15)
/-- Full 1-pass Bellman soundness for `evalMidPStepFromSummary` (`includeRm3 = false`) at
  `210 ≤ subN`: bounds `ghMidPOneDimUpper` by `(hir: ℝ) * (((π / 4) * √(2 ^ subN)) /
  M_scale)`. -/
theorem evalMidPStepFromSummary_sound {m r subN hir : ℕ} {rowSpec : MidPRowSpec} {s : MidPSummary}
    {vNext : List ℕ} (hsum : evalMidPRowSummary m r false rowSpec = some s) (hstep :
    evalMidPStepFromSummary m r false s vNext = some hir) (hsub : 210 ≤ subN) {fNext : ℕ → ℝ} (hf :
    ∀ u ≤ r, 0 ≤ fNext u ∧ fNext u ≤ (vNext.getD u 0 : ℝ) * (((π / 4) * √(2 ^ subN : ℝ)) /
    (Stage2CertInternals.M_scale : ℝ))) :
    let p := Stage2CertInternals.gridExp m
    ghMidPOneDimUpper subN p m (compileMidPRow m r rowSpec subN) fNext r ≤
      (hir : ℝ) * (((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ)) := by
  intro p; have hB : 0 < wdScaleR := wdScaleR_pos; set D : ℝ := (2 ^ subN : ℝ)
  set scale : ℝ := ((π / 4) * √D) / (Stage2CertInternals.M_scale : ℝ)
  set scale15 : ℝ := ((π / 4) * √D) / wdScaleR
  have hscale_eq : scale = 1000000 * scale15 := by
    dsimp only [scale, scale15]; unfold Stage2CertInternals.M_scale wdScaleR wdScale; ring
  have hs15_nn : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
  have hscale_nn : 0 ≤ scale := (by rw [hscale_eq]; positivity)
  obtain ⟨⟨hr3, hr16, hrm, hm_pow⟩, kInit, probes, kZoom, hcomp, _, _, _, _, hqDist, hqColl, hqZoom,
    hzHit_lo, huAbs, hz0Abs, hz1Abs, hstWt, htpWt⟩ := evalMidPRowSummary_sound hsum hsub
  unfold evalMidPStepFromSummary at hstep
  by_cases hg1 : 4 ≤ m ∧ 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ r < vNext.length
  · rw [ite_eq_left hg1] at hstep
    by_cases hg2 : (midPBleZ 0 s.zHitLo && midPBleZ s.zHitLo midPScaleZ &&
        midPBleZ (Int.add s.qCollHi s.qZoomHi) (Int.mul 12 midPScaleZ)) = true
    · rw [ite_eq_left hg2] at hstep; dsimp only at hstep
      set fHi : ℕ → ℤ := fun u ↦ Int.mul (Int.ofNat (vNext.getD u 0)) 1000000
      set remMiss1 : ℤ := Int.add s.qZoomHi (fHi 1)
      set remHit1 : ℤ := Int.add s.qZoomHi (wdDivCeil (Int.mul (Int.sub midPScaleZ s.zHitLo) (fHi
        1)) midPScaleZ)
      set remDistZ : ℤ := midPSumRangeZ r fun w ↦
        let cNext := if w + 1 == r then remMiss1 else fHi (r - w)
        wdDivCeil
          (Int.mul (Int.mul (Int.ofNat (ghBinom r w)) (s.uAbs2Hi.getD w 0)) cNext)
          midPScaleZ
      set remSp0Z : ℤ := midPSumRangeZ (r - 1) fun w1 ↦ wdDivCeil (Int.mul (Int.mul (Int.ofNat
        (ghBinom (r - 2) w1)) (s.z0Abs2Hi.getD w1 0)) (fHi (r - w1))) midPScaleZ
      set remSp1Z : ℤ := midPSumRangeZ (r - 1) fun w1 ↦
        let cNext := if w1 + 2 == r then remHit1 else fHi (r - 1 - w1)
        wdDivCeil
          (Int.mul (Int.mul (Int.ofNat (ghBinom (r - 2) w1)) (s.z1Abs2Hi.getD w1 0)) cNext)
          midPScaleZ
      set remTpZ : ℤ := if Nat.ble 4 r then midPSumRangeZ (r - 1) fun wt ↦ wdDivCeil (Int.mul
        (s.tpWtHi.getD wt 0) (fHi (r - wt))) midPScaleZ else 0
      set remStZ : ℤ := midPSumRangeZ (r - 1) fun wt ↦
        wdDivCeil (Int.mul (s.stWtHi.getD wt 0) (fHi (r - wt))) midPScaleZ
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hstep
      set mPow : ℤ := Int.ofNat (m ^ r)
      set nInjZ : ℤ := if Nat.ble r m then Int.ofNat (midPDescFact m r) else 0
      set nSpZ : ℤ := Int.ofNat (ghBinom r 2 * midPDescFact m (r - 1))
      set nTpZ : ℤ :=
        if Nat.ble 4 r then Int.ofNat (3 * ghBinom r 4 * midPDescFact m (r - 2)) else 0
      set nStZ : ℤ := Int.ofNat (ghBinom r 3 * midPDescFact m (r - 2))
      set usedZ : ℤ := Int.add (Int.add (Int.add (Int.add nInjZ nSpZ) nTpZ) nStZ) 0
      set nRemZ : ℤ := Int.sub mPow usedZ; by_cases hnRem : midPBleZ 0 nRemZ = true
      · rw [ite_eq_left hnRem] at hstep; set tInj := Int.mul nInjZ (Int.add s.qDistHi remDistZ)
        set tSp := Int.mul nSpZ (Int.add s.qCollHi (Int.add remSp0Z remSp1Z))
        set tTp := Int.mul nTpZ (Int.add s.qCollHi remTpZ)
        set tSt := Int.mul nStZ (Int.add s.qCollHi remStZ)
        set tSq := Int.mul (0 : ℤ) (Int.add s.qCollHi 0)
        set tRem := Int.mul nRemZ (Int.add s.qCollHi (fHi r))
        set tot := Int.add (Int.add (Int.add (Int.add (Int.add tInj tSp) tTp) tSt) tSq) tRem
        set outZ := wdDivCeil tot (Int.mul mPow 1000000); by_cases hout : midPBleZ 0 outZ = true
        · rw [ite_eq_left hout] at hstep
          injection hstep with hhir
          subst hhir; simp only [midPBleZ_iff] at hnRem hout
          have hf_s15 : ∀ u ≤ r, 0 ≤ fNext u ∧ fNext u ≤ (fHi u : ℝ) * scale15 := by
            intro u hu; obtain ⟨hnn, hbd⟩ := hf u hu; refine ⟨hnn, ?_⟩
            have h1 : (vNext.getD u 0 : ℝ) * scale = (fHi u : ℝ) * scale15 := by
              rw [hscale_eq]; change (vNext.getD u 0 : ℝ) * (1000000 * scale15) =
                (((vNext.getD u 0 : ℤ) * 1000000 : ℤ) : ℝ) * scale15
              push_cast; ring
            exact hbd.trans_eq h1
          unfold ghMidPOneDimUpper; have hr0 : r ≠ 0 := (by omega); rw [ite_eq_right hr0, hcomp]
          dsimp only; rw [ite_eq_left ⟨hr3, hr16, hrm, hm_pow⟩]; set θ₁ := Real.arcsin (1 / √D)
          set θ₂ := Real.arcsin (√2 / √D); set θ₃ := Real.arcsin (√3 / √D)
          set θZoom := Real.arcsin (1 / √(((r - 1) * 2 ^ (subN - p) : ℕ) : ℝ))
          set pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2
          set qZoom := ((kZoom + 1 : ℕ) : ℝ)
          have hmiss1_bd : 0 ≤ qZoom + fNext 1 ∧ qZoom + fNext 1 ≤ (remMiss1 : ℝ) * scale15 := by
            obtain ⟨hf1_nn, hf1_bd⟩ := hf_s15 1 (by omega); refine ⟨by positivity, ?_⟩
            have hrm_eq : remMiss1 = s.qZoomHi + fHi 1 := rfl; rw [hrm_eq]; push_cast; linarith
          have hhit1_bd : 0 ≤ qZoom + (1 - pZoom) * fNext 1 ∧
              qZoom + (1 - pZoom) * fNext 1 ≤ (remHit1 : ℝ) * scale15 := by
            obtain ⟨hf1_nn, hf1_bd⟩ := hf_s15 1 (by omega)
            have hpZ_le1 : pZoom ≤ 1 := Real.sin_sq_le_one _
            have h1m_nn : 0 ≤ 1 - pZoom := (by linarith)
            have h1m_bd : 1 - pZoom ≤ ((Int.sub midPScaleZ s.zHitLo : ℤ) : ℝ) / wdScaleR := by
              have hsub_eq : Int.sub midPScaleZ s.zHitLo = (wdScale : ℤ) - s.zHitLo := rfl
              rw [hsub_eq]; push_cast; rw [sub_div]
              have hdiv1 : (wdScale : ℝ) / wdScaleR = 1 := by unfold wdScaleR; exact div_self hB.ne'
              linarith
            have hprod := midP_divCeil_scale15_bound hs15_nn h1m_nn h1m_bd hf1_nn hf1_bd
            refine ⟨by positivity, ?_⟩
            have hrh_eq : remHit1 = s.qZoomHi +
                wdDivCeil (Int.mul (Int.sub midPScaleZ s.zHitLo) (fHi 1)) midPScaleZ := rfl
            rw [hrh_eq]; push_cast; linarith
          set uf := ghMidPChainFinalAmp r θ₁ probes (ghMidPInitAmp r θ₁ kInit)
          have hremDist_bd : (∑ w ∈ Finset.range r, (r.choose w : ℝ) * Complex.normSq (uf w) * (if
            w + 1 = r then qZoom + fNext 1 else fNext (r - w))) ≤ (remDistZ : ℝ) * scale15 := by
            dsimp only [remDistZ]; rw [midPSumRangeZ_eq]; push_cast; rw [Finset.sum_mul]
            refine Finset.sum_le_sum fun w hw ↦ ?_
            have hw_lt : w < r := Finset.mem_range.mp hw
            have hp_nn : 0 ≤ (r.choose w : ℝ) * Complex.normSq (uf w) :=
              mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
            have hp_bd : (r.choose w : ℝ) * Complex.normSq (uf w) ≤
                ((Int.mul (Int.ofNat (ghBinom r w)) (s.uAbs2Hi.getD w 0) : ℤ) : ℝ) / wdScaleR := by
              have hmul_eq : Int.mul (Int.ofNat (ghBinom r w)) (s.uAbs2Hi.getD w 0) =
                  (r.choose w : ℤ) * (s.uAbs2Hi.getD w 0) := by rw [← ghBinom_eq]; rfl
              rw [hmul_eq]; push_cast; rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_left (huAbs w (by omega)).2 (Nat.cast_nonneg _)
            by_cases hwr : w + 1 = r
            · have hbeq : (w + 1 == r) = true := beq_iff_eq.mpr hwr
              rw [ite_eq_left hwr, ite_eq_left hbeq]
              exact midP_divCeil_scale15_bound hs15_nn hp_nn hp_bd hmiss1_bd.1 hmiss1_bd.2
            · have hbeq : ¬((w + 1 == r) = true) := (by rw [beq_iff_eq]; exact hwr)
              obtain ⟨hc_nn, hc_bd⟩ := hf_s15 (r - w) (by omega)
              rw [ite_eq_right hwr, ite_eq_right hbeq]
              exact midP_divCeil_scale15_bound hs15_nn hp_nn hp_bd hc_nn hc_bd
          set spf := ghMidPChainFinal2Row (r - 2) θ₁ θ₂ probes (ghMidPInit2Row (r - 2) θ₁ θ₂ kInit)
          have hremSp0_bd : (∑ w₁ ∈ Finset.range (r - 1), ((r - 2).choose w₁ : ℝ) * Complex.normSq
            (spf.1 w₁) * fNext (r - w₁)) ≤ (remSp0Z : ℝ) * scale15 := by
            dsimp only [remSp0Z]; rw [midPSumRangeZ_eq]; push_cast; rw [Finset.sum_mul]
            refine Finset.sum_le_sum fun w₁ hw₁ ↦ ?_
            have hw₁_lt : w₁ < r - 1 := Finset.mem_range.mp hw₁
            have hp_nn : 0 ≤ ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.1 w₁) :=
              mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
            have hp_bd : ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.1 w₁) ≤ ((Int.mul (Int.ofNat
              (ghBinom (r - 2) w₁)) (s.z0Abs2Hi.getD w₁ 0) : ℤ) : ℝ) / wdScaleR := by
              have hmul_eq : Int.mul (Int.ofNat (ghBinom (r - 2) w₁)) (s.z0Abs2Hi.getD w₁ 0) =
                  ((r - 2).choose w₁ : ℤ) * (s.z0Abs2Hi.getD w₁ 0) := by
                rw [← ghBinom_eq]; rfl
              rw [hmul_eq]; push_cast; rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_left (hz0Abs w₁ (by omega)).2 (Nat.cast_nonneg _)
            obtain ⟨hc_nn, hc_bd⟩ := hf_s15 (r - w₁) (by omega)
            exact midP_divCeil_scale15_bound hs15_nn hp_nn hp_bd hc_nn hc_bd
          have hremSp1_bd : (∑ w₁ ∈ Finset.range (r - 1), ((r - 2).choose w₁ : ℝ) * Complex.normSq
            (spf.2 w₁) * (if w₁ + 2 = r then qZoom + (1 - pZoom) * fNext 1 else fNext (r - 1 - w₁)))
            ≤ (remSp1Z : ℝ) * scale15 := by
            dsimp only [remSp1Z]; rw [midPSumRangeZ_eq]; push_cast; rw [Finset.sum_mul]
            refine Finset.sum_le_sum fun w₁ hw₁ ↦ ?_
            have hw₁_lt : w₁ < r - 1 := Finset.mem_range.mp hw₁
            have hp_nn : 0 ≤ ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.2 w₁) :=
              mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
            have hp_bd : ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.2 w₁) ≤ ((Int.mul (Int.ofNat
              (ghBinom (r - 2) w₁)) (s.z1Abs2Hi.getD w₁ 0) : ℤ) : ℝ) / wdScaleR := by
              have hmul_eq : Int.mul (Int.ofNat (ghBinom (r - 2) w₁)) (s.z1Abs2Hi.getD w₁ 0) =
                  ((r - 2).choose w₁ : ℤ) * (s.z1Abs2Hi.getD w₁ 0) := by
                rw [← ghBinom_eq]; rfl
              rw [hmul_eq]; push_cast; rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_left (hz1Abs w₁ (by omega)).2 (Nat.cast_nonneg _)
            by_cases hw1r : w₁ + 2 = r
            · have hbeq : (w₁ + 2 == r) = true := beq_iff_eq.mpr hw1r
              rw [ite_eq_left hw1r, ite_eq_left hbeq]
              exact midP_divCeil_scale15_bound hs15_nn hp_nn hp_bd hhit1_bd.1 hhit1_bd.2
            · have hbeq : ¬((w₁ + 2 == r) = true) := (by rw [beq_iff_eq]; exact hw1r)
              obtain ⟨hc_nn, hc_bd⟩ := hf_s15 (r - 1 - w₁) (by omega)
              rw [ite_eq_right hw1r, ite_eq_right hbeq]
              exact midP_divCeil_scale15_bound hs15_nn hp_nn hp_bd hc_nn hc_bd
          set stf := ghMidPChainFinal2Row (r - 3) θ₁ θ₃ probes (ghMidPInit2Row (r - 3) θ₁ θ₃ kInit)
          have hremSt_bd : (∑ w₁ ∈ Finset.range (r - 2), (((r - 3).choose w₁ : ℝ) * Complex.normSq
            (stf.1 w₁) * fNext (r - w₁) + ((r - 3).choose w₁ : ℝ) * Complex.normSq (stf.2 w₁) *
            fNext (r - (w₁ + 1)))) ≤ (remStZ : ℝ) * scale15 := by
            rw [sum_singleTriple_by_wt hr3]; dsimp only [remStZ]; rw [midPSumRangeZ_eq]; push_cast
            rw [Finset.sum_mul]; refine Finset.sum_le_sum fun wt hwt ↦ ?_
            have hwt_lt : wt < r - 1 := Finset.mem_range.mp hwt
            have hp_nn : 0 ≤ (if wt ≤ r - 3 then ((r - 3).choose wt : ℝ) * Complex.normSq (stf.1 wt)
              else 0) + (if 1 ≤ wt ∧ wt - 1 ≤ r - 3 then ((r - 3).choose (wt - 1) : ℝ) *
              Complex.normSq (stf.2 (wt - 1)) else 0) := by
              refine add_nonneg ?_ ?_
              · split_ifs
                · exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
                · exact le_rfl
              · split_ifs
                · exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
                · exact le_rfl
            obtain ⟨hc_nn, hc_bd⟩ := hf_s15 (r - wt) (by omega)
            exact midP_divCeil_scale15_bound hs15_nn hp_nn (hstWt wt (by omega)).2 hc_nn hc_bd
          set tpf := ghMidPChainFinalTwoPair (r - 4) θ₁ θ₂ probes
            (ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit)
          have hremTp_bd : (if 4 ≤ r then ∑ w₁ ∈ Finset.range (r - 3), (((r - 4).choose w₁ : ℝ) *
            Complex.normSq (tpf.1 w₁) * fNext (r - w₁) + (2 * (r - 4).choose w₁ : ℝ) *
            Complex.normSq (tpf.2.1 w₁) * fNext (r - (w₁ + 1)) + ((r - 4).choose w₁ : ℝ) *
            Complex.normSq (tpf.2.2 w₁) * fNext (r - (w₁ + 2))) else 0) ≤ (remTpZ : ℝ) *
            scale15 := by
            dsimp only [remTpZ]; by_cases hr4 : 4 ≤ r
            · have hble4 : Nat.ble 4 r = true := Nat.ble_eq.mpr hr4; rw [ite_eq_left hr4, hble4]
              simp only [↓reduceIte]; rw [sum_twoPair_by_wt hr4, midPSumRangeZ_eq]; push_cast
              rw [Finset.sum_mul]; refine Finset.sum_le_sum fun wt hwt ↦ ?_
              have hwt_lt : wt < r - 1 := Finset.mem_range.mp hwt
              have hp_nn : 0 ≤ (if wt ≤ r - 4 then ((r - 4).choose wt : ℝ) * Complex.normSq (tpf.1
                wt) else 0) + (if 1 ≤ wt ∧ wt - 1 ≤ r - 4 then (2 * (r - 4).choose (wt - 1) : ℝ) *
                Complex.normSq (tpf.2.1 (wt - 1)) else 0) + (if 2 ≤ wt ∧ wt - 2 ≤ r - 4 then ((r -
                4).choose (wt - 2) : ℝ) * Complex.normSq (tpf.2.2 (wt - 2)) else 0) := by
                refine add_nonneg (add_nonneg ?_ ?_) ?_
                · split_ifs
                  · exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
                  · exact le_rfl
                · split_ifs
                  · exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
                  · exact le_rfl
                · split_ifs
                  · exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
                  · exact le_rfl
              obtain ⟨hc_nn, hc_bd⟩ := hf_s15 (r - wt) (by omega)
              exact midP_divCeil_scale15_bound hs15_nn hp_nn ((htpWt hr4) wt (by omega)).2
                hc_nn hc_bd
            · have hble4 : Nat.ble 4 r = false := by
                cases hb : Nat.ble 4 r
                · rfl
                · exfalso; exact hr4 (Nat.ble_eq.mp hb)
              rw [ite_eq_right hr4, hble4]; simp
          have hr_le_m : r ≤ m := (by omega)
          have hnInj_eq : ((m.descFactorial r : ℕ) : ℤ) = nInjZ := by
            dsimp only [nInjZ]; rw [Nat.ble_eq.mpr hr_le_m, midPDescFact_eq]; rfl
          have hnSp_eq : ((r.choose 2 * m.descFactorial (r - 1) : ℕ) : ℤ) = nSpZ := by
            dsimp only [nSpZ]; rw [ghBinom_eq, midPDescFact_eq]; rfl
          have hnTp_eq : (((if 4 ≤ r then 3 * r.choose 4 * m.descFactorial (r - 2) else 0 : ℕ) : ℤ))
            = nTpZ := by
            dsimp only [nTpZ]; by_cases hr4 : 4 ≤ r
            · rw [ite_eq_left hr4, Nat.ble_eq.mpr hr4, ghBinom_eq, midPDescFact_eq]; rfl
            · have hble4 : Nat.ble 4 r = false := by
                cases hb : Nat.ble 4 r
                · rfl
                · exfalso; exact hr4 (Nat.ble_eq.mp hb)
              rw [ite_eq_right hr4, hble4]; rfl
          have hnSt_eq : ((r.choose 3 * m.descFactorial (r - 2) : ℕ) : ℤ) = nStZ := by
            dsimp only [nStZ]; rw [ghBinom_eq, midPDescFact_eq]; rfl
          set nInjN : ℕ := m.descFactorial r; set nSpN : ℕ := r.choose 2 * m.descFactorial (r - 1)
          set nTpN : ℕ := if 4 ≤ r then 3 * r.choose 4 * m.descFactorial (r - 2) else 0
          set nStN : ℕ := r.choose 3 * m.descFactorial (r - 2)
          have hused_eq : ((nInjN + nSpN + nTpN + nStN : ℕ) : ℤ) = usedZ := by
            change ((nInjN : ℤ) + (nSpN : ℤ) + (nTpN : ℤ) + (nStN : ℤ)) =
              nInjZ + nSpZ + nTpZ + nStZ + 0
            rw [hnInj_eq, hnSp_eq, hnTp_eq, hnSt_eq]; ring
          have hremN_eq : ((m ^ r - (nInjN + nSpN + nTpN + nStN) : ℕ) : ℤ) = nRemZ := by
            have hmPow_eq : ((m ^ r : ℕ) : ℤ) = mPow := rfl
            have hle_Z : ((nInjN + nSpN + nTpN + nStN : ℕ) : ℤ) ≤ ((m ^ r : ℕ) : ℤ) := by
              rw [hused_eq, hmPow_eq]; have hnRem_def : nRemZ = mPow - usedZ := rfl; omega
            have hle_N : nInjN + nSpN + nTpN + nStN ≤ m ^ r := Int.ofNat_le.mp hle_Z
            rw [Int.ofNat_sub hle_N, hmPow_eq, hused_eq]; rfl
          obtain ⟨_, hfr_bd⟩ := hf_s15 r le_rfl
          have htInj_bd : (nInjN : ℝ) * (((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQueries r θ₁ probes
            (ghMidPInitAmp r θ₁ kInit) + ∑ w ∈ Finset.range r, (r.choose w : ℝ) * Complex.normSq (uf
            w) * (if w + 1 = r then qZoom + fNext 1 else fNext (r - w))) ≤ (tInj : ℝ) *
            scale15 := by
            have hsum_in : ((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQueries r θ₁ probes
              (ghMidPInitAmp r θ₁ kInit) + (∑ w ∈ Finset.range r, (r.choose w : ℝ) * Complex.normSq
              (uf w) * (if w + 1 = r then qZoom + fNext 1 else fNext (r - w))) ≤ ((Int.add s.qDistHi
              remDistZ : ℤ) : ℝ) * scale15 := by
              change _ ≤ ((s.qDistHi + remDistZ : ℤ) : ℝ) * scale15; rw [Int.cast_add, add_mul]
              exact add_le_add hqDist hremDist_bd
            have hm := mul_le_mul_of_nonneg_left hsum_in (Nat.cast_nonneg nInjN)
            have heq : (nInjN : ℝ) * (((Int.add s.qDistHi remDistZ : ℤ) : ℝ) * scale15) =
                (tInj : ℝ) * scale15 := by
              have hZ : (nInjN : ℝ) = (nInjZ : ℝ) := (by exact_mod_cast hnInj_eq); rw [hZ]
              change (nInjZ : ℝ) * (((s.qDistHi + remDistZ : ℤ) : ℝ) * scale15) =
                ((nInjZ * (s.qDistHi + remDistZ) : ℤ) : ℝ) * scale15
              push_cast; ring
            exact hm.trans_eq heq
          have htSp_bd : (nSpN : ℝ) * ((ghMidPPreMaxQueries kInit probes : ℝ) + (∑ w₁ ∈ Finset.range
            (r - 1), ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.1 w₁) * fNext (r - w₁)) + (∑ w₁ ∈
            Finset.range (r - 1), ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.2 w₁) * (if w₁ + 2 =
            r then qZoom + (1 - pZoom) * fNext 1 else fNext (r - 1 - w₁)))) ≤ (tSp : ℝ) *
            scale15 := by
            have hsum_in : (ghMidPPreMaxQueries kInit probes : ℝ) + (∑ w₁ ∈ Finset.range (r - 1),
              ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.1 w₁) * fNext (r - w₁)) + (∑ w₁ ∈
              Finset.range (r - 1), ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.2 w₁) * (if w₁ + 2
              = r then qZoom + (1 - pZoom) * fNext 1 else fNext (r - 1 - w₁))) ≤ ((Int.add s.qCollHi
              (Int.add remSp0Z remSp1Z) : ℤ) : ℝ) * scale15 := by
              change _ ≤ ((s.qCollHi + (remSp0Z + remSp1Z) : ℤ) : ℝ) * scale15
              push_cast; linarith [hqColl, hremSp0_bd, hremSp1_bd]
            have hm := mul_le_mul_of_nonneg_left hsum_in (Nat.cast_nonneg nSpN)
            have heq : (nSpN : ℝ) * (((Int.add s.qCollHi (Int.add remSp0Z remSp1Z) : ℤ) : ℝ) *
              scale15) = (tSp : ℝ) * scale15 := by
              have hZ : (nSpN : ℝ) = (nSpZ : ℝ) := (by exact_mod_cast hnSp_eq); rw [hZ]
              change (nSpZ : ℝ) * (((s.qCollHi + (remSp0Z + remSp1Z) : ℤ) : ℝ) * scale15) =
                ((nSpZ * (s.qCollHi + (remSp0Z + remSp1Z)) : ℤ) : ℝ) * scale15
              push_cast; ring
            exact hm.trans_eq heq
          have htTp_bd : (nTpN : ℝ) * ((ghMidPPreMaxQueries kInit probes : ℝ) + if 4 ≤ r then ∑ w₁ ∈
            Finset.range (r - 3), (((r - 4).choose w₁ : ℝ) * Complex.normSq (tpf.1 w₁) * fNext (r -
            w₁) + (2 * (r - 4).choose w₁ : ℝ) * Complex.normSq (tpf.2.1 w₁) * fNext (r - (w₁ + 1)) +
            ((r - 4).choose w₁ : ℝ) * Complex.normSq (tpf.2.2 w₁) * fNext (r - (w₁ + 2))) else 0) ≤
            (tTp : ℝ) * scale15 := by
            have hsum_in : (ghMidPPreMaxQueries kInit probes : ℝ) + (if 4 ≤ r then ∑ w₁ ∈
              Finset.range (r - 3), (((r - 4).choose w₁ : ℝ) * Complex.normSq (tpf.1 w₁) * fNext
              (r - w₁) + (2 * (r - 4).choose w₁ : ℝ) * Complex.normSq (tpf.2.1 w₁) * fNext (r -
              (w₁ + 1)) + ((r - 4).choose w₁ : ℝ) * Complex.normSq (tpf.2.2 w₁) * fNext (r - (w₁ +
              2))) else 0) ≤ ((Int.add s.qCollHi remTpZ : ℤ) : ℝ) * scale15 := by
              change _ ≤ ((s.qCollHi + remTpZ : ℤ) : ℝ) * scale15
              push_cast; linarith [hqColl, hremTp_bd]
            have hm := mul_le_mul_of_nonneg_left hsum_in (Nat.cast_nonneg nTpN)
            have heq : (nTpN : ℝ) * (((Int.add s.qCollHi remTpZ : ℤ) : ℝ) * scale15) =
                (tTp : ℝ) * scale15 := by
              have hZ : (nTpN : ℝ) = (nTpZ : ℝ) := (by exact_mod_cast hnTp_eq); rw [hZ]
              change (nTpZ : ℝ) * (((s.qCollHi + remTpZ : ℤ) : ℝ) * scale15) =
                ((nTpZ * (s.qCollHi + remTpZ) : ℤ) : ℝ) * scale15
              push_cast; ring
            exact hm.trans_eq heq
          have htSt_bd : (nStN : ℝ) * ((ghMidPPreMaxQueries kInit probes : ℝ) + ∑ w₁ ∈ Finset.range
            (r - 2), (((r - 3).choose w₁ : ℝ) * Complex.normSq (stf.1 w₁) * fNext (r - w₁) + ((r -
            3).choose w₁ : ℝ) * Complex.normSq (stf.2 w₁) * fNext (r - (w₁ + 1)))) ≤ (tSt : ℝ) *
            scale15 := by
            have hsum_in : (ghMidPPreMaxQueries kInit probes : ℝ) + (∑ w₁ ∈ Finset.range (r - 2),
              (((r - 3).choose w₁ : ℝ) * Complex.normSq (stf.1 w₁) * fNext (r - w₁) + ((r -
              3).choose w₁ : ℝ) * Complex.normSq (stf.2 w₁) * fNext (r - (w₁ + 1)))) ≤ ((Int.add
              s.qCollHi remStZ : ℤ) : ℝ) * scale15 := by
              change _ ≤ ((s.qCollHi + remStZ : ℤ) : ℝ) * scale15
              push_cast; linarith [hqColl, hremSt_bd]
            have hm := mul_le_mul_of_nonneg_left hsum_in (Nat.cast_nonneg nStN)
            have heq : (nStN : ℝ) * (((Int.add s.qCollHi remStZ : ℤ) : ℝ) * scale15) =
                (tSt : ℝ) * scale15 := by
              have hZ : (nStN : ℝ) = (nStZ : ℝ) := (by exact_mod_cast hnSt_eq); rw [hZ]
              change (nStZ : ℝ) * (((s.qCollHi + remStZ : ℤ) : ℝ) * scale15) =
                ((nStZ * (s.qCollHi + remStZ) : ℤ) : ℝ) * scale15
              push_cast; ring
            exact hm.trans_eq heq
          set nRemN : ℕ := m ^ r - (nInjN + nSpN + nTpN + nStN)
          have htRem_bd : (nRemN : ℝ) * ((ghMidPPreMaxQueries kInit probes : ℝ) + fNext r) ≤ (tRem :
            ℝ) * scale15 := by
            have hsum_in : (ghMidPPreMaxQueries kInit probes : ℝ) + fNext r ≤ ((Int.add s.qCollHi
              (fHi r) : ℤ) : ℝ) * scale15 := by
              change _ ≤ ((s.qCollHi + fHi r : ℤ) : ℝ) * scale15
              push_cast; linarith [hqColl, hfr_bd]
            have hm := mul_le_mul_of_nonneg_left hsum_in (Nat.cast_nonneg nRemN)
            have heq : (nRemN : ℝ) * (((Int.add s.qCollHi (fHi r) : ℤ) : ℝ) * scale15) =
                (tRem : ℝ) * scale15 := by
              have hZ : (nRemN : ℝ) = (nRemZ : ℝ) := (by exact_mod_cast hremN_eq); rw [hZ]
              change (nRemZ : ℝ) * (((s.qCollHi + fHi r : ℤ) : ℝ) * scale15) =
                ((nRemZ * (s.qCollHi + fHi r) : ℤ) : ℝ) * scale15
              push_cast; ring
            exact hm.trans_eq heq
          have htot_eq : (tot : ℝ) * scale15 = (tInj : ℝ) * scale15 + (tSp : ℝ) * scale15 + (tTp :
            ℝ) * scale15 + (tSt : ℝ) * scale15 + (tRem : ℝ) * scale15 := by
            have htSq0 : tSq = 0 := Int.zero_mul _
            change ((tInj + tSp + tTp + tSt + tSq + tRem : ℤ) : ℝ) * scale15 = _; rw [htSq0]
            push_cast; ring
          have hnum_bd : (nInjN : ℝ) * (((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQueries r θ₁ probes
            (ghMidPInitAmp r θ₁ kInit) + ∑ w ∈ Finset.range r, (r.choose w : ℝ) * Complex.normSq (uf
            w) * (if w + 1 = r then qZoom + fNext 1 else fNext (r - w))) + (nSpN : ℝ) *
            ((ghMidPPreMaxQueries kInit probes : ℝ) + (∑ w₁ ∈ Finset.range (r - 1), ((r - 2).choose
            w₁ : ℝ) * Complex.normSq (spf.1 w₁) * fNext (r - w₁)) + (∑ w₁ ∈ Finset.range (r - 1),
            ((r - 2).choose w₁ : ℝ) * Complex.normSq (spf.2 w₁) * (if w₁ + 2 = r then qZoom + (1 -
            pZoom) * fNext 1 else fNext (r - 1 - w₁)))) + (nTpN : ℝ) * ((ghMidPPreMaxQueries kInit
            probes : ℝ) + if 4 ≤ r then ∑ w₁ ∈ Finset.range (r - 3), (((r - 4).choose w₁ : ℝ) *
            Complex.normSq (tpf.1 w₁) * fNext (r - w₁) + (2 * (r - 4).choose w₁ : ℝ) *
            Complex.normSq (tpf.2.1 w₁) * fNext (r - (w₁ + 1)) + ((r - 4).choose w₁ : ℝ) *
            Complex.normSq (tpf.2.2 w₁) * fNext (r - (w₁ + 2))) else 0) + (nStN : ℝ) *
            ((ghMidPPreMaxQueries kInit probes : ℝ) + ∑ w₁ ∈ Finset.range (r - 2), (((r - 3).choose
            w₁ : ℝ) * Complex.normSq (stf.1 w₁) * fNext (r - w₁) + ((r - 3).choose w₁ : ℝ) *
            Complex.normSq (stf.2 w₁) * fNext (r - (w₁ + 1)))) + (nRemN : ℝ) * ((ghMidPPreMaxQueries
            kInit probes : ℝ) + fNext r) ≤ (tot : ℝ) * scale15 := by
            rw [htot_eq]; linarith [htInj_bd, htSp_bd, htTp_bd, htSt_bd, htRem_bd]
          have hmPow_pos : (0 : ℝ) < ((m ^ r : ℕ) : ℝ) := by
            exact_mod_cast pow_pos (by omega : 0 < m) r
          have hmPow_eqR : ((m ^ r : ℕ) : ℝ) = (mPow : ℝ) := rfl
          have hdiv_bd : ((tot : ℝ) * scale15) / (mPow : ℝ) = ((tot : ℝ) / ((Int.mul mPow 1000000 :
            ℤ) : ℝ)) * scale := by
            rw [hscale_eq]; change ((tot : ℝ) * scale15) / (mPow : ℝ) =
              ((tot : ℝ) / ((mPow * 1000000 : ℤ) : ℝ)) * (1000000 * scale15)
            have hmPow_ne : (mPow : ℝ) ≠ 0 := (by rw [← hmPow_eqR]; exact hmPow_pos.ne'); push_cast
            field_simp [hmPow_ne]
          have hmPow6_pos : (0 : ℤ) < Int.mul mPow 1000000 := by
            have hmPow_posN : 0 < m ^ r := pow_pos (by omega : 0 < m) r
            change 0 < ((m ^ r : ℕ) : ℤ) * 1000000; omega
          have hceil := le_wdDivCeil (a := tot) hmPow6_pos
          have hout_cast : (outZ.toNat : ℝ) = (outZ : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hout
          rw [hmPow_eqR, hout_cast]
          exact ((div_le_div_of_nonneg_right hnum_bd hmPow_pos.le).trans_eq hdiv_bd).trans
            (mul_le_mul_of_nonneg_right hceil hscale_nn)
        · rw [ite_eq_right hout] at hstep; cases hstep
      · rw [ite_eq_right hnRem] at hstep; cases hstep
    · rw [ite_eq_right hg2] at hstep; cases hstep
  · rw [ite_eq_right hg1] at hstep; cases hstep
/-- Unpacks `evalMidPRowSummaries` into row-by-row `evalMidPRowSummary` equalities. -/
theorem evalMidPRowSummaries_length_and_getD {includeRm3 : Bool} {m : ℕ} :
    ∀ (rStart : ℕ) {specs : List GHMidPRowSpec} {sums : List GHMidPSummary},
      evalMidPRowSummaries includeRm3 m rStart specs = some sums →
      sums.length = specs.length ∧
      ∀ j < specs.length,
        ∃ spec, specs[j]? = some spec ∧
          evalMidPRowSummary m (rStart + j) includeRm3 spec =
            some (sums.getD j midPEmptySummary)
  | _, [], _, h => by
      simp only [evalMidPRowSummaries, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ hj ↦ by simp at hj⟩
  | rStart, spec :: rest, _, h => by
      unfold evalMidPRowSummaries at h
      cases h1 : evalMidPRowSummary m rStart includeRm3 spec with
      | none => rw [h1] at h; cases h
      | some s =>
          cases h2 : evalMidPRowSummaries includeRm3 m (Nat.add rStart 1) rest with
          | none => rw [h1, h2] at h; cases h
          | some tl =>
              rw [h1, h2] at h
              injection h with hcons
              subst hcons
              have hr1 : Nat.add rStart 1 = rStart + 1 := rfl
              rw [hr1] at h2
              obtain ⟨hlen, hget⟩ := evalMidPRowSummaries_length_and_getD (rStart + 1) h2
              refine ⟨by simp [hlen], fun j hj ↦ ?_⟩
              cases j with
              | zero =>
                  refine ⟨spec, rfl, ?_⟩
                  simpa [List.getD_cons_zero] using h1
              | succ j' =>
                  have hj' : j' < rest.length := by simp at hj; omega
                  obtain ⟨sp', hsp', hev'⟩ := hget j' hj'; refine ⟨sp', hsp', ?_⟩
                  have hadd : rStart + (j' + 1) = (rStart + 1) + j' := (by omega)
                  rw [hadd, List.getD_cons_succ]; exact hev'
end
end QuantumComputation.Specs.DickeSol
end GHMidPZoomBounds

section GHMidPFibersQHL
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open Complex (normSq)
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
open scoped Matrix NNReal NNRat ENNReal
@[expose] public section
/-
 ## 1. `r = 2` Schedule Bridge (`GHZoomProbe` / `GHZoomSpec` -> `GHMidPProbe` / `GHMidPSpec`)
-/

/-- Embeds an `r = 2` `GHZoomProbe` into `GHMidPProbe`. -/
def ghZoomProbeToMidP (pr : GHZoomProbe) : GHMidPProbe :=
  { phases := [pr.1, pr.2.1], rotTop := pr.2.2.1, kNext := pr.2.2.2 }
/-- Embeds an `r = 2` `GHZoomSpec` into `GHMidPSpec`. -/
def ghZoomSpecToMidP : GHZoomSpec → GHMidPSpec
  | none => none
  | some (kInit, probes, kZoom) => some (kInit, probes.map ghZoomProbeToMidP, kZoom)
/- ## 2. Multi-Collision Fiber Combinatorics on `Fin r → Fin m` -/

/-- Multiplicity of slot `j: Fin m` in `R` under `pref`. -/
def ghMidPOcc {α : Type*} [DecidableEq α] {m : ℕ} (pref : α → Fin m) (R : Finset α)
    (j : Fin m) : ℕ :=
  (R.filter fun x ↦ pref x = j).card
private abbrev ghMidPFiberOcc {r m : ℕ} (h : Fin r → Fin m) (j : Fin m) : ℕ :=
  ghMidPOcc h Finset.univ j
private lemma ghMidPSumOccEq {r m : ℕ} (h : Fin r → Fin m) :
    (∑ j : Fin m, ghMidPFiberOcc h j) = r := by
  have hunion :
      (Finset.univ : Finset (Fin m)).biUnion
        (fun j ↦ Finset.univ.filter fun a : Fin r ↦ h a = j) = Finset.univ := by
    ext a
    simp
  have hdisj :
      Set.PairwiseDisjoint ((Finset.univ : Finset (Fin m)) : Set (Fin m))
        (fun j ↦ Finset.univ.filter fun a : Fin r ↦ h a = j) :=
    fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun _ h1 h2 ↦
      hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  simpa [ghMidPFiberOcc, ghMidPOcc] using
    (Finset.card_biUnion hdisj).symm.trans (congrArg Finset.card hunion)
private lemma ghMidP_mul_descFactorial_sub_one (m d : ℕ) :
    m * (m - 1).descFactorial d = m.descFactorial (d + 1) := by
  cases m with
  | zero => simp
  | succ m' => exact (Nat.succ_descFactorial_succ m' d).symm
private def ghMidPExtSet {r m : ℕ} (A : Finset (Fin r)) (B : Finset (Fin m))
    (base : Fin r → Fin m) : Finset (Fin r → Fin m) :=
  Finset.univ.filter fun h : Fin r → Fin m ↦
    (∀ i ∈ A, h i = base i) ∧
      (∀ i, i ∉ A → h i ∉ B) ∧
      Set.InjOn h ((Finset.univ \ A : Finset (Fin r)) : Set (Fin r))
private lemma card_ghMidPExtSet {r m : ℕ} (A : Finset (Fin r)) (B : Finset (Fin m))
    (base : Fin r → Fin m) :
    (ghMidPExtSet A B base).card = (m - B.card).descFactorial (r - A.card) := by
  have hcard_compl {n : ℕ} (S : Finset (Fin n)) :
      Fintype.card {x : Fin n // x ∉ S} = n - S.card := by
    rw [Fintype.card_subtype]
    have hfeq : (Finset.univ.filter fun x : Fin n ↦ x ∉ S) = Finset.univ \ S := by
      ext x
      simp
    rw [hfeq]
    have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at hadd
    omega
  let Dom := {i : Fin r // i ∉ A}
  let Cod := {j : Fin m // j ∉ B}
  let extFun (e : Dom ↪ Cod) : Fin r → Fin m :=
    fun i ↦ if hi : i ∈ A then base i else (e ⟨i, hi⟩).1
  have hbij : (Finset.univ : Finset (Dom ↪ Cod)).card = (ghMidPExtSet A B base).card := by
    refine Finset.card_bij (fun e _ ↦ extFun e) (fun e _ ↦ ?_) (fun e₁ _ e₂ _ heq ↦ ?_)
      (fun h hh ↦ ?_)
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · intro i hi
        exact dite_eq_left hi
      · intro i hi
        dsimp only [extFun]
        rw [dite_eq_right hi]
        exact (e ⟨i, hi⟩).2
      · intro i₁ hi₁ i₂ hi₂ heq
        have hn₁ : i₁ ∉ A := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hi₁)).2
        have hn₂ : i₂ ∉ A := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hi₂)).2
        dsimp only [extFun] at heq
        rw [dite_eq_right hn₁, dite_eq_right hn₂] at heq
        exact congrArg Subtype.val (e.injective (Subtype.ext heq))
    · apply DFunLike.ext
      intro x
      apply Subtype.ext
      have hx := congrFun heq x.1
      dsimp only [extFun] at hx
      rwa [dite_eq_right x.2, dite_eq_right x.2] at hx
    · rcases (Finset.mem_filter.mp hh).2 with ⟨hA, hnotB, hinj⟩
      let e : Dom ↪ Cod :=
        ⟨fun x ↦ ⟨h x.1, hnotB x.1 x.2⟩, fun x₁ x₂ hx_eq ↦
          Subtype.ext (hinj
            (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x₁.2⟩))
            (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x₂.2⟩))
            (congrArg Subtype.val hx_eq))⟩
      refine ⟨e, Finset.mem_univ e, funext fun i ↦ ?_⟩
      dsimp only [extFun, e]
      by_cases hi : i ∈ A
      · rw [dite_eq_left hi, hA i hi]
      · rw [dite_eq_right hi]
        rfl
  rw [← hbij, Finset.card_univ, Fintype.card_embedding_eq, hcard_compl B, hcard_compl A]
private lemma ghMidPExtSet_occ {r m : ℕ} {A : Finset (Fin r)} {B : Finset (Fin m)}
    {base : Fin r → Fin m} (hbase : ∀ i ∈ A, base i ∈ B)
    {h : Fin r → Fin m} (hh : h ∈ ghMidPExtSet A B base) :
    (∀ j ∈ B, (Finset.univ.filter fun i : Fin r ↦ h i = j) = A.filter fun i ↦ base i = j) ∧
      ∀ j, j ∉ B → ghMidPFiberOcc h j ≤ 1 := by
  rcases (Finset.mem_filter.mp hh).2 with ⟨hA, hnotB, hinj⟩
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ A
    · rw [hA i hi]
      exact ⟨fun heq ↦ ⟨hi, heq⟩, fun ⟨_, heq⟩ ↦ heq⟩
    · exact ⟨fun heq ↦ absurd (heq ▸ hj) (hnotB i hi), fun ⟨hiA, _⟩ ↦ absurd hiA hi⟩
  · refine Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ ↦ ?_
    have heq₁ : h i₁ = j := (Finset.mem_filter.mp hi₁).2
    have heq₂ : h i₂ = j := (Finset.mem_filter.mp hi₂).2
    have hn₁ : i₁ ∉ A := fun hm ↦ hj (heq₁ ▸ hA i₁ hm ▸ hbase i₁ hm)
    have hn₂ : i₂ ∉ A := fun hm ↦ hj (heq₂ ▸ hA i₂ hm ▸ hbase i₂ hm)
    exact hinj (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn₁⟩))
      (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn₂⟩))
      (heq₁.trans heq₂.symm)
private def ghMidPInjFibers (r m : ℕ) : Finset (Fin r → Fin m) :=
  Finset.univ.filter Function.Injective
private lemma card_ghMidPInjFibers (r m : ℕ) (hm1 : 1 ≤ m) :
    (ghMidPInjFibers r m).card = m.descFactorial r := by
  let j₀ : Fin m := ⟨0, by omega⟩
  have heq : ghMidPInjFibers r m = ghMidPExtSet ∅ ∅ (fun _ ↦ j₀) := by
    ext h
    simp only [ghMidPInjFibers, ghMidPExtSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.sdiff_empty, Finset.coe_univ,
      Set.injOn_univ]
    exact ⟨fun hh ↦ ⟨fun _ hf ↦ hf, hh⟩, fun hh ↦ hh.2⟩
  rw [heq, card_ghMidPExtSet]
  simp
private def ghMidPIsSingleMult (c : ℕ) {r m : ℕ} (h : Fin r → Fin m) : Prop :=
  ∃ jc : Fin m, ghMidPFiberOcc h jc = c ∧ ∀ j : Fin m, j ≠ jc → ghMidPFiberOcc h j ≤ 1
open Classical in
private noncomputable def ghMidPSingleMultFibers (c r m : ℕ) : Finset (Fin r → Fin m) :=
  Finset.univ.filter (ghMidPIsSingleMult c)
private lemma card_ghMidPSingleMultFibers {c r m : ℕ} (hc2 : 2 ≤ c) (_hcr : c ≤ r) :
    (ghMidPSingleMultFibers c r m).card = r.choose c * m.descFactorial (r - c + 1) := by
  classical
  let Idx : Finset (Finset (Fin r) × Fin m) :=
    (Finset.univ : Finset (Fin r)).powersetCard c ×ˢ (Finset.univ : Finset (Fin m))
  let cell (pj : Finset (Fin r) × Fin m) : Finset (Fin r → Fin m) :=
    ghMidPExtSet pj.1 {pj.2} (fun _ ↦ pj.2)
  have hcell_occ {pj : Finset (Fin r) × Fin m} (hpj : pj ∈ Idx) {h : Fin r → Fin m}
      (hh : h ∈ cell pj) :
      (Finset.univ.filter fun i : Fin r ↦ h i = pj.2) = pj.1 ∧
        ghMidPFiberOcc h pj.2 = c ∧
        ∀ j : Fin m, j ≠ pj.2 → ghMidPFiberOcc h j ≤ 1 := by
    have hP_card : pj.1.card = c := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hpj).1).2
    have hocc := ghMidPExtSet_occ (fun _ _ ↦ Finset.mem_singleton_self pj.2) hh
    have hfilt : (Finset.univ.filter fun i : Fin r ↦ h i = pj.2) = pj.1 := by
      rw [hocc.1 pj.2 (Finset.mem_singleton_self pj.2)]
      exact Finset.filter_true_of_mem fun _ _ ↦ rfl
    refine ⟨hfilt, ?_, fun j hj ↦ hocc.2 j (Finset.notMem_singleton.mpr hj)⟩
    dsimp only [ghMidPFiberOcc, ghMidPOcc]
    rw [hfilt, hP_card]
  have hunion : Idx.biUnion cell = ghMidPSingleMultFibers c r m := by
    ext h
    simp only [Finset.mem_biUnion, ghMidPSingleMultFibers, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨pj, hpj, hh⟩
      rcases hcell_occ hpj hh with ⟨_, hjc, hle1⟩
      exact ⟨pj.2, hjc, hle1⟩
    · rintro ⟨jc, hjc, hle1⟩
      let P := Finset.univ.filter fun i : Fin r ↦ h i = jc
      have hP_idx : (P, jc) ∈ Idx :=
        Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ P, hjc⟩,
          Finset.mem_univ jc⟩
      refine ⟨(P, jc), hP_idx, Finset.mem_filter.mpr ⟨Finset.mem_univ h, ?_, ?_, ?_⟩⟩
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi
        rw [Finset.mem_singleton]
        exact fun heq ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, heq⟩)
      · intro i₁ hi₁ i₂ _ heq
        have hn₁ : i₁ ∉ P := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hi₁)).2
        by_cases hne : h i₁ = jc
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i₁, hne⟩) hn₁
        · exact Finset.card_le_one.mp (hle1 (h i₁) hne)
            i₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ i₁, rfl⟩)
            i₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ i₂, heq.symm⟩)
  have hdisj : Set.PairwiseDisjoint (Idx : Set (Finset (Fin r) × Fin m)) cell := by
    intro pj₁ hpj₁ pj₂ hpj₂ hne
    refine Finset.disjoint_left.mpr fun h hh₁ hh₂ ↦ hne ?_
    rcases hcell_occ hpj₁ hh₁ with ⟨hf₁, hc₁, hle₁⟩
    rcases hcell_occ hpj₂ hh₂ with ⟨hf₂, hc₂, _⟩
    have hj_eq : pj₁.2 = pj₂.2 := by
      by_contra hj_ne
      have hle := hle₁ pj₂.2 (Ne.symm hj_ne)
      omega
    have hP_eq : pj₁.1 = pj₂.1 := by rw [← hf₁, ← hf₂, hj_eq]
    exact Prod.ext hP_eq hj_eq
  rw [← hunion, Finset.card_biUnion hdisj]
  have hterm : ∀ pj ∈ Idx, (cell pj).card = (m - 1).descFactorial (r - c) := by
    intro pj hpj
    have hP_card : pj.1.card = c := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hpj).1).2
    dsimp only [cell]
    rw [card_ghMidPExtSet, hP_card, Finset.card_singleton]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hIdx_card : Idx.card = r.choose c * m := by
    dsimp only [Idx]
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin]
  rw [hIdx_card, Nat.mul_assoc, ghMidP_mul_descFactorial_sub_one]
private def ghMidPIsTwoPair {r m : ℕ} (h : Fin r → Fin m) : Prop :=
  ∃ J₂ : Finset (Fin m), J₂.card = 2 ∧
    (∀ j ∈ J₂, ghMidPFiberOcc h j = 2) ∧
    (∀ j, j ∉ J₂ → ghMidPFiberOcc h j ≤ 1)
open Classical in
private noncomputable def ghMidPTwoPairFibers (r m : ℕ) : Finset (Fin r → Fin m) :=
  Finset.univ.filter ghMidPIsTwoPair
private lemma card_ghMidPTwoPairFibers {r m : ℕ} (hr4 : 4 ≤ r) :
    (ghMidPTwoPairFibers r m).card = 3 * r.choose 4 * m.descFactorial (r - 2) := by
  classical
  let pairSplits (Q : Finset (Fin r)) : Finset (Finset (Fin r)) :=
    if hQ : Q.Nonempty then
      (Q.erase (Q.min' hQ)).image fun i₁ ↦ ({Q.min' hQ, i₁} : Finset (Fin r))
    else ∅
  let ordPairsM : Finset (Fin m × Fin m) :=
    (Finset.univ : Finset (Fin m)).biUnion fun j₁ ↦
      ((Finset.univ : Finset (Fin m)).erase j₁).image fun j₂ ↦ (j₁, j₂)
  let Idx : Finset (Finset (Fin r) × Finset (Fin r) × Fin m × Fin m) :=
    ((Finset.univ : Finset (Fin r)).powersetCard 4).biUnion fun Q ↦
      (pairSplits Q).biUnion fun P₁ ↦
        ordPairsM.image fun jj ↦ (Q, P₁, jj.1, jj.2)
  let cell (t : Finset (Fin r) × Finset (Fin r) × Fin m × Fin m) : Finset (Fin r → Fin m) :=
    ghMidPExtSet t.1 {t.2.2.1, t.2.2.2} (fun i ↦ if i ∈ t.2.1 then t.2.2.1 else t.2.2.2)
  have hQ_props {Q : Finset (Fin r)} (hQ4 : Q ∈ (Finset.univ : Finset (Fin r)).powersetCard 4) :
      Q.card = 4 ∧ Q.Nonempty := by
    have hc4 : Q.card = 4 := (Finset.mem_powersetCard.mp hQ4).2
    exact ⟨hc4, Finset.card_pos.mp (by omega)⟩
  have hsplits_card {Q : Finset (Fin r)}
      (hQ4 : Q ∈ (Finset.univ : Finset (Fin r)).powersetCard 4) :
      (pairSplits Q).card = 3 := by
    rcases hQ_props hQ4 with ⟨hc4, hQne⟩
    dsimp only [pairSplits]
    rw [dite_eq_left hQne]
    set i₀ := Q.min' hQne
    have hi₀ : i₀ ∈ Q := Finset.min'_mem Q hQne
    have hinj : Set.InjOn (fun i₁ : Fin r ↦ ({i₀, i₁} : Finset (Fin r)))
        (Q.erase i₀ : Set (Fin r)) := by
      intro a ha b hb heq
      have ha_ne : a ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_coe.mp ha)).1
      have hb_ne : b ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_coe.mp hb)).1
      have her := congrArg (fun X : Finset (Fin r) ↦ X.erase i₀) heq
      have ha_er : ({i₀, a} : Finset (Fin r)).erase i₀ = {a} := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨hne, hx⟩ ↦ hx.resolve_left hne, fun hx ↦ ⟨hx ▸ ha_ne, Or.inr hx⟩⟩
      have hb_er : ({i₀, b} : Finset (Fin r)).erase i₀ = {b} := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨hne, hx⟩ ↦ hx.resolve_left hne, fun hx ↦ ⟨hx ▸ hb_ne, Or.inr hx⟩⟩
      rw [ha_er, hb_er] at her
      exact Finset.singleton_injective her
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hi₀, hc4]
  have hordM_card : ordPairsM.card = m * (m - 1) := by
    dsimp only [ordPairsM]
    have hdisj_m : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin m)) : Set (Fin m))
        (fun j₁ ↦ ((Finset.univ : Finset (Fin m)).erase j₁).image fun j₂ ↦ (j₁, j₂)) := by
      intro _ _ _ _ hne
      refine Finset.disjoint_left.mpr fun _ h1 h2 ↦ hne ?_
      rcases Finset.mem_image.mp h1 with ⟨_, _, heq1⟩
      rcases Finset.mem_image.mp h2 with ⟨_, _, heq2⟩
      exact (congrArg Prod.fst heq1).trans (congrArg Prod.fst heq2).symm
    rw [Finset.card_biUnion hdisj_m]
    have hc_m : ∀ j₁ ∈ (Finset.univ : Finset (Fin m)),
        (((Finset.univ : Finset (Fin m)).erase j₁).image fun j₂ ↦ (j₁, j₂)).card = m - 1 := by
      intro j₁ _
      rw [Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.snd h),
        Finset.card_erase_of_mem (Finset.mem_univ j₁), Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_congr rfl hc_m, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have hIdx_mem {t : Finset (Fin r) × Finset (Fin r) × Fin m × Fin m} (ht : t ∈ Idx) :
      t.1.card = 4 ∧ ∃ hQ : t.1.Nonempty,
        t.1.min' hQ ∈ t.2.1 ∧ t.2.1 ⊆ t.1 ∧ t.2.1.card = 2 ∧ t.2.2.2 ≠ t.2.2.1 := by
    rcases Finset.mem_biUnion.mp ht with ⟨Q, hQ4, ht1⟩
    rcases Finset.mem_biUnion.mp ht1 with ⟨P₁, hP₁, ht2⟩
    rcases Finset.mem_image.mp ht2 with ⟨⟨j₁, j₂⟩, hjj, rfl⟩
    rcases hQ_props hQ4 with ⟨hc4, hQne⟩
    dsimp only [pairSplits] at hP₁
    rw [dite_eq_left hQne] at hP₁
    rcases Finset.mem_image.mp hP₁ with ⟨i₁, hi₁_er, rfl⟩
    rcases Finset.mem_erase.mp hi₁_er with ⟨hi₁_ne, hi₁Q⟩
    rcases Finset.mem_biUnion.mp hjj with ⟨j₁', _, hjj'⟩
    rcases Finset.mem_image.mp hjj' with ⟨j₂', hj₂_er, hj_eq⟩
    have hj1_eq : j₁' = j₁ := congrArg Prod.fst hj_eq
    have hj2_eq : j₂' = j₂ := congrArg Prod.snd hj_eq
    subst hj1_eq hj2_eq
    refine ⟨hc4, hQne, Finset.mem_insert_self _ _, ?_, ?_, (Finset.mem_erase.mp hj₂_er).1⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx1
      · exact Finset.min'_mem Q hQne
      · exact Finset.mem_singleton.mp hx1 ▸ hi₁Q
    · rw [Finset.card_pair hi₁_ne.symm]
  have hcell_props {t : Finset (Fin r) × Finset (Fin r) × Fin m × Fin m} (ht : t ∈ Idx)
      {h : Fin r → Fin m} (hh : h ∈ cell t) :
      let J₂ : Finset (Fin m) := {t.2.2.1, t.2.2.2}
      (Finset.univ.filter fun j : Fin m ↦ ghMidPFiberOcc h j = 2) = J₂ ∧
        (Finset.univ.filter fun i : Fin r ↦ ghMidPFiberOcc h (h i) = 2) = t.1 ∧
        (t.1.filter fun i : Fin r ↦ h i = t.2.2.1) = t.2.1 ∧
        ghMidPIsTwoPair h := by
    intro J₂
    rcases hIdx_mem ht with ⟨_, _, _, hP₁_sub, hP₁_card, hj_ne⟩
    have hbase_mem : ∀ i ∈ t.1, (if i ∈ t.2.1 then t.2.2.1 else t.2.2.2) ∈ J₂ := fun i _ ↦ by
      by_cases hi : i ∈ t.2.1 <;> simp [J₂, hi]
    rcases ghMidPExtSet_occ hbase_mem hh with ⟨hocc_mem, hocc_not⟩
    have hf1 :
        (t.1.filter fun i ↦ (if i ∈ t.2.1 then t.2.2.1 else t.2.2.2) = t.2.2.1) = t.2.1 := by
      ext i
      simp only [Finset.mem_filter]
      by_cases hi : i ∈ t.2.1
      · simp [hi, hP₁_sub hi]
      · simp [hi, hj_ne]
    have hf2 :
        (t.1.filter fun i ↦ (if i ∈ t.2.1 then t.2.2.1 else t.2.2.2) = t.2.2.2) =
          t.1 \ t.2.1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      by_cases hi : i ∈ t.2.1
      · simp [hi, Ne.symm hj_ne]
      · simp [hi]
    have hocc_j1 : ghMidPFiberOcc h t.2.2.1 = 2 := by
      dsimp only [ghMidPFiberOcc, ghMidPOcc]
      rw [hocc_mem t.2.2.1 (by simp [J₂]), hf1, hP₁_card]
    have hocc_j2 : ghMidPFiberOcc h t.2.2.2 = 2 := by
      have hQ4 : t.1.card = 4 := (hIdx_mem ht).1
      dsimp only [ghMidPFiberOcc, ghMidPOcc]
      rw [hocc_mem t.2.2.2 (by simp [J₂]), hf2]
      have hadd := Finset.card_sdiff_add_card_eq_card hP₁_sub
      omega
    have hJ₂_all : ∀ j ∈ J₂, ghMidPFiberOcc h j = 2 := fun j hj ↦ by
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hocc_j1
      · rw [Finset.mem_singleton.mp hj']
        exact hocc_j2
    have hJ₂_filt : (Finset.univ.filter fun j : Fin m ↦ ghMidPFiberOcc h j = 2) = J₂ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hj : j ∈ J₂
      · exact ⟨fun _ ↦ hj, fun _ ↦ hJ₂_all j hj⟩
      · have hle := hocc_not j hj
        exact ⟨fun h2 ↦ by omega, fun hm ↦ absurd hm hj⟩
    rcases (Finset.mem_filter.mp hh).2 with ⟨hQ_val, hnotB, _⟩
    have hQ_filt : (Finset.univ.filter fun i : Fin r ↦ ghMidPFiberOcc h (h i) = 2) = t.1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i ∈ t.1
      · have hmemB : h i ∈ J₂ := hQ_val i hi ▸ hbase_mem i hi
        exact ⟨fun _ ↦ hi, fun _ ↦ hJ₂_all (h i) hmemB⟩
      · have hle := hocc_not (h i) (hnotB i hi)
        exact ⟨fun h2 ↦ by omega, fun hm ↦ absurd hm hi⟩
    have hP₁_filt : (t.1.filter fun i : Fin r ↦ h i = t.2.2.1) = t.2.1 := by
      have huf := (hocc_mem t.2.2.1 (by simp [J₂])).trans hf1
      ext i
      constructor
      · intro hi
        rw [← huf]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      · intro hiP
        have hi_u : i ∈ Finset.univ.filter fun i : Fin r ↦ h i = t.2.2.1 := by rwa [huf]
        exact Finset.mem_filter.mpr ⟨hP₁_sub hiP, (Finset.mem_filter.mp hi_u).2⟩
    exact ⟨hJ₂_filt, hQ_filt, hP₁_filt,
      ⟨J₂, Finset.card_pair hj_ne.symm, hJ₂_all, hocc_not⟩⟩
  have hunion : Idx.biUnion cell = ghMidPTwoPairFibers r m := by
    ext h
    simp only [Finset.mem_biUnion, ghMidPTwoPairFibers, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨t, ht, hh⟩
      exact (hcell_props ht hh).2.2.2
    · rintro ⟨J₂, hJ₂_card, hJ₂_occ, hJ₂_not⟩
      let Q : Finset (Fin r) := Finset.univ.filter fun i : Fin r ↦ h i ∈ J₂
      have hQ_bi : Q = J₂.biUnion fun j ↦ Finset.univ.filter fun i : Fin r ↦ h i = j := by
        ext i
        simp [Q]
      have hQ_disj : Set.PairwiseDisjoint (J₂ : Set (Fin m))
          (fun j ↦ Finset.univ.filter fun i : Fin r ↦ h i = j) :=
        fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun _ h1 h2 ↦
          hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hQ_card : Q.card = 4 := by
        rw [hQ_bi, Finset.card_biUnion hQ_disj]
        have hc2 : ∀ j ∈ J₂, (Finset.univ.filter fun i : Fin r ↦ h i = j).card = 2 := hJ₂_occ
        rw [Finset.sum_congr rfl hc2, Finset.sum_const, hJ₂_card, smul_eq_mul]
      have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
      set i₀ := Q.min' hQne
      have hi₀Q : i₀ ∈ Q := Finset.min'_mem Q hQne
      set j₁ := h i₀
      have hj₁J₂ : j₁ ∈ J₂ := (Finset.mem_filter.mp hi₀Q).2
      have her_j : (J₂.erase j₁).card = 1 := by
        rw [Finset.card_erase_of_mem hj₁J₂, hJ₂_card]
      obtain ⟨j₂, hj₂_eq⟩ := Finset.card_eq_one.mp her_j
      have hj₂_er : j₂ ∈ J₂.erase j₁ := hj₂_eq ▸ Finset.mem_singleton_self j₂
      have hj₂_ne : j₂ ≠ j₁ := (Finset.mem_erase.mp hj₂_er).1
      have hJ₂_eq : J₂ = {j₁, j₂} := by
        ext j
        by_cases hj1 : j = j₁
        · subst hj1
          simp [hj₁J₂]
        · have hmem_er : j ∈ J₂.erase j₁ ↔ j ∈ ({j₂} : Finset (Fin m)) := by rw [hj₂_eq]
          rw [Finset.mem_erase, Finset.mem_singleton] at hmem_er
          have hmem_j : j ∈ J₂ ↔ j = j₂ :=
            ⟨fun hj ↦ hmem_er.mp ⟨hj1, hj⟩, fun hj ↦ (hmem_er.mpr hj).2⟩
          simp [hj1, hmem_j]
      let P₁ : Finset (Fin r) := Finset.univ.filter fun i : Fin r ↦ h i = j₁
      have hP₁_card : P₁.card = 2 := hJ₂_occ j₁ hj₁J₂
      have hi₀P₁ : i₀ ∈ P₁ := Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, rfl⟩
      have her_i : (P₁.erase i₀).card = 1 := by
        rw [Finset.card_erase_of_mem hi₀P₁, hP₁_card]
      obtain ⟨i₁, hi₁_eq⟩ := Finset.card_eq_one.mp her_i
      have hi₁_er : i₁ ∈ P₁.erase i₀ := hi₁_eq ▸ Finset.mem_singleton_self i₁
      have hi₁_ne : i₁ ≠ i₀ := (Finset.mem_erase.mp hi₁_er).1
      have hi₁P₁ : i₁ ∈ P₁ := (Finset.mem_erase.mp hi₁_er).2
      have hi₁Q : i₁ ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ i₁,
        (Finset.mem_filter.mp hi₁P₁).2 ▸ hj₁J₂⟩
      have hP₁_eq : P₁ = {i₀, i₁} := by
        ext i
        by_cases hi0 : i = i₀
        · subst hi0
          simp [hi₀P₁]
        · have hmem_er : i ∈ P₁.erase i₀ ↔ i ∈ ({i₁} : Finset (Fin r)) := by rw [hi₁_eq]
          rw [Finset.mem_erase, Finset.mem_singleton] at hmem_er
          have hmem_i : i ∈ P₁ ↔ i = i₁ :=
            ⟨fun hi ↦ hmem_er.mp ⟨hi0, hi⟩, fun hi ↦ (hmem_er.mpr hi).2⟩
          simp [hi0, hmem_i]
      have ht_mem : (Q, P₁, j₁, j₂) ∈ Idx := by
        refine Finset.mem_biUnion.mpr ⟨Q,
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Q, hQ_card⟩,
          Finset.mem_biUnion.mpr ⟨P₁, ?_, Finset.mem_image.mpr ⟨(j₁, j₂), ?_, rfl⟩⟩⟩
        · dsimp only [pairSplits]
          rw [dite_eq_left hQne]
          exact Finset.mem_image.mpr ⟨i₁, Finset.mem_erase.mpr ⟨hi₁_ne, hi₁Q⟩, hP₁_eq.symm⟩
        · exact Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ j₁,
            Finset.mem_image.mpr ⟨j₂, Finset.mem_erase.mpr ⟨hj₂_ne, Finset.mem_univ j₂⟩, rfl⟩⟩
      refine ⟨(Q, P₁, j₁, j₂), ht_mem, Finset.mem_filter.mpr ⟨Finset.mem_univ h, ?_, ?_, ?_⟩⟩
      · intro i hiQ
        dsimp only
        have hiJ₂ : h i ∈ J₂ := (Finset.mem_filter.mp hiQ).2
        rw [hJ₂_eq] at hiJ₂
        by_cases hiP : i ∈ P₁
        · rw [ite_eq_left hiP]
          exact (Finset.mem_filter.mp hiP).2
        · rw [ite_eq_right hiP]
          rcases Finset.mem_insert.mp hiJ₂ with hj1 | hj2
          · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hj1⟩) hiP
          · exact Finset.mem_singleton.mp hj2
      · intro i hinotQ
        rw [← hJ₂_eq]
        exact fun hm ↦ hinotQ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hm⟩)
      · intro a ha b _ heq
        have hna : a ∉ Q := (Finset.mem_sdiff.mp (Finset.mem_coe.mp ha)).2
        have hnotJ₂ : h a ∉ J₂ := fun hm ↦ hna (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hm⟩)
        exact Finset.card_le_one.mp (hJ₂_not (h a) hnotJ₂)
          a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, rfl⟩)
          b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, heq.symm⟩)
  have hdisj : Set.PairwiseDisjoint (Idx : Set _) cell := by
    intro t₁ ht₁ t₂ ht₂ hne
    refine Finset.disjoint_left.mpr fun h hh₁ hh₂ ↦ hne ?_
    rcases hcell_props ht₁ hh₁ with ⟨hJ₂_1, hQ_1, hP₁_1, _⟩
    rcases hcell_props ht₂ hh₂ with ⟨hJ₂_2, hQ_2, hP₁_2, _⟩
    rcases hIdx_mem ht₁ with ⟨_, hQne₁, hmin₁, hsub₁, _, hjne₁⟩
    rcases hIdx_mem ht₂ with ⟨_, _, hmin₂, hsub₂, _, hjne₂⟩
    have hQ_eq : t₁.1 = t₂.1 := hQ_1.symm.trans hQ_2
    rcases t₁ with ⟨Q₁, P₁₁, j₁₁, j₂₁⟩
    rcases t₂ with ⟨Q₂, P₁₂, j₁₂, j₂₂⟩
    dsimp only at hQ_eq hJ₂_1 hJ₂_2 hP₁_1 hP₁_2 hQne₁ hmin₁ hmin₂ hsub₁ hsub₂ hjne₁ hjne₂
    subst hQ_eq
    rcases (Finset.mem_filter.mp hh₁).2 with ⟨hval₁, _, _⟩
    rcases (Finset.mem_filter.mp hh₂).2 with ⟨hval₂, _, _⟩
    have hj1_eq : j₁₁ = j₁₂ := by
      have v1 := hval₁ (Q₁.min' hQne₁) (hsub₁ hmin₁)
      have v2 := hval₂ (Q₁.min' hQne₁) (hsub₂ hmin₂)
      dsimp only at v1 v2
      rw [ite_eq_left hmin₁] at v1
      rw [ite_eq_left hmin₂] at v2
      exact v1.symm.trans v2
    subst hj1_eq
    have hP1_eq : P₁₁ = P₁₂ := hP₁_1.symm.trans hP₁_2
    subst hP1_eq
    have hpair_eq : ({j₁₁, j₂₁} : Finset (Fin m)) = {j₁₁, j₂₂} := hJ₂_1.symm.trans hJ₂_2
    have her_eq := congrArg (fun X : Finset (Fin m) ↦ X.erase j₁₁) hpair_eq
    have her1 : ({j₁₁, j₂₁} : Finset (Fin m)).erase j₁₁ = {j₂₁} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨hne', hx⟩ ↦ hx.resolve_left hne', fun hx ↦ ⟨hx ▸ hjne₁, Or.inr hx⟩⟩
    have her2 : ({j₁₁, j₂₂} : Finset (Fin m)).erase j₁₁ = {j₂₂} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨hne', hx⟩ ↦ hx.resolve_left hne', fun hx ↦ ⟨hx ▸ hjne₂, Or.inr hx⟩⟩
    rw [her1, her2] at her_eq
    rw [Finset.singleton_injective her_eq]
  rw [← hunion, Finset.card_biUnion hdisj]
  have hterm : ∀ t ∈ Idx, (cell t).card = (m - 2).descFactorial (r - 4) := by
    intro t ht
    rcases hIdx_mem ht with ⟨hQ4, _, _, _, _, hj_ne⟩
    dsimp only [cell]
    rw [card_ghMidPExtSet, hQ4, Finset.card_pair hj_ne.symm]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hIdx_card : Idx.card = r.choose 4 * (3 * (m * (m - 1))) := by
    dsimp only [Idx]
    have hd1 : Set.PairwiseDisjoint
        (((Finset.univ : Finset (Fin r)).powersetCard 4) : Set (Finset (Fin r)))
        (fun Q ↦ (pairSplits Q).biUnion fun P₁ ↦ ordPairsM.image fun jj ↦ (Q, P₁, jj.1, jj.2)) := by
      intro _ _ _ _ hne
      refine Finset.disjoint_left.mpr fun _ h1 h2 ↦ hne ?_
      rcases Finset.mem_biUnion.mp h1 with ⟨_, _, hi1⟩
      rcases Finset.mem_image.mp hi1 with ⟨_, _, heq1⟩
      rcases Finset.mem_biUnion.mp h2 with ⟨_, _, hi2⟩
      rcases Finset.mem_image.mp hi2 with ⟨_, _, heq2⟩
      exact (congrArg Prod.fst heq1).trans (congrArg Prod.fst heq2).symm
    rw [Finset.card_biUnion hd1]
    have hc_Q : ∀ Q ∈ (Finset.univ : Finset (Fin r)).powersetCard 4,
        ((pairSplits Q).biUnion fun P₁ ↦ ordPairsM.image fun jj ↦ (Q, P₁, jj.1, jj.2)).card =
          3 * (m * (m - 1)) := by
      intro Q hQ4
      have hd2 : Set.PairwiseDisjoint (pairSplits Q : Set (Finset (Fin r)))
          (fun P₁ ↦ ordPairsM.image fun jj ↦ (Q, P₁, jj.1, jj.2)) := by
        intro _ _ _ _ hne
        refine Finset.disjoint_left.mpr fun _ h1 h2 ↦ hne ?_
        rcases Finset.mem_image.mp h1 with ⟨_, _, heq1⟩
        rcases Finset.mem_image.mp h2 with ⟨_, _, heq2⟩
        exact (congrArg (fun x ↦ x.2.1) heq1).trans (congrArg (fun x ↦ x.2.1) heq2).symm
      rw [Finset.card_biUnion hd2]
      have hc_P : ∀ P₁ ∈ pairSplits Q,
          (ordPairsM.image fun jj ↦ (Q, P₁, jj.1, jj.2)).card = m * (m - 1) := by
        intro P₁ _
        rw [Finset.card_image_of_injective _
            (fun a b h ↦ Prod.ext (congrArg (fun x ↦ x.2.2.1) h) (congrArg (fun x ↦ x.2.2.2) h)),
          hordM_card]
      rw [Finset.sum_congr rfl hc_P, Finset.sum_const, hsplits_card hQ4, smul_eq_mul]
    rw [Finset.sum_congr rfl hc_Q, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hIdx_card]
  have hm_step1 : (m - 1) * (m - 2).descFactorial (r - 4) = (m - 1).descFactorial (r - 3) := by
    have hm2_eq : m - 2 = (m - 1) - 1 := by omega
    have hr3_eq : r - 3 = (r - 4) + 1 := by omega
    rw [hm2_eq, hr3_eq, ghMidP_mul_descFactorial_sub_one]
  have hm_step2 : m * (m - 1).descFactorial (r - 3) = m.descFactorial (r - 2) := by
    have hr2_eq : r - 2 = (r - 3) + 1 := by omega
    rw [hr2_eq, ghMidP_mul_descFactorial_sub_one]
  calc r.choose 4 * (3 * (m * (m - 1))) * (m - 2).descFactorial (r - 4)
      = 3 * r.choose 4 * (m * ((m - 1) * (m - 2).descFactorial (r - 4))) := by ring
    _ = 3 * r.choose 4 * (m * (m - 1).descFactorial (r - 3)) := by rw [hm_step1]
    _ = 3 * r.choose 4 * m.descFactorial (r - 2) := by rw [hm_step2]
/- ## 3. Abstract Subset Evolution, `SlotRot`, & Exact Fiber Steps -/

/-- Selected hit subset from a per-slot `Option α` choice vector. -/
def ghMidPChoiceSet {α : Type*} [DecidableEq α] {m : ℕ}
    (c : Fin m → Option α) : Finset α :=
  Finset.univ.biUnion fun j : Fin m ↦
    match c j with
    | none => ∅
    | some x => {x}
/-- Uniform hit choices picking one element of `R ∩ pref ⁻¹' {j}` for each `j ∈ A`. -/
def ghMidPHitChoices {α : Type*} [DecidableEq α] {m : ℕ} (pref : α → Fin m)
    (R : Finset α) (A : Finset (Fin m)) : Finset (Fin m → Option α) :=
  Fintype.piFinset fun j : Fin m ↦
    if j ∈ A then (R.filter fun x ↦ pref x = j).image Option.some else {none}
/-- Reciprocal-occupancy probability weight `∏ j ∈ A, 1 / occ(j)` of each choice in
  `ghMidPHitChoices pref R A`. -/
noncomputable def ghMidPChoiceWeight {α : Type*} [DecidableEq α] {m : ℕ}
    (pref : α → Fin m) (R : Finset α) (A : Finset (Fin m)) : ℝ :=
  ∏ j ∈ A, (1 / (ghMidPOcc pref R j : ℝ))
lemma ghMidPChoiceWeight_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (pref : α → Fin m) (R : Finset α) (A : Finset (Fin m)) :
    0 ≤ ghMidPChoiceWeight pref R A :=
  Finset.prod_nonneg fun _ _ ↦ by positivity
lemma ghMidPHitChoices_sum_weight {α : Type*} [DecidableEq α] {m : ℕ}
    (pref : α → Fin m) (R : Finset α) {A : Finset (Fin m)} (hA : A ⊆ R.image pref) :
    (∑ _c ∈ ghMidPHitChoices pref R A, ghMidPChoiceWeight pref R A) = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul, ghMidPHitChoices, Fintype.card_piFinset]
  have hcard_j (j : Fin m) :
      (if j ∈ A then (R.filter fun x ↦ pref x = j).image Option.some else {none}).card =
        if j ∈ A then ghMidPOcc pref R j else 1 := by
    split_ifs
    · exact Finset.card_image_of_injective _ (Option.some_injective α)
    · exact Finset.card_singleton none
  simp_rw [hcard_j]
  have hprod_A :
      (∏ j : Fin m, if j ∈ A then ghMidPOcc pref R j else 1) =
        ∏ j ∈ A, ghMidPOcc pref R j := by
    rw [← Finset.prod_subset (Finset.subset_univ A) fun j _ hj ↦ ite_eq_right hj]
    exact Finset.prod_congr rfl fun j hj ↦ ite_eq_left hj
  rw [hprod_A, Nat.cast_prod, ghMidPChoiceWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j hj ↦ ?_
  rcases Finset.mem_image.mp (hA hj) with ⟨x, hxR, hxj⟩
  have hpos : 0 < ghMidPOcc pref R j :=
    Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxR, hxj⟩⟩
  exact mul_one_div_cancel (Nat.cast_ne_zero.mpr hpos.ne')
lemma ghMidPChoiceSet_props {α : Type*} [DecidableEq α] {m : ℕ}
    {pref : α → Fin m} {R : Finset α} {A : Finset (Fin m)}
    {c : Fin m → Option α} (hc : c ∈ ghMidPHitChoices pref R A) :
    ghMidPChoiceSet c ⊆ R ∧
      (ghMidPChoiceSet c).image pref = A ∧
      (ghMidPChoiceSet c).card = A.card ∧
      (R \ ghMidPChoiceSet c).card = R.card - A.card := by
  have hc_pi := Fintype.mem_piFinset.mp hc
  have hmem_iff (x : α) : x ∈ ghMidPChoiceSet c ↔ ∃ j : Fin m, c j = some x := by
    unfold ghMidPChoiceSet
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨fun ⟨j, hj⟩ ↦ ⟨j, ?_⟩, fun ⟨j, hj⟩ ↦ ⟨j, ?_⟩⟩
    · cases hcj : c j with
      | none => rw [hcj] at hj; exact False.elim (Finset.notMem_empty x hj)
      | some y => rw [hcj, Finset.mem_singleton] at hj; rw [hj]
    · rw [hj]; exact Finset.mem_singleton_self x
  have hslot_some {j : Fin m} {x : α} (hcj : c j = some x) :
      j ∈ A ∧ x ∈ R ∧ pref x = j := by
    have hmj := hc_pi j
    rw [hcj] at hmj
    by_cases hjA : j ∈ A
    · rw [ite_eq_left hjA, Finset.mem_image] at hmj
      rcases hmj with ⟨y, hyf, hy_eq⟩
      have hxy : y = x := Option.some.inj hy_eq
      subst hxy
      rcases Finset.mem_filter.mp hyf with ⟨hxR, hxj⟩
      exact ⟨hjA, hxR, hxj⟩
    · rw [ite_eq_right hjA, Finset.mem_singleton] at hmj
      cases hmj
  have hsub : ghMidPChoiceSet c ⊆ R := fun x hx ↦ by
    rcases (hmem_iff x).mp hx with ⟨j, hcj⟩
    exact (hslot_some hcj).2.1
  have himg : (ghMidPChoiceSet c).image pref = A := by
    ext j
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (hmem_iff x).mp hx with ⟨j', hcj'⟩
      rcases hslot_some hcj' with ⟨hj'A, _, hpx⟩
      rwa [hpx]
    · intro hjA
      have hmj := hc_pi j
      rw [ite_eq_left hjA, Finset.mem_image] at hmj
      rcases hmj with ⟨x, hxf, hcx⟩
      rcases Finset.mem_filter.mp hxf with ⟨_, hpx⟩
      exact ⟨x, (hmem_iff x).mpr ⟨j, hcx.symm⟩, hpx⟩
  have hinj_c : Set.InjOn pref (ghMidPChoiceSet c : Set α) := by
    intro x₁ hx₁ x₂ hx₂ heq
    rcases (hmem_iff x₁).mp (Finset.mem_coe.mp hx₁) with ⟨j₁, hcj₁⟩
    rcases (hmem_iff x₂).mp (Finset.mem_coe.mp hx₂) with ⟨j₂, hcj₂⟩
    have hj₁ : pref x₁ = j₁ := (hslot_some hcj₁).2.2
    have hj₂ : pref x₂ = j₂ := (hslot_some hcj₂).2.2
    have hjj : j₁ = j₂ := hj₁.symm.trans (heq.trans hj₂)
    subst hjj
    exact Option.some.inj (hcj₁.symm.trans hcj₂)
  have hcard_c : (ghMidPChoiceSet c).card = A.card := by
    rw [← himg, Finset.card_image_of_injOn hinj_c]
  have hsdiff_c : (R \ ghMidPChoiceSet c).card = R.card - A.card := by
    have hadd := Finset.card_sdiff_add_card_eq_card hsub
    omega
  exact ⟨hsub, himg, hcard_c, hsdiff_c⟩
private lemma ghMidP_normSq_rot2D_real (cr sr : ℝ) (hcs : cr ^ 2 + sr ^ 2 = 1) (a b : ℂ) :
    normSq ((cr : ℂ) * a - (sr : ℂ) * b) + normSq ((sr : ℂ) * a + (cr : ℂ) * b) =
      normSq a + normSq b := by
  have key :
      normSq ((cr : ℂ) * a - (sr : ℂ) * b) + normSq ((sr : ℂ) * a + (cr : ℂ) * b) =
        (cr ^ 2 + sr ^ 2) * (normSq a + normSq b) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [key, hcs, one_mul]
private lemma ghMidP_sum_powerset_insert {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommMonoid M] {J : Finset ι} {a : ι} (ha : a ∉ J) (f : Finset ι → M) :
    (∑ A ∈ (insert a J).powerset, f A) =
      (∑ A ∈ J.powerset, f A) + ∑ A ∈ J.powerset, f (insert a A) := by
  have hdisj : Disjoint J.powerset (J.powerset.image (insert a)) := by
    refine Finset.disjoint_left.mpr fun X hX₁ hX₂ ↦ ?_
    rcases Finset.mem_image.mp hX₂ with ⟨Y, _, rfl⟩
    exact ha (Finset.mem_powerset.mp hX₁ (Finset.mem_insert_self a Y))
  have hinj : Set.InjOn (insert a) (J.powerset : Set (Finset ι)) := by
    intro A₁ hA₁ A₂ hA₂ heq
    have ha₁ : a ∉ A₁ := fun hm ↦ ha (Finset.mem_powerset.mp hA₁ hm)
    have ha₂ : a ∉ A₂ := fun hm ↦ ha (Finset.mem_powerset.mp hA₂ hm)
    have her := congrArg (fun X : Finset ι ↦ X.erase a) heq
    simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using her
  rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj]
/-- Tensor-product `2 × 2` Grover slot rotation across `J: Finset ι`. -/
noncomputable def ghMidPSlotRot {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (cr sr : ι → ℝ) (coeff : Finset ι → ℂ) (B : Finset ι) : ℂ :=
  ∑ A ∈ J.powerset,
    coeff A *
      ∏ j ∈ J,
        if j ∈ B then
          if j ∈ A then (cr j : ℂ) else (sr j : ℂ)
        else
          if j ∈ A then -(sr j : ℂ) else (cr j : ℂ)
lemma ghMidPSlotRot_insert_notMem {ι : Type*} [DecidableEq ι] {J : Finset ι} {a : ι}
    (ha : a ∉ J) (cr sr : ι → ℝ) (coeff : Finset ι → ℂ) {B : Finset ι} (hB : B ⊆ J) :
    ghMidPSlotRot (insert a J) cr sr coeff B =
        ghMidPSlotRot J cr sr
          (fun A ↦ (cr a : ℂ) * coeff A - (sr a : ℂ) * coeff (insert a A)) B ∧
      ghMidPSlotRot (insert a J) cr sr coeff (insert a B) =
        ghMidPSlotRot J cr sr
          (fun A ↦ (sr a : ℂ) * coeff A + (cr a : ℂ) * coeff (insert a A)) B := by
  have haB : a ∉ B := fun hm ↦ ha (hB hm)
  constructor
  · unfold ghMidPSlotRot
    rw [ghMidP_sum_powerset_insert ha, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    have haA : a ∉ A := fun hm ↦ ha (Finset.mem_powerset.mp hA hm)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hprod_eq :
        (∏ j ∈ J,
          if j ∈ B then
            if j ∈ insert a A then (cr j : ℂ) else (sr j : ℂ)
          else
            if j ∈ insert a A then -(sr j : ℂ) else (cr j : ℂ)) =
        ∏ j ∈ J,
          if j ∈ B then
            if j ∈ A then (cr j : ℂ) else (sr j : ℂ)
          else
            if j ∈ A then -(sr j : ℂ) else (cr j : ℂ) := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hja : j ≠ a := fun h ↦ ha (h ▸ hj)
      simp [hja]
    rw [hprod_eq]
    simp only [haB, haA, Finset.mem_insert_self, ↓reduceIte]
    ring
  · unfold ghMidPSlotRot
    rw [ghMidP_sum_powerset_insert ha, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    have haA : a ∉ A := fun hm ↦ ha (Finset.mem_powerset.mp hA hm)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hprod_eq₁ :
        (∏ j ∈ J,
          if j ∈ insert a B then
            if j ∈ A then (cr j : ℂ) else (sr j : ℂ)
          else
            if j ∈ A then -(sr j : ℂ) else (cr j : ℂ)) =
        ∏ j ∈ J,
          if j ∈ B then
            if j ∈ A then (cr j : ℂ) else (sr j : ℂ)
          else
            if j ∈ A then -(sr j : ℂ) else (cr j : ℂ) := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hja : j ≠ a := fun h ↦ ha (h ▸ hj)
      simp [hja]
    have hprod_eq₂ :
        (∏ j ∈ J,
          if j ∈ insert a B then
            if j ∈ insert a A then (cr j : ℂ) else (sr j : ℂ)
          else
            if j ∈ insert a A then -(sr j : ℂ) else (cr j : ℂ)) =
        ∏ j ∈ J,
          if j ∈ B then
            if j ∈ A then (cr j : ℂ) else (sr j : ℂ)
          else
            if j ∈ A then -(sr j : ℂ) else (cr j : ℂ) := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hja : j ≠ a := fun h ↦ ha (h ▸ hj)
      simp [hja]
    rw [hprod_eq₁, hprod_eq₂]
    simp only [haA, Finset.mem_insert_self, ↓reduceIte]
    ring
lemma ghMidPSlotRot_mul_prod_eq {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (cr sr : ι → ℝ) (coeff : Finset ι → ℂ) (x₀ x₁ : ι → ℂ) :
    (∑ A ∈ J.powerset,
      coeff A * ∏ j ∈ J,
        (if j ∈ A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
         else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) =
    ∑ B ∈ J.powerset,
      ghMidPSlotRot J cr sr coeff B * ∏ j ∈ J, (if j ∈ B then x₁ j else x₀ j) := by
  induction J using Finset.induction_on generalizing coeff with
  | empty =>
    simp [ghMidPSlotRot]
  | @insert a J ha ih =>
    rw [ghMidP_sum_powerset_insert ha, ghMidP_sum_powerset_insert ha]
    have hlhs :
        (∑ A ∈ J.powerset,
          coeff A * ∏ j ∈ insert a J,
            (if j ∈ A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
             else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) +
        (∑ A ∈ J.powerset,
          coeff (insert a A) * ∏ j ∈ insert a J,
            (if j ∈ insert a A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
             else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) =
        x₀ a *
          (∑ A ∈ J.powerset,
            ((cr a : ℂ) * coeff A - (sr a : ℂ) * coeff (insert a A)) *
              ∏ j ∈ J,
                (if j ∈ A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
                 else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) +
        x₁ a *
          (∑ A ∈ J.powerset,
            ((sr a : ℂ) * coeff A + (cr a : ℂ) * coeff (insert a A)) *
              ∏ j ∈ J,
                (if j ∈ A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
                 else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun A hA ↦ ?_
      have haA : a ∉ A := fun hm ↦ ha (Finset.mem_powerset.mp hA hm)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hp_eq :
          (∏ j ∈ J,
            (if j ∈ insert a A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
             else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) =
          ∏ j ∈ J,
            (if j ∈ A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
             else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j) := by
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        have hja : j ≠ a := fun h ↦ ha (h ▸ hj)
        simp [hja]
      rw [hp_eq]
      simp only [haA, Finset.mem_insert_self, ↓reduceIte]
      ring
    rw [hlhs, ih, ih, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun B hB ↦ ?_
      have hBJ := Finset.mem_powerset.mp hB
      have haB : a ∉ B := fun hm ↦ ha (hBJ hm)
      rw [(ghMidPSlotRot_insert_notMem ha cr sr coeff hBJ).1, Finset.prod_insert ha,
        ite_eq_right haB]
      ring
    · refine Finset.sum_congr rfl fun B hB ↦ ?_
      have hBJ := Finset.mem_powerset.mp hB
      rw [(ghMidPSlotRot_insert_notMem ha cr sr coeff hBJ).2, Finset.prod_insert ha,
        ite_eq_left (Finset.mem_insert_self a B)]
      have hpB :
          (∏ j ∈ J, if j ∈ insert a B then x₁ j else x₀ j) =
            ∏ j ∈ J, if j ∈ B then x₁ j else x₀ j := by
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        have hja : j ≠ a := fun h ↦ ha (h ▸ hj)
        simp [hja]
      rw [hpB]
      ring
lemma ghMidPSlotRot_sum_normSq {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (cr sr : ι → ℝ) (hcs : ∀ j ∈ J, cr j ^ 2 + sr j ^ 2 = 1) (coeff : Finset ι → ℂ) :
    (∑ B ∈ J.powerset, normSq (ghMidPSlotRot J cr sr coeff B)) =
      ∑ A ∈ J.powerset, normSq (coeff A) := by
  induction J using Finset.induction_on generalizing coeff with
  | empty =>
    simp [ghMidPSlotRot]
  | @insert a J ha ih =>
    have hcs_a : cr a ^ 2 + sr a ^ 2 = 1 := hcs a (Finset.mem_insert_self a J)
    have hcs_J : ∀ j ∈ J, cr j ^ 2 + sr j ^ 2 = 1 :=
      fun j hj ↦ hcs j (Finset.mem_insert_of_mem hj)
    rw [ghMidP_sum_powerset_insert ha, ghMidP_sum_powerset_insert ha]
    have hb0 :
        (∑ B ∈ J.powerset, normSq (ghMidPSlotRot (insert a J) cr sr coeff B)) =
          ∑ B ∈ J.powerset,
            normSq (ghMidPSlotRot J cr sr
              (fun A ↦ (cr a : ℂ) * coeff A - (sr a : ℂ) * coeff (insert a A)) B) :=
      Finset.sum_congr rfl fun B hB ↦ by
        rw [(ghMidPSlotRot_insert_notMem ha cr sr coeff (Finset.mem_powerset.mp hB)).1]
    have hb1 :
        (∑ B ∈ J.powerset, normSq (ghMidPSlotRot (insert a J) cr sr coeff (insert a B))) =
          ∑ B ∈ J.powerset,
            normSq (ghMidPSlotRot J cr sr
              (fun A ↦ (sr a : ℂ) * coeff A + (cr a : ℂ) * coeff (insert a A)) B) :=
      Finset.sum_congr rfl fun B hB ↦ by
        rw [(ghMidPSlotRot_insert_notMem ha cr sr coeff (Finset.mem_powerset.mp hB)).2]
    rw [hb0, hb1, ih hcs_J, ih hcs_J, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun A _ ↦ ghMidP_normSq_rot2D_real (cr a) (sr a) hcs_a _ _
lemma ghMidPSlotRot_linear {ι : Type*} [DecidableEq ι] (J : Finset ι) (cr sr : ι → ℝ)
    (α β : ℂ) (f g : Finset ι → ℂ) (B : Finset ι) :
    ghMidPSlotRot J cr sr (fun A ↦ α * f A + β * g A) B =
      α * ghMidPSlotRot J cr sr f B + β * ghMidPSlotRot J cr sr g B := by
  unfold ghMidPSlotRot
  simp_rw [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
lemma ghMidPSlotRot_sub {ι : Type*} [DecidableEq ι] (J : Finset ι) (cr sr : ι → ℝ)
    (α β : ℂ) (f g : Finset ι → ℂ) (B : Finset ι) :
    ghMidPSlotRot J cr sr (fun A ↦ α * f A - β * g A) B =
      α * ghMidPSlotRot J cr sr f B - β * ghMidPSlotRot J cr sr g B := by
  simpa [sub_eq_add_neg, neg_mul] using ghMidPSlotRot_linear J cr sr α (-β) f g B
lemma ghMidPSlotRot_const_eq_dickeStep {m : ℕ}
    (J : Finset (Fin m)) {cr sr : Fin m → ℝ} {c₁ s₁ : ℝ}
    (hcr : ∀ j ∈ J, cr j = c₁) (hsr : ∀ j ∈ J, sr j = s₁)
    {coeff : Finset (Fin m) → ℂ} (u : ℕ → ℂ) (hu : ∀ A ∈ J.powerset, coeff A = u A.card)
    {B : Finset (Fin m)} (hB : B ∈ J.powerset) :
    ghMidPSlotRot J cr sr coeff B = dickeStep J.card (c₁ : ℂ) (s₁ : ℂ) u B.card := by
  let x₀ (j : Fin m) : ℂ := if j ∈ B then 0 else 1
  let x₁ (j : Fin m) : ℂ := if j ∈ B then 1 else 0
  have hdelta (B' : Finset (Fin m)) (hB' : B' ∈ J.powerset) :
      (∏ j ∈ J, if j ∈ B' then x₁ j else x₀ j) = if B' = B then 1 else 0 := by
    by_cases heq : B' = B
    · subst heq
      rw [ite_eq_left rfl]
      refine Finset.prod_eq_one fun j _ ↦ ?_
      by_cases hj : j ∈ B' <;> simp [x₀, x₁, hj]
    · rw [ite_eq_right heq]
      have hex : ∃ j₀ ∈ J, ¬ ((if j₀ ∈ B' then x₁ j₀ else x₀ j₀) = 1) := by
        by_contra hall
        apply heq
        ext j
        by_cases hjJ : j ∈ J
        · have hj1 : (if j ∈ B' then x₁ j else x₀ j) = 1 := by
            by_contra hne1
            exact hall ⟨j, hjJ, hne1⟩
          by_cases hjB' : j ∈ B' <;> by_cases hjB : j ∈ B <;>
            simp [x₀, x₁, hjB', hjB] at hj1 ⊢
        · exact ⟨fun h1 ↦ absurd (Finset.mem_powerset.mp hB' h1) hjJ,
            fun h2 ↦ absurd (Finset.mem_powerset.mp hB h2) hjJ⟩
      rcases hex with ⟨j₀, hj₀J, hne1⟩
      refine Finset.prod_eq_zero hj₀J ?_
      by_cases hjB' : j₀ ∈ B' <;> by_cases hjB : j₀ ∈ B <;>
        simp [x₀, x₁, hjB', hjB] at hne1 ⊢
  have hlhs := ghMidPSlotRot_mul_prod_eq J cr sr coeff x₀ x₁
  have hrhs := prod_dickeStep_powerset J (c₁ : ℂ) (s₁ : ℂ) x₀ x₁ (fun _ ↦ 1) u
  have hlhs_eq_rhs :
      (∑ A ∈ J.powerset,
        coeff A * ∏ j ∈ J,
          (if j ∈ A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j
           else (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) =
      ∑ A ∈ J.powerset,
        u A.card * ∏ j : Fin m,
          if j ∈ J then
            if j ∈ A then -(s₁ : ℂ) * x₀ j + (c₁ : ℂ) * x₁ j
            else (c₁ : ℂ) * x₀ j + (s₁ : ℂ) * x₁ j
          else 1 := by
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    rw [hu A hA]
    congr 1
    have hp_univ :
        (∏ j : Fin m,
          if j ∈ J then
            if j ∈ A then -(s₁ : ℂ) * x₀ j + (c₁ : ℂ) * x₁ j
            else (c₁ : ℂ) * x₀ j + (s₁ : ℂ) * x₁ j
          else 1) =
        ∏ j ∈ J,
          (if j ∈ A then -(s₁ : ℂ) * x₀ j + (c₁ : ℂ) * x₁ j
           else (c₁ : ℂ) * x₀ j + (s₁ : ℂ) * x₁ j) := by
      rw [← Finset.prod_subset (Finset.subset_univ J) fun j _ hj ↦ ite_eq_right hj]
      exact Finset.prod_congr rfl fun j hj ↦ ite_eq_left hj
    rw [hp_univ]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [hcr j hj, hsr j hj]
  have hrhs_B :
      (∑ B' ∈ J.powerset,
        dickeStep J.card (c₁ : ℂ) (s₁ : ℂ) u B'.card *
          ∏ j : Fin m, if j ∈ J then if j ∈ B' then x₁ j else x₀ j else 1) =
      dickeStep J.card (c₁ : ℂ) (s₁ : ℂ) u B.card := by
    have hcongr : ∀ B' ∈ J.powerset,
        dickeStep J.card (c₁ : ℂ) (s₁ : ℂ) u B'.card *
          (∏ j : Fin m, if j ∈ J then if j ∈ B' then x₁ j else x₀ j else 1) =
        dickeStep J.card (c₁ : ℂ) (s₁ : ℂ) u B'.card * (if B' = B then 1 else 0) := by
      intro B' hB'
      congr 1
      have hp_u :
          (∏ j : Fin m, if j ∈ J then if j ∈ B' then x₁ j else x₀ j else 1) =
            ∏ j ∈ J, if j ∈ B' then x₁ j else x₀ j := by
        rw [← Finset.prod_subset (Finset.subset_univ J) fun j _ hj ↦ ite_eq_right hj]
        exact Finset.prod_congr rfl fun j hj ↦ ite_eq_left hj
      rw [hp_u, hdelta B' hB']
    rw [Finset.sum_congr rfl hcongr,
      Finset.sum_eq_single B (fun B' _ hne ↦ by rw [ite_eq_right hne, mul_zero])
        (fun hnot ↦ absurd hB hnot),
      ite_eq_left rfl, mul_one]
  have hlhs_B :
      (∑ B' ∈ J.powerset,
        ghMidPSlotRot J cr sr coeff B' * ∏ j ∈ J, (if j ∈ B' then x₁ j else x₀ j)) =
      ghMidPSlotRot J cr sr coeff B := by
    have hcongr : ∀ B' ∈ J.powerset,
        ghMidPSlotRot J cr sr coeff B' * (∏ j ∈ J, if j ∈ B' then x₁ j else x₀ j) =
          ghMidPSlotRot J cr sr coeff B' * (if B' = B then 1 else 0) :=
      fun B' hB' ↦ by rw [hdelta B' hB']
    rw [Finset.sum_congr rfl hcongr,
      Finset.sum_eq_single B (fun B' _ hne ↦ by rw [ite_eq_right hne, mul_zero])
        (fun hnot ↦ absurd hB hnot),
      ite_eq_left rfl, mul_one]
  exact hlhs_B.symm.trans (hlhs.symm.trans (hlhs_eq_rhs.trans (hrhs.trans hrhs_B)))
private lemma ghMidP_sum_powerset_disjoint_union {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommMonoid M] {J₂ J₁ : Finset ι} (hdisj : Disjoint J₂ J₁) (f : Finset ι → M) :
    (∑ A ∈ (J₂ ∪ J₁).powerset, f A) =
      ∑ A₂ ∈ J₂.powerset, ∑ A₁ ∈ J₁.powerset, f (A₂ ∪ A₁) := by
  rw [← Finset.sum_product']
  refine (Finset.sum_bij (fun (p : Finset ι × Finset ι) _ ↦ p.1 ∪ p.2)
    (fun p hp ↦ ?_) (fun p₁ hp₁ p₂ hp₂ heq ↦ ?_) (fun A hA ↦ ?_)
    (fun _ _ ↦ rfl)).symm
  · rcases Finset.mem_product.mp hp with ⟨h2, h1⟩
    exact Finset.mem_powerset.mpr
      (Finset.union_subset_union (Finset.mem_powerset.mp h2) (Finset.mem_powerset.mp h1))
  · rcases Finset.mem_product.mp hp₁ with ⟨h2₁, h1₁⟩
    rcases Finset.mem_product.mp hp₂ with ⟨h2₂, h1₂⟩
    have hs2₁ := Finset.mem_powerset.mp h2₁
    have hs1₁ := Finset.mem_powerset.mp h1₁
    have hs2₂ := Finset.mem_powerset.mp h2₂
    have hs1₂ := Finset.mem_powerset.mp h1₂
    have hinter_left {A B : Finset ι} (hA : A ⊆ J₂) (hB : B ⊆ J₁) : (A ∪ B) ∩ J₂ = A := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun ⟨hab, hx2⟩ ↦ hab.elim id fun hxb ↦
          False.elim (Finset.disjoint_left.mp hdisj hx2 (hB hxb)),
        fun hxa ↦ ⟨Or.inl hxa, hA hxa⟩⟩
    have hinter_right {A B : Finset ι} (hA : A ⊆ J₂) (hB : B ⊆ J₁) : (A ∪ B) ∩ J₁ = B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun ⟨hab, hx1⟩ ↦ hab.elim
          (fun hxa ↦ False.elim (Finset.disjoint_left.mp hdisj (hA hxa) hx1)) id,
        fun hxb ↦ ⟨Or.inr hxb, hB hxb⟩⟩
    exact Prod.ext
      (by rw [← hinter_left hs2₁ hs1₁, ← hinter_left hs2₂ hs1₂, heq])
      (by rw [← hinter_right hs2₁ hs1₁, ← hinter_right hs2₂ hs1₂, heq])
  · have hA_sub := Finset.mem_powerset.mp hA
    refine ⟨(A ∩ J₂, A ∩ J₁),
      Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩, ?_⟩
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hA_sub]
lemma ghMidPSlotRot_disjoint_union {ι : Type*} [DecidableEq ι]
    {J₂ J₁ : Finset ι} (hdisj : Disjoint J₂ J₁) (cr sr : ι → ℝ)
    (coeff : Finset ι → ℂ) {B₂ B₁ : Finset ι} (hB₂ : B₂ ⊆ J₂) (hB₁ : B₁ ⊆ J₁) :
    ghMidPSlotRot (J₂ ∪ J₁) cr sr coeff (B₂ ∪ B₁) =
      ghMidPSlotRot J₂ cr sr
        (fun A₂ ↦ ghMidPSlotRot J₁ cr sr (fun A₁ ↦ coeff (A₂ ∪ A₁)) B₁) B₂ := by
  unfold ghMidPSlotRot
  rw [ghMidP_sum_powerset_disjoint_union hdisj]
  refine Finset.sum_congr rfl fun A₂ hA₂ ↦ ?_
  have hA₂_sub := Finset.mem_powerset.mp hA₂
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun A₁ hA₁ ↦ ?_
  have hA₁_sub := Finset.mem_powerset.mp hA₁
  rw [Finset.prod_union hdisj]
  have hp₂ :
      (∏ j ∈ J₂,
        if j ∈ B₂ ∪ B₁ then
          if j ∈ A₂ ∪ A₁ then (cr j : ℂ) else (sr j : ℂ)
        else
          if j ∈ A₂ ∪ A₁ then -(sr j : ℂ) else (cr j : ℂ)) =
      ∏ j ∈ J₂,
        if j ∈ B₂ then
          if j ∈ A₂ then (cr j : ℂ) else (sr j : ℂ)
        else
          if j ∈ A₂ then -(sr j : ℂ) else (cr j : ℂ) := by
    refine Finset.prod_congr rfl fun j hj₂ ↦ ?_
    have hj_not1 : j ∉ J₁ := Finset.disjoint_left.mp hdisj hj₂
    have hjB₁ : j ∉ B₁ := fun hm ↦ hj_not1 (hB₁ hm)
    have hjA₁ : j ∉ A₁ := fun hm ↦ hj_not1 (hA₁_sub hm)
    simp [hjB₁, hjA₁]
  have hp₁ :
      (∏ j ∈ J₁,
        if j ∈ B₂ ∪ B₁ then
          if j ∈ A₂ ∪ A₁ then (cr j : ℂ) else (sr j : ℂ)
        else
          if j ∈ A₂ ∪ A₁ then -(sr j : ℂ) else (cr j : ℂ)) =
      ∏ j ∈ J₁,
        if j ∈ B₁ then
          if j ∈ A₁ then (cr j : ℂ) else (sr j : ℂ)
        else
          if j ∈ A₁ then -(sr j : ℂ) else (cr j : ℂ) := by
    refine Finset.prod_congr rfl fun j hj₁ ↦ ?_
    have hj_not2 : j ∉ J₂ := Finset.disjoint_right.mp hdisj hj₁
    have hjB₂ : j ∉ B₂ := fun hm ↦ hj_not2 (hB₂ hm)
    have hjA₂ : j ∉ A₂ := fun hm ↦ hj_not2 (hA₂_sub hm)
    simp [hjB₂, hjA₂]
  rw [hp₂, hp₁]
  ring
private lemma ghMidP_powerset_sum_card {ι : Type*} (J : Finset ι) (φ : ℕ → ℝ) :
    (∑ A ∈ J.powerset, φ A.card) =
      ∑ w ∈ Finset.range (J.card + 1), (J.card.choose w : ℝ) * φ w := by
  classical
  have hbiU : J.powerset = (Finset.range (J.card + 1)).biUnion J.powersetCard := by
    ext A
    simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Nat.lt_succ_iff]
    exact ⟨fun hA ↦ ⟨A.card, Finset.card_le_card hA, hA, rfl⟩, fun ⟨_, _, hA, _⟩ ↦ hA⟩
  have hdisj : Set.PairwiseDisjoint (Finset.range (J.card + 1) : Set ℕ) J.powersetCard :=
    fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun _ h1 h2 ↦
      hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
  rw [hbiU, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hc : ∀ A ∈ J.powersetCard w, φ A.card = φ w :=
    fun A hA ↦ by rw [(Finset.mem_powersetCard.mp hA).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
/-- Hamming-weight table `wSpec: ℕ → GaussPyth × PythPair` of a `GHMidPProbe` at `R.card =
  r`. -/
def ghMidPWSpec (r : ℕ) (pr : GHMidPProbe) (b : ℕ) : GaussPyth × PythPair :=
  if b = 0 then (gaussOne, pythOne)
  else if b < r then (pr.phases.getD (b - 1) gaussOne, pythOne)
  else if b = r then (pr.phases.getD (r - 1) gaussOne, pr.rotTop)
  else (gaussOne, pythOne)
/-- Subcube Grover angle `arcsin √(occ(j) / 2 ^ subN)` on slot `j`. -/
noncomputable def ghMidPSlotTheta {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) (j : Fin m) : ℝ :=
  Real.arcsin (√((ghMidPOcc pref R j : ℝ) / (2 ^ subN : ℝ)))
/-- Initial slot-subset amplitude on `R.image pref` after `kInit` Grover steps + oracle. -/
noncomputable def ghMidPInitCoeff {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) (kInit : ℕ) (A : Finset (Fin m)) : ℂ :=
  ∏ j ∈ R.image pref,
    if j ∈ A then
      (Real.sin ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN pref R j) : ℂ)
    else
      (Real.cos ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN pref R j) : ℂ)
/-- No-click damped slot-subset amplitude under `pr: GHMidPProbe`. -/
noncomputable def ghMidPDampCoeff {m : ℕ} (r : ℕ) (pr : GHMidPProbe)
    (coeff : Finset (Fin m) → ℂ) (A : Finset (Fin m)) : ℂ :=
  ((ghMidPWSpec r pr A.card).2.cVal : ℂ) * (ghMidPWSpec r pr A.card).1.val * coeff A
/-- Next slot-subset amplitude on `R.image pref` after one `GHMidPProbe` on no-click. -/
noncomputable def ghMidPProbeNextCoeff {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) (pr : GHMidPProbe)
    (coeff : Finset (Fin m) → ℂ) : Finset (Fin m) → ℂ :=
  ghMidPSlotRot (R.image pref)
    (fun j ↦ Real.cos (2 * (pr.kNext : ℝ) * ghMidPSlotTheta subN pref R j))
    (fun j ↦ Real.sin (2 * (pr.kNext : ℝ) * ghMidPSlotTheta subN pref R j))
    (ghMidPDampCoeff R.card pr coeff)
/-- Total all-hit click probability accumulated along `probes` (`1 ≤ R.card`). -/
noncomputable def ghMidPChainClickProb {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) :
    List GHMidPProbe → (Finset (Fin m) → ℂ) → ℝ
  | [], _ => 0
  | pr :: rest, coeff =>
      (if 1 ≤ R.card ∧ (R.image pref).card = R.card then
        (pr.rotTop.sVal : ℝ) ^ 2 * normSq (coeff (R.image pref))
      else 0) +
        ghMidPChainClickProb subN pref R rest (ghMidPProbeNextCoeff subN pref R pr coeff)
/-- Expected extra parallel oracle queries accumulated along `probes`. -/
noncomputable def ghMidPChainExtraQ {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) :
    List GHMidPProbe → (Finset (Fin m) → ℂ) → ℝ
  | [], _ => 0
  | pr :: rest, coeff =>
      (∑ A ∈ (R.image pref).powerset, normSq (ghMidPDampCoeff R.card pr coeff A)) *
          ((pr.kNext + 2 : ℕ) : ℝ) +
        ghMidPChainExtraQ subN pref R rest (ghMidPProbeNextCoeff subN pref R pr coeff)
/-- Final slot-subset amplitude on `R.image pref` at readout when no probe clicks. -/
noncomputable def ghMidPChainFinalCoeff {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) :
    List GHMidPProbe → (Finset (Fin m) → ℂ) → (Finset (Fin m) → ℂ)
  | [], coeff => coeff
  | pr :: rest, coeff =>
      ghMidPChainFinalCoeff subN pref R rest (ghMidPProbeNextCoeff subN pref R pr coeff)
/-- Exact 1-round expectation functional of `wdPrepAndNoClick + probes` before zoom. -/
noncomputable def ghMidPBaseStep {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool)
    (kInit : ℕ) (probes : List GHMidPProbe) (Ψ : Finset α → ℝ) (R : Finset α) : ℝ :=
  let c0 := ghMidPInitCoeff subN pref R kInit
  let cf := ghMidPChainFinalCoeff subN pref R probes c0
  (if withCost then ((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQ subN pref R probes c0 else 0) +
    ghMidPChainClickProb subN pref R probes c0 * Ψ ∅ +
    ∑ A ∈ (R.image pref).powerset,
      normSq (cf A) *
        ∑ c ∈ ghMidPHitChoices pref R A, ghMidPChoiceWeight pref R A * Ψ (R \ ghMidPChoiceSet c)
/-- Post-readout middle-`p` `wt = r - 1` collision-zoom continuation (`R'.card = 1`). -/
noncomputable def ghMidPZoomPost {α : Type*} [DecidableEq α] {m : ℕ}
    (wt subNZoom kZoom : ℕ) (withCost : Bool) (pref : α → Fin m) (R : Finset α)
    (Ψ : Finset α → ℝ) (R' : Finset α) : ℝ :=
  if R'.card = 1 then
    let θZoom := Real.arcsin (1 / √((wt * 2 ^ subNZoom : ℕ) : ℝ))
    let pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2
    (if withCost then ((kZoom + 1 : ℕ) : ℝ) else 0) +
      if ((R \ R').image pref ∩ R'.image pref).Nonempty then
        pZoom * Ψ ∅ + (1 - pZoom) * Ψ R'
      else Ψ R'
  else Ψ R'
/-- Abstract 1-pass expectation step on subset `R` under `spec_fn: ℕ → GHMidPSpec`. -/
noncomputable def ghMidPSubsetStep {α : Type*} [DecidableEq α] {m : ℕ}
    (subN p : ℕ) (pref : α → Fin m) (withCost : Bool) (spec_fn : ℕ → GHMidPSpec)
    (Ψ : Finset α → ℝ) (R : Finset α) : ℝ :=
  match spec_fn R.card with
  | none => Ψ R
  | some (kInit, probes, kZoom) =>
      if 2 ≤ R.card ∧ R.card ≤ 16 ∧ R.card - 1 < m then
        ghMidPBaseStep subN pref withCost kInit probes
          (ghMidPZoomPost (R.card - 1) (subN - p) kZoom withCost pref R Ψ) R
      else Ψ R
/-- Multi-pass circuit dynamic program parameterized by permutations `Equiv.Perm (Fin (2 ^
  n))`. -/
noncomputable def ghMidPCircDP {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (withCost : Bool) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)) →
      (Finset (Fin (2 ^ n)) → ℝ) → Finset (Fin (2 ^ n)) → ℝ
  | [], Ψ, R => Ψ R
  | (perm, spec_fn) :: rest, Ψ, R =>
      ghMidPSubsetStep (n - p) p (fun x ↦ subcubePref hp hm (perm x)) withCost spec_fn
        (ghMidPCircDP hp hm withCost rest Ψ) R
/-- Multi-pass subset dynamic program parameterized by `W` independent coordinate slices. -/
noncomputable def ghMidPSubsetDP {α : Type*} [DecidableEq α] {W m : ℕ}
    (subN p : ℕ) (slices : α → Fin W → Fin m) :
    List (Fin W × (ℕ → GHMidPSpec)) → (Finset α → ℝ) → Finset α → ℝ
  | [], Ψ, R => Ψ R
  | (t, spec_fn) :: rest, Ψ, R =>
      ghMidPSubsetStep subN p (fun x ↦ slices x t) true spec_fn
        (ghMidPSubsetDP subN p slices rest Ψ) R
/-- Exact uniform-average 1-pass Bellman operator over `Fin r → Fin m`. -/
noncomputable def ghMidPExactOneDimStep (subN p m : ℕ)
    (spec_fn : ℕ → GHMidPSpec) (g : ℕ → ℝ) (r : ℕ) : ℝ :=
  (∑ h : Fin r → Fin m,
    ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ g I'.card) Finset.univ) / ((m : ℝ) ^ r)
/-- Multi-pass exact 1D Bellman dynamic program. -/
noncomputable def ghMidPExactOneDimDP (subN p m : ℕ) :
    List (ℕ → GHMidPSpec) → (ℕ → ℝ) → ℕ → ℝ
  | [], V_tail, r => V_tail r
  | spec_fn :: rest, V_tail, r =>
      ghMidPExactOneDimStep subN p m spec_fn (ghMidPExactOneDimDP subN p m rest V_tail) r
lemma ghMidPChainClickProb_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) :
    ∀ (probes : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      0 ≤ ghMidPChainClickProb subN pref R probes coeff
  | [], _ => le_rfl
  | _ :: rest, _ => by
      dsimp only [ghMidPChainClickProb]
      refine add_nonneg ?_ (ghMidPChainClickProb_nonneg subN pref R rest _)
      split_ifs
      · exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
      · exact le_rfl
lemma ghMidPChainExtraQ_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) :
    ∀ (probes : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      0 ≤ ghMidPChainExtraQ subN pref R probes coeff
  | [], _ => le_rfl
  | _ :: rest, _ =>
      add_nonneg
        (mul_nonneg (Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _) (Nat.cast_nonneg _))
        (ghMidPChainExtraQ_nonneg subN pref R rest _)
lemma ghMidPZoomPost_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (wt subNZoom kZoom : ℕ) (withCost : Bool) (pref : α → Fin m)
    {R : Finset α} {Ψ : Finset α → ℝ} (hΨ : ∀ T ⊆ R, 0 ≤ Ψ T)
    {R' : Finset α} (hR' : R' ⊆ R) :
    0 ≤ ghMidPZoomPost wt subNZoom kZoom withCost pref R Ψ R' := by
  unfold ghMidPZoomPost
  split_ifs
  · exact add_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg (sq_nonneg _) (hΨ ∅ (Finset.empty_subset R)))
        (mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one _)) (hΨ R' hR')))
  · exact add_nonneg (Nat.cast_nonneg _) (hΨ R' hR')
  · simpa using add_nonneg (mul_nonneg (sq_nonneg _) (hΨ ∅ (Finset.empty_subset R)))
      (mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one _)) (hΨ R' hR'))
  · simpa using hΨ R' hR'
  · exact hΨ R' hR'
lemma ghMidPZoomPost_false_bounds {α : Type*} [DecidableEq α] {m : ℕ}
    (wt subNZoom kZoom : ℕ) (pref : α → Fin m) (R : Finset α)
    {Ψ : Finset α → ℝ} {R' : Finset α}
    (h0_lo : 0 ≤ Ψ ∅) (h0_hi : Ψ ∅ ≤ 1) (hr_lo : 0 ≤ Ψ R') (hr_hi : Ψ R' ≤ 1) :
    0 ≤ ghMidPZoomPost wt subNZoom kZoom false pref R Ψ R' ∧
      ghMidPZoomPost wt subNZoom kZoom false pref R Ψ R' ≤ 1 := by
  unfold ghMidPZoomPost
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  split_ifs
  · set θZoom := Real.arcsin (1 / √((wt * 2 ^ subNZoom : ℕ) : ℝ))
    set pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2
    have hp0 : 0 ≤ pZoom := sq_nonneg _
    have hp1 : pZoom ≤ 1 := Real.sin_sq_le_one _
    exact ⟨by nlinarith, by nlinarith⟩
  · exact ⟨hr_lo, hr_hi⟩
  · exact ⟨hr_lo, hr_hi⟩
lemma ghMidPBaseStep_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool)
    (kInit : ℕ) (probes : List GHMidPProbe) {Ψ : Finset α → ℝ} {R : Finset α}
    (hΨ : ∀ T ⊆ R, 0 ≤ Ψ T) :
    0 ≤ ghMidPBaseStep subN pref withCost kInit probes Ψ R := by
  unfold ghMidPBaseStep
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · cases withCost
    · simp
    · exact add_nonneg (Nat.cast_nonneg _) (ghMidPChainExtraQ_nonneg subN pref R probes _)
  · exact mul_nonneg (ghMidPChainClickProb_nonneg subN pref R probes _)
      (hΨ ∅ (Finset.empty_subset R))
  · refine Finset.sum_nonneg fun A _ ↦ mul_nonneg (Complex.normSq_nonneg _) ?_
    exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (ghMidPChoiceWeight_nonneg _ _ _)
      (hΨ _ Finset.sdiff_subset)
lemma ghMidPInitCoeff_sum_normSq {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) (kInit : ℕ) :
    (∑ B ∈ (R.image pref).powerset, normSq (ghMidPInitCoeff subN pref R kInit B)) = 1 := by
  let J := R.image pref
  let coeff0 : Finset (Fin m) → ℂ := fun A ↦ if A = ∅ then 1 else 0
  let cr (j : Fin m) : ℝ := Real.cos ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN pref R j)
  let sr (j : Fin m) : ℝ := Real.sin ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN pref R j)
  have hrot_eq (B : Finset (Fin m)) :
      ghMidPInitCoeff subN pref R kInit B = ghMidPSlotRot J cr sr coeff0 B := by
    unfold ghMidPInitCoeff ghMidPSlotRot
    rw [Finset.sum_eq_single ∅
      (fun A _ hne ↦ by simp [coeff0, hne])
      (fun hnot ↦ absurd (Finset.empty_mem_powerset J) hnot)]
    dsimp only [coeff0, J, cr, sr]
    rw [ite_eq_left rfl, one_mul]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    by_cases hjB : j ∈ B <;> simp [hjB]
  simp_rw [hrot_eq]
  rw [ghMidPSlotRot_sum_normSq J cr sr (fun _ _ ↦ Real.cos_sq_add_sin_sq _) coeff0,
    Finset.sum_eq_single ∅
      (fun A _ hne ↦ by simp [coeff0, hne])
      (fun hnot ↦ absurd (Finset.empty_mem_powerset J) hnot)]
  simp [coeff0]
lemma ghMidPChain_norm_eq {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) :
    ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      ghMidPChainClickProb subN pref R ps coeff +
        (∑ A ∈ (R.image pref).powerset,
          normSq (ghMidPChainFinalCoeff subN pref R ps coeff A)) =
      ∑ A ∈ (R.image pref).powerset, normSq (coeff A) := by
  let J := R.image pref
  intro ps
  induction ps with
  | nil =>
    intro coeff
    simp [ghMidPChainClickProb, ghMidPChainFinalCoeff]
  | cons pr rest ih =>
    intro coeff
    dsimp only [ghMidPChainClickProb, ghMidPChainFinalCoeff]
    rw [add_assoc, ih]
    unfold ghMidPProbeNextCoeff
    rw [ghMidPSlotRot_sum_normSq J _ _ (fun _ _ ↦ Real.cos_sq_add_sin_sq _)]
    have hdamp_pt (A : Finset (Fin m)) (hA : A ∈ J.powerset) :
        (if (1 ≤ R.card ∧ J.card = R.card) ∧ A = J then
          (pr.rotTop.sVal : ℝ) ^ 2 * normSq (coeff A) else 0) +
          normSq (ghMidPDampCoeff R.card pr coeff A) = normSq (coeff A) := by
      have hA_sub : A ⊆ J := Finset.mem_powerset.mp hA
      have hJ_le : J.card ≤ R.card := Finset.card_image_le
      have hA_le : A.card ≤ J.card := Finset.card_le_card hA_sub
      unfold ghMidPDampCoeff ghMidPWSpec
      by_cases h0 : A.card = 0
      · have hnot : ¬ ((1 ≤ R.card ∧ J.card = R.card) ∧ A = J) := by
          rintro ⟨⟨h1, hJr⟩, rfl⟩
          omega
        rw [ite_eq_right hnot, zero_add]
        simp [h0, pythOne_cVal, gaussOne_val]
      · by_cases hlt : A.card < R.card
        · have hnot : ¬ ((1 ≤ R.card ∧ J.card = R.card) ∧ A = J) := by
            rintro ⟨⟨_, hJr⟩, rfl⟩
            omega
          rw [ite_eq_right hnot, zero_add]
          simp [h0, hlt, pythOne_cVal, map_mul, GaussPyth.normSq_val]
        · have heq_r : A.card = R.card := by omega
          have hJr : J.card = R.card := by omega
          have h1 : 1 ≤ R.card := by omega
          have hAJ : A = J := Finset.eq_of_subset_of_card_le hA_sub (by omega)
          have hyes : (1 ≤ R.card ∧ J.card = R.card) ∧ A = J := ⟨⟨h1, hJr⟩, hAJ⟩
          rw [ite_eq_left hyes, ite_eq_right h0, ite_eq_right hlt, ite_eq_left heq_r]
          simp only [map_mul, Complex.normSq_ofReal, GaussPyth.normSq_val, mul_one]
          have hpy : (pr.rotTop.cVal : ℝ) ^ 2 + (pr.rotTop.sVal : ℝ) ^ 2 = 1 := by
            exact_mod_cast pr.rotTop.cVal_sq_add_sVal_sq
          calc (pr.rotTop.sVal : ℝ) ^ 2 * normSq (coeff A) +
                (pr.rotTop.cVal * pr.rotTop.cVal) * normSq (coeff A)
              = ((pr.rotTop.cVal : ℝ) ^ 2 + (pr.rotTop.sVal : ℝ) ^ 2) * normSq (coeff A) := by
                ring
            _ = normSq (coeff A) := by rw [hpy, one_mul]
    have hclick_sum :
        (∑ A ∈ J.powerset,
          if (1 ≤ R.card ∧ J.card = R.card) ∧ A = J then
            (pr.rotTop.sVal : ℝ) ^ 2 * normSq (coeff A) else 0) =
        if 1 ≤ R.card ∧ J.card = R.card then
          (pr.rotTop.sVal : ℝ) ^ 2 * normSq (coeff J) else 0 := by
      rw [Finset.sum_eq_single J
        (fun A _ hne ↦ by
          have hn : ¬ ((1 ≤ R.card ∧ J.card = R.card) ∧ A = J) := fun h ↦ hne h.2
          rw [ite_eq_right hn])
        (fun hnot ↦ absurd (Finset.mem_powerset.mpr Finset.Subset.rfl) hnot)]
      by_cases hc : 1 ≤ R.card ∧ J.card = R.card
      · have hcy : (1 ≤ R.card ∧ J.card = R.card) ∧ J = J := ⟨hc, rfl⟩
        rw [ite_eq_left hcy, ite_eq_left hc]
      · have hcn : ¬ ((1 ≤ R.card ∧ J.card = R.card) ∧ J = J) := fun h ↦ hc h.1
        rw [ite_eq_right hcn, ite_eq_right hc]
    change (if 1 ≤ R.card ∧ J.card = R.card then
          (pr.rotTop.sVal : ℝ) ^ 2 * normSq (coeff J) else 0) +
        (∑ A ∈ J.powerset, normSq (ghMidPDampCoeff R.card pr coeff A)) = _
    rw [← hclick_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hdamp_pt
lemma ghMidPBaseStep_false_bounds {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHMidPProbe)
    {Ψ : Finset α → ℝ} {R : Finset α}
    (hlo : ∀ T ⊆ R, 0 ≤ Ψ T) (hhi : ∀ T ⊆ R, Ψ T ≤ 1) :
    0 ≤ ghMidPBaseStep subN pref false kInit probes Ψ R ∧
      ghMidPBaseStep subN pref false kInit probes Ψ R ≤ 1 := by
  refine ⟨ghMidPBaseStep_nonneg subN pref false kInit probes hlo, ?_⟩
  let J := R.image pref
  let c0 := ghMidPInitCoeff subN pref R kInit
  let cf := ghMidPChainFinalCoeff subN pref R probes c0
  have hnorm :
      ghMidPChainClickProb subN pref R probes c0 +
        (∑ A ∈ J.powerset, normSq (cf A)) = 1 :=
    (ghMidPChain_norm_eq subN pref R probes c0).trans (ghMidPInitCoeff_sum_normSq subN pref R kInit)
  unfold ghMidPBaseStep
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  have hcl_le :
      ghMidPChainClickProb subN pref R probes c0 * Ψ ∅ ≤
        ghMidPChainClickProb subN pref R probes c0 :=
    mul_le_of_le_one_right (ghMidPChainClickProb_nonneg subN pref R probes c0)
      (hhi ∅ (Finset.empty_subset R))
  have hsum_le :
      (∑ A ∈ J.powerset,
        normSq (cf A) *
          ∑ c ∈ ghMidPHitChoices pref R A,
            ghMidPChoiceWeight pref R A * Ψ (R \ ghMidPChoiceSet c)) ≤
      ∑ A ∈ J.powerset, normSq (cf A) := by
    refine Finset.sum_le_sum fun A hA ↦ mul_le_of_le_one_right (Complex.normSq_nonneg _) ?_
    calc (∑ c ∈ ghMidPHitChoices pref R A,
            ghMidPChoiceWeight pref R A * Ψ (R \ ghMidPChoiceSet c))
        ≤ ∑ _c ∈ ghMidPHitChoices pref R A, ghMidPChoiceWeight pref R A * 1 :=
          Finset.sum_le_sum fun c _ ↦
            mul_le_mul_of_nonneg_left (hhi _ Finset.sdiff_subset)
              (ghMidPChoiceWeight_nonneg pref R A)
      _ = 1 := by
          simp_rw [mul_one]
          exact ghMidPHitChoices_sum_weight pref R (Finset.mem_powerset.mp hA)
  exact (add_le_add hcl_le hsum_le).trans_eq hnorm
lemma ghMidPChainExtraQ_le_preMax {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (R : Finset α) :
    ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      (∑ A ∈ (R.image pref).powerset, normSq (coeff A)) ≤ 1 →
      ghMidPChainExtraQ subN pref R ps coeff ≤
        (((ps.map fun pr ↦ pr.kNext + 2).sum : ℕ) : ℝ)
  | [], _, _ => by simp [ghMidPChainExtraQ]
  | pr :: rest, coeff, hle1 => by
      let J := R.image pref
      have hdamp_le (A : Finset (Fin m)) (_hA : A ∈ J.powerset) :
          normSq (ghMidPDampCoeff R.card pr coeff A) ≤ normSq (coeff A) := by
        have hd_pt :
            normSq (ghMidPDampCoeff R.card pr coeff A) =
              normSq ((ghMidPWSpec R.card pr A.card).2.cVal : ℂ) * normSq (coeff A) := by
          unfold ghMidPDampCoeff
          rw [map_mul, map_mul, GaussPyth.normSq_val, mul_one]
        have hc_le1 : normSq ((ghMidPWSpec R.card pr A.card).2.cVal : ℂ) ≤ 1 := by
          rw [Complex.normSq_ofReal]
          have hsq :
              ((ghMidPWSpec R.card pr A.card).2.cVal : ℝ) ^ 2 +
                ((ghMidPWSpec R.card pr A.card).2.sVal : ℝ) ^ 2 = 1 := by
            exact_mod_cast (ghMidPWSpec R.card pr A.card).2.cVal_sq_add_sVal_sq
          have hs_nn : 0 ≤ ((ghMidPWSpec R.card pr A.card).2.sVal : ℝ) ^ 2 := sq_nonneg _
          nlinarith
        rw [hd_pt]
        exact mul_le_of_le_one_left (Complex.normSq_nonneg _) hc_le1
      have hsum_damp :
          (∑ A ∈ J.powerset, normSq (ghMidPDampCoeff R.card pr coeff A)) ≤ 1 :=
        (Finset.sum_le_sum hdamp_le).trans hle1
      have hnext_le1 :
          (∑ B ∈ J.powerset, normSq (ghMidPProbeNextCoeff subN pref R pr coeff B)) ≤ 1 := by
        unfold ghMidPProbeNextCoeff
        rw [ghMidPSlotRot_sum_normSq J _ _ (fun _ _ ↦ Real.cos_sq_add_sin_sq _)]
        exact hsum_damp
      dsimp only [ghMidPChainExtraQ]
      rw [List.map_cons, List.sum_cons,
        Nat.cast_add (pr.kNext + 2) ((rest.map fun pr ↦ pr.kNext + 2).sum)]
      refine add_le_add ?_ (ghMidPChainExtraQ_le_preMax subN pref R rest _ hnext_le1)
      exact mul_le_of_le_one_left (Nat.cast_nonneg _) hsum_damp
lemma ghMidPBaseStep_congr_on_subset {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool) (kInit : ℕ) (probes : List GHMidPProbe)
    {Ψ₁ Ψ₂ : Finset α → ℝ} {R : Finset α} (hΨ : ∀ T ⊆ R, Ψ₁ T = Ψ₂ T) :
    ghMidPBaseStep subN pref withCost kInit probes Ψ₁ R =
      ghMidPBaseStep subN pref withCost kInit probes Ψ₂ R := by
  unfold ghMidPBaseStep
  dsimp only
  rw [hΨ ∅ (Finset.empty_subset R)]
  refine congrArg₂ (HAdd.hAdd (α := ℝ) (β := ℝ) (γ := ℝ)) rfl
    (Finset.sum_congr rfl fun A _ ↦
      congrArg₂ (HMul.hMul (α := ℝ) (β := ℝ) (γ := ℝ)) rfl ?_)
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [hΨ _ Finset.sdiff_subset]
lemma ghMidPBaseStep_mono_on {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool) (kInit : ℕ) (probes : List GHMidPProbe)
    {Ψ₁ Ψ₂ : Finset α → ℝ} {R : Finset α} (hΨ : ∀ T ⊆ R, Ψ₁ T ≤ Ψ₂ T) :
    ghMidPBaseStep subN pref withCost kInit probes Ψ₁ R ≤
      ghMidPBaseStep subN pref withCost kInit probes Ψ₂ R := by
  unfold ghMidPBaseStep
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · exact mul_le_mul_of_nonneg_left (hΨ ∅ (Finset.empty_subset R))
      (ghMidPChainClickProb_nonneg subN pref R probes _)
  · refine Finset.sum_le_sum fun A _ ↦ mul_le_mul_of_nonneg_left ?_ (Complex.normSq_nonneg _)
    exact Finset.sum_le_sum fun _ _ ↦
      mul_le_mul_of_nonneg_left (hΨ _ Finset.sdiff_subset) (ghMidPChoiceWeight_nonneg _ _ _)
lemma ghMidPSubsetStep_congr_on_subset {α : Type*} [DecidableEq α] {m : ℕ}
    (subN p : ℕ) (pref : α → Fin m) (withCost : Bool) (spec_fn : ℕ → GHMidPSpec)
    {Ψ₁ Ψ₂ : Finset α → ℝ} {R : Finset α} (hΨ : ∀ T ⊆ R, Ψ₁ T = Ψ₂ T) :
    ghMidPSubsetStep subN p pref withCost spec_fn Ψ₁ R =
      ghMidPSubsetStep subN p pref withCost spec_fn Ψ₂ R := by
  unfold ghMidPSubsetStep
  cases spec_fn R.card with
  | none => exact hΨ R Finset.Subset.rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    split_ifs
    · refine ghMidPBaseStep_congr_on_subset subN pref withCost kInit probes fun R' hR' ↦ ?_
      unfold ghMidPZoomPost
      rw [hΨ ∅ (Finset.empty_subset R), hΨ R' hR']
    · exact hΨ R Finset.Subset.rfl
lemma ghMidPSubsetStep_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (subN p : ℕ) (pref : α → Fin m) (withCost : Bool) (spec_fn : ℕ → GHMidPSpec)
    {Ψ : Finset α → ℝ} {R : Finset α} (hΨ : ∀ T ⊆ R, 0 ≤ Ψ T) :
    0 ≤ ghMidPSubsetStep subN p pref withCost spec_fn Ψ R := by
  unfold ghMidPSubsetStep
  cases spec_fn R.card with
  | none => exact hΨ R Finset.Subset.rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    split_ifs
    · exact ghMidPBaseStep_nonneg subN pref withCost kInit probes fun R' hR' ↦
        ghMidPZoomPost_nonneg _ _ _ withCost pref hΨ hR'
    · exact hΨ R Finset.Subset.rfl
lemma ghMidPCircDP_nonneg {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (withCost : Bool) :
    ∀ (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
      {Ψ : Finset (Fin (2 ^ n)) → ℝ} {R : Finset (Fin (2 ^ n))},
      (∀ T ⊆ R, 0 ≤ Ψ T) → 0 ≤ ghMidPCircDP hp hm withCost passes Ψ R
  | [], _, R, hΨ => hΨ R Finset.Subset.rfl
  | _ :: rest, _, _, hΨ =>
      ghMidPSubsetStep_nonneg (n - p) p _ withCost _ fun _ hR' ↦
        ghMidPCircDP_nonneg hp hm withCost rest fun T hT ↦ hΨ T (hT.trans hR')
lemma ghMidPCircDP_false_bounds {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) :
    ∀ (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
      {Ψ : Finset (Fin (2 ^ n)) → ℝ} {R : Finset (Fin (2 ^ n))},
      (∀ T ⊆ R, 0 ≤ Ψ T) → (∀ T ⊆ R, Ψ T ≤ 1) →
      0 ≤ ghMidPCircDP hp hm false passes Ψ R ∧ ghMidPCircDP hp hm false passes Ψ R ≤ 1
  | [], _, R, hlo, hhi => ⟨hlo R Finset.Subset.rfl, hhi R Finset.Subset.rfl⟩
  | (perm, spec_fn) :: rest, Ψ, R, hlo, hhi => by
      have hrest : ∀ T ⊆ R,
          0 ≤ ghMidPCircDP hp hm false rest Ψ T ∧ ghMidPCircDP hp hm false rest Ψ T ≤ 1 :=
        fun T hT ↦ ghMidPCircDP_false_bounds hp hm rest
          (fun U hU ↦ hlo U (hU.trans hT)) (fun U hU ↦ hhi U (hU.trans hT))
      dsimp only [ghMidPCircDP]
      unfold ghMidPSubsetStep
      cases spec_fn R.card with
      | none => exact hrest R Finset.Subset.rfl
      | some kpz =>
        rcases kpz with ⟨kInit, probes, kZoom⟩
        dsimp only
        split_ifs
        · refine ghMidPBaseStep_false_bounds (n - p) (fun x ↦ subcubePref hp hm (perm x))
            kInit probes (fun T hT ↦ ?_) (fun T hT ↦ ?_)
          · exact (ghMidPZoomPost_false_bounds _ _ _ _ R
              (hrest ∅ (Finset.empty_subset R)).1 (hrest ∅ (Finset.empty_subset R)).2
              (hrest T hT).1 (hrest T hT).2).1
          · exact (ghMidPZoomPost_false_bounds _ _ _ _ R
              (hrest ∅ (Finset.empty_subset R)).1 (hrest ∅ (Finset.empty_subset R)).2
              (hrest T hT).1 (hrest T hT).2).2
        · exact hrest R Finset.Subset.rfl
lemma ghMidPSubsetDP_congr_on_subset {α : Type*} [DecidableEq α] {W m : ℕ}
    (subN p : ℕ) (slices : α → Fin W → Fin m)
    (passes : List (Fin W × (ℕ → GHMidPSpec)))
    {Ψ₁ Ψ₂ : Finset α → ℝ} {R : Finset α} (hΨ : ∀ R' ⊆ R, Ψ₁ R' = Ψ₂ R') :
    ghMidPSubsetDP subN p slices passes Ψ₁ R = ghMidPSubsetDP subN p slices passes Ψ₂ R := by
  induction passes generalizing R with
  | nil => exact hΨ R Finset.Subset.rfl
  | cons _ rest ih =>
    exact ghMidPSubsetStep_congr_on_subset _ _ _ _ _ fun R' hR' ↦
      ih fun R'' hR'' ↦ hΨ R'' (hR''.trans hR')
lemma ghMidPCircDP_map_swap_eq {n p m W : ℕ}
    (hs : (n - W * p) + W * p = n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List GHMidPPassFn) (hW_eq : passes.length = W)
    (l : List (Fin W)) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghMidPCircDP hp hm true
        (l.map fun i ↦
          (rotatedSliceSwapPerm hs hm (Nat.zero_lt_of_lt i.isLt) i,
            (passes[i.val]'(by rw [hW_eq]; exact i.isLt)) (n - p))) Ψ R =
      ghMidPSubsetDP (n - p) p (slicesOf (rotatedSliceEquiv hs hm))
        (l.map fun i ↦ (i, (passes[i.val]'(by rw [hW_eq]; exact i.isLt)) (n - p))) Ψ R := by
  induction l generalizing R with
  | nil => rfl
  | cons i rest ih =>
    dsimp only [List.map, ghMidPCircDP, ghMidPSubsetDP]
    have hpref :
        (fun x ↦ subcubePref hp hm
          (rotatedSliceSwapPerm hs hm (Nat.zero_lt_of_lt i.isLt) i x)) =
        (fun x ↦ slicesOf (rotatedSliceEquiv hs hm) x i) :=
      funext fun x ↦ subcubePref_rotatedSliceSwapPerm hs hp hm (Nat.zero_lt_of_lt i.isLt) i x
    rw [hpref, funext ih]
private lemma ghMidP_unitNorm_and_qColl_of_card_lt {r m : ℕ} (subN : ℕ) (h : Fin r → Fin m)
    (kInit : ℕ) (probes : List GHMidPProbe)
    (hJ_lt : ((Finset.univ : Finset (Fin r)).image h).card < r) :
    let U_r : Finset (Fin r) := Finset.univ
    let c0 := ghMidPInitCoeff subN h U_r kInit
    ((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQ subN h U_r probes c0 =
        (ghMidPPreMaxQueries kInit probes : ℝ) ∧
      ghMidPChainClickProb subN h U_r probes c0 = 0 ∧
      (∑ A ∈ (U_r.image h).powerset,
        normSq (ghMidPChainFinalCoeff subN h U_r probes c0 A)) = 1 := by
  intro U_r c0
  let J := U_r.image h
  have hU_card : U_r.card = r := by simp [U_r]
  have hnot_all : ¬ (1 ≤ U_r.card ∧ J.card = U_r.card) := by
    rw [hU_card]
    intro h1
    exact hJ_lt.ne h1.2
  have hdamp_norm (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) (A : Finset (Fin m))
      (hA : A ∈ J.powerset) :
      normSq (ghMidPDampCoeff U_r.card pr coeff A) = normSq (coeff A) := by
    have hA_lt : A.card < r := (Finset.card_le_card (Finset.mem_powerset.mp hA)).trans_lt hJ_lt
    rw [hU_card]
    unfold ghMidPDampCoeff ghMidPWSpec
    by_cases h0 : A.card = 0
    · simp [h0, pythOne_cVal, gaussOne_val]
    · simp [h0, hA_lt, pythOne_cVal, map_mul, GaussPyth.normSq_val]
  have hstep_norm (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) :
      (∑ B ∈ J.powerset, normSq (ghMidPProbeNextCoeff subN h U_r pr coeff B)) =
        ∑ A ∈ J.powerset, normSq (coeff A) := by
    unfold ghMidPProbeNextCoeff
    rw [ghMidPSlotRot_sum_normSq J _ _ (fun _ _ ↦ Real.cos_sq_add_sin_sq _)]
    exact Finset.sum_congr rfl (hdamp_norm pr coeff)
  have hc0_norm : (∑ B ∈ J.powerset, normSq (c0 B)) = 1 :=
    ghMidPInitCoeff_sum_normSq subN h U_r kInit
  have hchain : ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      (∑ A ∈ J.powerset, normSq (coeff A)) = 1 →
        ghMidPChainExtraQ subN h U_r ps coeff =
            (((ps.map fun pr ↦ pr.kNext + 2).sum : ℕ) : ℝ) ∧
          ghMidPChainClickProb subN h U_r ps coeff = 0 ∧
          (∑ A ∈ J.powerset, normSq (ghMidPChainFinalCoeff subN h U_r ps coeff A)) = 1 := by
    intro ps
    induction ps with
    | nil =>
      intro coeff hnorm
      exact ⟨by simp [ghMidPChainExtraQ], by simp [ghMidPChainClickProb], hnorm⟩
    | cons pr rest ih =>
      intro coeff hnorm
      rcases ih (ghMidPProbeNextCoeff subN h U_r pr coeff)
        ((hstep_norm pr coeff).trans hnorm) with ⟨hex_r, hcl_r, hnf_r⟩
      refine ⟨?_, ?_, hnf_r⟩
      · dsimp only [ghMidPChainExtraQ]
        rw [Finset.sum_congr rfl (hdamp_norm pr coeff), hnorm, one_mul, hex_r]
        simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_ofNat]
      · dsimp only [ghMidPChainClickProb]
        rw [ite_eq_right hnot_all, zero_add, hcl_r]
  rcases hchain probes c0 hc0_norm with ⟨hex, hcl, hnf⟩
  refine ⟨?_, hcl, hnf⟩
  unfold ghMidPPreMaxQueries
  rw [hex]
  simp only [Nat.cast_add]
private lemma ghMidP_image_card_le_sub_two_of_rem {r m : ℕ} {h : Fin r → Fin m}
    (hnot_inj : ¬ Function.Injective h) (hnot_sp : ¬ ghMidPIsSingleMult 2 h) :
    ((Finset.univ : Finset (Fin r)).image h).card ≤ r - 2 := by
  let U_r : Finset (Fin r) := Finset.univ
  let J := U_r.image h
  have hJ_le : J.card ≤ r := Finset.card_image_le.trans_eq (by simp [U_r])
  have hocc_zero (j : Fin m) (hj : j ∉ J) : ghMidPOcc h U_r j = 0 := by
    rw [ghMidPOcc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha heq
    exact hj (Finset.mem_image.mpr ⟨a, ha, heq⟩)
  have hocc_pos (j : Fin m) (hj : j ∈ J) : 1 ≤ ghMidPOcc h U_r j := by
    rcases Finset.mem_image.mp hj with ⟨a, ha, rfl⟩
    exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  have hsum_J : (∑ j ∈ J, ghMidPOcc h U_r j) = r :=
    (Finset.sum_subset (Finset.subset_univ J) fun j _ hj ↦ hocc_zero j hj).trans
      (ghMidPSumOccEq h)
  have hsum_exc : (∑ j ∈ J, (ghMidPOcc h U_r j - 1)) + J.card = r := by
    have h1 : J.card = ∑ _ ∈ J, (1 : ℕ) := by simp
    rw [h1, ← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl fun j hj ↦ Nat.sub_add_cancel (hocc_pos j hj)).trans hsum_J
  have hne_r : J.card ≠ r := by
    intro hJr
    have hexc0 : (∑ j ∈ J, (ghMidPOcc h U_r j - 1)) = 0 := by omega
    have hle1_J : ∀ j ∈ J, ghMidPOcc h U_r j ≤ 1 := fun j hj ↦ by
      have hz := Finset.sum_eq_zero_iff.mp hexc0 j hj
      omega
    apply hnot_inj
    intro a₁ a₂ heq
    have hj : h a₁ ∈ J := Finset.mem_image_of_mem h (Finset.mem_univ a₁)
    exact Finset.card_le_one.mp (hle1_J (h a₁) hj)
      a₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ a₁, rfl⟩)
      a₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ a₂, heq.symm⟩)
  have hne_r1 : ¬ (1 ≤ r ∧ J.card = r - 1) := by
    rintro ⟨hr1, hJr1⟩
    have hexc1 : (∑ j ∈ J, (ghMidPOcc h U_r j - 1)) = 1 := by omega
    have hex_j₂ : ∃ j₂ ∈ J, ghMidPOcc h U_r j₂ - 1 ≠ 0 := by
      by_contra hall
      have hz : (∑ j ∈ J, (ghMidPOcc h U_r j - 1)) = 0 :=
        Finset.sum_eq_zero fun j hj ↦ by
          by_contra hnz
          exact hall ⟨j, hj, hnz⟩
      omega
    rcases hex_j₂ with ⟨j₂, hj₂J, hj₂_nz⟩
    have hsplit_j₂ := (Finset.add_sum_erase J (fun j ↦ ghMidPOcc h U_r j - 1) hj₂J).symm
    rw [hexc1] at hsplit_j₂
    have hj₂_pos := hocc_pos j₂ hj₂J
    have hj₂_2 : ghMidPOcc h U_r j₂ = 2 := by omega
    have herase0 : (∑ j ∈ J.erase j₂, (ghMidPOcc h U_r j - 1)) = 0 := by omega
    apply hnot_sp
    refine ⟨j₂, hj₂_2, fun j hj_ne ↦ ?_⟩
    change ghMidPOcc h U_r j ≤ 1
    by_cases hjJ : j ∈ J
    · have hz : ghMidPOcc h U_r j - 1 = 0 :=
        Finset.sum_eq_zero_iff.mp herase0 j (Finset.mem_erase.mpr ⟨hj_ne, hjJ⟩)
      omega
    · rw [hocc_zero j hjJ]
      exact Nat.zero_le 1
  change J.card ≤ r - 2
  omega
private lemma ghMidP_inj_step_eq {r m : ℕ} (subN p kInit : ℕ) (probes : List GHMidPProbe)
    (kZoom : ℕ) (hr2 : 2 ≤ r) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    {h : Fin r → Fin m} (hInj : Function.Injective h) :
    let U_r : Finset (Fin r) := Finset.univ
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    let u₀ := ghMidPInitAmp r θ₁ kInit
    let uf := ghMidPChainFinalAmp r θ₁ probes u₀
    let qDist := ((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQueries r θ₁ probes u₀
    let remDist := ∑ w ∈ Finset.range r,
      (r.choose w : ℝ) * normSq (uf w) *
        (if w + 1 = r then ((kZoom + 1 : ℕ) : ℝ) + f 1 else f (r - w))
    ghMidPBaseStep subN h true kInit probes
        (ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)) U_r =
      qDist + remDist := by
  intro U_r θ₁ u₀ uf qDist remDist
  let J := U_r.image h
  have hU_card : U_r.card = r := by simp [U_r]
  have hJ_card : J.card = r := (Finset.card_image_of_injective U_r hInj).trans hU_card
  have hr0 : r ≠ 0 := by omega
  have hθ_eq (j : Fin m) (hj : j ∈ J) : ghMidPSlotTheta subN h U_r j = θ₁ := by
    rcases Finset.mem_image.mp hj with ⟨a₀, ha₀, rfl⟩
    have hge1 : 1 ≤ ghMidPOcc h U_r (h a₀) :=
      Finset.card_pos.mpr ⟨a₀, Finset.mem_filter.mpr ⟨ha₀, rfl⟩⟩
    have hle1 : ghMidPOcc h U_r (h a₀) ≤ 1 :=
      Finset.card_le_one.mpr fun _ h1 _ h2 ↦
        hInj ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
    have hocc1 : ghMidPOcc h U_r (h a₀) = 1 := le_antisymm hle1 hge1
    unfold ghMidPSlotTheta
    rw [hocc1, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hc0_eq (B : Finset (Fin m)) (hB : B ∈ J.powerset) :
      ghMidPInitCoeff subN h U_r kInit B = u₀ B.card := by
    let coeff0 : Finset (Fin m) → ℂ := fun A ↦ if A = ∅ then 1 else 0
    let u_zero : ℕ → ℂ := fun b ↦ if b = 0 then 1 else 0
    let cr (j : Fin m) : ℝ := Real.cos ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN h U_r j)
    let sr (j : Fin m) : ℝ := Real.sin ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN h U_r j)
    have hrot : ghMidPInitCoeff subN h U_r kInit B = ghMidPSlotRot J cr sr coeff0 B := by
      unfold ghMidPInitCoeff ghMidPSlotRot
      rw [Finset.sum_eq_single ∅
        (fun A _ hne ↦ by simp [coeff0, hne])
        (fun hnot ↦ absurd (Finset.empty_mem_powerset J) hnot)]
      dsimp only [coeff0, J, cr, sr]
      rw [ite_eq_left rfl, one_mul]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      by_cases hjB : j ∈ B <;> simp [hjB]
    rw [hrot, ghMidPSlotRot_const_eq_dickeStep J
      (fun j hj ↦ by dsimp only [cr]; rw [hθ_eq j hj])
      (fun j hj ↦ by dsimp only [sr]; rw [hθ_eq j hj])
      u_zero (fun A _ ↦ by simp [coeff0, u_zero]) hB, hJ_card]
    rfl
  have hdamp_eq (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) (u : ℕ → ℂ)
      (hu : ∀ A ∈ J.powerset, coeff A = u A.card) (A : Finset (Fin m)) (hA : A ∈ J.powerset) :
      ghMidPDampCoeff U_r.card pr coeff A = ghMidPDampAmp r pr u A.card := by
    have hA_le : A.card ≤ r := (Finset.card_le_card (Finset.mem_powerset.mp hA)).trans_eq hJ_card
    unfold ghMidPDampCoeff
    rw [hU_card, hu A hA]
    by_cases h0 : A.card = 0
    · simp [ghMidPWSpec, ghMidPDampAmp, h0, pythOne_cVal, gaussOne_val]
    · by_cases hlt : A.card < r
      · simp [ghMidPWSpec, ghMidPDampAmp, h0, hlt, pythOne_cVal]
      · have heq : A.card = r := by omega
        simp [ghMidPWSpec, ghMidPDampAmp, heq, hr0]
  have hnext_eq (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) (u : ℕ → ℂ)
      (hu : ∀ A ∈ J.powerset, coeff A = u A.card) (B : Finset (Fin m)) (hB : B ∈ J.powerset) :
      ghMidPProbeNextCoeff subN h U_r pr coeff B = ghMidPProbeNextAmp r θ₁ pr u B.card := by
    unfold ghMidPProbeNextCoeff ghMidPProbeNextAmp
    rw [ghMidPSlotRot_const_eq_dickeStep J
      (fun j hj ↦ by rw [hθ_eq j hj])
      (fun j hj ↦ by rw [hθ_eq j hj])
      (ghMidPDampAmp r pr u) (hdamp_eq pr coeff u hu) hB, hJ_card]
  have hchain : ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ) (u : ℕ → ℂ),
      (∀ A ∈ J.powerset, coeff A = u A.card) →
        (∀ A ∈ J.powerset,
          ghMidPChainFinalCoeff subN h U_r ps coeff A = ghMidPChainFinalAmp r θ₁ ps u A.card) ∧
          ghMidPChainExtraQ subN h U_r ps coeff = ghMidPChainExtraQueries r θ₁ ps u := by
    intro ps
    induction ps with
    | nil =>
      intro coeff u hu
      exact ⟨hu, rfl⟩
    | cons pr rest ih =>
      intro coeff u hu
      rcases ih (ghMidPProbeNextCoeff subN h U_r pr coeff) (ghMidPProbeNextAmp r θ₁ pr u)
        (hnext_eq pr coeff u hu) with ⟨hf_r, hex_r⟩
      refine ⟨hf_r, ?_⟩
      dsimp only [ghMidPChainExtraQ, ghMidPChainExtraQueries]
      have hsum_d :
          (∑ A ∈ J.powerset, normSq (ghMidPDampCoeff U_r.card pr coeff A)) =
            ∑ w ∈ Finset.range (r + 1),
              (r.choose w : ℝ) * normSq (ghMidPDampAmp r pr u w) := by
        have hc : ∀ A ∈ J.powerset,
            normSq (ghMidPDampCoeff U_r.card pr coeff A) =
              normSq (ghMidPDampAmp r pr u A.card) :=
          fun A hA ↦ by rw [hdamp_eq pr coeff u hu A hA]
        rw [Finset.sum_congr rfl hc,
          ghMidP_powerset_sum_card J (fun w ↦ normSq (ghMidPDampAmp r pr u w)), hJ_card]
      rw [hsum_d, hex_r]
  rcases hchain probes (ghMidPInitCoeff subN h U_r kInit) u₀ hc0_eq with ⟨hcf_eq, hex_eq⟩
  unfold ghMidPBaseStep
  simp only [↓reduceIte]
  have hpost0 : ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card) ∅ = 0 := by
    unfold ghMidPZoomPost
    simp [hf0]
  rw [hpost0, mul_zero, add_zero, hex_eq]
  congr 1
  have hread_A (A : Finset (Fin m)) (hA : A ∈ J.powerset) :
      normSq (ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) A) *
          (∑ c ∈ ghMidPHitChoices h U_r A,
            ghMidPChoiceWeight h U_r A *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c)) =
        normSq (uf A.card) *
          (if A.card + 1 = r then ((kZoom + 1 : ℕ) : ℝ) + f 1 else f (r - A.card)) := by
    have hA_sub : A ⊆ J := Finset.mem_powerset.mp hA
    have hA_le : A.card ≤ r := (Finset.card_le_card hA_sub).trans_eq hJ_card
    rw [hcf_eq A hA]
    have hc_val (c : Fin m → Option (Fin r)) (hc : c ∈ ghMidPHitChoices h U_r A) :
        ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
            (U_r \ ghMidPChoiceSet c) =
          if A.card + 1 = r then ((kZoom + 1 : ℕ) : ℝ) + f 1 else f (r - A.card) := by
      have hcard_I' : (U_r \ ghMidPChoiceSet c).card = r - A.card := by
        rw [(ghMidPChoiceSet_props hc).2.2.2, hU_card]
      unfold ghMidPZoomPost
      by_cases hw1 : A.card + 1 = r
      · have hI'1 : (U_r \ ghMidPChoiceSet c).card = 1 := by omega
        have hnot_ne :
            ¬ (((U_r \ (U_r \ ghMidPChoiceSet c)).image h) ∩
              ((U_r \ ghMidPChoiceSet c).image h)).Nonempty := by
          rintro ⟨j, hj⟩
          rcases Finset.mem_inter.mp hj with ⟨hj1, hj2⟩
          rcases Finset.mem_image.mp hj1 with ⟨x₁, hx₁, rfl⟩
          rcases Finset.mem_image.mp hj2 with ⟨x₂, hx₂, hx₂_eq⟩
          exact (Finset.mem_sdiff.mp hx₁).2 (hInj hx₂_eq ▸ hx₂)
        rw [ite_eq_left hI'1]
        simp only [↓reduceIte]
        rw [ite_eq_right hnot_ne, ite_eq_left hw1, hI'1]
      · have hI'ne : (U_r \ ghMidPChoiceSet c).card ≠ 1 := by omega
        rw [ite_eq_right hI'ne]
        dsimp only
        rw [ite_eq_right hw1, hcard_I']
    have hc_congr :
        (∑ c ∈ ghMidPHitChoices h U_r A,
          ghMidPChoiceWeight h U_r A *
            ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c)) =
        ∑ _c ∈ ghMidPHitChoices h U_r A,
          ghMidPChoiceWeight h U_r A *
            (if A.card + 1 = r then ((kZoom + 1 : ℕ) : ℝ) + f 1 else f (r - A.card)) :=
      Finset.sum_congr rfl fun c hc ↦ by rw [hc_val c hc]
    rw [hc_congr, ← Finset.sum_mul, ghMidPHitChoices_sum_weight h U_r hA_sub, one_mul]
  rw [Finset.sum_congr rfl hread_A,
    ghMidP_powerset_sum_card J
      (fun w ↦ normSq (uf w) *
        (if w + 1 = r then ((kZoom + 1 : ℕ) : ℝ) + f 1 else f (r - w))),
    hJ_card, Finset.sum_range_succ]
  have htop_zero :
      (r.choose r : ℝ) *
        (normSq (uf r) * (if r + 1 = r then ((kZoom + 1 : ℕ) : ℝ) + f 1 else f (r - r))) = 0 := by
    have hne : ¬ (r + 1 = r) := by omega
    rw [ite_eq_right hne, Nat.sub_self, hf0, mul_zero, mul_zero]
  rw [htop_zero, add_zero]
  exact Finset.sum_congr rfl fun _ _ ↦ (mul_assoc _ _ _).symm
/-
 ## 4. Linearity, Multi-Collision Fiber Steps (`SinglePair`, `SingleTriple`, `TwoPair`,
 `Rem`),
   `r = 2` Bridge, & Rotated-Slice Fubini
-/

lemma ghMidPBaseStep_true_eq_cost_add_false {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHMidPProbe)
    (Ψ : Finset α → ℝ) (R : Finset α) :
    ghMidPBaseStep subN pref true kInit probes Ψ R =
      ghMidPBaseStep subN pref true kInit probes (fun _ ↦ 0) R +
        ghMidPBaseStep subN pref false kInit probes Ψ R := by
  unfold ghMidPBaseStep
  simp only [↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add]
  ring
lemma ghMidPBaseStep_false_mul {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHMidPProbe)
    (a : ℝ) (Ψ : Finset α → ℝ) (R : Finset α) :
    ghMidPBaseStep subN pref false kInit probes (fun T ↦ a * Ψ T) R =
      a * ghMidPBaseStep subN pref false kInit probes Ψ R := by
  unfold ghMidPBaseStep
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add, mul_add]
  congr 1
  · ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    have hinner :
        (∑ c ∈ ghMidPHitChoices pref R A,
          ghMidPChoiceWeight pref R A * (a * Ψ (R \ ghMidPChoiceSet c))) =
        a * ∑ c ∈ ghMidPHitChoices pref R A,
          ghMidPChoiceWeight pref R A * Ψ (R \ ghMidPChoiceSet c) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hinner]
    ring
lemma ghMidPBaseStep_false_add {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHMidPProbe)
    (Ψ₁ Ψ₂ : Finset α → ℝ) (R : Finset α) :
    ghMidPBaseStep subN pref false kInit probes (fun T ↦ Ψ₁ T + Ψ₂ T) R =
      ghMidPBaseStep subN pref false kInit probes Ψ₁ R +
        ghMidPBaseStep subN pref false kInit probes Ψ₂ R := by
  unfold ghMidPBaseStep
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  have hsum :
      (∑ A ∈ (R.image pref).powerset,
        normSq (ghMidPChainFinalCoeff subN pref R probes (ghMidPInitCoeff subN pref R kInit) A) *
          ∑ c ∈ ghMidPHitChoices pref R A,
            ghMidPChoiceWeight pref R A * (Ψ₁ (R \ ghMidPChoiceSet c) +
              Ψ₂ (R \ ghMidPChoiceSet c))) =
      (∑ A ∈ (R.image pref).powerset,
        normSq (ghMidPChainFinalCoeff subN pref R probes (ghMidPInitCoeff subN pref R kInit) A) *
          ∑ c ∈ ghMidPHitChoices pref R A,
            ghMidPChoiceWeight pref R A * Ψ₁ (R \ ghMidPChoiceSet c)) +
      (∑ A ∈ (R.image pref).powerset,
        normSq (ghMidPChainFinalCoeff subN pref R probes (ghMidPInitCoeff subN pref R kInit) A) *
          ∑ c ∈ ghMidPHitChoices pref R A,
            ghMidPChoiceWeight pref R A * Ψ₂ (R \ ghMidPChoiceSet c)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hsum]
  ring
lemma ghMidPZoomPost_true_eq_cost_add_false {α : Type*} [DecidableEq α] {m : ℕ}
    (wt subNZoom kZoom : ℕ) (pref : α → Fin m) (R : Finset α)
    (Ψ : Finset α → ℝ) (R' : Finset α) :
    ghMidPZoomPost wt subNZoom kZoom true pref R Ψ R' =
      ghMidPZoomPost wt subNZoom kZoom true pref R (fun _ ↦ 0) R' +
        ghMidPZoomPost wt subNZoom kZoom false pref R Ψ R' := by
  unfold ghMidPZoomPost
  simp only [↓reduceIte, Bool.false_eq_true, mul_zero, add_zero, zero_add]
  split_ifs <;> ring
lemma ghMidPZoomPost_false_mul {α : Type*} [DecidableEq α] {m : ℕ}
    (wt subNZoom kZoom : ℕ) (pref : α → Fin m) (R : Finset α)
    (a : ℝ) (Ψ : Finset α → ℝ) (R' : Finset α) :
    ghMidPZoomPost wt subNZoom kZoom false pref R (fun T ↦ a * Ψ T) R' =
      a * ghMidPZoomPost wt subNZoom kZoom false pref R Ψ R' := by
  unfold ghMidPZoomPost
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  split_ifs <;> ring
lemma ghMidPZoomPost_false_add {α : Type*} [DecidableEq α] {m : ℕ}
    (wt subNZoom kZoom : ℕ) (pref : α → Fin m) (R : Finset α)
    (Ψ₁ Ψ₂ : Finset α → ℝ) (R' : Finset α) :
    ghMidPZoomPost wt subNZoom kZoom false pref R (fun T ↦ Ψ₁ T + Ψ₂ T) R' =
      ghMidPZoomPost wt subNZoom kZoom false pref R Ψ₁ R' +
        ghMidPZoomPost wt subNZoom kZoom false pref R Ψ₂ R' := by
  unfold ghMidPZoomPost
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  split_ifs <;> ring
lemma ghMidPSubsetStep_true_eq_cost_add_false {α : Type*} [DecidableEq α] {m : ℕ}
    (subN p : ℕ) (pref : α → Fin m) (spec_fn : ℕ → GHMidPSpec)
    (Ψ : Finset α → ℝ) (R : Finset α) :
    ghMidPSubsetStep subN p pref true spec_fn Ψ R =
      ghMidPSubsetStep subN p pref true spec_fn (fun _ ↦ 0) R +
        ghMidPSubsetStep subN p pref false spec_fn Ψ R := by
  unfold ghMidPSubsetStep
  cases spec_fn R.card with
  | none => simp
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    split_ifs
    · have hpost :
          ghMidPZoomPost (R.card - 1) (subN - p) kZoom true pref R Ψ =
            fun R' ↦
              ghMidPZoomPost (R.card - 1) (subN - p) kZoom true pref R (fun _ ↦ 0) R' +
                ghMidPZoomPost (R.card - 1) (subN - p) kZoom false pref R Ψ R' :=
        funext (ghMidPZoomPost_true_eq_cost_add_false _ _ kZoom pref R Ψ)
      rw [hpost, ghMidPBaseStep_true_eq_cost_add_false, ghMidPBaseStep_false_add,
        ← add_assoc, ← ghMidPBaseStep_true_eq_cost_add_false]
    · simp
lemma ghMidPSubsetStep_false_mul {α : Type*} [DecidableEq α] {m : ℕ}
    (subN p : ℕ) (pref : α → Fin m) (spec_fn : ℕ → GHMidPSpec)
    (a : ℝ) (Ψ : Finset α → ℝ) (R : Finset α) :
    ghMidPSubsetStep subN p pref false spec_fn (fun T ↦ a * Ψ T) R =
      a * ghMidPSubsetStep subN p pref false spec_fn Ψ R := by
  unfold ghMidPSubsetStep
  cases spec_fn R.card with
  | none => rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    split_ifs
    · rw [funext (ghMidPZoomPost_false_mul _ _ kZoom pref R a Ψ), ghMidPBaseStep_false_mul]
    · rfl
lemma ghMidPSubsetStep_false_add {α : Type*} [DecidableEq α] {m : ℕ}
    (subN p : ℕ) (pref : α → Fin m) (spec_fn : ℕ → GHMidPSpec)
    (Ψ₁ Ψ₂ : Finset α → ℝ) (R : Finset α) :
    ghMidPSubsetStep subN p pref false spec_fn (fun T ↦ Ψ₁ T + Ψ₂ T) R =
      ghMidPSubsetStep subN p pref false spec_fn Ψ₁ R +
        ghMidPSubsetStep subN p pref false spec_fn Ψ₂ R := by
  unfold ghMidPSubsetStep
  cases spec_fn R.card with
  | none => rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    split_ifs
    · rw [funext (ghMidPZoomPost_false_add _ _ kZoom pref R Ψ₁ Ψ₂), ghMidPBaseStep_false_add]
    · rfl
lemma ghMidPCircDP_false_mul {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
    (a : ℝ) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghMidPCircDP hp hm false passes (fun R' ↦ a * Ψ R') R =
      a * ghMidPCircDP hp hm false passes Ψ R := by
  induction passes generalizing R with
  | nil => rfl
  | cons _ rest ih =>
    dsimp only [ghMidPCircDP]
    rw [funext ih, ghMidPSubsetStep_false_mul]
lemma ghMidPCircDP_false_sum {ι : Type*} {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
    (s : Finset ι) (F : ι → Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghMidPCircDP hp hm false passes (fun R' ↦ ∑ i ∈ s, F i R') R =
      ∑ i ∈ s, ghMidPCircDP hp hm false passes (F i) R := by
  classical
  induction s using Finset.induction generalizing R with
  | empty =>
    have hzero : ∀ (l : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
        (T : Finset (Fin (2 ^ n))), ghMidPCircDP hp hm false l (fun _ ↦ (0 : ℝ)) T = 0 := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons ps rest _ =>
        intro T
        simpa using ghMidPCircDP_false_mul hp hm (ps :: rest) 0 (fun _ ↦ 0) T
    simpa using hzero passes R
  | @insert x s hx ihs =>
    have hadd : ∀ (l : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
        (A B : Finset (Fin (2 ^ n)) → ℝ) (T : Finset (Fin (2 ^ n))),
        ghMidPCircDP hp hm false l (fun R' ↦ A R' + B R') T =
          ghMidPCircDP hp hm false l A T + ghMidPCircDP hp hm false l B T := by
      intro l
      induction l with
      | nil => intro _ _ _; rfl
      | cons _ rest ihl =>
        intro A B T
        dsimp only [ghMidPCircDP]
        rw [funext (ihl A B), ghMidPSubsetStep_false_add]
    simp_rw [Finset.sum_insert hx]
    rw [hadd, ihs]
lemma ghMidPCircDP_true_eq_cost_add_false {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
    (Ψ : Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghMidPCircDP hp hm true passes Ψ R =
      ghMidPCircDP hp hm true passes (fun _ ↦ 0) R +
        ghMidPCircDP hp hm false passes Ψ R := by
  induction passes generalizing R with
  | nil => simp [ghMidPCircDP]
  | cons _ rest ih =>
    dsimp only [ghMidPCircDP]
    rw [funext ih, ghMidPSubsetStep_true_eq_cost_add_false, ghMidPSubsetStep_false_add,
      ← add_assoc, ← ghMidPSubsetStep_true_eq_cost_add_false]
private lemma ghMidP_singleMult_chain_eq {c r m : ℕ} (subN kInit : ℕ)
    (probes : List GHMidPProbe) (hc2 : 2 ≤ c) (hcr : c ≤ r)
    {h : Fin r → Fin m} (hsm : ghMidPIsSingleMult c h) :
    let U_r : Finset (Fin r) := Finset.univ
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    let θC := Real.arcsin (√(c : ℝ) / √(2 ^ subN : ℝ))
    let zf := ghMidPChainFinal2Row (r - c) θ₁ θC probes (ghMidPInit2Row (r - c) θ₁ θC kInit)
    ∃ (jc : Fin m) (J₁ : Finset (Fin m)),
      ghMidPOcc h U_r jc = c ∧
        J₁ = Finset.univ.filter (fun j ↦ ghMidPOcc h U_r j = 1) ∧
        jc ∉ J₁ ∧
        U_r.image h = insert jc J₁ ∧
        J₁.card = r - c ∧
        ((kInit + 1 : ℕ) : ℝ) +
            ghMidPChainExtraQ subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) =
          (ghMidPPreMaxQueries kInit probes : ℝ) ∧
        ghMidPChainClickProb subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) = 0 ∧
        ∀ B ∈ J₁.powerset,
          ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) B =
              zf.1 B.card ∧
            ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit)
                (insert jc B) =
              zf.2 B.card := by
  intro U_r θ₁ θC zf
  rcases hsm with ⟨jc, hjc, hle1⟩
  change ghMidPOcc h U_r jc = c at hjc
  change ∀ j, j ≠ jc → ghMidPOcc h U_r j ≤ 1 at hle1
  let J := U_r.image h
  let J₁ : Finset (Fin m) := Finset.univ.filter fun j ↦ ghMidPOcc h U_r j = 1
  have hU_card : U_r.card = r := by simp [U_r]
  have hjc_not_J₁ : jc ∉ J₁ := fun hm ↦ by
    have hc1 : ghMidPOcc h U_r jc = 1 := (Finset.mem_filter.mp hm).2
    omega
  have hmem_J_iff (j : Fin m) : j ∈ J ↔ 0 < ghMidPOcc h U_r j := by
    simp only [J, ghMidPOcc, Finset.card_pos, Finset.Nonempty, Finset.mem_image, Finset.mem_filter]
  have hJ_eq : J = insert jc J₁ := by
    ext j
    rw [hmem_J_iff, Finset.mem_insert, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hj : j = jc
    · subst hj
      omega
    · have hle := hle1 j hj
      omega
  have hocc_zero (j : Fin m) (hj : j ∉ J) : ghMidPOcc h U_r j = 0 := by
    have hnot : ¬ 0 < ghMidPOcc h U_r j := fun hp ↦ hj ((hmem_J_iff j).mpr hp)
    omega
  have hJ₁_card : J₁.card = r - c := by
    have hsum_J : (∑ j ∈ J, ghMidPOcc h U_r j) = r :=
      (Finset.sum_subset (Finset.subset_univ J) fun j _ hj ↦ hocc_zero j hj).trans
        (ghMidPSumOccEq h)
    rw [hJ_eq, Finset.sum_insert hjc_not_J₁, hjc] at hsum_J
    have hsum1 : (∑ j ∈ J₁, ghMidPOcc h U_r j) = J₁.card := by
      have hc : ∀ j ∈ J₁, ghMidPOcc h U_r j = 1 := fun j hj ↦ (Finset.mem_filter.mp hj).2
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  have hJ_lt : J.card < r := by
    rw [hJ_eq, Finset.card_insert_of_notMem hjc_not_J₁, hJ₁_card]
    omega
  rcases ghMidP_unitNorm_and_qColl_of_card_lt subN h kInit probes hJ_lt with ⟨hq_eq, hcl_eq, _⟩
  have hθ_J₁ (j : Fin m) (hj : j ∈ J₁) : ghMidPSlotTheta subN h U_r j = θ₁ := by
    unfold ghMidPSlotTheta
    rw [(Finset.mem_filter.mp hj).2, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hθ_jc : ghMidPSlotTheta subN h U_r jc = θC := by
    unfold ghMidPSlotTheta
    rw [hjc, Real.sqrt_div (Nat.cast_nonneg c)]
  let z₀ := ghMidPInit2Row (r - c) θ₁ θC kInit
  have hc0_pair (B : Finset (Fin m)) (hB : B ∈ J₁.powerset) :
      ghMidPInitCoeff subN h U_r kInit B = z₀.1 B.card ∧
        ghMidPInitCoeff subN h U_r kInit (insert jc B) = z₀.2 B.card := by
    have hB_sub : B ⊆ J₁ := Finset.mem_powerset.mp hB
    have hjcB : jc ∉ B := fun hm ↦ hjc_not_J₁ (hB_sub hm)
    let coeff0 : Finset (Fin m) → ℂ := fun A ↦ if A = ∅ then 1 else 0
    let u_zero : ℕ → ℂ := fun b ↦ if b = 0 then 1 else 0
    let cr (j : Fin m) : ℝ := Real.cos ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN h U_r j)
    let sr (j : Fin m) : ℝ := Real.sin ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN h U_r j)
    have hsing :
        (∏ j ∈ J₁, if j ∈ B then (sr j : ℂ) else (cr j : ℂ)) =
          ghMidPInitAmp (r - c) θ₁ kInit B.card := by
      have hrot :
          (∏ j ∈ J₁, if j ∈ B then (sr j : ℂ) else (cr j : ℂ)) =
            ghMidPSlotRot J₁ cr sr coeff0 B := by
        unfold ghMidPSlotRot
        rw [Finset.sum_eq_single ∅
          (fun A _ hne ↦ by simp [coeff0, hne])
          (fun hnot ↦ absurd (Finset.empty_mem_powerset J₁) hnot)]
        dsimp only [coeff0]
        rw [ite_eq_left rfl, one_mul]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        by_cases hjB : j ∈ B <;> simp [hjB]
      rw [hrot, ghMidPSlotRot_const_eq_dickeStep J₁
        (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₁ j hj])
        (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₁ j hj])
        u_zero (fun A _ ↦ by simp [coeff0, u_zero]) hB, hJ₁_card]
      rfl
    have hprod_ins :
        (∏ j ∈ J₁, if j ∈ insert jc B then (sr j : ℂ) else (cr j : ℂ)) =
          ∏ j ∈ J₁, if j ∈ B then (sr j : ℂ) else (cr j : ℂ) := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hne : j ≠ jc := fun heq ↦ hjc_not_J₁ (heq ▸ hj)
      simp [hne]
    unfold ghMidPInitCoeff
    change (∏ j ∈ J, _) = _ ∧ (∏ j ∈ J, _) = _
    rw [hJ_eq, Finset.prod_insert hjc_not_J₁, Finset.prod_insert hjc_not_J₁,
      ite_eq_right hjcB, ite_eq_left (Finset.mem_insert_self jc B)]
    change (cr jc : ℂ) * _ = _ ∧ (sr jc : ℂ) * _ = _
    rw [hprod_ins, hsing]
    dsimp only [cr, sr, z₀, ghMidPInit2Row]
    rw [hθ_jc]
    exact ⟨rfl, rfl⟩
  have hdamp_pair (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) (z : (ℕ → ℂ) × (ℕ → ℂ))
      (hz : ∀ B ∈ J₁.powerset, coeff B = z.1 B.card ∧ coeff (insert jc B) = z.2 B.card)
      (B : Finset (Fin m)) (hB : B ∈ J₁.powerset) :
      ghMidPDampCoeff U_r.card pr coeff B = ghMidPDamp2Row0 (r - c) pr z.1 B.card ∧
        ghMidPDampCoeff U_r.card pr coeff (insert jc B) =
          ghMidPDamp2Row1 (r - c) pr z.2 B.card := by
    have hB_sub : B ⊆ J₁ := Finset.mem_powerset.mp hB
    have hjcB : jc ∉ B := fun hm ↦ hjc_not_J₁ (hB_sub hm)
    have hB_le : B.card ≤ r - c := (Finset.card_le_card hB_sub).trans_eq hJ₁_card
    have hB_lt : B.card < r := by omega
    have hins_card : (insert jc B).card = B.card + 1 := Finset.card_insert_of_notMem hjcB
    have hins_lt : B.card + 1 < r := by omega
    unfold ghMidPDampCoeff
    rw [hU_card]
    constructor
    · rw [(hz B hB).1]
      by_cases h0 : B.card = 0
      · simp [ghMidPWSpec, ghMidPDamp2Row0, h0, pythOne_cVal, gaussOne_val]
      · simp [ghMidPWSpec, ghMidPDamp2Row0, h0, hB_le, hB_lt, pythOne_cVal]
    · rw [(hz B hB).2]
      unfold ghMidPWSpec ghMidPDamp2Row1
      rw [hins_card]
      simp [hins_lt, hB_le, pythOne_cVal]
  have hnext_pair (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) (z : (ℕ → ℂ) × (ℕ → ℂ))
      (hz : ∀ B ∈ J₁.powerset, coeff B = z.1 B.card ∧ coeff (insert jc B) = z.2 B.card)
      (B : Finset (Fin m)) (hB : B ∈ J₁.powerset) :
      ghMidPProbeNextCoeff subN h U_r pr coeff B =
          (ghMidPProbeNext2Row (r - c) θ₁ θC pr z).1 B.card ∧
        ghMidPProbeNextCoeff subN h U_r pr coeff (insert jc B) =
          (ghMidPProbeNext2Row (r - c) θ₁ θC pr z).2 B.card := by
    have hB_sub : B ⊆ J₁ := Finset.mem_powerset.mp hB
    let cr (j : Fin m) : ℝ := Real.cos (2 * (pr.kNext : ℝ) * ghMidPSlotTheta subN h U_r j)
    let sr (j : Fin m) : ℝ := Real.sin (2 * (pr.kNext : ℝ) * ghMidPSlotTheta subN h U_r j)
    let dC := ghMidPDampCoeff U_r.card pr coeff
    have hd0 : ghMidPSlotRot J₁ cr sr dC B =
        dickeStep (r - c) (Real.cos (2 * (pr.kNext : ℝ) * θ₁) : ℂ)
          (Real.sin (2 * (pr.kNext : ℝ) * θ₁) : ℂ) (ghMidPDamp2Row0 (r - c) pr z.1) B.card := by
      rw [ghMidPSlotRot_const_eq_dickeStep J₁
        (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₁ j hj])
        (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₁ j hj])
        (ghMidPDamp2Row0 (r - c) pr z.1) (fun A hA ↦ (hdamp_pair pr coeff z hz A hA).1) hB,
        hJ₁_card]
    have hd1 : ghMidPSlotRot J₁ cr sr (fun A ↦ dC (insert jc A)) B =
        dickeStep (r - c) (Real.cos (2 * (pr.kNext : ℝ) * θ₁) : ℂ)
          (Real.sin (2 * (pr.kNext : ℝ) * θ₁) : ℂ) (ghMidPDamp2Row1 (r - c) pr z.2) B.card := by
      rw [ghMidPSlotRot_const_eq_dickeStep J₁
        (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₁ j hj])
        (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₁ j hj])
        (ghMidPDamp2Row1 (r - c) pr z.2) (fun A hA ↦ (hdamp_pair pr coeff z hz A hA).2) hB,
        hJ₁_card]
    unfold ghMidPProbeNextCoeff
    change ghMidPSlotRot J cr sr dC B = _ ∧ ghMidPSlotRot J cr sr dC (insert jc B) = _
    rw [hJ_eq, (ghMidPSlotRot_insert_notMem hjc_not_J₁ cr sr dC hB_sub).1,
      (ghMidPSlotRot_insert_notMem hjc_not_J₁ cr sr dC hB_sub).2,
      ghMidPSlotRot_sub, ghMidPSlotRot_linear, hd0, hd1]
    dsimp only [cr, sr, ghMidPProbeNext2Row]
    rw [hθ_jc]
    exact ⟨rfl, rfl⟩
  have hchain_pair : ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ)
      (z : (ℕ → ℂ) × (ℕ → ℂ)),
      (∀ B ∈ J₁.powerset, coeff B = z.1 B.card ∧ coeff (insert jc B) = z.2 B.card) →
        ∀ B ∈ J₁.powerset,
          ghMidPChainFinalCoeff subN h U_r ps coeff B =
              (ghMidPChainFinal2Row (r - c) θ₁ θC ps z).1 B.card ∧
            ghMidPChainFinalCoeff subN h U_r ps coeff (insert jc B) =
              (ghMidPChainFinal2Row (r - c) θ₁ θC ps z).2 B.card := by
    intro ps
    induction ps with
    | nil =>
      intro _ _ hz
      exact hz
    | cons pr rest ih =>
      intro coeff z hz
      exact ih (ghMidPProbeNextCoeff subN h U_r pr coeff)
        (ghMidPProbeNext2Row (r - c) θ₁ θC pr z) (hnext_pair pr coeff z hz)
  exact ⟨jc, J₁, hjc, rfl, hjc_not_J₁, hJ_eq, hJ₁_card, hq_eq, hcl_eq,
    hchain_pair probes (ghMidPInitCoeff subN h U_r kInit) z₀ hc0_pair⟩
private lemma ghMidP_singlePair_step_eq {r m : ℕ} (subN p kInit : ℕ) (probes : List GHMidPProbe)
    (kZoom : ℕ) (hr2 : 2 ≤ r) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    {h : Fin r → Fin m} (hsp : ghMidPIsSingleMult 2 h) :
    let U_r : Finset (Fin r) := Finset.univ
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    let θZoom := Real.arcsin (1 / √(((r - 1) * 2 ^ (subN - p) : ℕ) : ℝ))
    let pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2
    let qZoom := ((kZoom + 1 : ℕ) : ℝ)
    let qColl := (ghMidPPreMaxQueries kInit probes : ℝ)
    let sp₀ := ghMidPInit2Row (r - 2) θ₁ θ₂ kInit
    let spf := ghMidPChainFinal2Row (r - 2) θ₁ θ₂ probes sp₀
    let remSp0 := ∑ w₁ ∈ Finset.range (r - 1),
      ((r - 2).choose w₁ : ℝ) * normSq (spf.1 w₁) * f (r - w₁)
    let remSp1 := ∑ w₁ ∈ Finset.range (r - 1),
      ((r - 2).choose w₁ : ℝ) * normSq (spf.2 w₁) *
        (if w₁ + 2 = r then qZoom + (1 - pZoom) * f 1 else f (r - 1 - w₁))
    ghMidPBaseStep subN h true kInit probes
        (ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)) U_r =
      qColl + remSp0 + remSp1 := by
  intro U_r θ₁ θ₂ θZoom pZoom qZoom qColl sp₀ spf remSp0 remSp1
  rcases ghMidP_singleMult_chain_eq subN kInit probes le_rfl hr2 hsp with
    ⟨j₂, J₁, _, hJ₁_def, hj₂_not_J₁, hJ_eq, hJ₁_card, hq_eq, hcl_eq, hcf_pair'⟩
  have hc2_cast : ((2 : ℕ) : ℝ) = 2 := Nat.cast_ofNat
  have hcf_pair : ∀ B ∈ J₁.powerset,
      ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) B =
          spf.1 B.card ∧
        ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit)
            (insert j₂ B) =
          spf.2 B.card := by
    simpa only [hc2_cast] using hcf_pair'
  have hU_card : U_r.card = r := by simp [U_r]
  let J := U_r.image h
  change J = insert j₂ J₁ at hJ_eq
  unfold ghMidPBaseStep
  simp only [↓reduceIte]
  rw [hq_eq, hcl_eq, zero_mul, add_zero]
  change qColl + ∑ A ∈ J.powerset, _ = qColl + remSp0 + remSp1
  rw [hJ_eq, ghMidP_sum_powerset_insert hj₂_not_J₁, ← add_assoc]
  have hr2_succ : r - 2 + 1 = r - 1 := by omega
  congr 1
  · congr 1
    have hread0 (B : Finset (Fin m)) (hB : B ∈ J₁.powerset) :
        normSq (ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) B) *
          (∑ c ∈ ghMidPHitChoices h U_r B,
            ghMidPChoiceWeight h U_r B *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c)) =
          normSq (spf.1 B.card) * f (r - B.card) := by
      have hB_sub : B ⊆ J₁ := Finset.mem_powerset.mp hB
      have hB_J : B ⊆ J := hB_sub.trans (hJ_eq ▸ Finset.subset_insert j₂ J₁)
      have hB_le : B.card ≤ r - 2 := (Finset.card_le_card hB_sub).trans_eq hJ₁_card
      rw [(hcf_pair B hB).1]
      have hc0_val (c : Fin m → Option (Fin r)) (hc : c ∈ ghMidPHitChoices h U_r B) :
          ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c) =
            f (r - B.card) := by
        have hcard_I' : (U_r \ ghMidPChoiceSet c).card = r - B.card := by
          rw [(ghMidPChoiceSet_props hc).2.2.2, hU_card]
        have hne1 : (U_r \ ghMidPChoiceSet c).card ≠ 1 := by omega
        unfold ghMidPZoomPost
        rw [ite_eq_right hne1]
        dsimp only
        rw [hcard_I']
      have hc_congr :
          (∑ c ∈ ghMidPHitChoices h U_r B,
            ghMidPChoiceWeight h U_r B *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c)) =
          ∑ _c ∈ ghMidPHitChoices h U_r B, ghMidPChoiceWeight h U_r B * f (r - B.card) :=
        Finset.sum_congr rfl fun c hc ↦ by rw [hc0_val c hc]
      rw [hc_congr, ← Finset.sum_mul, ghMidPHitChoices_sum_weight h U_r hB_J, one_mul]
    rw [Finset.sum_congr rfl hread0,
      ghMidP_powerset_sum_card J₁ (fun w₁ ↦ normSq (spf.1 w₁) * f (r - w₁)),
      hJ₁_card, hr2_succ]
    exact Finset.sum_congr rfl fun _ _ ↦ (mul_assoc _ _ _).symm
  · have hread1 (B : Finset (Fin m)) (hB : B ∈ J₁.powerset) :
        normSq (ghMidPChainFinalCoeff subN h U_r probes
            (ghMidPInitCoeff subN h U_r kInit) (insert j₂ B)) *
          (∑ c ∈ ghMidPHitChoices h U_r (insert j₂ B),
            ghMidPChoiceWeight h U_r (insert j₂ B) *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c)) =
          normSq (spf.2 B.card) *
            (if B.card + 2 = r then qZoom + (1 - pZoom) * f 1 else f (r - 1 - B.card)) := by
      have hB_sub : B ⊆ J₁ := Finset.mem_powerset.mp hB
      have hj₂B : j₂ ∉ B := fun hm ↦ hj₂_not_J₁ (hB_sub hm)
      have hins_J : insert j₂ B ⊆ J := hJ_eq ▸ Finset.insert_subset_insert j₂ hB_sub
      have hB_le : B.card ≤ r - 2 := (Finset.card_le_card hB_sub).trans_eq hJ₁_card
      have hins_card : (insert j₂ B).card = B.card + 1 := Finset.card_insert_of_notMem hj₂B
      rw [(hcf_pair B hB).2]
      have hc1_val (c : Fin m → Option (Fin r)) (hc : c ∈ ghMidPHitChoices h U_r (insert j₂ B)) :
          ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c) =
            if B.card + 2 = r then qZoom + (1 - pZoom) * f 1 else f (r - 1 - B.card) := by
        rcases ghMidPChoiceSet_props hc with ⟨_, hc_img, _, hc_sdiff⟩
        set I' := U_r \ ghMidPChoiceSet c
        have hcard_I' : I'.card = r - 1 - B.card := by
          rw [hc_sdiff, hU_card, hins_card]
          omega
        unfold ghMidPZoomPost
        by_cases hw : B.card + 2 = r
        · have hI'1 : I'.card = 1 := by omega
          have hB_eq : B = J₁ := Finset.eq_of_subset_of_card_le hB_sub (by omega)
          have hsdiff_eq : U_r \ I' = ghMidPChoiceSet c := by
            ext x
            simp only [I', U_r, Finset.mem_sdiff, Finset.mem_univ, true_and]
            tauto
          obtain ⟨x', hx'_eq⟩ := Finset.card_eq_one.mp hI'1
          have hx'_mem : x' ∈ I' := hx'_eq ▸ Finset.mem_singleton_self x'
          have hx'_j₂ : h x' = j₂ := by
            by_contra hne_j₂
            have hx'_J : h x' ∈ J := Finset.mem_image_of_mem h (Finset.mem_univ x')
            rw [hJ_eq] at hx'_J
            have hx'_J₁ : h x' ∈ J₁ := Finset.mem_of_mem_insert_of_ne hx'_J hne_j₂
            have hocc1 : ghMidPOcc h U_r (h x') = 1 := by
              rw [hJ₁_def] at hx'_J₁
              exact (Finset.mem_filter.mp hx'_J₁).2
            have hx'_img : h x' ∈ (ghMidPChoiceSet c).image h := by
              rw [hc_img, hB_eq]
              exact Finset.mem_insert_of_mem hx'_J₁
            rcases Finset.mem_image.mp hx'_img with ⟨x₀, hx₀c, hx₀_eq⟩
            have hxx : x₀ = x' := Finset.card_le_one.mp (le_of_eq hocc1)
              x₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ x₀, hx₀_eq⟩)
              x' (Finset.mem_filter.mpr ⟨Finset.mem_univ x', rfl⟩)
            exact (Finset.mem_sdiff.mp hx'_mem).2 (hxx ▸ hx₀c)
          have hne_inter : (((U_r \ I').image h) ∩ (I'.image h)).Nonempty :=
            ⟨j₂, Finset.mem_inter.mpr
              ⟨by rw [hsdiff_eq, hc_img]; exact Finset.mem_insert_self j₂ B,
                Finset.mem_image.mpr ⟨x', hx'_mem, hx'_j₂⟩⟩⟩
          rw [ite_eq_left hI'1]
          simp only [↓reduceIte]
          rw [ite_eq_left hne_inter, ite_eq_left hw, Finset.card_empty, hI'1, hf0,
            mul_zero, zero_add]
        · have hI'ne : I'.card ≠ 1 := by omega
          rw [ite_eq_right hI'ne]
          dsimp only
          rw [ite_eq_right hw, hcard_I']
      have hc_congr :
          (∑ c ∈ ghMidPHitChoices h U_r (insert j₂ B),
            ghMidPChoiceWeight h U_r (insert j₂ B) *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c)) =
          ∑ _c ∈ ghMidPHitChoices h U_r (insert j₂ B),
            ghMidPChoiceWeight h U_r (insert j₂ B) *
              (if B.card + 2 = r then qZoom + (1 - pZoom) * f 1 else f (r - 1 - B.card)) :=
        Finset.sum_congr rfl fun c hc ↦ by rw [hc1_val c hc]
      rw [hc_congr, ← Finset.sum_mul, ghMidPHitChoices_sum_weight h U_r hins_J, one_mul]
    rw [Finset.sum_congr rfl hread1,
      ghMidP_powerset_sum_card J₁
        (fun w₁ ↦ normSq (spf.2 w₁) *
          (if w₁ + 2 = r then qZoom + (1 - pZoom) * f 1 else f (r - 1 - w₁))),
      hJ₁_card, hr2_succ]
    exact Finset.sum_congr rfl fun _ _ ↦ (mul_assoc _ _ _).symm
private lemma ghMidP_singleTriple_step_eq {r m : ℕ} (subN p kInit : ℕ) (probes : List GHMidPProbe)
    (kZoom : ℕ) (hr3 : 3 ≤ r) (f : ℕ → ℝ)
    {h : Fin r → Fin m} (hst : ghMidPIsSingleMult 3 h) :
    let U_r : Finset (Fin r) := Finset.univ
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    let θ₃ := Real.arcsin (√3 / √(2 ^ subN : ℝ))
    let qColl := (ghMidPPreMaxQueries kInit probes : ℝ)
    let st₀ := ghMidPInit2Row (r - 3) θ₁ θ₃ kInit
    let stf := ghMidPChainFinal2Row (r - 3) θ₁ θ₃ probes st₀
    let remSt := ∑ w₁ ∈ Finset.range (r - 2),
      (((r - 3).choose w₁ : ℝ) * normSq (stf.1 w₁) * f (r - w₁) +
        ((r - 3).choose w₁ : ℝ) * normSq (stf.2 w₁) * f (r - (w₁ + 1)))
    ghMidPBaseStep subN h true kInit probes
        (ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)) U_r =
      qColl + remSt := by
  intro U_r θ₁ θ₃ qColl st₀ stf remSt
  rcases ghMidP_singleMult_chain_eq subN kInit probes (by omega : 2 ≤ 3) hr3 hst with
    ⟨j₃, J₁, _, _, hj₃_not_J₁, hJ_eq, hJ₁_card, hq_eq, hcl_eq, hcf_st'⟩
  have hc3_cast : ((3 : ℕ) : ℝ) = 3 := Nat.cast_ofNat
  have hcf_st : ∀ B ∈ J₁.powerset,
      ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) B =
          stf.1 B.card ∧
        ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit)
            (insert j₃ B) =
          stf.2 B.card := by
    simpa only [hc3_cast] using hcf_st'
  have hU_card : U_r.card = r := by simp [U_r]
  let J := U_r.image h
  change J = insert j₃ J₁ at hJ_eq
  unfold ghMidPBaseStep
  simp only [↓reduceIte]
  rw [hq_eq, hcl_eq, zero_mul, add_zero]
  congr 1
  change (∑ A ∈ J.powerset, _) = remSt
  rw [hJ_eq, ghMidP_sum_powerset_insert hj₃_not_J₁]
  have hr3_succ : r - 3 + 1 = r - 2 := by omega
  have hread0 (B : Finset (Fin m)) (hB : B ∈ J₁.powerset) :
      normSq (ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) B) *
        (∑ c ∈ ghMidPHitChoices h U_r B,
          ghMidPChoiceWeight h U_r B *
            ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c)) =
        normSq (stf.1 B.card) * f (r - B.card) := by
    have hB_sub : B ⊆ J₁ := Finset.mem_powerset.mp hB
    have hB_J : B ⊆ J := hB_sub.trans (hJ_eq ▸ Finset.subset_insert j₃ J₁)
    have hB_le : B.card ≤ r - 3 := (Finset.card_le_card hB_sub).trans_eq hJ₁_card
    rw [(hcf_st B hB).1]
    have hc_val (c : Fin m → Option (Fin r)) (hc : c ∈ ghMidPHitChoices h U_r B) :
        ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
            (U_r \ ghMidPChoiceSet c) =
          f (r - B.card) := by
      have hcard_I' : (U_r \ ghMidPChoiceSet c).card = r - B.card := by
        rw [(ghMidPChoiceSet_props hc).2.2.2, hU_card]
      have hne1 : (U_r \ ghMidPChoiceSet c).card ≠ 1 := by omega
      unfold ghMidPZoomPost
      rw [ite_eq_right hne1]
      dsimp only
      rw [hcard_I']
    have hc_congr :
        (∑ c ∈ ghMidPHitChoices h U_r B,
          ghMidPChoiceWeight h U_r B *
            ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c)) =
        ∑ _c ∈ ghMidPHitChoices h U_r B, ghMidPChoiceWeight h U_r B * f (r - B.card) :=
      Finset.sum_congr rfl fun c hc ↦ by rw [hc_val c hc]
    rw [hc_congr, ← Finset.sum_mul, ghMidPHitChoices_sum_weight h U_r hB_J, one_mul]
  have hread1 (B : Finset (Fin m)) (hB : B ∈ J₁.powerset) :
      normSq (ghMidPChainFinalCoeff subN h U_r probes
          (ghMidPInitCoeff subN h U_r kInit) (insert j₃ B)) *
        (∑ c ∈ ghMidPHitChoices h U_r (insert j₃ B),
          ghMidPChoiceWeight h U_r (insert j₃ B) *
            ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c)) =
        normSq (stf.2 B.card) * f (r - (B.card + 1)) := by
    have hB_sub : B ⊆ J₁ := Finset.mem_powerset.mp hB
    have hj₃B : j₃ ∉ B := fun hm ↦ hj₃_not_J₁ (hB_sub hm)
    have hins_J : insert j₃ B ⊆ J := hJ_eq ▸ Finset.insert_subset_insert j₃ hB_sub
    have hB_le : B.card ≤ r - 3 := (Finset.card_le_card hB_sub).trans_eq hJ₁_card
    have hins_card : (insert j₃ B).card = B.card + 1 := Finset.card_insert_of_notMem hj₃B
    rw [(hcf_st B hB).2]
    have hc_val (c : Fin m → Option (Fin r)) (hc : c ∈ ghMidPHitChoices h U_r (insert j₃ B)) :
        ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
            (U_r \ ghMidPChoiceSet c) =
          f (r - (B.card + 1)) := by
      have hcard_I' : (U_r \ ghMidPChoiceSet c).card = r - (B.card + 1) := by
        rw [(ghMidPChoiceSet_props hc).2.2.2, hU_card, hins_card]
      have hne1 : (U_r \ ghMidPChoiceSet c).card ≠ 1 := by omega
      unfold ghMidPZoomPost
      rw [ite_eq_right hne1]
      dsimp only
      rw [hcard_I']
    have hc_congr :
        (∑ c ∈ ghMidPHitChoices h U_r (insert j₃ B),
          ghMidPChoiceWeight h U_r (insert j₃ B) *
            ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c)) =
        ∑ _c ∈ ghMidPHitChoices h U_r (insert j₃ B),
          ghMidPChoiceWeight h U_r (insert j₃ B) * f (r - (B.card + 1)) :=
      Finset.sum_congr rfl fun c hc ↦ by rw [hc_val c hc]
    rw [hc_congr, ← Finset.sum_mul, ghMidPHitChoices_sum_weight h U_r hins_J, one_mul]
  rw [Finset.sum_congr rfl hread0, Finset.sum_congr rfl hread1,
    ghMidP_powerset_sum_card J₁ (fun w₁ ↦ normSq (stf.1 w₁) * f (r - w₁)),
    ghMidP_powerset_sum_card J₁ (fun w₁ ↦ normSq (stf.2 w₁) * f (r - (w₁ + 1))),
    hJ₁_card, hr3_succ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring
private lemma ghMidP_twoPair_step_eq {r m : ℕ} (subN p kInit : ℕ) (probes : List GHMidPProbe)
    (kZoom : ℕ) (hr4 : 4 ≤ r) (f : ℕ → ℝ)
    {h : Fin r → Fin m} (htp : ghMidPIsTwoPair h) :
    let U_r : Finset (Fin r) := Finset.univ
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    let qColl := (ghMidPPreMaxQueries kInit probes : ℝ)
    let tp₀ := ghMidPInitTwoPair (r - 4) θ₁ θ₂ kInit
    let tpf := ghMidPChainFinalTwoPair (r - 4) θ₁ θ₂ probes tp₀
    let remTp := ∑ w₁ ∈ Finset.range (r - 3),
      (((r - 4).choose w₁ : ℝ) * normSq (tpf.1 w₁) * f (r - w₁) +
        (2 * (r - 4).choose w₁ : ℝ) * normSq (tpf.2.1 w₁) * f (r - (w₁ + 1)) +
        ((r - 4).choose w₁ : ℝ) * normSq (tpf.2.2 w₁) * f (r - (w₁ + 2)))
    ghMidPBaseStep subN h true kInit probes
        (ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)) U_r =
      qColl + remTp := by
  intro U_r θ₁ θ₂ qColl tp₀ tpf remTp
  rcases htp with ⟨J₂, hJ₂_card, hJ₂_occ, hJ₂_not⟩
  let J := U_r.image h
  let J₁ : Finset (Fin m) := Finset.univ.filter fun j ↦ ghMidPOcc h U_r j = 1
  have hU_card : U_r.card = r := by simp [U_r]
  have hdisj : Disjoint J₂ J₁ := Finset.disjoint_left.mpr fun j hj₂ hj₁ ↦ by
    have h2 : ghMidPOcc h U_r j = 2 := hJ₂_occ j hj₂
    have h1 : ghMidPOcc h U_r j = 1 := (Finset.mem_filter.mp hj₁).2
    omega
  have hmem_J_iff (j : Fin m) : j ∈ J ↔ 0 < ghMidPOcc h U_r j := by
    simp only [J, ghMidPOcc, Finset.card_pos, Finset.Nonempty, Finset.mem_image, Finset.mem_filter]
  have hJ_eq : J = J₂ ∪ J₁ := by
    ext j
    rw [hmem_J_iff, Finset.mem_union, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hj₂ : j ∈ J₂
    · have h2 : ghMidPOcc h U_r j = 2 := hJ₂_occ j hj₂
      exact ⟨fun _ ↦ Or.inl hj₂, fun _ ↦ by omega⟩
    · have hle : ghMidPOcc h U_r j ≤ 1 := hJ₂_not j hj₂
      exact ⟨fun hp ↦ Or.inr (by omega), fun hor ↦ by
        rcases hor with hm | h1
        · exact absurd hm hj₂
        · omega⟩
  have hocc_zero (j : Fin m) (hj : j ∉ J) : ghMidPOcc h U_r j = 0 := by
    have hnot : ¬ 0 < ghMidPOcc h U_r j := fun hp ↦ hj ((hmem_J_iff j).mpr hp)
    omega
  have hJ₁_card : J₁.card = r - 4 := by
    have hsum_J : (∑ j ∈ J, ghMidPOcc h U_r j) = r :=
      (Finset.sum_subset (Finset.subset_univ J) fun j _ hj ↦ hocc_zero j hj).trans
        (ghMidPSumOccEq h)
    rw [hJ_eq, Finset.sum_union hdisj] at hsum_J
    have hsum2 : (∑ j ∈ J₂, ghMidPOcc h U_r j) = 4 := by
      have hc2 : ∀ j ∈ J₂, ghMidPOcc h U_r j = 2 := hJ₂_occ
      rw [Finset.sum_congr rfl hc2, Finset.sum_const, hJ₂_card, smul_eq_mul]
    have hsum1 : (∑ j ∈ J₁, ghMidPOcc h U_r j) = J₁.card := by
      have hc1 : ∀ j ∈ J₁, ghMidPOcc h U_r j = 1 := fun j hj ↦ (Finset.mem_filter.mp hj).2
      rw [Finset.sum_congr rfl hc1, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  have hJ_lt : J.card < r := by
    rw [hJ_eq, Finset.card_union_of_disjoint hdisj, hJ₂_card, hJ₁_card]
    omega
  rcases ghMidP_unitNorm_and_qColl_of_card_lt subN h kInit probes hJ_lt with ⟨hq_eq, hcl_eq, _⟩
  have hθ_J₁ (j : Fin m) (hj : j ∈ J₁) : ghMidPSlotTheta subN h U_r j = θ₁ := by
    unfold ghMidPSlotTheta
    rw [(Finset.mem_filter.mp hj).2, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hθ_J₂ (j : Fin m) (hj : j ∈ J₂) : ghMidPSlotTheta subN h U_r j = θ₂ := by
    unfold ghMidPSlotTheta
    have h2 : ghMidPOcc h U_r j = 2 := hJ₂_occ j hj
    rw [h2, Nat.cast_ofNat, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  let rowOf (z : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ)) (w₁ j : ℕ) : ℂ :=
    match j with
    | 0 => z.1 w₁
    | 1 => z.2.1 w₁
    | _ => z.2.2 w₁
  have hc0_tp (B₂ : Finset (Fin m)) (hB₂ : B₂ ∈ J₂.powerset)
      (B₁ : Finset (Fin m)) (hB₁ : B₁ ∈ J₁.powerset) :
      ghMidPInitCoeff subN h U_r kInit (B₂ ∪ B₁) = rowOf tp₀ B₁.card B₂.card := by
    have hB₂_sub : B₂ ⊆ J₂ := Finset.mem_powerset.mp hB₂
    have hB₁_sub : B₁ ⊆ J₁ := Finset.mem_powerset.mp hB₁
    have hB₂_le : B₂.card ≤ 2 := (Finset.card_le_card hB₂_sub).trans_eq hJ₂_card
    let coeff0 : Finset (Fin m) → ℂ := fun A ↦ if A = ∅ then 1 else 0
    let u_zero : ℕ → ℂ := fun b ↦ if b = 0 then 1 else 0
    let cr (j : Fin m) : ℝ := Real.cos ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN h U_r j)
    let sr (j : Fin m) : ℝ := Real.sin ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta subN h U_r j)
    have hprod2 :
        (∏ j ∈ J₂, if j ∈ B₂ ∪ B₁ then (sr j : ℂ) else (cr j : ℂ)) =
          ghMidPInitAmp 2 θ₂ kInit B₂.card := by
      have hp_eq :
          (∏ j ∈ J₂, if j ∈ B₂ ∪ B₁ then (sr j : ℂ) else (cr j : ℂ)) =
            ghMidPSlotRot J₂ cr sr coeff0 B₂ := by
        unfold ghMidPSlotRot
        rw [Finset.sum_eq_single ∅
          (fun A _ hne ↦ by simp [coeff0, hne])
          (fun hnot ↦ absurd (Finset.empty_mem_powerset J₂) hnot)]
        dsimp only [coeff0]
        rw [ite_eq_left rfl, one_mul]
        refine Finset.prod_congr rfl fun j hj₂ ↦ ?_
        have hjB₁ : j ∉ B₁ := fun hm ↦ Finset.disjoint_left.mp hdisj hj₂ (hB₁_sub hm)
        by_cases hjB₂ : j ∈ B₂ <;> simp [hjB₂, hjB₁]
      rw [hp_eq, ghMidPSlotRot_const_eq_dickeStep J₂
        (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₂ j hj])
        (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₂ j hj])
        u_zero (fun A _ ↦ by simp [coeff0, u_zero]) hB₂, hJ₂_card]
      rfl
    have hprod1 :
        (∏ j ∈ J₁, if j ∈ B₂ ∪ B₁ then (sr j : ℂ) else (cr j : ℂ)) =
          ghMidPInitAmp (r - 4) θ₁ kInit B₁.card := by
      have hp_eq :
          (∏ j ∈ J₁, if j ∈ B₂ ∪ B₁ then (sr j : ℂ) else (cr j : ℂ)) =
            ghMidPSlotRot J₁ cr sr coeff0 B₁ := by
        unfold ghMidPSlotRot
        rw [Finset.sum_eq_single ∅
          (fun A _ hne ↦ by simp [coeff0, hne])
          (fun hnot ↦ absurd (Finset.empty_mem_powerset J₁) hnot)]
        dsimp only [coeff0]
        rw [ite_eq_left rfl, one_mul]
        refine Finset.prod_congr rfl fun j hj₁ ↦ ?_
        have hjB₂ : j ∉ B₂ := fun hm ↦ Finset.disjoint_right.mp hdisj hj₁ (hB₂_sub hm)
        by_cases hjB₁ : j ∈ B₁ <;> simp [hjB₂, hjB₁]
      rw [hp_eq, ghMidPSlotRot_const_eq_dickeStep J₁
        (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₁ j hj])
        (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₁ j hj])
        u_zero (fun A _ ↦ by simp [coeff0, u_zero]) hB₁, hJ₁_card]
      rfl
    unfold ghMidPInitCoeff
    change (∏ j ∈ J, _) = _
    rw [hJ_eq, Finset.prod_union hdisj]
    change (∏ j ∈ J₂, if j ∈ B₂ ∪ B₁ then (sr j : ℂ) else (cr j : ℂ)) *
        (∏ j ∈ J₁, if j ∈ B₂ ∪ B₁ then (sr j : ℂ) else (cr j : ℂ)) = _
    rw [hprod2, hprod1]
    rcases (by omega : B₂.card = 0 ∨ B₂.card = 1 ∨ B₂.card = 2) with hc0 | hc1 | hc2
    · rw [hc0]
      rfl
    · rw [hc1]
      rfl
    · rw [hc2]
      rfl
  have hdamp_tp (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ)
      (z : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ))
      (hz : ∀ B₂ ∈ J₂.powerset, ∀ B₁ ∈ J₁.powerset,
        coeff (B₂ ∪ B₁) = rowOf z B₁.card B₂.card)
      (A₂ : Finset (Fin m)) (hA₂ : A₂ ∈ J₂.powerset)
      (A₁ : Finset (Fin m)) (hA₁ : A₁ ∈ J₁.powerset) :
      ghMidPDampCoeff U_r.card pr coeff (A₂ ∪ A₁) =
        match A₂.card with
        | 0 => ghMidPDamp2Row0 (r - 4) pr z.1 A₁.card
        | 1 => ghMidPDamp2Row1 (r - 4) pr z.2.1 A₁.card
        | _ => ghMidPDampTwoPair2 (r - 4) pr z.2.2 A₁.card := by
    have hA₂_sub : A₂ ⊆ J₂ := Finset.mem_powerset.mp hA₂
    have hA₁_sub : A₁ ⊆ J₁ := Finset.mem_powerset.mp hA₁
    have hA₂_le : A₂.card ≤ 2 := (Finset.card_le_card hA₂_sub).trans_eq hJ₂_card
    have hA₁_le : A₁.card ≤ r - 4 := (Finset.card_le_card hA₁_sub).trans_eq hJ₁_card
    have hdisj_A : Disjoint A₂ A₁ := Disjoint.mono hA₂_sub hA₁_sub hdisj
    have hcard_u : (A₂ ∪ A₁).card = A₂.card + A₁.card := Finset.card_union_of_disjoint hdisj_A
    unfold ghMidPDampCoeff
    rw [hU_card, hz A₂ hA₂ A₁ hA₁, hcard_u]
    rcases (by omega : A₂.card = 0 ∨ A₂.card = 1 ∨ A₂.card = 2) with hc0 | hc1 | hc2
    · rw [hc0, zero_add]
      dsimp only [rowOf]
      by_cases ha0 : A₁.card = 0
      · simp [ghMidPWSpec, ghMidPDamp2Row0, ha0, pythOne_cVal, gaussOne_val]
      · have hlt : A₁.card < r := by omega
        simp [ghMidPWSpec, ghMidPDamp2Row0, ha0, hA₁_le, hlt, pythOne_cVal]
    · rw [hc1]
      dsimp only [rowOf]
      have hlt : 1 + A₁.card < r := by omega
      have hsub1 : 1 + A₁.card - 1 = A₁.card := by omega
      unfold ghMidPWSpec ghMidPDamp2Row1
      simp [hlt, hsub1, hA₁_le, pythOne_cVal]
    · rw [hc2]
      dsimp only [rowOf]
      have hlt : 2 + A₁.card < r := by omega
      have hsub2 : 2 + A₁.card - 1 = A₁.card + 1 := by omega
      unfold ghMidPWSpec ghMidPDampTwoPair2
      simp [hlt, hsub2, hA₁_le, pythOne_cVal]
  have hnext_tp (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ)
      (z : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ))
      (hz : ∀ B₂ ∈ J₂.powerset, ∀ B₁ ∈ J₁.powerset,
        coeff (B₂ ∪ B₁) = rowOf z B₁.card B₂.card)
      (B₂ : Finset (Fin m)) (hB₂ : B₂ ∈ J₂.powerset)
      (B₁ : Finset (Fin m)) (hB₁ : B₁ ∈ J₁.powerset) :
      ghMidPProbeNextCoeff subN h U_r pr coeff (B₂ ∪ B₁) =
        rowOf (ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr z) B₁.card B₂.card := by
    have hB₂_sub : B₂ ⊆ J₂ := Finset.mem_powerset.mp hB₂
    have hB₁_sub : B₁ ⊆ J₁ := Finset.mem_powerset.mp hB₁
    have hB₂_le : B₂.card ≤ 2 := (Finset.card_le_card hB₂_sub).trans_eq hJ₂_card
    let cr (j : Fin m) : ℝ := Real.cos (2 * (pr.kNext : ℝ) * ghMidPSlotTheta subN h U_r j)
    let sr (j : Fin m) : ℝ := Real.sin (2 * (pr.kNext : ℝ) * ghMidPSlotTheta subN h U_r j)
    let dC := ghMidPDampCoeff U_r.card pr coeff
    let c₁ : ℂ := Real.cos (2 * (pr.kNext : ℝ) * θ₁)
    let s₁ : ℂ := Real.sin (2 * (pr.kNext : ℝ) * θ₁)
    let col_fn (w₁ j : ℕ) : ℂ :=
      match j with
      | 0 => dickeStep (r - 4) c₁ s₁ (ghMidPDamp2Row0 (r - 4) pr z.1) w₁
      | 1 => dickeStep (r - 4) c₁ s₁ (ghMidPDamp2Row1 (r - 4) pr z.2.1) w₁
      | _ => dickeStep (r - 4) c₁ s₁ (ghMidPDampTwoPair2 (r - 4) pr z.2.2) w₁
    have hinner (A₂ : Finset (Fin m)) (hA₂ : A₂ ∈ J₂.powerset) :
        ghMidPSlotRot J₁ cr sr (fun A₁ ↦ dC (A₂ ∪ A₁)) B₁ = col_fn B₁.card A₂.card := by
      have hA₂_le : A₂.card ≤ 2 :=
        (Finset.card_le_card (Finset.mem_powerset.mp hA₂)).trans_eq hJ₂_card
      rcases (by omega : A₂.card = 0 ∨ A₂.card = 1 ∨ A₂.card = 2) with hc0 | hc1 | hc2
      · rw [hc0]
        dsimp only [col_fn]
        rw [ghMidPSlotRot_const_eq_dickeStep J₁
          (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₁ j hj])
          (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₁ j hj])
          (ghMidPDamp2Row0 (r - 4) pr z.1)
          (fun A₁ hA₁ ↦ by
            have hd := hdamp_tp pr coeff z hz A₂ hA₂ A₁ hA₁
            rw [hc0] at hd
            exact hd)
          hB₁, hJ₁_card]
        rfl
      · rw [hc1]
        dsimp only [col_fn]
        rw [ghMidPSlotRot_const_eq_dickeStep J₁
          (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₁ j hj])
          (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₁ j hj])
          (ghMidPDamp2Row1 (r - 4) pr z.2.1)
          (fun A₁ hA₁ ↦ by
            have hd := hdamp_tp pr coeff z hz A₂ hA₂ A₁ hA₁
            rw [hc1] at hd
            exact hd)
          hB₁, hJ₁_card]
        rfl
      · rw [hc2]
        dsimp only [col_fn]
        rw [ghMidPSlotRot_const_eq_dickeStep J₁
          (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₁ j hj])
          (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₁ j hj])
          (ghMidPDampTwoPair2 (r - 4) pr z.2.2)
          (fun A₁ hA₁ ↦ by
            have hd := hdamp_tp pr coeff z hz A₂ hA₂ A₁ hA₁
            rw [hc2] at hd
            exact hd)
          hB₁, hJ₁_card]
        rfl
    unfold ghMidPProbeNextCoeff
    change ghMidPSlotRot J cr sr dC (B₂ ∪ B₁) = _
    rw [hJ_eq, ghMidPSlotRot_disjoint_union hdisj cr sr dC hB₂_sub hB₁_sub,
      ghMidPSlotRot_const_eq_dickeStep J₂
        (fun j hj ↦ by dsimp only [cr]; rw [hθ_J₂ j hj])
        (fun j hj ↦ by dsimp only [sr]; rw [hθ_J₂ j hj])
        (col_fn B₁.card) hinner hB₂, hJ₂_card]
    unfold ghMidPProbeNextTwoPair
    rcases (by omega : B₂.card = 0 ∨ B₂.card = 1 ∨ B₂.card = 2) with hc0 | hc1 | hc2
    · rw [hc0]
      dsimp only [rowOf]
      exact congrArg (dickeStep 2 _ _ · 0) (funext fun j ↦ by rcases j with _ | _ | _ <;> rfl)
    · rw [hc1]
      dsimp only [rowOf]
      exact congrArg (dickeStep 2 _ _ · 1) (funext fun j ↦ by rcases j with _ | _ | _ <;> rfl)
    · rw [hc2]
      dsimp only [rowOf]
      exact congrArg (dickeStep 2 _ _ · 2) (funext fun j ↦ by rcases j with _ | _ | _ <;> rfl)
  have hchain_tp : ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ)
      (z : (ℕ → ℂ) × (ℕ → ℂ) × (ℕ → ℂ)),
      (∀ B₂ ∈ J₂.powerset, ∀ B₁ ∈ J₁.powerset,
        coeff (B₂ ∪ B₁) = rowOf z B₁.card B₂.card) →
        ∀ B₂ ∈ J₂.powerset, ∀ B₁ ∈ J₁.powerset,
          ghMidPChainFinalCoeff subN h U_r ps coeff (B₂ ∪ B₁) =
            rowOf (ghMidPChainFinalTwoPair (r - 4) θ₁ θ₂ ps z) B₁.card B₂.card := by
    intro ps
    induction ps with
    | nil =>
      intro _ _ hz
      exact hz
    | cons pr rest ih =>
      intro coeff z hz
      exact ih (ghMidPProbeNextCoeff subN h U_r pr coeff)
        (ghMidPProbeNextTwoPair (r - 4) θ₁ θ₂ pr z) (hnext_tp pr coeff z hz)
  have hcf_tp := hchain_tp probes (ghMidPInitCoeff subN h U_r kInit) tp₀ hc0_tp
  unfold ghMidPBaseStep
  simp only [↓reduceIte]
  rw [hq_eq, hcl_eq, zero_mul, add_zero]
  congr 1
  change (∑ A ∈ J.powerset, _) = remTp
  rw [hJ_eq, ghMidP_sum_powerset_disjoint_union hdisj, Finset.sum_comm]
  have hread_tp (B₁ : Finset (Fin m)) (hB₁ : B₁ ∈ J₁.powerset) :
      (∑ B₂ ∈ J₂.powerset,
        normSq (ghMidPChainFinalCoeff subN h U_r probes
            (ghMidPInitCoeff subN h U_r kInit) (B₂ ∪ B₁)) *
          (∑ c ∈ ghMidPHitChoices h U_r (B₂ ∪ B₁),
            ghMidPChoiceWeight h U_r (B₂ ∪ B₁) *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c))) =
        normSq (tpf.1 B₁.card) * f (r - B₁.card) +
          2 * normSq (tpf.2.1 B₁.card) * f (r - (B₁.card + 1)) +
          normSq (tpf.2.2 B₁.card) * f (r - (B₁.card + 2)) := by
    have hB₁_sub : B₁ ⊆ J₁ := Finset.mem_powerset.mp hB₁
    have hB₁_le : B₁.card ≤ r - 4 := (Finset.card_le_card hB₁_sub).trans_eq hJ₁_card
    have hterm_B₂ (B₂ : Finset (Fin m)) (hB₂ : B₂ ∈ J₂.powerset) :
        normSq (ghMidPChainFinalCoeff subN h U_r probes
            (ghMidPInitCoeff subN h U_r kInit) (B₂ ∪ B₁)) *
          (∑ c ∈ ghMidPHitChoices h U_r (B₂ ∪ B₁),
            ghMidPChoiceWeight h U_r (B₂ ∪ B₁) *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c)) =
          normSq (rowOf tpf B₁.card B₂.card) * f (r - (B₁.card + B₂.card)) := by
      have hB₂_sub : B₂ ⊆ J₂ := Finset.mem_powerset.mp hB₂
      have hB₂_le : B₂.card ≤ 2 := (Finset.card_le_card hB₂_sub).trans_eq hJ₂_card
      have hu_J : B₂ ∪ B₁ ⊆ J := hJ_eq ▸ Finset.union_subset_union hB₂_sub hB₁_sub
      have hdisj_B : Disjoint B₂ B₁ := Disjoint.mono hB₂_sub hB₁_sub hdisj
      have hu_card : (B₂ ∪ B₁).card = B₁.card + B₂.card := by
        rw [Finset.card_union_of_disjoint hdisj_B, add_comm]
      rw [hcf_tp B₂ hB₂ B₁ hB₁]
      have hc_val (c : Fin m → Option (Fin r)) (hc : c ∈ ghMidPHitChoices h U_r (B₂ ∪ B₁)) :
          ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
              (U_r \ ghMidPChoiceSet c) =
            f (r - (B₁.card + B₂.card)) := by
        have hcard_I' : (U_r \ ghMidPChoiceSet c).card = r - (B₁.card + B₂.card) := by
          rw [(ghMidPChoiceSet_props hc).2.2.2, hU_card, hu_card]
        have hne1 : (U_r \ ghMidPChoiceSet c).card ≠ 1 := by omega
        unfold ghMidPZoomPost
        rw [ite_eq_right hne1]
        dsimp only
        rw [hcard_I']
      have hc_congr :
          (∑ c ∈ ghMidPHitChoices h U_r (B₂ ∪ B₁),
            ghMidPChoiceWeight h U_r (B₂ ∪ B₁) *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c)) =
          ∑ _c ∈ ghMidPHitChoices h U_r (B₂ ∪ B₁),
            ghMidPChoiceWeight h U_r (B₂ ∪ B₁) * f (r - (B₁.card + B₂.card)) :=
        Finset.sum_congr rfl fun c hc ↦ by rw [hc_val c hc]
      rw [hc_congr, ← Finset.sum_mul, ghMidPHitChoices_sum_weight h U_r hu_J, one_mul]
    rw [Finset.sum_congr rfl hterm_B₂,
      ghMidP_powerset_sum_card J₂
        (fun w₂ ↦ normSq (rowOf tpf B₁.card w₂) * f (r - (B₁.card + w₂))),
      hJ₂_card]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, rowOf, add_zero]
    norm_num [Nat.choose]
    ring
  have hr4_succ : r - 4 + 1 = r - 3 := by omega
  rw [Finset.sum_congr rfl hread_tp,
    ghMidP_powerset_sum_card J₁
      (fun w₁ ↦ normSq (tpf.1 w₁) * f (r - w₁) +
        2 * normSq (tpf.2.1 w₁) * f (r - (w₁ + 1)) +
        normSq (tpf.2.2 w₁) * f (r - (w₁ + 2))),
    hJ₁_card, hr4_succ]
  refine Finset.sum_congr rfl fun w₁ _ ↦ ?_
  ring
private lemma ghMidP_rem_step_le {r m : ℕ} (subN p kInit : ℕ) (probes : List GHMidPProbe)
    (kZoom : ℕ) (hr2 : 2 ≤ r) {f : ℕ → ℝ}
    (hf_mono : ∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ r → f u₁ ≤ f u₂)
    {h : Fin r → Fin m} (himg_le : ((Finset.univ : Finset (Fin r)).image h).card ≤ r - 2) :
    let U_r : Finset (Fin r) := Finset.univ
    ghMidPBaseStep subN h true kInit probes
        (ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)) U_r ≤
      (ghMidPPreMaxQueries kInit probes : ℝ) + f r := by
  intro U_r
  let J := U_r.image h
  have hU_card : U_r.card = r := by simp [U_r]
  have hJ_le : J.card ≤ r - 2 := himg_le
  have hJ_lt : J.card < r := by omega
  rcases ghMidP_unitNorm_and_qColl_of_card_lt subN h kInit probes hJ_lt with ⟨hq_eq, hcl_eq, hnf1⟩
  unfold ghMidPBaseStep
  simp only [↓reduceIte]
  rw [hq_eq, hcl_eq, zero_mul, add_zero]
  refine add_le_add le_rfl ?_
  calc (∑ A ∈ J.powerset,
        normSq (ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) A) *
          ∑ c ∈ ghMidPHitChoices h U_r A,
            ghMidPChoiceWeight h U_r A *
              ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                (U_r \ ghMidPChoiceSet c))
      ≤ ∑ A ∈ J.powerset,
          normSq (ghMidPChainFinalCoeff subN h U_r probes (ghMidPInitCoeff subN h U_r kInit) A) *
            f r := by
        refine Finset.sum_le_sum fun A hA ↦ mul_le_mul_of_nonneg_left ?_ (Complex.normSq_nonneg _)
        have hA_sub : A ⊆ J := Finset.mem_powerset.mp hA
        have hA_le : A.card ≤ r - 2 := (Finset.card_le_card hA_sub).trans himg_le
        calc (∑ c ∈ ghMidPHitChoices h U_r A,
              ghMidPChoiceWeight h U_r A *
                ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r (fun I' ↦ f I'.card)
                  (U_r \ ghMidPChoiceSet c))
            ≤ ∑ _c ∈ ghMidPHitChoices h U_r A, ghMidPChoiceWeight h U_r A * f r := by
              refine Finset.sum_le_sum fun c hc ↦
                mul_le_mul_of_nonneg_left ?_ (ghMidPChoiceWeight_nonneg h U_r A)
              have hcard_I' : (U_r \ ghMidPChoiceSet c).card = r - A.card := by
                rw [(ghMidPChoiceSet_props hc).2.2.2, hU_card]
              have hne1 : (U_r \ ghMidPChoiceSet c).card ≠ 1 := by omega
              unfold ghMidPZoomPost
              rw [ite_eq_right hne1]
              dsimp only
              rw [hcard_I']
              exact hf_mono (r - A.card) r (Nat.sub_le r A.card) le_rfl
          _ = f r := by rw [← Finset.sum_mul, ghMidPHitChoices_sum_weight h U_r hA_sub, one_mul]
    _ = f r := by rw [← Finset.sum_mul, hnf1, one_mul]
lemma ghMidPExactOneDimStep_zero (subN p m : ℕ) (spec_fn : ℕ → GHMidPSpec) (g : ℕ → ℝ) :
    ghMidPExactOneDimStep subN p m spec_fn g 0 = g 0 := by
  unfold ghMidPExactOneDimStep
  have hterm (h : Fin 0 → Fin m) :
      ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ g I'.card) Finset.univ = g 0 := by
    unfold ghMidPSubsetStep
    simp only [Finset.card_univ, Fintype.card_fin]
    cases spec_fn 0 with
    | none => rfl
    | some kpz =>
      rcases kpz with ⟨_, _, _⟩
      simp
  simp_rw [hterm]
  simp [Finset.sum_const]
lemma ghMidPExactOneDimStep_one (subN p m : ℕ) (hm1 : 1 ≤ m)
    (spec_fn : ℕ → GHMidPSpec) (g : ℕ → ℝ) :
    ghMidPExactOneDimStep subN p m spec_fn g 1 = g 1 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  unfold ghMidPExactOneDimStep
  have hterm (h : Fin 1 → Fin m) :
      ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ g I'.card) Finset.univ = g 1 := by
    unfold ghMidPSubsetStep
    simp only [Finset.card_univ, Fintype.card_fin]
    cases spec_fn 1 with
    | none => rfl
    | some kpz =>
      rcases kpz with ⟨_, _, _⟩
      simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    pow_one, pow_one, nsmul_eq_mul, mul_div_cancel_left₀ _ hm_pos.ne']
lemma ghMidPExactOneDimStep_two_eq_ghZoomOneDimUpper (subN p m : ℕ) (hm2 : 2 ≤ m)
    (spec2 : GHZoomSpec) {spec_fn : ℕ → GHMidPSpec}
    (hspec2 : spec_fn 2 = ghZoomSpecToMidP spec2)
    {f : ℕ → ℝ} (hf0 : f 0 = 0) :
    ghMidPExactOneDimStep subN p m spec_fn f 2 = ghZoomOneDimUpper subN p m spec2 f 2 := by
  classical
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hm_pos 2
  unfold ghMidPExactOneDimStep ghZoomOneDimUpper
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  cases spec2 with
  | none =>
    dsimp only [ghZoomSpecToMidP] at hspec2 ⊢
    have hconst (h : Fin 2 → Fin m) :
        ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ f I'.card) Finset.univ = f 2 := by
      unfold ghMidPSubsetStep
      rw [Finset.card_univ, Fintype.card_fin, hspec2]
      dsimp only
      rw [Finset.card_univ, Fintype.card_fin]
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, mul_div_cancel_left₀ _ hm2_pos.ne']
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only [ghZoomSpecToMidP] at hspec2 ⊢
    have hcond : 2 ≤ 2 ∧ 2 ≤ 16 ∧ 2 - 1 < m := ⟨le_rfl, by omega, by omega⟩
    let U : Finset (Fin 2 → Fin m) := Finset.univ
    let Inj := U.filter Function.Injective
    let Coll := U.filter fun h ↦ ¬ Function.Injective h
    let U_2 : Finset (Fin 2) := Finset.univ
    let term (h : Fin 2 → Fin m) : ℝ :=
      ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ f I'.card) U_2
    have hterm_rew (h : Fin 2 → Fin m) :
        term h = ghMidPBaseStep subN h true kInit (probes.map ghZoomProbeToMidP)
          (ghMidPZoomPost (2 - 1) (subN - p) kZoom true h U_2 (fun I' ↦ f I'.card)) U_2 := by
      unfold term ghMidPSubsetStep
      have hc2 : U_2.card = 2 := by simp [U_2]
      rw [hc2, hspec2]
      dsimp only
      rw [ite_eq_left hcond]
    have hsplit : (∑ h ∈ U, term h) = (∑ h ∈ Inj, term h) + ∑ h ∈ Coll, term h :=
      (Finset.sum_filter_add_sum_filter_not U Function.Injective term).symm
    have hinj_card : Inj.card = m.descFactorial 2 := card_ghMidPInjFibers 2 m (by omega)
    have hcoll_prob : (Coll.card : ℝ) / (m : ℝ) ^ 2 = 1 - rotCfProb m 2 := by
      have hadd : Inj.card + Coll.card = U.card := by
        simpa [Inj, Coll] using
          Finset.sum_filter_add_sum_filter_not U Function.Injective (fun _ ↦ (1 : ℕ))
      have hU_c : U.card = m ^ 2 := by simp [U]
      have hadd_r : (m.descFactorial 2 : ℝ) + (Coll.card : ℝ) = (m : ℝ) ^ 2 := by
        have hc := congrArg (Nat.cast (R := ℝ)) hadd
        simpa only [hinj_card, hU_c, Nat.cast_add, Nat.cast_pow] using hc
      unfold rotCfProb
      field_simp [hm2_pos.ne']
      linarith
    set θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    set θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    have hdamp2 (pr : GHZoomProbe) (u : ℕ → ℂ) :
        ghMidPDampAmp 2 (ghZoomProbeToMidP pr) u = ghDampAmp2 pr.1 pr.2.1 pr.2.2.1 u := by
      funext b
      rcases b with _ | _ | _ | b <;> simp [ghMidPDampAmp, ghZoomProbeToMidP, ghDampAmp2]
    have hnext2 (pr : GHZoomProbe) (u : ℕ → ℂ) :
        ghMidPProbeNextAmp 2 θ₁ (ghZoomProbeToMidP pr) u = ghProbeNextAmp2 θ₁ pr u := by
      unfold ghMidPProbeNextAmp ghProbeNextAmp2
      rw [hdamp2]
      rfl
    have hchain2 : ∀ (ps : List GHZoomProbe) (u : ℕ → ℂ),
        ghMidPChainFinalAmp 2 θ₁ (ps.map ghZoomProbeToMidP) u = ghChainFinalAmp2 θ₁ ps u ∧
          ghMidPChainExtraQueries 2 θ₁ (ps.map ghZoomProbeToMidP) u =
            ghChainExtraQueries2 θ₁ ps u := by
      intro ps
      induction ps with
      | nil => intro _; exact ⟨rfl, rfl⟩
      | cons pr rest ih =>
        intro u
        dsimp only [List.map, ghMidPChainFinalAmp, ghChainFinalAmp2,
          ghMidPChainExtraQueries, ghChainExtraQueries2]
        rw [hnext2]
        rcases ih (ghProbeNextAmp2 θ₁ pr u) with ⟨hf_r, hex_r⟩
        refine ⟨hf_r, ?_⟩
        rw [hdamp2, hex_r]
        dsimp only [ghZoomProbeToMidP]
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
        norm_num [Nat.choose]
    have hu0_eq : ghMidPInitAmp 2 θ₁ kInit = ghInitAmp2 θ₁ kInit := rfl
    rcases hchain2 probes (ghInitAmp2 θ₁ kInit) with ⟨huf_eq, hex_eq⟩
    have hcoll_sp (h : Fin 2 → Fin m) (hh : h ∈ Coll) : ghMidPIsSingleMult 2 h := by
      have hnot_inj : ¬ Function.Injective h := (Finset.mem_filter.mp hh).2
      have h01 : h 0 = h 1 := by
        by_contra hne
        apply hnot_inj
        intro a b hab
        fin_cases a <;> fin_cases b
        · rfl
        · exact absurd hab hne
        · exact absurd hab.symm hne
        · rfl
      refine ⟨h 0, ?_, fun j hj ↦ ?_⟩
      · have hfilt_all : (Finset.univ.filter fun i : Fin 2 ↦ h i = h 0) = Finset.univ := by
          ext i
          fin_cases i <;> simp [h01]
        dsimp only [ghMidPFiberOcc, ghMidPOcc]
        rw [hfilt_all, Finset.card_univ, Fintype.card_fin]
      · refine Finset.card_le_one.mpr fun i hi _ _ ↦ ?_
        exfalso
        have hi0 : h i = h 0 := by fin_cases i <;> simp [h01]
        exact hj ((Finset.mem_filter.mp hi).2.symm.trans hi0)
    have hpre_q :
        ghMidPPreMaxQueries kInit (probes.map ghZoomProbeToMidP) = ghMaxQueries kInit probes := by
      simp [ghMidPPreMaxQueries, ghMaxQueries, List.map_map, Function.comp_def, ghZoomProbeToMidP]
    have hsp0_eq :
        ((ghMidPInit2Row 0 θ₁ θ₂ kInit).1 0, (ghMidPInit2Row 0 θ₁ θ₂ kInit).2 0) =
          ghInitColl2 θ₂ kInit := by
      dsimp only [ghMidPInit2Row, ghMidPInitAmp, dickeStep, ghInitColl2]
      simp
    have hnext_coll (pr : GHZoomProbe) (z : (ℕ → ℂ) × (ℕ → ℂ)) :
        ((ghMidPProbeNext2Row 0 θ₁ θ₂ (ghZoomProbeToMidP pr) z).1 0,
          (ghMidPProbeNext2Row 0 θ₁ θ₂ (ghZoomProbeToMidP pr) z).2 0) =
          ghProbeNextColl2 θ₂ pr (z.1 0, z.2 0) := by
      dsimp only [ghMidPProbeNext2Row, ghMidPDamp2Row0, ghMidPDamp2Row1,
        ghZoomProbeToMidP, dickeStep, ghProbeNextColl2]
      simp
    have hchain_coll : ∀ (ps : List GHZoomProbe) (z : (ℕ → ℂ) × (ℕ → ℂ)),
        ((ghMidPChainFinal2Row 0 θ₁ θ₂ (ps.map ghZoomProbeToMidP) z).1 0,
          (ghMidPChainFinal2Row 0 θ₁ θ₂ (ps.map ghZoomProbeToMidP) z).2 0) =
          ghChainFinalColl2 θ₂ ps (z.1 0, z.2 0) := by
      intro ps
      induction ps with
      | nil => intro _; rfl
      | cons pr rest ih =>
        intro z
        dsimp only [List.map, ghMidPChainFinal2Row, ghChainFinalColl2]
        rw [ih, hnext_coll]
    have hpZoom_eq :
        Real.sin ((2 * (kZoom : ℝ) + 1) *
            Real.arcsin (1 / √(((2 - 1) * 2 ^ (subN - p) : ℕ) : ℝ))) ^ 2 =
          p_succ_frac kZoom 1 (2 ^ (subN - p)) := by
      unfold p_succ_frac
      have h1 : ((2 - 1) * 2 ^ (subN - p) : ℕ) = 2 ^ (subN - p) := by simp
      rw [h1, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]
    have hinj_term (h : Fin 2 → Fin m) (hh : h ∈ Inj) :
        term h = ((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes (ghInitAmp2 θ₁ kInit) +
          normSq (ghChainFinalAmp2 θ₁ probes (ghInitAmp2 θ₁ kInit) 0) * f 2 +
          2 * normSq (ghChainFinalAmp2 θ₁ probes (ghInitAmp2 θ₁ kInit) 1) *
            (((kZoom + 1 : ℕ) : ℝ) + f 1) := by
      rw [hterm_rew h,
        ghMidP_inj_step_eq subN p kInit (probes.map ghZoomProbeToMidP) kZoom le_rfl hf0
          (Finset.mem_filter.mp hh).2]
      rw [hu0_eq, huf_eq, hex_eq]
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.choose]
      ring
    have hcoll_term (h : Fin 2 → Fin m) (hh : h ∈ Coll) :
        term h = (ghMaxQueries kInit probes : ℝ) +
          normSq (ghChainFinalColl2 θ₂ probes (ghInitColl2 θ₂ kInit)).1 * f 2 +
          normSq (ghChainFinalColl2 θ₂ probes (ghInitColl2 θ₂ kInit)).2 *
            (((kZoom + 1 : ℕ) : ℝ) + (1 - p_succ_frac kZoom 1 (2 ^ (subN - p))) * f 1) := by
      rw [hterm_rew h,
        ghMidP_singlePair_step_eq subN p kInit (probes.map ghZoomProbeToMidP) kZoom le_rfl hf0
          (hcoll_sp h hh)]
      have hzf_coll := hchain_coll probes (ghMidPInit2Row 0 θ₁ θ₂ kInit)
      rw [hsp0_eq] at hzf_coll
      have hzf1 :
          (ghMidPChainFinal2Row 0 θ₁ θ₂ (probes.map ghZoomProbeToMidP)
            (ghMidPInit2Row 0 θ₁ θ₂ kInit)).1 0 =
          (ghChainFinalColl2 θ₂ probes (ghInitColl2 θ₂ kInit)).1 :=
        congrArg Prod.fst hzf_coll
      have hzf2 :
          (ghMidPChainFinal2Row 0 θ₁ θ₂ (probes.map ghZoomProbeToMidP)
            (ghMidPInit2Row 0 θ₁ θ₂ kInit)).2 0 =
          (ghChainFinalColl2 θ₂ probes (ghInitColl2 θ₂ kInit)).2 :=
        congrArg Prod.snd hzf_coll
      have hr21 : (2 - 1 : ℕ) = 1 := rfl
      have hr22 : (2 - 2 : ℕ) = 0 := rfl
      rw [hpre_q, hpZoom_eq, hr21, hr22, Finset.range_one, Finset.sum_singleton,
        Finset.sum_singleton, hzf1, hzf2]
      norm_num [Nat.choose]
    change (∑ h ∈ U, term h) / (m : ℝ) ^ 2 = _
    rw [hsplit, add_div, Finset.sum_congr rfl hinj_term, Finset.sum_const, nsmul_eq_mul,
      hinj_card, ← div_mul_eq_mul_div, Finset.sum_congr rfl hcoll_term, Finset.sum_const,
      nsmul_eq_mul, ← div_mul_eq_mul_div, hcoll_prob]
    rfl
lemma ghMidPExactOneDimStep_le_ghMidPOneDimUpper (subN p m : ℕ) (hm1 : 1 ≤ m)
    (hm_pow : m = 2 ^ p) {spec_fn : ℕ → GHMidPSpec} {f : ℕ → ℝ} {r : ℕ} (hr3 : 3 ≤ r)
    (hf0 : f 0 = 0) (hf_mono : ∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ r → f u₁ ≤ f u₂) :
    ghMidPExactOneDimStep subN p m spec_fn f r ≤ ghMidPOneDimUpper subN p m (spec_fn r) f r := by
  classical
  by_cases hr0 : r = 0
  · exact absurd hr0 (by omega)
  · unfold ghMidPExactOneDimStep ghMidPOneDimUpper
    rw [ite_eq_right hr0]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hmr_pos : (0 : ℝ) < (m : ℝ) ^ r := pow_pos hm_pos r
    let U_r : Finset (Fin r) := Finset.univ
    have hU_card : U_r.card = r := by simp [U_r]
    cases hspec : spec_fn r with
    | none =>
      dsimp only
      refine le_of_eq ?_
      have hconst (h : Fin r → Fin m) :
          ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ f I'.card) Finset.univ = f r := by
        unfold ghMidPSubsetStep
        rw [Finset.card_univ, Fintype.card_fin, hspec]
        dsimp only
        rw [Finset.card_univ, Fintype.card_fin]
      simp_rw [hconst]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, mul_div_cancel_left₀ _ hmr_pos.ne']
    | some kpz =>
      rcases kpz with ⟨kInit, probes, kZoom⟩
      dsimp only
      by_cases hcond : 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ m = 2 ^ p
      · rw [ite_eq_left hcond]
        have hsub_cond : 2 ≤ r ∧ r ≤ 16 ∧ r - 1 < m := ⟨by omega, hcond.2.1, hcond.2.2.1⟩
        let U : Finset (Fin r → Fin m) := Finset.univ
        let Inj := U.filter Function.Injective
        let C1 := U.filter fun h ↦ ¬ Function.Injective h
        let SP := C1.filter (ghMidPIsSingleMult 2)
        let C2 := C1.filter fun h ↦ ¬ ghMidPIsSingleMult 2 h
        let ST := C2.filter (ghMidPIsSingleMult 3)
        let C3 := C2.filter fun h ↦ ¬ ghMidPIsSingleMult 3 h
        let TP := C3.filter ghMidPIsTwoPair
        let Rem := C3.filter fun h ↦ ¬ ghMidPIsTwoPair h
        let term (h : Fin r → Fin m) : ℝ :=
          ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ f I'.card) U_r
        have hterm_rew (h : Fin r → Fin m) :
            term h = ghMidPBaseStep subN h true kInit probes
              (ghMidPZoomPost (r - 1) (subN - p) kZoom true h U_r
                (fun I' ↦ f I'.card)) U_r := by
          unfold term ghMidPSubsetStep
          rw [hU_card, hspec]
          dsimp only
          rw [ite_eq_left hsub_cond]
        have hsum_split :
            (∑ h ∈ U, term h) =
              (∑ h ∈ Inj, term h) + (∑ h ∈ SP, term h) + (∑ h ∈ ST, term h) +
                (∑ h ∈ TP, term h) + (∑ h ∈ Rem, term h) := by
          have hs0 := (Finset.sum_filter_add_sum_filter_not U Function.Injective term).symm
          have hs1 := (Finset.sum_filter_add_sum_filter_not C1 (ghMidPIsSingleMult 2) term).symm
          have hs2 := (Finset.sum_filter_add_sum_filter_not C2 (ghMidPIsSingleMult 3) term).symm
          have hs3 := (Finset.sum_filter_add_sum_filter_not C3 ghMidPIsTwoPair term).symm
          dsimp only [Inj, C1, SP, C2, ST, C3, TP, Rem] at hs0 hs1 hs2 hs3 ⊢
          linarith
        have hcard_split :
            Inj.card + SP.card + ST.card + TP.card + Rem.card = m ^ r := by
          have hc0 : Inj.card + C1.card = U.card := by
            simpa [Inj, C1] using
              Finset.sum_filter_add_sum_filter_not U Function.Injective (fun _ ↦ (1 : ℕ))
          have hc1 : SP.card + C2.card = C1.card := by
            simpa [SP, C2] using
              Finset.sum_filter_add_sum_filter_not C1 (ghMidPIsSingleMult 2) (fun _ ↦ (1 : ℕ))
          have hc2 : ST.card + C3.card = C2.card := by
            simpa [ST, C3] using
              Finset.sum_filter_add_sum_filter_not C2 (ghMidPIsSingleMult 3) (fun _ ↦ (1 : ℕ))
          have hc3 : TP.card + Rem.card = C3.card := by
            simpa [TP, Rem] using
              Finset.sum_filter_add_sum_filter_not C3 ghMidPIsTwoPair (fun _ ↦ (1 : ℕ))
          have hUc : U.card = m ^ r := by simp [U]
          omega
        have hsm_not_inj {c : ℕ} (hc2 : 2 ≤ c) {h : Fin r → Fin m}
            (hsm : ghMidPIsSingleMult c h) : ¬ Function.Injective h := by
          rcases hsm with ⟨jc, hjc, _⟩
          intro hinj
          have hle1 : ghMidPFiberOcc h jc ≤ 1 :=
            Finset.card_le_one.mpr fun _ h1 _ h2 ↦
              hinj ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
          omega
        have hSP_eq : SP = ghMidPSingleMultFibers 2 r m := by
          ext h
          simp only [SP, C1, U, ghMidPSingleMultFibers, Finset.mem_filter, Finset.mem_univ,
            true_and, and_iff_right_iff_imp]
          exact hsm_not_inj le_rfl
        have hST_eq : ST = ghMidPSingleMultFibers 3 r m := by
          ext h
          simp only [ST, C2, C1, U, ghMidPSingleMultFibers, Finset.mem_filter, Finset.mem_univ,
            true_and]
          refine ⟨fun hh ↦ hh.2, fun h3 ↦ ⟨⟨hsm_not_inj (by omega) h3, ?_⟩, h3⟩⟩
          rcases h3 with ⟨j₃, hj₃, _⟩
          rintro ⟨j₂, hj₂, hle₂⟩
          by_cases heq : j₃ = j₂
          · subst heq; omega
          · have := hle₂ j₃ heq; omega
        have hTP_eq : TP = ghMidPTwoPairFibers r m := by
          ext h
          simp only [TP, C3, C2, C1, U, ghMidPTwoPairFibers, Finset.mem_filter, Finset.mem_univ,
            true_and]
          refine ⟨fun hh ↦ hh.2, fun htp ↦ ⟨⟨⟨?_, ?_⟩, ?_⟩, htp⟩⟩
          · rcases htp with ⟨J₂, hJ₂_c, hJ₂_occ, _⟩
            obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp (by omega : 0 < J₂.card)
            intro hinj
            have hle1 : ghMidPFiberOcc h j₀ ≤ 1 :=
              Finset.card_le_one.mpr fun _ h1 _ h2 ↦
                hinj ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
            have h2 := hJ₂_occ j₀ hj₀
            omega
          · rcases htp with ⟨J₂, hJ₂_c, hJ₂_occ, _⟩
            rintro ⟨j₂, _, hle₂⟩
            have her : 0 < (J₂.erase j₂).card := by
              by_cases hm : j₂ ∈ J₂
              · rw [Finset.card_erase_of_mem hm, hJ₂_c]; omega
              · rw [Finset.erase_eq_of_notMem hm, hJ₂_c]; omega
            obtain ⟨j', hj'_er⟩ := Finset.card_pos.mp her
            have hj'_ne : j' ≠ j₂ := (Finset.mem_erase.mp hj'_er).1
            have h2 := hJ₂_occ j' (Finset.mem_erase.mp hj'_er).2
            have h1 := hle₂ j' hj'_ne
            omega
          · rcases htp with ⟨J₂, _, hJ₂_occ, hJ₂_not⟩
            rintro ⟨j₃, hj₃, _⟩
            by_cases hm : j₃ ∈ J₂
            · have := hJ₂_occ j₃ hm; omega
            · have := hJ₂_not j₃ hm; omega
        have hInj_card : Inj.card = m.descFactorial r := card_ghMidPInjFibers r m hm1
        have hSP_card : SP.card = r.choose 2 * m.descFactorial (r - 1) := by
          have hr21 : r - 2 + 1 = r - 1 := by omega
          rw [hSP_eq, card_ghMidPSingleMultFibers (c := 2) (r := r) (m := m) le_rfl (by omega),
            hr21]
        have hST_card : ST.card = r.choose 3 * m.descFactorial (r - 2) := by
          have hr32 : r - 3 + 1 = r - 2 := by omega
          rw [hST_eq, card_ghMidPSingleMultFibers (c := 3) (r := r) (m := m) (by omega) hcond.1,
            hr32]
        have hTP_card :
            TP.card = if 4 ≤ r then 3 * r.choose 4 * m.descFactorial (r - 2) else 0 := by
          rw [hTP_eq]
          by_cases hr4 : 4 ≤ r
          · rw [ite_eq_left hr4]
            exact card_ghMidPTwoPairFibers hr4
          · rw [ite_eq_right hr4]
            refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun h hh ↦ ?_)
            rcases (Finset.mem_filter.mp hh).2 with ⟨J₂, hJ₂_c, hJ₂_occ, _⟩
            have hsum_ge : 4 ≤ ∑ j : Fin m, ghMidPFiberOcc h j := by
              have h4 : (∑ j ∈ J₂, ghMidPFiberOcc h j) = 4 := by
                rw [Finset.sum_congr rfl hJ₂_occ, Finset.sum_const, hJ₂_c, smul_eq_mul]
              rw [← h4]
              exact Finset.sum_le_sum_of_subset (Finset.subset_univ J₂)
            rw [ghMidPSumOccEq h] at hsum_ge
            omega
        let nInj : ℕ := m.descFactorial r
        let nSp : ℕ := r.choose 2 * m.descFactorial (r - 1)
        let nTp : ℕ := if 4 ≤ r then 3 * r.choose 4 * m.descFactorial (r - 2) else 0
        let nSt : ℕ := r.choose 3 * m.descFactorial (r - 2)
        let nRem : ℕ := m ^ r - (nInj + nSp + nTp + nSt)
        have hRem_card : Rem.card = nRem := by
          dsimp only [nRem, nInj, nSp, nTp, nSt]
          rw [← hInj_card, ← hSP_card, ← hTP_card, ← hST_card]
          omega
        have hinj_sum :
            (∑ h ∈ Inj, term h) =
              (nInj : ℝ) *
                (((kInit + 1 : ℕ) : ℝ) +
                  ghMidPChainExtraQueries r (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
                    (ghMidPInitAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) +
                  ∑ w ∈ Finset.range r,
                    (r.choose w : ℝ) *
                      normSq (ghMidPChainFinalAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
                        (ghMidPInitAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) w) *
                      (if w + 1 = r then ((kZoom + 1 : ℕ) : ℝ) + f 1 else f (r - w))) := by
          have hc : ∀ h ∈ Inj, term h = _ := fun h hh ↦
            (hterm_rew h).trans
              (ghMidP_inj_step_eq subN p kInit probes kZoom (by omega) hf0
                (Finset.mem_filter.mp hh).2)
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hInj_card]
        have hsp_sum :
            (∑ h ∈ SP, term h) =
              (nSp : ℝ) *
                ((ghMidPPreMaxQueries kInit probes : ℝ) +
                  (∑ w₁ ∈ Finset.range (r - 1),
                    ((r - 2).choose w₁ : ℝ) *
                      normSq ((ghMidPChainFinal2Row (r - 2)
                        (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                        (Real.arcsin (√2 / √(2 ^ subN : ℝ))) probes
                        (ghMidPInit2Row (r - 2) (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                          (Real.arcsin (√2 / √(2 ^ subN : ℝ))) kInit)).1 w₁) *
                      f (r - w₁)) +
                  ∑ w₁ ∈ Finset.range (r - 1),
                    ((r - 2).choose w₁ : ℝ) *
                      normSq ((ghMidPChainFinal2Row (r - 2)
                        (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                        (Real.arcsin (√2 / √(2 ^ subN : ℝ))) probes
                        (ghMidPInit2Row (r - 2) (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                          (Real.arcsin (√2 / √(2 ^ subN : ℝ))) kInit)).2 w₁) *
                      (if w₁ + 2 = r then
                        ((kZoom + 1 : ℕ) : ℝ) +
                          (1 - Real.sin ((2 * (kZoom : ℝ) + 1) *
                            Real.arcsin (1 / √(((r - 1) * 2 ^ (subN - p) : ℕ) : ℝ))) ^ 2) * f 1
                       else f (r - 1 - w₁))) := by
          have hc : ∀ h ∈ SP, term h = _ := fun h hh ↦
            (hterm_rew h).trans
              (ghMidP_singlePair_step_eq subN p kInit probes kZoom (by omega) hf0
                (Finset.mem_filter.mp hh).2)
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hSP_card]
        have hst_sum :
            (∑ h ∈ ST, term h) =
              (nSt : ℝ) *
                ((ghMidPPreMaxQueries kInit probes : ℝ) +
                  ∑ w₁ ∈ Finset.range (r - 2),
                    (((r - 3).choose w₁ : ℝ) *
                        normSq ((ghMidPChainFinal2Row (r - 3)
                          (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                          (Real.arcsin (√3 / √(2 ^ subN : ℝ))) probes
                          (ghMidPInit2Row (r - 3) (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                            (Real.arcsin (√3 / √(2 ^ subN : ℝ))) kInit)).1 w₁) *
                        f (r - w₁) +
                      ((r - 3).choose w₁ : ℝ) *
                        normSq ((ghMidPChainFinal2Row (r - 3)
                          (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                          (Real.arcsin (√3 / √(2 ^ subN : ℝ))) probes
                          (ghMidPInit2Row (r - 3) (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                            (Real.arcsin (√3 / √(2 ^ subN : ℝ))) kInit)).2 w₁) *
                        f (r - (w₁ + 1)))) := by
          have hc : ∀ h ∈ ST, term h = _ := fun h hh ↦
            (hterm_rew h).trans
              (ghMidP_singleTriple_step_eq subN p kInit probes kZoom hcond.1 f
                (Finset.mem_filter.mp hh).2)
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hST_card]
        have htp_sum :
            (∑ h ∈ TP, term h) =
              (nTp : ℝ) *
                ((ghMidPPreMaxQueries kInit probes : ℝ) +
                  if 4 ≤ r then
                    ∑ w₁ ∈ Finset.range (r - 3),
                      (((r - 4).choose w₁ : ℝ) *
                          normSq ((ghMidPChainFinalTwoPair (r - 4)
                            (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                            (Real.arcsin (√2 / √(2 ^ subN : ℝ))) probes
                            (ghMidPInitTwoPair (r - 4) (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                              (Real.arcsin (√2 / √(2 ^ subN : ℝ))) kInit)).1 w₁) *
                          f (r - w₁) +
                        (2 * (r - 4).choose w₁ : ℝ) *
                          normSq ((ghMidPChainFinalTwoPair (r - 4)
                            (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                            (Real.arcsin (√2 / √(2 ^ subN : ℝ))) probes
                            (ghMidPInitTwoPair (r - 4) (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                              (Real.arcsin (√2 / √(2 ^ subN : ℝ))) kInit)).2.1 w₁) *
                          f (r - (w₁ + 1)) +
                        ((r - 4).choose w₁ : ℝ) *
                          normSq ((ghMidPChainFinalTwoPair (r - 4)
                            (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                            (Real.arcsin (√2 / √(2 ^ subN : ℝ))) probes
                            (ghMidPInitTwoPair (r - 4) (Real.arcsin (1 / √(2 ^ subN : ℝ)))
                              (Real.arcsin (√2 / √(2 ^ subN : ℝ))) kInit)).2.2 w₁) *
                          f (r - (w₁ + 2)))
                  else 0) := by
          by_cases hr4 : 4 ≤ r
          · rw [ite_eq_left hr4]
            have hc : ∀ h ∈ TP, term h = _ := fun h hh ↦
              (hterm_rew h).trans
                (ghMidP_twoPair_step_eq subN p kInit probes kZoom hr4 f
                  (Finset.mem_filter.mp hh).2)
            rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hTP_card]
          · have hTP_empty : TP = ∅ := Finset.card_eq_zero.mp (by rw [hTP_card, ite_eq_right hr4])
            have hnTp0 : nTp = 0 := ite_eq_right hr4
            rw [hTP_empty, Finset.sum_empty, hnTp0, Nat.cast_zero, zero_mul]
        have hrem_le :
            (∑ h ∈ Rem, term h) ≤ (nRem : ℝ) * ((ghMidPPreMaxQueries kInit probes : ℝ) + f r) := by
          calc (∑ h ∈ Rem, term h)
              ≤ ∑ _h ∈ Rem, ((ghMidPPreMaxQueries kInit probes : ℝ) + f r) := by
                refine Finset.sum_le_sum fun h hh ↦ ?_
                have hh_c3 := (Finset.mem_filter.mp hh).1
                have hh_c2 := (Finset.mem_filter.mp hh_c3).1
                rcases Finset.mem_filter.mp hh_c2 with ⟨hh_c1, hnot_sp⟩
                have hnot_inj := (Finset.mem_filter.mp hh_c1).2
                rw [hterm_rew h]
                exact ghMidP_rem_step_le subN p kInit probes kZoom (by omega) hf_mono
                  (ghMidP_image_card_le_sub_two_of_rem hnot_inj hnot_sp)
            _ = (nRem : ℝ) * ((ghMidPPreMaxQueries kInit probes : ℝ) + f r) := by
                rw [Finset.sum_const, nsmul_eq_mul, hRem_card]
        change (∑ h ∈ U, term h) / (m : ℝ) ^ r ≤ _
        rw [Nat.cast_pow]
        refine div_le_div_of_nonneg_right ?_ hmr_pos.le
        rw [hsum_split, hinj_sum, hsp_sum, hst_sum, htp_sum]
        linarith [hrem_le]
      · rw [ite_eq_right hcond]
        refine le_of_eq ?_
        have hnot_sub : ¬ (2 ≤ r ∧ r ≤ 16 ∧ r - 1 < m) :=
          fun hs ↦ hcond ⟨hr3, hs.2.1, hs.2.2, hm_pow⟩
        have hconst (h : Fin r → Fin m) :
            ghMidPSubsetStep subN p h true spec_fn (fun I' ↦ f I'.card) Finset.univ = f r := by
          unfold ghMidPSubsetStep
          rw [Finset.card_univ, Fintype.card_fin, hspec]
          dsimp only
          rw [ite_eq_right hnot_sub, Finset.card_univ, Fintype.card_fin]
        simp_rw [hconst]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, mul_div_cancel_left₀ _ hmr_pos.ne']
private lemma ghMidP_image_comp {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (s : Finset α) :
    (s.image f).image g = s.image (fun x ↦ g (f x)) := by
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
private lemma ghMidP_image_sdiff_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    {emb : α → β} (hemb : Function.Injective emb) (A B : Finset α) :
    A.image emb \ B.image emb = (A \ B).image emb := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, haA, rfl⟩, hnot⟩
    exact ⟨a, ⟨haA, fun haB ↦ hnot ⟨a, haB, rfl⟩⟩, rfl⟩
  · rintro ⟨a, ⟨haA, haB⟩, rfl⟩
    refine ⟨⟨a, haA, rfl⟩, ?_⟩
    rintro ⟨a', ha'B, heq⟩
    exact haB (hemb heq ▸ ha'B)
private lemma ghMidPBaseStep_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {m : ℕ}
    (subN : ℕ) {emb : α → β} (hemb : Function.Injective emb)
    (pref : β → Fin m) (kInit : ℕ) (probes : List GHMidPProbe)
    (Ψ : Finset β → ℝ) (I : Finset α) :
    ghMidPBaseStep subN pref true kInit probes Ψ (I.image emb) =
      ghMidPBaseStep subN (fun i ↦ pref (emb i)) true kInit probes
        (fun I' ↦ Ψ (I'.image emb)) I := by
  let pref' : α → Fin m := fun i ↦ pref (emb i)
  have himg : (I.image emb).image pref = I.image pref' := ghMidP_image_comp emb pref I
  have hcard : (I.image emb).card = I.card := Finset.card_image_of_injective I hemb
  have hfilt (j : Fin m) :
      ((I.image emb).filter fun y ↦ pref y = j) = (I.filter fun i ↦ pref' i = j).image emb := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hj⟩
      exact ⟨i, ⟨hi, hj⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hj⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hj⟩
  have hocc (j : Fin m) : ghMidPOcc pref (I.image emb) j = ghMidPOcc pref' I j := by
    unfold ghMidPOcc
    rw [hfilt j, Finset.card_image_of_injective _ hemb]
  have htheta : ghMidPSlotTheta subN pref (I.image emb) = ghMidPSlotTheta subN pref' I := by
    funext j
    unfold ghMidPSlotTheta
    rw [hocc j]
  have hinit :
      ghMidPInitCoeff subN pref (I.image emb) kInit = ghMidPInitCoeff subN pref' I kInit := by
    funext A
    unfold ghMidPInitCoeff
    rw [himg, htheta]
  have hdamp (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) :
      ghMidPDampCoeff (I.image emb).card pr coeff = ghMidPDampCoeff I.card pr coeff := by
    funext A
    unfold ghMidPDampCoeff
    rw [hcard]
  have hnext (pr : GHMidPProbe) (coeff : Finset (Fin m) → ℂ) :
      ghMidPProbeNextCoeff subN pref (I.image emb) pr coeff =
        ghMidPProbeNextCoeff subN pref' I pr coeff := by
    unfold ghMidPProbeNextCoeff
    rw [himg, htheta, hdamp]
  have hclick : ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      ghMidPChainClickProb subN pref (I.image emb) ps coeff =
        ghMidPChainClickProb subN pref' I ps coeff := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons pr rest ih =>
      intro coeff
      dsimp only [ghMidPChainClickProb]
      rw [himg, hcard, hnext, ih]
  have hextra : ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      ghMidPChainExtraQ subN pref (I.image emb) ps coeff =
        ghMidPChainExtraQ subN pref' I ps coeff := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons pr rest ih =>
      intro coeff
      dsimp only [ghMidPChainExtraQ]
      rw [himg, hdamp, hnext, ih]
  have hfinal : ∀ (ps : List GHMidPProbe) (coeff : Finset (Fin m) → ℂ),
      ghMidPChainFinalCoeff subN pref (I.image emb) ps coeff =
        ghMidPChainFinalCoeff subN pref' I ps coeff := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons pr rest ih =>
      intro coeff
      dsimp only [ghMidPChainFinalCoeff]
      rw [hnext, ih]
  have hw (A : Finset (Fin m)) :
      ghMidPChoiceWeight pref (I.image emb) A = ghMidPChoiceWeight pref' I A := by
    unfold ghMidPChoiceWeight
    exact Finset.prod_congr rfl fun j _ ↦ by rw [hocc j]
  let mc (c : Fin m → Option α) : Fin m → Option β := fun j ↦ (c j).map emb
  have hmc_inj : Function.Injective mc := fun c₁ c₂ heq ↦ funext fun j ↦ by
    have hj := congrFun heq j
    cases h1 : c₁ j <;> cases h2 : c₂ j
    · rfl
    · dsimp only [mc] at hj; rw [h1, h2] at hj; cases hj
    · dsimp only [mc] at hj; rw [h1, h2] at hj; cases hj
    · dsimp only [mc] at hj; rw [h1, h2] at hj
      exact congrArg Option.some (hemb (Option.some.inj hj))
  have hcs (c : Fin m → Option α) : ghMidPChoiceSet (mc c) = (ghMidPChoiceSet c).image emb := by
    ext y
    simp only [ghMidPChoiceSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨j, hj⟩
      cases hcj : c j with
      | none =>
        have hm : mc c j = none := by simp [mc, hcj]
        rw [hm] at hj
        exact False.elim (Finset.notMem_empty y hj)
      | some a =>
        have hm : mc c j = some (emb a) := by simp [mc, hcj]
        rw [hm, Finset.mem_singleton] at hj
        refine ⟨a, ⟨j, ?_⟩, hj.symm⟩
        rw [hcj]
        exact Finset.mem_singleton_self a
    · rintro ⟨a, ⟨j, hj⟩, rfl⟩
      cases hcj : c j with
      | none =>
        rw [hcj] at hj
        exact False.elim (Finset.notMem_empty a hj)
      | some a' =>
        rw [hcj, Finset.mem_singleton] at hj
        subst hj
        refine ⟨j, ?_⟩
        have hm : mc c j = some (emb a) := by simp [mc, hcj]
        rw [hm]
        exact Finset.mem_singleton_self (emb a)
  have hhits (A : Finset (Fin m)) :
      ghMidPHitChoices pref (I.image emb) A = (ghMidPHitChoices pref' I A).image mc := by
    classical
    ext d
    simp only [Finset.mem_image]
    constructor
    · intro hd
      have hd_pi := Fintype.mem_piFinset.mp hd
      have hex (j : Fin m) (hj : j ∈ A) :
          ∃ a ∈ I.filter (fun i ↦ pref' i = j), some (emb a) = d j := by
        have hmj := hd_pi j
        rw [ite_eq_left hj, hfilt j] at hmj
        rcases Finset.mem_image.mp hmj with ⟨y, hy, hyd⟩
        rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
        exact ⟨a, ha, hyd⟩
      let c : Fin m → Option α := fun j ↦
        if hj : j ∈ A then some (Classical.choose (hex j hj)) else none
      refine ⟨c, Fintype.mem_piFinset.mpr fun j ↦ ?_, funext fun j ↦ ?_⟩
      · by_cases hj : j ∈ A
        · rw [ite_eq_left hj]
          have hc_j : c j = some (Classical.choose (hex j hj)) := dite_eq_left hj
          rw [hc_j]
          exact Finset.mem_image_of_mem Option.some (Classical.choose_spec (hex j hj)).1
        · rw [ite_eq_right hj]
          have hc_j : c j = none := dite_eq_right hj
          rw [hc_j]
          exact Finset.mem_singleton_self none
      · by_cases hj : j ∈ A
        · have hc_j : c j = some (Classical.choose (hex j hj)) := dite_eq_left hj
          dsimp only [mc]
          rw [hc_j, Option.map_some]
          exact (Classical.choose_spec (hex j hj)).2
        · have hc_j : c j = none := dite_eq_right hj
          have hmj := hd_pi j
          rw [ite_eq_right hj, Finset.mem_singleton] at hmj
          dsimp only [mc]
          rw [hc_j, hmj, Option.map_none]
    · rintro ⟨c, hc, rfl⟩
      have hc_pi := Fintype.mem_piFinset.mp hc
      refine Fintype.mem_piFinset.mpr fun j ↦ ?_
      have hmj := hc_pi j
      by_cases hj : j ∈ A
      · rw [ite_eq_left hj] at hmj ⊢
        rcases Finset.mem_image.mp hmj with ⟨a, ha, hca⟩
        dsimp only [mc]
        rw [← hca, Option.map_some, hfilt j]
        exact Finset.mem_image_of_mem Option.some (Finset.mem_image_of_mem emb ha)
      · rw [ite_eq_right hj] at hmj ⊢
        dsimp only [mc]
        rw [Finset.mem_singleton.mp hmj, Option.map_none]
        exact Finset.mem_singleton_self none
  unfold ghMidPBaseStep
  change (if true = true then ((kInit + 1 : ℕ) : ℝ) +
      ghMidPChainExtraQ subN pref (I.image emb) probes
        (ghMidPInitCoeff subN pref (I.image emb) kInit)
    else 0) +
    ghMidPChainClickProb subN pref (I.image emb) probes
      (ghMidPInitCoeff subN pref (I.image emb) kInit) * Ψ ∅ +
    ∑ A ∈ ((I.image emb).image pref).powerset,
      normSq (ghMidPChainFinalCoeff subN pref (I.image emb) probes
        (ghMidPInitCoeff subN pref (I.image emb) kInit) A) *
        ∑ d ∈ ghMidPHitChoices pref (I.image emb) A,
          ghMidPChoiceWeight pref (I.image emb) A * Ψ (I.image emb \ ghMidPChoiceSet d) = _
  simp only [↓reduceIte]
  rw [hinit, hextra, hclick, hfinal, himg, Finset.image_empty]
  congr 1
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  congr 1
  rw [hhits A, Finset.sum_image (fun _ _ _ _ h ↦ hmc_inj h), hw A]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [hcs c, ghMidP_image_sdiff_of_inj hemb]
private lemma ghMidPSubsetStep_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {m : ℕ}
    (subN p : ℕ) {emb : α → β} (hemb : Function.Injective emb)
    (pref : β → Fin m) (spec_fn : ℕ → GHMidPSpec) (Ψ : Finset β → ℝ) (I : Finset α) :
    ghMidPSubsetStep subN p pref true spec_fn Ψ (I.image emb) =
      ghMidPSubsetStep subN p (fun i ↦ pref (emb i)) true spec_fn
        (fun I' ↦ Ψ (I'.image emb)) I := by
  have hcard : (I.image emb).card = I.card := Finset.card_image_of_injective I hemb
  unfold ghMidPSubsetStep
  rw [hcard]
  cases spec_fn I.card with
  | none => rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    by_cases hcond : 2 ≤ I.card ∧ I.card ≤ 16 ∧ I.card - 1 < m
    · rw [ite_eq_left hcond, ite_eq_left hcond,
        ghMidPBaseStep_image_of_inj subN hemb pref kInit probes _ I]
      refine ghMidPBaseStep_congr_on_subset _ _ _ _ _ fun I' _ ↦ ?_
      unfold ghMidPZoomPost
      dsimp only
      rw [Finset.card_image_of_injective I' hemb, Finset.image_empty,
        ghMidP_image_sdiff_of_inj hemb, ghMidP_image_comp emb pref (I \ I'),
        ghMidP_image_comp emb pref I']
    · rw [ite_eq_right hcond, ite_eq_right hcond]
private lemma ghMidPSubsetDP_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {W m : ℕ}
    (subN p : ℕ) {emb : α → β} (hemb : Function.Injective emb)
    (slices : β → Fin W → Fin m)
    (passes : List (Fin W × (ℕ → GHMidPSpec)))
    (Ψ : Finset β → ℝ) (I : Finset α) :
    ghMidPSubsetDP subN p slices passes Ψ (I.image emb) =
      ghMidPSubsetDP subN p (fun i t ↦ slices (emb i) t) passes
        (fun I' ↦ Ψ (I'.image emb)) I := by
  induction passes generalizing I with
  | nil => rfl
  | cons ps rest ih =>
    rcases ps with ⟨t, spec_fn⟩
    dsimp only [ghMidPSubsetDP]
    rw [ghMidPSubsetStep_image_of_inj subN p hemb (fun y ↦ slices y t) spec_fn _ I]
    exact ghMidPSubsetStep_congr_on_subset _ _ _ _ _ fun I' _ ↦ ih I'
lemma ghMidPExactOneDimStep_mono_on (subN p m : ℕ)
    (spec_fn : ℕ → GHMidPSpec) {g₁ g₂ : ℕ → ℝ} {r : ℕ} (hg : ∀ u ≤ r, g₁ u ≤ g₂ u) :
    ghMidPExactOneDimStep subN p m spec_fn g₁ r ≤
      ghMidPExactOneDimStep subN p m spec_fn g₂ r := by
  unfold ghMidPExactOneDimStep
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun _ _ ↦ ?_)
    (pow_nonneg (Nat.cast_nonneg m) r)
  unfold ghMidPSubsetStep
  cases spec_fn (Finset.univ : Finset (Fin r)).card with
  | none =>
    simp only [Finset.card_univ, Fintype.card_fin]
    exact hg r le_rfl
  | some kpz =>
    rcases kpz with ⟨_, _, _⟩
    dsimp only
    split_ifs
    · unfold ghMidPBaseStep
      refine add_le_add (add_le_add le_rfl ?_) (Finset.sum_le_sum fun _ _ ↦
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left ?_ (ghMidPChoiceWeight_nonneg _ _ _))
          (Complex.normSq_nonneg _))
      · refine mul_le_mul_of_nonneg_left ?_ (ghMidPChainClickProb_nonneg _ _ _ _ _)
        unfold ghMidPZoomPost
        simp only [Finset.card_empty, ↓reduceIte]
        exact hg 0 (Nat.zero_le r)
      · unfold ghMidPZoomPost
        simp only [↓reduceIte]
        have hle_r : ((Finset.univ : Finset (Fin r)) \ ghMidPChoiceSet c).card ≤ r :=
          (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
        split_ifs
        · refine add_le_add le_rfl (add_le_add ?_ ?_)
          · exact mul_le_mul_of_nonneg_left (hg 0 (Nat.zero_le r)) (sq_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hg _ hle_r)
              (sub_nonneg.mpr (Real.sin_sq_le_one _))
        · exact add_le_add le_rfl (hg _ hle_r)
        · exact hg _ hle_r
    · simp only [Finset.card_univ, Fintype.card_fin]
      exact hg r le_rfl
lemma ghMidPExactOneDimDP_mono_on (subN p m : ℕ) :
    ∀ (specs : List (ℕ → GHMidPSpec)) {v₁ v₂ : ℕ → ℝ} {k : ℕ},
      (∀ u ≤ k, v₁ u ≤ v₂ u) →
      ∀ r ≤ k, ghMidPExactOneDimDP subN p m specs v₁ r ≤
        ghMidPExactOneDimDP subN p m specs v₂ r
  | [], _, _, _, hv, r, hr => hv r hr
  | spec_fn :: rest, _, _, _, hv, _r, hr =>
      ghMidPExactOneDimStep_mono_on subN p m spec_fn
        (fun u hu ↦ ghMidPExactOneDimDP_mono_on subN p m rest hv u (hu.trans hr))
private lemma sum_ghMidPSubsetStep_of_card_eq {k m : ℕ} (hm1 : 1 ≤ m) (subN p : ℕ)
    (spec_fn : ℕ → GHMidPSpec) (g : ℕ → ℝ) (I : Finset (Fin k)) :
    (∑ f_t : Fin k → Fin m,
      ghMidPSubsetStep subN p f_t true spec_fn (fun I' ↦ g I'.card) I) =
      ((m : ℝ) ^ k) * ghMidPExactOneDimStep subN p m spec_fn g I.card := by
  classical
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set r := I.card
  have hmr_ne : (m : ℝ) ^ r ≠ 0 := (pow_pos hm_pos r).ne'
  let eI : Fin r ≃ I := (Finset.equivFinOfCardEq rfl).symm
  let emb : Fin r → Fin k := fun a ↦ (eI a).1
  have hemb : Function.Injective emb := fun a₁ a₂ h ↦ eI.injective (Subtype.ext h)
  have himg_univ : (Finset.univ : Finset (Fin r)).image emb = I := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ (eI a).2, fun hx ↦ ⟨eI.symm ⟨x, hx⟩, by simp [emb]⟩⟩
  have hrew_ft (f_t : Fin k → Fin m) :
      ghMidPSubsetStep subN p f_t true spec_fn (fun J ↦ g J.card) I =
        ghMidPSubsetStep subN p (fun a ↦ f_t (emb a)) true spec_fn (fun A ↦ g A.card)
          Finset.univ := by
    conv_lhs => rw [← himg_univ]
    rw [ghMidPSubsetStep_image_of_inj subN p hemb f_t spec_fn (fun J ↦ g J.card) Finset.univ]
    refine ghMidPSubsetStep_congr_on_subset _ _ _ _ _ fun A _ ↦ ?_
    rw [Finset.card_image_of_injective A hemb]
  simp_rw [hrew_ft]
  let splitI : (Fin k → Fin m) ≃ (Fin r → Fin m) × ({i : Fin k // i ∉ I} → Fin m) :=
    { toFun := fun f_t ↦ (fun a ↦ f_t (eI a), fun b ↦ f_t b.1)
      invFun := fun q i ↦ if hi : i ∈ I then q.1 (eI.symm ⟨i, hi⟩) else q.2 ⟨i, hi⟩
      left_inv := fun f_t ↦ funext fun i ↦ by by_cases hi : i ∈ I <;> simp [hi]
      right_inv := fun ⟨_, _⟩ ↦ Prod.ext
        (funext fun a ↦ by simp [(eI a).2])
        (funext fun b ↦ by simp [b.2]) }
  have hcard_r :
      (m : ℝ) ^ k = (m : ℝ) ^ r * (Fintype.card ({i : Fin k // i ∉ I} → Fin m) : ℝ) := by
    have hc := Fintype.card_congr splitI
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
      Nat.cast_mul, Nat.cast_pow] using congrArg (Nat.cast (R := ℝ)) hc
  have hcomp_eq (h : Fin r → Fin m) (hc : {i : Fin k // i ∉ I} → Fin m) :
      (fun a ↦ splitI.symm (h, hc) (emb a)) = h := by
    funext a
    dsimp only [splitI, emb, Equiv.coe_fn_symm_mk]
    rw [dite_eq_left (eI a).2]
    simp
  rw [← splitI.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [hcomp_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    hcard_r, ghMidPExactOneDimStep]
  field_simp [hmr_ne]
private lemma ghMidPSubsetDP_congr_slices {α : Type*} [DecidableEq α] {W m : ℕ} (subN p : ℕ)
    {s₁ s₂ : α → Fin W → Fin m}
    (passes : List (Fin W × (ℕ → GHMidPSpec)))
    (hs : ∀ ps ∈ passes, ∀ x : α, s₁ x ps.1 = s₂ x ps.1)
    (Ψ : Finset α → ℝ) (R : Finset α) :
    ghMidPSubsetDP subN p s₁ passes Ψ R = ghMidPSubsetDP subN p s₂ passes Ψ R := by
  induction passes generalizing R with
  | nil => rfl
  | cons ps rest ih =>
    rcases ps with ⟨t, spec_fn⟩
    have ht : (fun x ↦ s₁ x t) = (fun x ↦ s₂ x t) :=
      funext fun x ↦ hs (t, spec_fn) List.mem_cons_self x
    dsimp only [ghMidPSubsetDP]
    rw [ht]
    exact ghMidPSubsetStep_congr_on_subset _ _ _ _ _ fun R' _ ↦
      ih (fun q hq x ↦ hs q (List.mem_cons_of_mem _ hq) x) R'
private lemma sum_fintype_ghMidPBaseStep {α β : Type*} [DecidableEq α] [Fintype β] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHMidPProbe)
    (F : β → Finset α → ℝ) (G : Finset α → ℝ) (I : Finset α)
    (hFG : ∀ I' ⊆ I, (∑ fr : β, F fr I') = (Fintype.card β : ℝ) * G I') :
    (∑ fr : β, ghMidPBaseStep subN pref true kInit probes (F fr) I) =
      (Fintype.card β : ℝ) * ghMidPBaseStep subN pref true kInit probes G I := by
  unfold ghMidPBaseStep
  simp only [↓reduceIte]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hFG ∅ (Finset.empty_subset I), Finset.sum_comm]
  have hA_sum (A : Finset (Fin m)) :
      (∑ fr : β,
        normSq (ghMidPChainFinalCoeff subN pref I probes
          (ghMidPInitCoeff subN pref I kInit) A) *
          ∑ c ∈ ghMidPHitChoices pref I A,
            ghMidPChoiceWeight pref I A * F fr (I \ ghMidPChoiceSet c)) =
      (Fintype.card β : ℝ) *
        (normSq (ghMidPChainFinalCoeff subN pref I probes
          (ghMidPInitCoeff subN pref I kInit) A) *
          ∑ c ∈ ghMidPHitChoices pref I A,
            ghMidPChoiceWeight pref I A * G (I \ ghMidPChoiceSet c)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hc_sum (c : Fin m → Option α) :
        (∑ fr : β, ghMidPChoiceWeight pref I A * F fr (I \ ghMidPChoiceSet c)) =
          (Fintype.card β : ℝ) * (ghMidPChoiceWeight pref I A * G (I \ ghMidPChoiceSet c)) := by
      rw [← Finset.mul_sum, hFG (I \ ghMidPChoiceSet c) Finset.sdiff_subset]
      ring
    simp_rw [hc_sum, ← Finset.mul_sum]
    ring
  simp_rw [hA_sum, ← Finset.mul_sum]
  ring
private lemma sum_fintype_ghMidPSubsetStep {α β : Type*} [DecidableEq α] [Fintype β] {m : ℕ}
    (subN p : ℕ) (pref : α → Fin m) (spec_fn : ℕ → GHMidPSpec)
    (F : β → Finset α → ℝ) (G : Finset α → ℝ) (I : Finset α)
    (hFG : ∀ I' ⊆ I, (∑ fr : β, F fr I') = (Fintype.card β : ℝ) * G I') :
    (∑ fr : β, ghMidPSubsetStep subN p pref true spec_fn (F fr) I) =
      (Fintype.card β : ℝ) * ghMidPSubsetStep subN p pref true spec_fn G I := by
  unfold ghMidPSubsetStep
  cases spec_fn I.card with
  | none => exact hFG I Finset.Subset.rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    by_cases hcond : 2 ≤ I.card ∧ I.card ≤ 16 ∧ I.card - 1 < m
    · simp_rw [ite_eq_left hcond]
      refine sum_fintype_ghMidPBaseStep subN pref kInit probes _ _ I fun I' hI' ↦ ?_
      unfold ghMidPZoomPost
      by_cases h1 : I'.card = 1
      · simp_rw [ite_eq_left h1]
        simp only [↓reduceIte]
        by_cases hne : (((I \ I').image pref) ∩ (I'.image pref)).Nonempty
        · simp_rw [ite_eq_left hne]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            hFG ∅ (Finset.empty_subset I), hFG I' hI']
          ring
        · simp_rw [ite_eq_right hne]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            hFG I' hI']
          ring
      · simp_rw [ite_eq_right h1]
        exact hFG I' hI'
    · simp_rw [ite_eq_right hcond]
      exact hFG I Finset.Subset.rfl
lemma avg_ghMidPSubsetDP_eq_ghMidPExactOneDimDP {W m k : ℕ} (hm1 : 1 ≤ m) (subN p : ℕ)
    (passes : List (Fin W × (ℕ → GHMidPSpec)))
    (hnodup : (passes.map Prod.fst).Nodup)
    (V_tail : ℕ → ℝ) (I : Finset (Fin k)) :
    (∑ f : Fin k → Fin W → Fin m,
      ghMidPSubsetDP subN p f passes (fun I' ↦ V_tail I'.card) I) /
      (((m ^ W) ^ k : ℕ) : ℝ) =
      ghMidPExactOneDimDP subN p m (passes.map Prod.snd) V_tail I.card := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hMW_pos : (0 : ℝ) < (((m ^ W) ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (Nat.pow_pos (by omega : 0 < m))
  rw [div_eq_iff hMW_pos.ne']
  induction passes generalizing I with
  | nil =>
    simp [ghMidPSubsetDP, ghMidPExactOneDimDP, Finset.sum_const, nsmul_eq_mul, mul_comm]
  | cons head rest ih =>
    rcases head with ⟨t, spec_fn⟩
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨ht_notMem, hrest_nodup⟩
    let splitW : (Fin k → Fin W → Fin m) ≃
        (Fin k → Fin m) × (Fin k → {t' : Fin W // t' ≠ t} → Fin m) :=
      { toFun := fun f ↦ (fun i ↦ f i t, fun i t' ↦ f i t'.1)
        invFun := fun q i t' ↦ if h : t' = t then q.1 i else q.2 i ⟨t', h⟩
        left_inv := fun f ↦ funext fun i ↦ funext fun t' ↦ by by_cases h : t' = t <;> simp [h]
        right_inv := fun ⟨_, _⟩ ↦ Prod.ext (funext fun i ↦ by simp)
          (funext fun i ↦ funext fun t' ↦ by simp [t'.2]) }
    let RestType := Fin k → {t' : Fin W // t' ≠ t} → Fin m
    have hcard_Wr : (((m ^ W) ^ k : ℕ) : ℝ) = ((m : ℝ) ^ k) * (Fintype.card RestType : ℝ) := by
      have hcard_W : Fintype.card (Fin k → Fin W → Fin m) =
          Fintype.card (Fin k → Fin m) * Fintype.card RestType := by
        rw [Fintype.card_congr splitW, Fintype.card_prod]
      have hlhs : Fintype.card (Fin k → Fin W → Fin m) = (m ^ W) ^ k := by simp [Fintype.card_fin]
      have hm_k : Fintype.card (Fin k → Fin m) = m ^ k := by simp [Fintype.card_fin]
      rw [hlhs, hm_k] at hcard_W
      have hr := congrArg (Nat.cast (R := ℝ)) hcard_W
      rw [Nat.cast_mul, Nat.cast_pow m k] at hr
      exact hr
    let f₀ : Fin k → Fin m := fun _ ↦ ⟨0, by omega⟩
    have hrest_indep (ft : Fin k → Fin m) (fr : RestType) (I' : Finset (Fin k)) :
        ghMidPSubsetDP subN p (splitW.symm (ft, fr)) rest (fun J ↦ V_tail J.card) I' =
          ghMidPSubsetDP subN p (splitW.symm (f₀, fr)) rest (fun J ↦ V_tail J.card) I' := by
      refine ghMidPSubsetDP_congr_slices subN p rest (fun q hq i ↦ ?_) _ I'
      have hne : q.1 ≠ t := fun heq ↦ ht_notMem (heq ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)
      dsimp only [splitW, Equiv.coe_fn_symm_mk]
      simp [hne]
    let g_rest : ℕ → ℝ := ghMidPExactOneDimDP subN p m (rest.map Prod.snd) V_tail
    have hsum_fr (I' : Finset (Fin k)) :
        (∑ fr : RestType,
          ghMidPSubsetDP subN p (splitW.symm (f₀, fr)) rest (fun J ↦ V_tail J.card) I') =
          (Fintype.card RestType : ℝ) * g_rest I'.card := by
      have hih := ih hrest_nodup I'
      rw [← splitW.symm.sum_comp, Fintype.sum_prod_type] at hih
      simp_rw [hrest_indep] at hih
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, hcard_Wr] at hih
      exact mul_left_cancel₀ (pow_pos hm_pos k).ne' (by dsimp only [g_rest]; linarith)
    dsimp only [ghMidPSubsetDP, List.map, ghMidPExactOneDimDP]
    rw [← splitW.symm.sum_comp, Fintype.sum_prod_type]
    have hhead_t (ft : Fin k → Fin m) (fr : RestType) :
        (fun i : Fin k ↦ splitW.symm (ft, fr) i t) = ft := by
      funext i
      dsimp only [splitW, Equiv.coe_fn_symm_mk]
      simp
    have hinner (ft : Fin k → Fin m) :
        (∑ fr : RestType,
          ghMidPSubsetStep subN p (fun i ↦ splitW.symm (ft, fr) i t) true spec_fn
            (ghMidPSubsetDP subN p (splitW.symm (ft, fr)) rest (fun J ↦ V_tail J.card)) I) =
          (Fintype.card RestType : ℝ) *
            ghMidPSubsetStep subN p ft true spec_fn (fun I' ↦ g_rest I'.card) I := by
      simp_rw [hhead_t ft]
      refine sum_fintype_ghMidPSubsetStep subN p ft spec_fn _ _ I fun I' _ ↦ ?_
      simp_rw [hrest_indep ft _ I']
      exact hsum_fr I'
    rw [Finset.sum_congr rfl fun ft _ ↦ hinner ft, ← Finset.mul_sum,
      sum_ghMidPSubsetStep_of_card_eq hm1 subN p spec_fn g_rest I, hcard_Wr]
    dsimp only [g_rest]
    ring
lemma avg_ghMidPSubsetDP_mkGoodTargetSet_eq {n s W m k : ℕ}
    (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)) (hm1 : 1 ≤ m) (subN p : ℕ)
    (passes : List (Fin W × (ℕ → GHMidPSpec)))
    (hnodup : (passes.map Prod.fst).Nodup)
    (V_tail : ℕ → ℝ) (U : Finset (Fin (2 ^ s))) (hU : U.card = k) :
    (∑ f : Fin k → Fin W → Fin m,
      ghMidPSubsetDP subN p (slicesOf e) passes
        (fun R' ↦ V_tail R'.card) (mkGoodTargetSet e U hU f)) /
      (((m ^ W) ^ k : ℕ) : ℝ) =
      ghMidPExactOneDimDP subN p m (passes.map Prod.snd) V_tail k := by
  have heq (f : Fin k → Fin W → Fin m) :
      ghMidPSubsetDP subN p (slicesOf e) passes
          (fun R' ↦ V_tail R'.card) (mkGoodTargetSet e U hU f) =
        ghMidPSubsetDP subN p f passes (fun I' ↦ V_tail I'.card) Finset.univ := by
    let emb : Fin k → Fin (2 ^ n) := fun i ↦ e.symm (U.orderEmbOfFin hU i, f i)
    have hemb : Function.Injective emb := fun i₁ i₂ h ↦
      (U.orderEmbOfFin hU).injective (congrArg Prod.fst (e.symm.injective h))
    have hslices : (fun i t ↦ slicesOf e (emb i) t) = f := by
      funext i t
      simp [slicesOf, emb]
    have hcard (I' : Finset (Fin k)) : (I'.image emb).card = I'.card :=
      Finset.card_image_of_injective I' hemb
    unfold mkGoodTargetSet
    change ghMidPSubsetDP subN p (slicesOf e) passes _ (Finset.univ.image emb) = _
    rw [ghMidPSubsetDP_image_of_inj subN p hemb (slicesOf e) passes _ Finset.univ, hslices]
    simp_rw [hcard]
  simp_rw [heq]
  simpa using avg_ghMidPSubsetDP_eq_ghMidPExactOneDimDP hm1 subN p passes hnodup V_tail Finset.univ
end
end QuantumComputation.Specs.DickeSol
end GHMidPFibersQHL

section GHMidPZoomQHLInlined
namespace QuantumComputation.Specs.DickeSol
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QProg.Notation QHLExpectation
open Operator ResourceCounting Real
open QProg (qAssign)
open OracleDynamicCircuit (compile sequence sequence_cons compile_seq)
open QRegister (basisBits_extractIndex embedUnitary_val tensorState basisSplitEquiv_apply_fst)
open Matrix (diagonal mulVec_mulVec mulVec_diagonal of_apply mul_apply conjTranspose_apply)
open Complex (normSq ofReal_sum ofReal_zero ofReal_mul normSq_zero normSq_ofReal ofReal_re)
open List (finRange map_cons mem_finRange prod_cons replicate mem_toFinset mem_cons_self)
open Fintype (sum_eq_single sum_prod_type card_fin)
open Pi (single single_eq_of_ne)
open Finset (mem_univ sum_congr prod_congr sum_add_distrib sum_sub_distrib prod_eq_zero sum_ite_mem
  mem_filter mem_image mem_union mem_singleton mem_inter mem_sdiff mem_erase sum_ite_eq' mem_product
  card_image_le sum_mul mul_sum sum_const univ_inter card_univ card_pos sum_eq_zero)
@[expose] public section
private lemma iL0 {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {a b : α} :
    (if c then a else b) = a := ite_eq_left hc
private lemma iR0 {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort*} {a b : α} :
    (if c then a else b) = b := ite_eq_right hc
private lemma sA0 {α β : Sort*} (e : α ≃ β) (b : β) : e (e.symm b) = b := Equiv.apply_symm_apply e b
private lemma gA0 {n m b g : ℕ} (hbg : b * g = m) (w : Fin (2 ^ (m * (n + 1)))) (c : Fin b) :
    groupSplitEquiv hbg w c = (groupReg hbg c).extractIndex w := groupSplitEquiv_apply hbg w c
/- ## 1. Real Householder Reflection and Subset Grover Recurrence on `Fin N` -/
/-- Real rank-`1` Householder reflection `2 |v⟩⟨v| - I` as a complex `N × N` matrix. -/
def midpReflRealMat {N : ℕ} (v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun x y ↦ (((2 * v x * v y - if x = y then 1 else 0) : ℝ) : ℂ)
lemma midpReflRealMat_conjTranspose {N : ℕ} (v : Fin N → ℝ) : (midpReflRealMat v)ᴴ = midpReflRealMat
  v := Matrix.ext fun x y ↦ by simp only [conjTranspose_apply, midpReflRealMat, of_apply,
  RCLike.star_def, Complex.conj_ofReal]; congr 1; exact if h : y = x then (by subst h; ring) else
                                (by simp only [h, Ne.symm h, ↓reduceIte]; ring)
lemma midpReflRealMat_mul_self {N : ℕ} {v : Fin N → ℝ} (hv : ∑ x, v x * v x = 1) : midpReflRealMat v
  * midpReflRealMat v = 1 := by
  ext x z; simp only [mul_apply, midpReflRealMat, of_apply, ← ofReal_mul, ← ofReal_sum,
  Matrix.one_apply]; have r : (∑ y : Fin N, (2 * v x * v y - if x = y then 1 else 0) * (2 * v y * v
  z - if y = z then 1 else 0)) = if x = z then (1 : ℝ) else 0 := (by
  have e (y) : (2 * v x * v y - if x = y then 1 else 0) * (2 * v y * v z - if y = z then 1 else 0) =
   4 * v x * v z * (v y * v y) - (if y = x then 2 * v x * v z else 0) - (if y = z then 2 * v x * v z
  else 0) + (if y = x then if x = z then (1 : ℝ) else 0 else 0) := if p : x = y then (by
  subst p; by_cases q : x = z <;> simp only [q, ↓reduceIte] <;> ring) else (by
  simp only [p, Ne.symm p, ↓reduceIte]; by_cases q : y = z <;> simp only [q, ↓reduceIte] <;> ring);
  simp_rw [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hv]; simp only [sum_ite_eq', mem_univ,
  ↓reduceIte]; ring); rw [r]; by_cases p : x = z <;> simp [p]
/-- Bundled unitary `2 |v⟩⟨v| - I` for a unit real vector `v: Fin N → ℝ`. -/
def midpReflRealUnitary {N : ℕ} (v : Fin N → ℝ) (hv : ∑ x : Fin N, v x * v x = 1) : Unitary N :=
  ⟨midpReflRealMat v, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, midpReflRealMat_conjTranspose]
    exact midpReflRealMat_mul_self hv⟩
private lemma mp01 {N} (v w : Fin N → ℝ) : midpReflRealMat v *ᵥ (fun y ↦ (w y : ℂ)) = fun x ↦ (((2 *
  (∑ y, v y * w y) * v x - w x) : ℝ) : ℂ) := by
  funext x; simp only [Matrix.mulVec, dotProduct, midpReflRealMat, of_apply, ← ofReal_mul, ←
  ofReal_sum]; congr 1; simp [sub_mul, ite_mul, sum_sub_distrib, mul_assoc, ← mul_sum]; ring
/-- Normalized real uniform indicator vector `|G⟩` on `G: Finset (Fin N)`. -/
noncomputable def midpUnifRealVec {N : ℕ} (G : Finset (Fin N)) (x : Fin N) : ℝ :=
  if x ∈ G then 1 / √(G.card : ℝ) else 0
lemma sum_sq_midpUnifRealVec {N : ℕ} {G : Finset (Fin N)} (hG : G.Nonempty) : ∑ x : Fin N,
  midpUnifRealVec G x * midpUnifRealVec G x = 1 := by
  have c0 : (0 : ℝ) < G.card := Nat.cast_pos.2 hG.card_pos; have p (x) : midpUnifRealVec G x *
   midpUnifRealVec G x = if x ∈ G then 1 / (G.card : ℝ) else 0 := if hx : x ∈ G then (by
  simp only [midpUnifRealVec, hx, ↓reduceIte, div_mul_div_comm, one_mul, mul_self_sqrt c0.le]) else
   (by simp only [midpUnifRealVec, hx, ↓reduceIte, mul_zero]); simp_rw [p]; rw [sum_ite_mem,
  univ_inter, sum_const, nsmul_eq_mul, mul_one_div_cancel c0.ne']
/-- Positive-denominator unit bisector `(|G⟩ + |0⟩) / √(2 (1 + ⟨0|G⟩))` mapping `|0⟩ ↦ |G⟩`. -/
noncomputable def midpBisectRealVec {N : ℕ} [NeZero N] (G : Finset (Fin N)) (x : Fin N) : ℝ :=
  (midpUnifRealVec G x + if x = 0 then 1 else 0) / √(2 * (1 + midpUnifRealVec G 0))
lemma sum_sq_midpBisectRealVec {N : ℕ} [NeZero N] {G : Finset (Fin N)} (hG : G.Nonempty) : ∑ x : Fin
  N, midpBisectRealVec G x * midpBisectRealVec G x = 1 := by
  set d : ℝ := 2 * (1 + midpUnifRealVec G 0); have d0 : 0 < d := (
  by dsimp only [d]; linarith [(show 0 ≤ midpUnifRealVec G 0
  by unfold midpUnifRealVec; split_ifs <;> positivity)]); have p (x : Fin N) : midpBisectRealVec G x
   * midpBisectRealVec G x = (midpUnifRealVec G x * midpUnifRealVec G x + if x = 0 then 2 *
   midpUnifRealVec G 0 + 1 else 0) / d := (by
  dsimp only [midpBisectRealVec]; rw [div_mul_div_comm, mul_self_sqrt d0.le]; congr 1; exact if hx :
   x = 0 then (by subst hx; simp only [↓reduceIte]; ring) else (by simp [hx])); simp_rw [p, ←
  Finset.sum_div, sum_add_distrib, sum_sq_midpUnifRealVec hG]; simp only [sum_ite_eq', mem_univ,
  ↓reduceIte];
  rw [(by dsimp only [d]; ring : 1 + (2 * midpUnifRealVec G 0 + 1) = d), div_self d0.ne']
/-- Real amplitude vector inside `G ⊆ Fin N` after `t` Householder Grover steps for `A`. -/
noncomputable def midpAddrGroverReal {N : ℕ} (G A : Finset (Fin N)) : ℕ → Fin N → ℝ
  | 0, x => midpUnifRealVec G x
  | t + 1, x =>
      let prev := fun y ↦ (if y ∈ A then (-1 : ℝ) else 1) * midpAddrGroverReal G A t y
      2 * (∑ y : Fin N, midpUnifRealVec G y * prev y) * midpUnifRealVec G x - prev x
/- ## 2. Middle-`p` `3`-Block Slice Domain and Cardinality -/
private def mp02 (n) : Fin (2 ^ (1 * n)) ≃ Fin (2 ^ n) := finCongr (by rw [Nat.one_mul])
private lemma mp03 {n} (v : Fin (2 ^ (1 * n))) : addrEquiv n 1 v 0 = mp02 n v := Fin.ext (by
  rw [addrEquiv_eq_div_pow_mod, mp02, finCongr_apply, Fin.val_cast]; simp only [Fin.val_zero,
  pow_zero, Nat.div_one]; exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using v.isLt))
lemma midp_p_le_sub {n p : ℕ} (h2p : 2 * p ≤ n) : p ≤ n - p := by omega
lemma midp_sub_sub_eq (n p : ℕ) : (n - p) - p = n - 2 * p := by omega
/-- Middle `p`-bit subcube prefix `Fin m` of `y: Fin (2 ^ n)` (bits `[n - 2 * p, n - p)`). -/
noncomputable def midpMidPref {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
    (y : Fin (2 ^ n)) : Fin m :=
  subcubePref (midp_p_le_sub h2p) hm (subcubeSplit hp hm y).1
/-- Per-slot middle-`p` zoom address slice `{u | topPref(perm u) ∈ L ∧ midPref(perm u) =
  s}`. -/
noncomputable def midpSliceSet {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) (L : Finset (Fin m)) (s : Fin m) :
    Finset (Fin (2 ^ (1 * n))) :=
  Finset.univ.filter fun u : Fin (2 ^ (1 * n)) ↦
    let y := perm (addrEquiv n 1 u 0); subcubePref hp hm y ∈ L ∧ midpMidPref hp hm h2p y = s
/-- Exact cardinality `L.card * 2 ^ (n - 2 * p)` of every slot's middle-`p` zoom slice. -/
lemma card_midpSliceSet {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm :
  Equiv.Perm (Fin (2 ^ n))) (L : Finset (Fin m)) (s : Fin m) : (midpSliceSet hp hm h2p perm L
  s).card = L.card * 2 ^ (n - 2 * p) := by
  let s1 := subcubeSplit hp hm; let s2 := subcubeSplit (midp_p_le_sub h2p) hm; let fc := finCongr
   (congrArg (2 ^ ·) (midp_sub_sub_eq n p)); rw [Finset.card_bij (fun u _ ↦ let y := perm (addrEquiv
  n 1 u 0); (subcubePref hp hm y, fc (s2 (s1 y).1).1)) (fun u hu ↦ mem_product.2 ⟨(mem_filter.1
  hu).2.1, mem_univ _⟩) (fun u₁ h₁ u₂ h₂ h ↦ by
  rcases Prod.mk.inj h with ⟨hj, hw⟩; have q1 : (s2 (s1 (perm (addrEquiv n 1 u₁ 0))).1).2 = s := (by
  simpa only [midpMidPref, subcubePref] using (mem_filter.1 h₁).2.2); have q2 : (s2 (s1 (perm
  (addrEquiv n 1 u₂ 0))).1).2 = s := (by simpa only [midpMidPref, subcubePref] using (mem_filter.1
  h₂).2.2); have a := perm.injective (s1.injective (Prod.ext (s2.injective (Prod.ext (fc.injective
  hw) (q1.trans q2.symm))) hj)); rw [mp03, mp03] at a; exact (mp02 n).injective a) (fun ⟨j, w⟩ p0 ↦
  by let v := s2.symm (fc.symm w, s); let y := s1.symm (v, j); let u := (mp02 n).symm (perm.symm y);
     have hy : perm (addrEquiv n 1 u 0) = y := (by dsimp only [u]; rw [mp03, sA0, sA0]); exact ⟨u,
  mem_filter.2 ⟨mem_univ _, by rw [hy]; unfold subcubePref; dsimp only [y]; rw [sA0]; exact
                                (mem_product.1 p0).1, by rw [hy]; unfold midpMidPref subcubePref;
                                                         dsimp only [y, v]; rw [sA0, sA0]⟩, by
  dsimp only; rw [hy]; unfold subcubePref; dsimp only [y, v]; rw [sA0, sA0, sA0]⟩),
  Finset.card_product, card_univ, card_fin]
/-- Nonemptiness of `midpSliceSet` whenever `L` is nonempty. -/
lemma nonempty_midpSliceSet {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm :
  Equiv.Perm (Fin (2 ^ n))) {L : Finset (Fin m)} (hL : L.Nonempty) (s : Fin m) : (midpSliceSet hp hm
  h2p perm L s).Nonempty := card_pos.mp (by rw [card_midpSliceSet]; exact Nat.mul_pos hL.card_pos
                                             (Nat.two_pow_pos _))
/- ## 3. Single-Slot Unitaries, Grover State, and Readout QHL on `Fin (2 ^ (1 * (n + 1)))` -/
/-- `(1 * (n + 1))`-qubit slot preparation unitary mapping `|0⟩ ↦ |U⟩ ⊗ |0⟩` for
  `U.Nonempty`. -/
noncomputable def midpSlotPrep {n : ℕ} (U : Finset (Fin (2 ^ (1 * n)))) :
    Unitary (2 ^ (1 * (n + 1))) :=
  if hU : U.Nonempty then (addrReg n 1).embedUnitary
    (midpReflRealUnitary (midpBisectRealVec U) (sum_sq_midpBisectRealVec hU)) else 1
/-- `(1 * (n + 1))`-qubit slot Householder reflection `2 |U⟩⟨U| - I` on the address wires. -/
noncomputable def midpSlotDiffuser {n : ℕ} (U : Finset (Fin (2 ^ (1 * n)))) :
    Unitary (2 ^ (1 * (n + 1))) :=
  if hU : U.Nonempty then (addrReg n 1).embedUnitary
    (midpReflRealUnitary (midpUnifRealVec U) (sum_sq_midpUnifRealVec hU)) else 1
/-- `(1 * (n + 1))`-qubit slot state after `t` middle-`p` Householder Grover steps on `U`. -/
noncomputable def midpSlotGroverVec {n : ℕ} (U : Finset (Fin (2 ^ (1 * n))))
    (R' : Finset (Fin (2 ^ n))) (t : ℕ) : Fin (2 ^ (1 * (n + 1))) → ℂ :=
  (addrReg n 1).tensorState (fun u ↦ (midpAddrGroverReal U (oddSet n 1 R') t u : ℂ)) (single 0 1)
/-- Preparation unitary maps `|0⟩` to `midpSlotGroverVec U R' 0`. -/
lemma midpSlotPrep_mulVec_zero {n : ℕ} {U : Finset (Fin (2 ^ (1 * n)))} (hU : U.Nonempty) (R' :
  Finset (Fin (2 ^ n))) : (midpSlotPrep U).1 *ᵥ single (0 : Fin (2 ^ (1 * (n + 1)))) 1 =
  midpSlotGroverVec U R' 0 := by
  have h1 : (addrReg n 1).extractIndex 0 = 0 := (basisBits (1 * n)).injective (funext fun _ ↦ by
  simp [basisBits_extractIndex]); have h2 : ((addrReg n 1).basisSplitEquiv 0).2 = 0 := funext fun _
   ↦ (by simp [QRegister.basisSplitEquiv]); unfold midpSlotPrep midpSlotGroverVec; rw [dite_eq_left
  hU, embedUnitary_val, QRegister.embedMatrix_mulVec_single_factors, h1, h2]; change (addrReg n
  1).tensorState (midpReflRealMat (midpBisectRealVec U) *ᵥ single 0 1) (single 0 1) = _; refine
   congrArg ((addrReg n 1).tensorState · (single 0 1)) ?_; dsimp only [midpAddrGroverReal]; let z0
   (y : Fin (2 ^ (1 * n))) : ℝ := if y = 0 then 1 else 0; rw [(show (single 0 (1 : ℂ) : Fin (2 ^ (1
  * n)) → ℂ) = (fun y ↦ (z0 y : ℂ)) by funext y; dsimp only [z0]; by_cases h : y = 0 <;> simp [h]),
  mp01]; dsimp only [z0]; funext x; congr 1; set d : ℝ := 2 * (1 + midpUnifRealVec U 0);
  have d0 : 0 < d := (by
  dsimp only [d];
  linarith [(show 0 ≤ midpUnifRealVec U 0 by dsimp only [midpUnifRealVec]; split_ifs <;>
                                                 positivity)]); rw [(show (∑ y, midpBisectRealVec U
  y * if y = 0 then 1 else 0) = midpBisectRealVec U 0 by simp [mul_ite])]; dsimp only
   [midpBisectRealVec]; simp only [↓reduceIte];
   rw [(show 2 * ((midpUnifRealVec U 0 + 1) / √d) * ((midpUnifRealVec U x + if
  x = 0 then 1 else 0) / √d) = (2 * (midpUnifRealVec U 0 + 1) * (midpUnifRealVec U x + if x =
  0 then 1 else 0)) / d by
  rw [mul_assoc, div_mul_div_comm, mul_self_sqrt d0.le];
  ring), (show 2 * (midpUnifRealVec U 0 + 1) = d by
  dsimp only [d]; ring), mul_div_cancel_left₀ _ d0.ne']; ring
/-- One phase-oracle + Householder-diffuser step advances `midpSlotGroverVec` to `t + 1`. -/
lemma midpSlotDiffuser_mulVec_sDiagM {n : ℕ} {U : Finset (Fin (2 ^ (1 * n)))} (hU : U.Nonempty) (R'
  : Finset (Fin (2 ^ n))) (t : ℕ) : (midpSlotDiffuser U).1 *ᵥ (sDiagM n 1 R' *ᵥ midpSlotGroverVec U
  R' t) = midpSlotGroverVec U R' (t + 1) := by
  have horac : oracleMat (oddSet n 1 R') *ᵥ (fun u ↦ (midpAddrGroverReal U (oddSet n 1 R') t u : ℂ))
  = fun u ↦
   (((if u ∈ oddSet n 1 R' then (-1 : ℝ) else 1) *
   midpAddrGroverReal U (oddSet n 1 R') t u : ℝ) : ℂ) := (by
  funext u; rw [oracleMat, mulVec_diagonal]; by_cases hu : u ∈ oddSet n 1 R' <;> simp [hu]); unfold
   midpSlotDiffuser midpSlotGroverVec; rw [dite_eq_left hU, sDiagM_mulVec_tensorState_zero, horac,
  embedUnitary_val, QRegister.embedMatrix_mulVec_tensorState]; change (addrReg n 1).tensorState
   (midpReflRealMat (midpUnifRealVec U) *ᵥ fun u ↦ (((if u ∈ oddSet n 1 R' then (-1 : ℝ) else 1) *
   midpAddrGroverReal U (oddSet
  n 1 R') t u : ℝ) : ℂ)) (single 0 1) = _; rw [mp01]; rfl
/-- Unit-norm preservation of `midpSlotGroverVec U R' t` for any `U.Nonempty`. -/
lemma sum_normSq_midpSlotGroverVec {n : ℕ} {U : Finset (Fin (2 ^ (1 * n)))} (hU : U.Nonempty) (R' :
  Finset (Fin (2 ^ n))) (t : ℕ) : (∑ z : Fin (2 ^ (1 * (n + 1))), normSq (midpSlotGroverVec U R' t
  z)) = 1 := by
  rw [← (addrReg n 1).basisSplitEquiv.symm.sum_comp, sum_prod_type]; set A := oddSet n 1 R'; have u1
   := sum_sq_midpUnifRealVec hU; have hf (u) : (∑ e, normSq (midpSlotGroverVec U R' t ((addrReg n
  1).basisSplitEquiv.symm (u, e)))) = midpAddrGroverReal U A t u * midpAddrGroverReal U A t u := (by
  rw [sum_eq_single 0 (fun e he ↦ by dsimp only [midpSlotGroverVec, tensorState, A]; rw [←
  basisSplitEquiv_apply_fst, sA0];
                                     dsimp only; rw [single_eq_of_ne he, mul_zero, normSq_zero])];
  dsimp only [midpSlotGroverVec, tensorState, A]; rw [← basisSplitEquiv_apply_fst, sA0]; dsimp only;
  rw [Pi.single_eq_same, mul_one, normSq_ofReal]); simp_rw [hf]; refine Nat.rec u1 (fun s ih ↦ ?_)
   t; rw [Nat.succ_eq_add_one]; set u := midpUnifRealVec U;
   set p := fun y ↦ (if y ∈ A then (-1 : ℝ) else 1) *
   midpAddrGroverReal U A s y; set c := ∑ y, u y * p y;
   have q : ∑ x, p x * p x = 1 := (sum_congr rfl fun x _ ↦ by
  dsimp only [p]; by_cases hx : x ∈ A <;> simp [hx]).trans ih;
  have e (x) : midpAddrGroverReal U A (s + 1) x * midpAddrGroverReal
   U A (s + 1) x = 4 * c ^ 2 * (u x * u x) - 4 * c * (u x * p x) + p x * p x := (by
  change (2 * c * u x - p x) * (2 * c * u x - p x) = _; ring); simp_rw [e, sum_add_distrib,
  sum_sub_distrib, ← mul_sum]; rw [(rfl : ∑ x, u x * p x = c)]; dsimp only [u]; rw [u1, q]; ring
/-- Every nonzero basis amplitude of `midpSlotGroverVec` has clean flag bit `0`. -/
lemma midpSlotGroverVec_flag_zero_of_ne_zero {n : ℕ} (U : Finset (Fin (2 ^ (1 * n)))) (R' : Finset
  (Fin (2 ^ n))) (t : ℕ) {z : Fin (2 ^ (1 * (n + 1)))} (hz : midpSlotGroverVec U R' t z ≠ 0) :
  ((addrReg n 1).basisSplitEquiv z).2 = 0 := Classical.byContradiction fun hne ↦ hz (by
  dsimp only [midpSlotGroverVec, tensorState]; rw [single_eq_of_ne hne, mul_zero])
private lemma fZ0 {n : ℕ} (U : Finset (Fin (2 ^ (1 * n))))
    (R' : Finset (Fin (2 ^ n))) (t : ℕ) {z : Fin (2 ^ (1 * (n + 1)))}
    (hz : midpSlotGroverVec U R' t z ≠ 0) :
    ((addrReg n 1).basisSplitEquiv z).2 = 0 := midpSlotGroverVec_flag_zero_of_ne_zero U R' t hz
/-- Exact singleton-target readout law on `midpSliceSet hp hm h2p perm L s` (`|R'| = 1`). -/
lemma midpSlotGroverVec_readout_singleton {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤
  n) (perm : Equiv.Perm (Fin (2 ^ n))) {L : Finset (Fin m)} (_hL : L.Nonempty) (x_last : Fin (2 ^
  n)) (s : Fin m) (t : ℕ) : let R' : Finset (Fin (2 ^ n)) := {x_last}
  let U := midpSliceSet hp hm h2p perm L s; (∀ z, midpSlotGroverVec U R' t z ≠ 0 → ((addrReg n
  1).basisSplitEquiv z).2 = 0) ∧ (¬ (subcubePref hp hm (perm x_last) ∈ L ∧ midpMidPref hp hm h2p
  (perm x_last) = s) → ∀ z, midpSlotGroverVec U R' t z ≠ 0 → firstMarkedAddr n 1 (parallelMarkPerm n
  1 R' z) = none) ∧ (subcubePref hp hm (perm x_last) ∈ L ∧ midpMidPref hp hm h2p (perm x_last) = s →
  (∑ z : Fin (2 ^ (1 * (n + 1))), if (firstMarkedAddr n 1 (parallelMarkPerm n 1 R' z)).isSome then
  normSq (midpSlotGroverVec U R' t z) else 0) = Real.sin ((2 * (t : ℝ) + 1) * Real.arcsin (1 /
  √((L.card * 2 ^ (n - 2 * p) : ℕ) : ℝ))) ^ 2) := by
  intro R' U; let xL := x_last; let uL := (mp02 n).symm xL; let bS := (addrReg n 1).basisSplitEquiv;
  have haL : addrEquiv n 1 uL 0 = xL := (by dsimp only [uL]; rw [mp03, sA0]); have hoi (u) : u ∈
   oddSet n 1 R' ↔ u = uL := (by
  rw [(by rw [oddSet, mem_filter]; simp : u ∈ oddSet n 1 R' ↔ addrEquiv n 1 u 0 ∈ R'),
   mem_singleton]; exact ⟨fun h ↦ (mp02 n).injective (by simpa only [mp03] using h.trans haL.symm),
  fun h ↦ by rw [h, haL]⟩); have hu0 : uL ∈ U ↔ subcubePref hp hm (perm xL) ∈ L ∧ midpMidPref hp hm
   h2p (perm xL) = s := (by dsimp only [U, midpSliceSet]; rw [mem_filter]; simp only [mem_univ,
  true_and, haL]); have hfe (u) : firstTupleHit n 1 R' u = if u = uL then some xL else none := (by
  unfold firstTupleHit; exact if hu : u = uL then (by
  subst hu; rw [dite_eq_left ((hoi _).2 rfl), iL0 rfl, ← haL]; exact congrArg (fun j : Fin 1 ↦ some
  (addrEquiv n 1 uL j)) (Subsingleton.elim _ _)) else (by rw [dite_eq_right (mt (hoi u).1 hu), iR0
  hu])); refine ⟨fun z hz ↦ fZ0 U R' t hz, fun hms z hz ↦ ?_, fun hht ↦ ?_⟩; {
  have hE := fZ0 U R' t hz; set u := (addrReg n 1).extractIndex z; have huU : u ∈ U := (by
  by_contra hnU; apply hz; dsimp only [midpSlotGroverVec, tensorState]; rw [(Nat.rec (by
  simp [midpAddrGroverReal, midpUnifRealVec, hnU]) (fun q ih ↦ by simp [midpAddrGroverReal,
  midpUnifRealVec, hnU, ih]) t : midpAddrGroverReal U (oddSet n 1 R') t u = 0),
  ofReal_zero, zero_mul]); rw
   [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R' z hE]; change firstTupleHit n 1 R' u =
   none; rw [hfe u]; exact iR0 fun heq ↦ hms (hu0.mp (by rw [← heq]; exact huU)) }; {
  have huU : uL ∈ U := hu0.mpr hht; set A := oddSet n 1 R'; have huA : uL ∈ A := (hoi uL).2 rfl; rw
   [← bS.symm.sum_comp, sum_prod_type]; have hin (u) : (∑ e, if (firstMarkedAddr n 1
  (parallelMarkPerm n 1 R' (bS.symm (u, e)))).isSome then normSq (midpSlotGroverVec U R' t (bS.symm
  (u, e))) else 0) = if u = uL then midpAddrGroverReal U A t u *
  midpAddrGroverReal U A t u else 0 := (by
  rw [sum_eq_single 0 (fun e he ↦ by dsimp only [midpSlotGroverVec, tensorState]; rw [←
  basisSplitEquiv_apply_fst];
                                     dsimp only [bS]; rw [sA0]; dsimp only; rw [single_eq_of_ne he,
  mul_zero, normSq_zero, ite_self])]; have hb := bS.apply_symm_apply (u, 0); have he0 : ((addrReg n
  1).basisSplitEquiv (bS.symm (u, 0))).2 = 0 := congrArg Prod.snd hb; have hx0 : (addrReg n
  1).extractIndex (bS.symm (u, 0)) = u := (basisSplitEquiv_apply_fst _ _).symm.trans (congrArg
  Prod.fst hb); dsimp only [midpSlotGroverVec, tensorState]; rw
   [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R' _ he0, hx0, he0, Pi.single_eq_same,
  mul_one, normSq_ofReal, hfe u]; by_cases hu : u = uL <;> simp [hu, A]);
  have hsq : midpAddrGroverReal U A t uL *
   midpAddrGroverReal U A t uL = sin ((2 * (t : ℝ) + 1) * arcsin (1 / √(U.card : ℝ))) ^ 2 := (by
  set g : ℝ := (U.card : ℝ); have hg : (U.card : ℝ) = g := rfl; set r : ℝ := g - 1; set θ := arcsin
   (1 / √g); have c1 : 1 ≤ U.card := card_pos.2 ⟨uL, huU⟩; have h1 : (1 : ℝ) ≤ g :=
   Nat.one_le_cast.2 c1; have gp : 0 < g := zero_lt_one.trans_le h1; have r0 : 0 ≤ r := sub_nonneg.2
   h1; have gs := sqrt_pos.2 gp; have gn := gs.ne'; have er : ((U.erase uL).card : ℝ) = r := (by
  dsimp only [r, g]; rw [Finset.card_erase_of_mem huU, Nat.cast_sub c1, Nat.cast_one]); have rp {y}
   (hy : y ∈ U.erase uL) : 0 < r := er ▸ Nat.cast_pos.2 (card_pos.2 ⟨y, hy⟩); have hsθ : sin θ = 1 /
   √g := (by dsimp only [θ]; exact sin_arcsin (by linarith [div_nonneg zero_le_one gs.le])
              ((div_le_one gs).2 (by simpa only [sqrt_one] using sqrt_le_sqrt h1))); have hcθ : cos
   θ = √r / √g := (by dsimp only [θ]; rw [cos_arcsin, (show 1 - (1 / √g) ^ 2 = r / g by
  dsimp only [r]; rw [div_pow, one_pow, sq_sqrt gp.le]; field_simp [gp.ne']), sqrt_div r0]); have
   hs2 : sin (2 * θ) = 2 * √r / g := (by rw [sin_two_mul, hsθ, hcθ]; field_simp [gn, gp.ne']; rw
                                          [sq_sqrt gp.le]; ring); have hc2 : cos (2 * θ) = (g - 2) /
   g := (by rw [cos_two_mul, cos_sq', hsθ, div_pow, one_pow, sq_sqrt gp.le]; field_simp [gp.ne'];
            ring);
  have hr (q : ℕ) (x) : midpAddrGroverReal U A q x = if x = uL then sin ((2 * (q : ℝ) + 1) * θ)
   else if x ∈ U then cos ((2 * (q : ℝ) + 1) * θ) / √r else 0 := (by
  refine Nat.rec (fun x ↦ ?_) (fun q ih x ↦ ?_) q x; {
  dsimp only [midpAddrGroverReal, midpUnifRealVec]; rw [hg]; simp only [Nat.cast_zero, mul_zero,
  zero_add, one_mul]; by_cases hx : x = uL; { subst hx; rw [iL0 huU, iL0 rfl, hsθ] }; {
  rw [iR0 hx]; by_cases hG : x ∈ U; { rw [iL0 hG, iL0 hG, hcθ]; field_simp [(sqrt_pos.2 (rp
  (mem_erase.2 ⟨hx, hG⟩))).ne'] }; { rw [iR0 hG, iR0 hG] } } }; {
  rw [Nat.succ_eq_add_one]; set α : ℝ := (2 * (q : ℝ) + 1) * θ; have hα : (2 * ((q + 1 : ℕ) : ℝ) +
  1) * θ = α + 2 * θ := (
  by push_cast; ring); have hd : (∑ y, midpUnifRealVec U y * ((if y ∈ A then (-1 : ℝ)
  else 1) * midpAddrGroverReal U A q y)) = (cos α * √r - sin α) / √g := (by
  dsimp only [midpUnifRealVec, α]; simp_rw [hg, ite_mul, zero_mul]; rw [sum_ite_mem, univ_inter, ←
  Finset.add_sum_erase _ _ huU, ih uL, iL0 huA, iL0 rfl, sum_congr rfl (g := fun _ ↦ (1 / √g) * (cos
  α / √r)) (fun y hy ↦ by
  rcases mem_erase.1 hy with ⟨y0, yG⟩; rw [ih y, iR0 (mt (hoi y).1 y0), iR0 y0, iL0 yG, one_mul]),
  sum_const, nsmul_eq_mul]; rcases eq_or_lt_of_le r0 with h0 | p0; { rw [er, ← h0, sqrt_zero]; ring
  }; { rw [er.trans (sq_sqrt r0).symm]; field_simp [(sqrt_pos.2 p0).ne', gn]; ring }); dsimp only
   [midpAddrGroverReal]; rw [hd, ih x, hα]; dsimp only [midpUnifRealVec, α]; rw [hg]; by_cases hx :
   x = uL; { subst hx; rw [iL0 huU, iL0 huA, iL0 rfl, iL0 rfl, sin_add, hs2, hc2]; field_simp [gn,
              gp.ne']; rw [sq_sqrt gp.le]; ring }; {
  rw [iR0 hx, iR0 hx, iR0 (mt (hoi x).1 hx)]; by_cases hG : x ∈ U; {
  have p0 := rp (mem_erase.2 ⟨hx, hG⟩); rw [iL0 hG, iL0 hG, iL0 hG, cos_add, hs2, hc2]; field_simp
   [(sqrt_pos.2 p0).ne', gn, gp.ne']; ring_nf; simp only [sq_sqrt p0.le, sq_sqrt gp.le]; dsimp only
   [r]; ring }; { rw [iR0 hG, iR0 hG, iR0 hG]; ring } } }); rw [hr t uL, iL0 rfl, sq]); simp_rw
   [hin]; rw [sum_eq_single uL (fun u hu ↦ iR0 hu), iL0 rfl, hsq, (show (U.card : ℝ) = ((L.card * 2
  ^ (n - 2 * p) : ℕ) : ℝ) by dsimp only [U]; rw [card_midpSliceSet])] }
/- ## 4. Memory-Controlled Work Unitaries (`wtR1MemCtrlWorkUnitary`) -/
/-- Block-diagonal matrix applying `A ν` on the `W`-qubit work register when memory holds
  `ν`. -/
def wtR1MemCtrlWorkMat {W M : ℕ} (A : Fin (2 ^ M) → Matrix (Fin (2 ^ W)) (Fin (2 ^ W)) ℂ) :
    Matrix (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ :=
  fun i j ↦ if (lowHighEquiv W M i).2 = (lowHighEquiv W M j).2 then
    A (lowHighEquiv W M i).2 (lowHighEquiv W M i).1 (lowHighEquiv W M j).1 else 0
lemma wtR1MemCtrlWorkMat_one (W M : ℕ) : wtR1MemCtrlWorkMat (W := W) (M := M) (fun _ ↦ 1) = 1 := by
  ext i j; unfold wtR1MemCtrlWorkMat;
  exact if q : (lowHighEquiv W M i).2 = (lowHighEquiv W M j).2 then (by
  rw [iL0 q]; change (1 : Matrix _ _ ℂ) _ _ = (1 : Matrix _ _ ℂ) i j; rw [Matrix.one_apply,
  Matrix.one_apply];
  exact if_congr ⟨fun p ↦ (lowHighEquiv W M).injective (Prod.ext p q), fun e ↦ e ▸ rfl⟩
   rfl rfl) else (by rw [iR0 q, Matrix.one_apply, iR0 fun e : i = j ↦ q (e ▸ rfl)])
lemma wtR1MemCtrlWorkMat_mul {W M : ℕ} (A B : Fin (2 ^ M) → Matrix (Fin (2 ^ W)) (Fin (2 ^ W)) ℂ) :
  wtR1MemCtrlWorkMat A * wtR1MemCtrlWorkMat B = wtR1MemCtrlWorkMat (fun ν ↦ A ν * B ν) := by
  ext i k; rw [mul_apply, ← (lowHighEquiv W M).symm.sum_comp, sum_prod_type];
  unfold wtR1MemCtrlWorkMat;
  exact if h : (lowHighEquiv W M i).2 = (lowHighEquiv W M k).2 then (by
  rw [iL0 h]; change _ = (A _ * B _) _ _; rw [mul_apply]; refine sum_congr rfl fun _ _ ↦ ?_; rw
   [sum_eq_single (lowHighEquiv W M i).2 (fun ν u ↦ by rw [sA0, iR0 (Ne.symm u), zero_mul]),
   sA0, iL0 rfl, h,
  iL0 rfl]) else (by
  rw [iR0 h]; refine sum_eq_zero fun _ _ ↦ sum_eq_zero fun ν _ ↦ ?_; rw [sA0];
  exact if q : (lowHighEquiv W M
  i).2 = ν then (by rw [iR0 (fun p ↦ h (q.trans p)), mul_zero]) else (by rw [iR0 q, zero_mul]))
lemma wtR1MemCtrlWorkMat_conjTranspose {W M : ℕ} (A : Fin (2 ^ M) → Matrix (Fin (2 ^ W)) (Fin (2 ^
  W)) ℂ) : (wtR1MemCtrlWorkMat A)ᴴ = wtR1MemCtrlWorkMat (fun ν ↦ (A ν)ᴴ) := Matrix.ext fun i j ↦ by
    rw [conjTranspose_apply]; unfold wtR1MemCtrlWorkMat;
    exact if h : (lowHighEquiv W M i).2 = (lowHighEquiv W M j).2
     then (by rw [iL0 h.symm, iL0 h, ← h]; rfl) else (by rw [iR0 (Ne.symm h), iR0 h, star_zero])
/-- Memory-controlled work unitary applying `U ν` on `W` wires conditioned on `M`-bit memory
  `ν`. -/
noncomputable def wtR1MemCtrlWorkUnitary {W M : ℕ}
    (U : Fin (2 ^ M) → Unitary (2 ^ W)) : Unitary (2 ^ (W + M)) :=
  ⟨wtR1MemCtrlWorkMat (fun ν ↦ (U ν).1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      wtR1MemCtrlWorkMat_conjTranspose, wtR1MemCtrlWorkMat_mul]
    have h1 : (fun ν ↦ (U ν).1 * ((U ν).1)ᴴ) = fun _ ↦ 1 := funext fun ν ↦ by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (U ν).2
    rw [h1, wtR1MemCtrlWorkMat_one]⟩
/-- Action of `wtR1MemCtrlWorkUnitary` on a product state `workMemState ψ |ν⟩`. -/
lemma wtR1MemCtrlWorkUnitary_mulVec_workMemState {W M : ℕ} (U : Fin (2 ^ M) → Unitary (2 ^ W)) (ψ :
  Fin (2 ^ W) → ℂ) (ν : Fin (2 ^ M)) : (wtR1MemCtrlWorkUnitary U).1 *ᵥ workMemState ψ (single ν 1) =
  workMemState ((U ν).1 *ᵥ ψ) (single ν 1) := by
  funext i; change (wtR1MemCtrlWorkMat (fun μ ↦ (U μ).1) *ᵥ workMemState ψ (single ν 1)) i = _; rw
   [Matrix.mulVec, dotProduct, ← (lowHighEquiv W M).symm.sum_comp, sum_prod_type];
   have r (w) : (∑ μ,
  wtR1MemCtrlWorkMat (fun μ' ↦ (U μ').1) i ((lowHighEquiv W M).symm (w,
  μ)) * workMemState ψ (single ν 1)
  ((lowHighEquiv W M).symm (w,
  μ))) = if (lowHighEquiv W M i).2 = ν then (U ν).1 (lowHighEquiv W M i).1 w * ψ w else 0 := (by
  rw [sum_eq_single ν (fun μ hμ ↦ by dsimp only [workMemState]; rw [sA0, single_eq_of_ne hμ,
  mul_zero, mul_zero])]; unfold wtR1MemCtrlWorkMat; dsimp only [workMemState]; rw [sA0,
  Pi.single_eq_same, mul_one];
  exact if h : (lowHighEquiv W M i).2 = ν then (by rw [iL0 h, h, iL0 rfl]) else
   (by rw [iR0 h, iR0 h, zero_mul])); simp_rw [r]; rw [workMemState];
   exact if h : (lowHighEquiv W M i).2 = ν
   then (by simp_rw [iL0 h]; rw [h, Pi.single_eq_same, mul_one]; rfl) else (by
  simp_rw [iR0 h]; rw [Finset.sum_const_zero, single_eq_of_ne h, mul_zero])
/- ## 5. Branch-Free Prefix Padding (`L_pad`) and `ghMidPZoomRound` QHL -/
/-- Memory slot indices `[active, k - 1)` written during the preceding probe round. -/
def midpZoomNewSlots (k active : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i : Fin k ↦ active ≤ i.val ∧ i.val < k - 1
/-- At most `(k - 1) - active` memory slots lie in `midpZoomNewSlots k active`. -/
lemma card_midpZoomNewSlots_le (k active : ℕ) : (midpZoomNewSlots k active).card ≤ (k - 1) - active
  := by have hb : (midpZoomNewSlots k active).card = (Finset.Ico active (k - 1)).card :=
         Finset.card_bij (fun i _ ↦ i.val) (fun i hi ↦ Finset.mem_Ico.mpr (mem_filter.mp hi).2) (fun
  _ _ _ _ h ↦ Fin.ext h) fun v hv ↦ (by rcases Finset.mem_Ico.mp hv with ⟨h1, h2⟩; exact ⟨⟨v, by
  omega⟩, mem_filter.mpr ⟨mem_univ _, h1, h2⟩, rfl⟩); rw [hb, Nat.card_Ico]
/-- Top `p`-bit rotated prefixes observed in memory slots `[active, k - 1)`. -/
noncomputable def midpRawPrefixes {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ) (ν : Fin (2 ^ (k * n))) : Finset (Fin m) :=
  (memSeen n k (midpZoomNewSlots k active) ν).image fun x ↦ subcubePref hp hm (perm x)
/-- `midpRawPrefixes` contains at most `(k - 1) - active` distinct top prefixes. -/
lemma card_midpRawPrefixes_le {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2
  ^ n))) (active : ℕ) (ν : Fin (2 ^ (k * n))) : (midpRawPrefixes hp hm perm active ν).card ≤ (k - 1)
  - active := card_image_le.trans (card_image_le.trans (card_midpZoomNewSlots_le k active))
/-- Under memory agreement on `< active` and `MemPrefixValid S (k - 1) ν`, `midpRawPrefixes`
  equals
  the top-prefix image of the newly discovered targets `R \ R'`. -/
lemma midpRawPrefixes_eq_image_sdiff {n p m k active : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (hact : active ≤ k - 1) {S : Finset (Fin (2 ^ n))} {μ ν : Fin (2 ^ (k *
  n))} (hν : MemPrefixValid S (k - 1) ν) (hag : ∀ i : Fin k, i.val < active → addrEquiv n k ν i =
  addrEquiv n k μ i) : midpRawPrefixes hp hm perm active ν = ((S \ memSeen n k (memPrefix k active)
  μ) \ (S \ memSeen n k (memPrefix k (k - 1)) ν)).image (fun x ↦ subcubePref hp hm (perm x)) := by
  unfold midpRawPrefixes; refine congrArg (Finset.image _) ?_; ext x; simp only [memSeen,
  midpZoomNewSlots, memPrefix, mem_image, mem_filter, mem_univ, true_and, mem_sdiff]; refine ⟨?_,
  ?_⟩; { rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨hν.2.1 i h2, fun ⟨j, hj, he⟩ ↦ absurd (hν.2.2.1 j i
  (lt_of_lt_of_le hj hact) h2 ((hag j hj).trans he) ▸ hj) (not_lt.mpr h1)⟩, fun hn ↦ hn.2 ⟨i, h2,
  rfl⟩⟩ }; { rintro ⟨⟨hS, ha⟩, hr⟩; rcases (show ∃ i : Fin k, i.val < k - 1 ∧ addrEquiv n k ν i = x
  by by_contra h; exact hr ⟨hS, h⟩) with ⟨i, h2, rfl⟩; exact ⟨i, ⟨by
  by_contra hl; exact ha ⟨i, lt_of_not_ge hl, (hag i (lt_of_not_ge hl)).symm⟩, h2⟩, rfl⟩ }
/-- Deterministic padding of `L_raw ⊆ Fin m` to exact cardinality `wt` using unused
  prefixes. -/
def midpPadPrefixes {m : ℕ} (wt : ℕ) (L_raw : Finset (Fin m)) : Finset (Fin m) :=
  L_raw ∪ (((finRange m).filter (· ∉ L_raw)).take (wt - L_raw.card)).toFinset
/-- `midpPadPrefixes` always contains `L_raw`. -/
lemma subset_midpPadPrefixes {m : ℕ} (wt : ℕ) (L_raw : Finset (Fin m)) : L_raw ⊆ midpPadPrefixes wt
  L_raw := Finset.subset_union_left
/-- Whenever `L_raw.card ≤ wt` and `wt ≤ m`, `midpPadPrefixes wt L_raw` has exact size `wt`. -/
lemma card_midpPadPrefixes {m wt : ℕ} {L_raw : Finset (Fin m)} (hL : L_raw.card ≤ wt) (hwt : wt ≤ m)
  : (midpPadPrefixes wt L_raw).card = wt := by
  set r := (finRange m).filter (· ∉ L_raw); set p := r.take (wt - L_raw.card); have hrn : r.Nodup :=
   (List.nodup_finRange m).filter _; have hrl : r.length = m - L_raw.card := (by rw [←
  List.toFinset_card_of_nodup hrn, (show r.toFinset = Finset.univ \ L_raw by ext j; simp [r]),
  Finset.card_sdiff_of_subset L_raw.subset_univ, card_univ, card_fin]); unfold midpPadPrefixes;
  change (L_raw ∪ p.toFinset).card = wt; rw [Finset.card_union_of_disjoint (Finset.disjoint_left.2
  fun j h1 h2 ↦ (of_decide_eq_true (List.mem_filter.1 (List.mem_of_mem_take (mem_toFinset.1 h2))).2)
  h1), List.toFinset_card_of_nodup (hrn.sublist (List.take_sublist _ _)), List.length_take, hrl,
  Nat.min_eq_left (Nat.sub_le_sub_right hwt _), Nat.add_sub_of_le hL]
/-- Nonemptiness of `midpPadPrefixes` whenever `1 ≤ wt ≤ m` and `L_raw.card ≤ wt`. -/
lemma nonempty_midpPadPrefixes {m wt : ℕ} {L_raw : Finset (Fin m)} (hwt1 : 1 ≤ wt) (hL : L_raw.card
  ≤ wt) (hwt : wt ≤ m) : (midpPadPrefixes wt L_raw).Nonempty := card_pos.mp (by
  rw [card_midpPadPrefixes hL hwt]; exact hwt1)
/-- Branch-free `m`-slot Householder state preparation unitary over `midpSliceSet`
  (`L_pad`). -/
noncomputable def ghMidPZoomWorkPrep {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ)
    (ν : Fin (2 ^ (k * n))) : Unitary (2 ^ (m * (n + 1))) :=
  let L_pad := midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν)
  ((finRange m).map fun s : Fin m ↦ (groupReg (Nat.mul_one m) s).embedUnitary
    (midpSlotPrep (midpSliceSet hp hm h2p perm L_pad s))).prod
/-- Branch-free `m`-slot Householder diffuser unitary over `midpSliceSet` (`L_pad`). -/
noncomputable def ghMidPZoomWorkDiffuser {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ)
    (ν : Fin (2 ^ (k * n))) : Unitary (2 ^ (m * (n + 1))) :=
  let L_pad := midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν)
  ((finRange m).map fun s : Fin m ↦ (groupReg (Nat.mul_one m) s).embedUnitary
    (midpSlotDiffuser (midpSliceSet hp hm h2p perm L_pad s))).prod
/-- One deflated oracle + memory-controlled middle-`p` Householder diffuser Grover step. -/
noncomputable def ghMidPZoomGroverStep {Var : Type} {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k (k - 1)))
    (.step (phaseTag (wtR1MemCtrlWorkUnitary
      (ghMidPZoomWorkDiffuser (k := k) hp hm h2p perm active))))
/-- Unitary prefix of `ghMidPZoomRound` before readout measurement and classical writeback. -/
noncomputable def ghMidPZoomPrefix {Var : Type} {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active kZoom : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (.step (phaseTag (wtR1MemCtrlWorkUnitary
      (ghMidPZoomWorkPrep (k := k) hp hm h2p perm active))))
    (.seq (OracleDynamicCircuit.sequence
        (List.replicate kZoom (ghMidPZoomGroverStep (k := k) hp hm h2p perm active)))
      (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k (k - 1))))
/-- Complete `kZoom`-step middle-`p` unpadded weight-`(r - 1)` zoom round (`kZoom + 1`
  queries). -/
noncomputable def ghMidPZoomRound {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) (active kZoom : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (ghMidPZoomPrefix hp hm h2p perm active kZoom) (wdReadoutWrite res hm1 hkN (k - 1))
/-- Per-slot middle-`p` Grover state after `t` steps conditioned on memory `ν`. -/
noncomputable def midpZoomSlotState {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ)
    (R' : Finset (Fin (2 ^ n))) (ν : Fin (2 ^ (k * n))) (t : ℕ) (s : Fin m) :
    Fin (2 ^ (1 * (n + 1))) → ℂ :=
  let L_pad := midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν)
  midpSlotGroverVec (midpSliceSet hp hm h2p perm L_pad s) R' t
/-- Exact `UnitaryEffect` of `ghMidPZoomPrefix`. -/
lemma ghMidP_unitaryEffect_zoomPrefix {Var : Type} [DecidableEq Var] {n p m k : ℕ} (hp : p ≤ n) (hm
  : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active kZoom : ℕ) (S : Finset
  (Fin (2 ^ n))) : let W := m * (n + 1); let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1
  let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary oracle).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k (k - 1)))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (wtR1MemCtrlWorkUnitary (ghMidPZoomWorkDiffuser (k := k) hp hm h2p perm active)).1
  let prepOp := (wtR1MemCtrlWorkUnitary (ghMidPZoomWorkPrep (k := k) hp hm h2p perm active)).1;
  UnitaryEffect ((ghMidPZoomPrefix (Var := Var) hp hm h2p perm active kZoom).compile qAssign oracle)
    ((unm * orac) * (((diffOp * phaseOp) ^ kZoom) * prepOp)) := by
  intro W M o _ oc unm pO dO _; let mP := memPrefix k (k - 1);
  have up (U : Unitary (2 ^ (W + M))) :=
   unitaryEffect_phaseTag (Var := Var) U; have us {c₁ c₂ U₁ U₂} (h₁ : UnitaryEffect (Var := Var) (d
  := 2 ^ (W + M)) c₁ U₁) (h₂ : UnitaryEffect c₂ U₂) := unitaryEffect_seq h₁ h₂; have hru :
   UnitaryEffect ((deflatedOracle (Var := Var) (m := m) (k := k) le_rfl mP).compile qAssign o) (unm
  * oc) := (by unfold deflatedOracle; dsimp only [compile]; rw [(by
  ext i; simp [workMemReg]; rfl : workMemReg n m k (W + M) le_rfl = QRegister.whole (W + M)),
                QRegister.whole_embedUnitary]; have h1 := unitaryEffect_qAssign (Var := Var)
                ((workFullReg n m (W + M) (Nat.le_add_right W M)).embedUnitary o); rw
                [workFullReg_embedUnitary_eq] at h1; exact us h1 (up _)); have hpu : UnitaryEffect
   ((deflatedPhaseStep (Var := Var) (m := m) (k := k) le_rfl mP).compile qAssign o) pO := (by
  unfold deflatedPhaseStep; dsimp only [compile]; rw [(rfl : workReg n m (W + M) (Nat.le_add_right W
  M) = lowBlock W M)]; have hf := up ((lowBlock W M).embedUnitary (flagConj n m)); rw
   [embedUnitary_val] at hf; dsimp only [pO]; simpa only [Matrix.mul_assoc] using us hf (us hru
  hf)); have hlu (t : ℕ) : UnitaryEffect ((sequence (replicate t (ghMidPZoomGroverStep (Var := Var)
  (k := k) hp hm h2p perm active))).compile qAssign o) ((dO * pO) ^ t) := (by
  refine Nat.rec (by simpa using unitaryEffect_skip (Var := Var) (d := 2 ^ (W + M))) (fun t ih ↦ ?_)
   t; simp only [List.replicate_succ, sequence_cons, compile_seq]; unfold ghMidPZoomGroverStep;
  dsimp only [compile]; rw [pow_succ]; exact us (us hpu (up _)) ih); unfold ghMidPZoomPrefix; dsimp
   only [compile]; simpa only [Matrix.mul_assoc] using us (up _) (us (hlu kZoom) hru)
/-- Query-cost bound `kZoom + 1` on `ghMidPZoomRound` (`0` query cost for Householder
  unitaries). -/
lemma ghMidP_costBound_zoomRound {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hm1 : 1 ≤
  m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^
  n))) (active kZoom : ℕ) (S : Finset (Fin (2 ^ n))) : CostBound (Var := Var)
  (CostModel.ofEmbeddedOracle (n := m * (n + 1) + k * n) (groverParallelMarkingOracle m S))
  ((ghMidPZoomRound res hm1 hkN hp hm h2p perm active kZoom).compile qAssign
  (groverParallelMarkingOracle m S)) ((kZoom + 1 : ℕ) : ℝ≥0) := by
  let Q := m * (n + 1) + k * n; let o := groverParallelMarkingOracle m S; let d :=
   CostModel.ofEmbeddedOracle (n := Q) o; let mP := memPrefix k (k - 1);
   let CB := CostBound (Var := Var)
   d; have h := isRealMatrix_groverParallelMarkingOracle m S; have cp (U : Unitary (2 ^ Q)) :=
   costBound_qAssign_phaseTag (Var := Var) h U; have l (t : ℕ) : CB ((sequence (replicate t
  (ghMidPZoomGroverStep (Var := Var) (k := k) hp hm h2p perm active))).compile qAssign o) t := (by
  refine Nat.rec (by simpa using CostBound.skip_zero (Var := Var) d) (fun t ih ↦ ?_) t; simp only
   [List.replicate_succ, sequence_cons, compile_seq]; unfold ghMidPZoomGroverStep; dsimp only
   [compile]; exact (((costBound_deflatedPhaseStep le_rfl mP S).seq (cp _)).seq ih).mono (le_of_eq
  (by push_cast; ring))); have w : CB ((wdReadoutWrite (Var := Var) (k := k) res hm1 hkN (k -
  1)).compile qAssign o) 0 := (by
  unfold wdReadoutWrite; dsimp only [compile]; exact ((cp _).seq (costBound_setCountAndResetWork
  (Var := Var) (M := k * n) res (batchNextCount hm1 hkN (Nat.mul_one m) (k - 1)) h)).mono (by
  simp)); unfold ghMidPZoomRound ghMidPZoomPrefix; dsimp only [compile]; exact (((cp _).seq ((l
  kZoom).seq (costBound_deflatedOracle le_rfl mP S))).seq w).mono (le_of_eq (by push_cast; ring))
/-- Combined `UnitaryEffect` of `ghMidPZoomPrefix` and `CostBound` of `ghMidPZoomRound`. -/
lemma ghMidP_unitaryEffect_and_costBound {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
  (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm : Equiv.Perm
  (Fin (2 ^ n))) (active kZoom : ℕ) (S : Finset (Fin (2 ^ n))) : let W := m * (n + 1)
  let M := k * n; let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1
  let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary oracle).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k (k - 1)))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (wtR1MemCtrlWorkUnitary (ghMidPZoomWorkDiffuser (k := k) hp hm h2p perm active)).1
  let prepOp := (wtR1MemCtrlWorkUnitary (ghMidPZoomWorkPrep (k := k) hp hm h2p perm active)).1;
  UnitaryEffect ((ghMidPZoomPrefix (Var := Var) hp hm h2p perm active kZoom).compile qAssign oracle)
    ((unm * orac) * (((diffOp * phaseOp) ^ kZoom) * prepOp)) ∧ CostBound (Var := Var) model
    ((ghMidPZoomRound res hm1 hkN hp hm h2p perm active kZoom).compile qAssign oracle) ((kZoom + 1 :
    ℕ) : ℝ≥0) := ⟨ghMidP_unitaryEffect_zoomPrefix hp hm h2p perm active kZoom S,
    ghMidP_costBound_zoomRound res hm1 hkN hp hm h2p perm active kZoom S⟩
private lemma ghMidP_prod_embedMatrix_mulVec_zoomProdState {n m : ℕ}
    (hb1 : m * 1 = m) (A : Fin m → Matrix (Fin (2 ^ (1 * (n + 1)))) (Fin (2 ^ (1 * (n + 1)))) ℂ)
    (f : Fin m → Fin (2 ^ (1 * (n + 1))) → ℂ) :
    ((finRange m).map fun c ↦ (groupReg (n := n) hb1 c).embedMatrix (A c)).prod *ᵥ
      zoomProdState f = zoomProdState fun c ↦ A c *ᵥ f c := by
  let gR := groupReg (n := n) hb1; unfold zoomProdState
  have al (l : List (Fin m)) (hl : l.Nodup) :
      ((l.map fun c ↦ (gR c).embedMatrix (A c)).prod) *ᵥ
        (fun w ↦ ∏ c, f c ((gR c).extractIndex w)) =
      fun w ↦ ∏ c, (if c ∈ l then A c *ᵥ f c else f c) ((gR c).extractIndex w) := by
    refine List.rec (fun _ ↦ ?_) (fun d l ih hl ↦ ?_) l hl
    · rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]
      funext w; exact prod_congr rfl fun c _ ↦ by rw [ite_eq_right List.not_mem_nil]
    · rcases List.nodup_cons.mp hl with ⟨hd, hl'⟩
      rw [List.map_cons, List.prod_cons, ← mulVec_mulVec, ih hl', embedMatrix_groupReg_mulVec_prod]
      funext w; refine prod_congr rfl fun c _ ↦ ?_; by_cases h : c = d
      · subst h; rw [ite_eq_left rfl, ite_eq_right hd, ite_eq_left mem_cons_self]
      · by_cases hc : c ∈ l
        · rw [ite_eq_right h, ite_eq_left hc, ite_eq_left (by simp [hc])]
        · rw [ite_eq_right h, ite_eq_right hc, ite_eq_right (by simp [h, hc])]
  exact (al (finRange m) (List.nodup_finRange m)).trans
    (funext fun w ↦ prod_congr rfl fun c _ ↦ by rw [ite_eq_left (mem_finRange c)])
private lemma ghMidP_zoomProdState_zero {n m : ℕ} :
    zoomProdState (n := n) (fun _ : Fin m ↦ single 0 1) = single 0 1 := by
  let hb1 : m * 1 = m := Nat.mul_one m
  have ex (s : Fin m) : (groupReg (n := n) hb1 s).extractIndex 0 = 0 :=
    (basisBits _).injective (funext fun _ ↦ by simp [basisBits_extractIndex])
  funext w; unfold zoomProdState; by_cases hw : w = 0
  · subst hw; simp [ex]
  · rw [single_eq_of_ne hw]; by_contra hne; apply hw; apply (groupSplitEquiv hb1).injective
    funext s; rw [groupSplitEquiv_apply, groupSplitEquiv_apply, ex]
    by_contra hn; exact hne (prod_eq_zero (mem_univ s) (single_eq_of_ne hn 1))
/-- Exact weakest-precondition diagonal evaluation of `ghMidPZoomRound` at `workMemIdx n m k
  0 ν`
  under `MemPrefixValid S (k - 1) ν` (`|R'| = 1`, slice dimension `(r - 1) * 2 ^ (n - 2 *
  p)`). -/
lemma ghMidP_wp_zoomRound_workMemIdx {Var : Type} [DecidableEq Var] (res : Var) {n p m k active r :
  ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm :
  Equiv.Perm (Fin (2 ^ n))) (hr_eq : r = k - active) (hr2 : 2 ≤ r) (hrm : r - 1 ≤ m) (kZoom : ℕ) {S
  : Finset (Fin (2 ^ n))} (hcard : S.card = k) {ν : Fin (2 ^ (k * n))} (hval : MemPrefixValid S (k -
  1) ν) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ
    : ∀ (s
  : ℕ) (τ : Store Var) (ν' : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν' →
  (Θ τ).1.1 (workMemIdx n m k 0 ν') (workMemIdx n m k 0 ν') = (Ψ (S \ memSeen n k (memPrefix k s)
  ν') : ℂ)) (τ : Store Var) : let R' := S \ memSeen n k (memPrefix k (k - 1)) ν
  let pref x := subcubePref hp hm (perm x)
  let L_pad := midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν)
  let θZoom := Real.arcsin (1 / √(((r - 1) * 2 ^ (n - 2 * p) : ℕ) : ℝ))
  let pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2; ((wp ((ghMidPZoomRound res hm1 hkN hp
  hm h2p perm active kZoom).compile qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx
  n m k 0 ν) (workMemIdx n m k 0 ν) = if (L_pad ∩ R'.image pref).Nonempty then ((pZoom * Ψ ∅ + (1 -
  pZoom) * Ψ R' : ℝ) : ℂ) else (Ψ R' : ℂ) := by
  classical
  dsimp only; have ⟨ha, w1, w2, w3⟩ : active < k ∧ 1 ≤ (k - 1) - active ∧ (k - 1) - active ≤ m ∧ (k
  - 1) - active = r - 1 := (by omega); let hb1 : m * 1 = m := Nat.mul_one m; let pf := fun x ↦
   subcubePref hp hm (perm x); let mP := memPrefix k (k - 1); let W := m * (n + 1); let M := k * n;
   let gH
   := groupHits (n := n) hb1; let w0 := workMemIdx n m k 0; let mS := memSeen n k; set R' := S \ mS
   mP ν; have hpI := parallelMarkPerm_involutive (n := n) (m := m) R'; have sn :=
   card_memSeen_of_memPrefixValid hval; have rc : R'.card = 1 := (by
  have : R'.card + (k - 1) = k := (congrArg (R'.card + ·) sn.1).symm.trans
   ((Finset.card_sdiff_add_card_eq_card sn.2).trans hcard); omega); obtain ⟨xL, hxL⟩ :=
   Finset.card_eq_one.mp rc; let Lr := midpRawPrefixes hp hm perm active ν; let Lp :=
   midpPadPrefixes ((k - 1) - active) Lr; have hLr := card_midpRawPrefixes_le hp hm perm active ν;
  have hLc := (card_midpPadPrefixes hLr w2).trans w3; have hLn := nonempty_midpPadPrefixes w1 hLr
   w2; have hUn (s) := nonempty_midpSliceSet hp hm h2p perm hLn s; let fc := (lowBlock W
  M).embedMatrix (flagConj n m).1; let pO := fc * (permutationUnitary (unmarkPerm n m k mP)).1 *
   (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 * fc;
  let wD := wtR1MemCtrlWorkUnitary (ghMidPZoomWorkDiffuser (k := k) hp hm h2p perm active); let wP
   := wtR1MemCtrlWorkUnitary (ghMidPZoomWorkPrep (k := k) hp hm h2p perm active); have hit (t : ℕ) :
   (((wD.1 * pO) ^ t) * wP.1) *ᵥ single (w0 ν) 1 = workMemState (zoomProdState (midpZoomSlotState hp
  hm h2p perm active R' ν t)) (single ν 1) := (by
  have cU (F : Fin m → Unitary _) : ((finRange m).map fun s ↦ (groupReg (n := n) hb1
  s).embedUnitary (F s)).prod.1 = ((finRange m).map fun s ↦ (groupReg (n := n) hb1
  s).embedMatrix (F s).1).prod := (by
  rw [Submonoid.coe_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun _ _ ↦ embedUnitary_val _ _));
  have pG := ghMidP_prod_embedMatrix_mulVec_zoomProdState (n := n) hb1;
  rw [← mulVec_mulVec]; refine Nat.rec ?_ (fun t ih ↦ ?_) t; {
  dsimp only [w0, wP]; simp only [pow_zero, Matrix.one_mulVec, workMemIdx, ← workMemState_single,
  wtR1MemCtrlWorkUnitary_mulVec_workMemState, ← ghMidP_zoomProdState_zero (n := n) (m := m)];
  unfold ghMidPZoomWorkPrep; rw [cU, pG]; congr
   1; congr 1; funext s; exact midpSlotPrep_mulVec_zero (hUn s) R' }; {
  rw [pow_succ', ← mulVec_mulVec, ih, ← mulVec_mulVec, deflatedPhaseMat_mulVec_workMemState mP _ ν
  sn.2, (show S \ mS mP ν = R' from rfl)]; dsimp only [wD]; rw
   [wtR1MemCtrlWorkUnitary_mulVec_workMemState]; congr 1; rw [sDiagM_eq_prod_groupReg hb1 R'];
  unfold ghMidPZoomWorkDiffuser; rw [pG, cU, pG]; congr 1; funext s; exact
   midpSlotDiffuser_mulVec_sDiagM (hUn s) R' t }); let ξ := midpZoomSlotState hp hm h2p perm active
   R' ν kZoom; let nsq (c) : ℂ := (normSq c : ℂ); have hξ (s : Fin m) : (∑ z, normSq (ξ s z)) = 1 :=
   sum_normSq_midpSlotGroverVec (hUn s) R' kZoom; have hsp (o) (nz : zoomProdState ξ
  (parallelMarkPerm n m R' o) ≠ 0) : ∀ x ∈ gH o, x ∈ R' := (by
  have fl (s) := fZ0 (midpSliceSet hp hm h2p perm Lp s) R' kZoom (fun h0 ↦ nz (prod_eq_zero
  (mem_univ s) h0)); intro x hx; rw [← hpI o] at hx; exact mem_of_mem_groupHits_parallelMarkPerm hb1
   fl hx); have ue := ghMidP_unitaryEffect_zoomPrefix (Var := Var) (k := k) hp hm h2p perm active
   kZoom S; let qfL {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (v : Fin q → ℂ) : ℂ := star v ⬝ᵥ (A *ᵥ
  v); have hqc {q : ℕ} (K A : Matrix (Fin q) (Fin q) ℂ) (v : Fin q → ℂ) : qfL (Kᴴ * A * K) v = qfL A
   (K *ᵥ v) := (by dsimp only [qfL]; simp only [Matrix.mul_assoc, ← mulVec_mulVec,
  Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]); let D := 2 ^ (W + M); have hq2
   {P : QProg Var D} {U} (hU : UnitaryEffect P U) (Φ : CQAssertion (Store Var) D) (v) : qfL ((wp P
     Φ) τ).1.1
   v = qfL (Φ τ).1.1 (U *ᵥ v) := (by dsimp only [qfL]; rw [unitaryEffect_apply hU Φ τ]; exact hqc U
                                      _ v); refine (diag_eq_star_single_dotProduct_mulVec _ (w0
  ν)).trans ?_; change qfL _ _ = _; unfold ghMidPZoomRound; dsimp only [compile]; rw [wp_qSeq, hq2
  ue, ← mulVec_mulVec, hit kZoom, ← mulVec_mulVec, unmark_mul_parallelOracle_workMemState mP _ ν
  sn.2, (show S \ mS mP ν = R' from rfl), fullReg_embedUnitary_eq_permutationUnitary R']; let pM :=
   parallelMarkPerm n m R'; let p1 := parallelMarkPerm n 1 R'; refine Eq.trans (b := ∑ zs, (∏ s, nsq
  (ξ s (zs s))) * (Ψ (R' \ (gH (pM ((groupSplitEquiv hb1).symm zs))).toFinset) : ℂ)) ?_ ?_; {
  refine Eq.trans (b := ∑ o, nsq (zoomProdState ξ (pM o)) * (Ψ (R' \ (gH o).toFinset) : ℂ)) ?_ ?_; {
  unfold wdReadoutWrite; dsimp only [compile]; have up := unitaryEffect_phaseTag (Var := Var) (d :=
  D) (permutationUnitary (memWriteBatchPerm (W := W) (n := n) (k := k) (k - 1) gH)); rw [wp_qSeq,
  hq2 up]; dsimp only [qfL, nsq]; rw [wp_setCountAndResetWork, Matrix.sum_mulVec, dotProduct_sum];
  refine sum_congr rfl fun o _ ↦ ?_; change qfL _ _ = _; rw [hqc, krausLowBlock_mulVec_memAddPerm];
  dsimp only [qfL]; have pa : ((permutationUnitary pM).1 *ᵥ zoomProdState ξ) o = zoomProdState ξ (pM
  o) := (by rw [Matrix.mulVec, dotProduct, sum_eq_single (pM o) (fun j hj ↦ by
  rw [permutationUnitary_apply, iR0 (fun h ↦ hj ((hpI j).symm.trans (congrArg pM h.symm))),
  zero_mul]), permutationUnitary_apply, iL0 (hpI o).symm, one_mul]); rw [pa, Matrix.mulVec_smul,
  star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
  RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, ← diag_eq_star_single_dotProduct_mulVec];
  by_cases nz : zoomProdState ξ (pM o) = 0; { simp [nz] }; {
  let gh := gH o; let ν' := writeMemBatch (k - 1) gh ν; let k' := (k - 1) + gh.length; have nd :
   gh.Nodup := nodup_groupHits hb1 o; obtain ⟨ln, hv'⟩ := memPrefixValid_writeMemBatch hcard hval nd
   (hsp o nz); have cn : (batchNextCount hm1 hkN hb1 (k - 1) o).val = k' := (by
  dsimp only [k', gh, gH] at ln ⊢; simp [batchNextCount, Nat.min_eq_right ln]); have ws (i) :
   addrEquiv n k ν' i = addrEquiv n k ν i + if k - 1 ≤ i.val then (gh[i.val - (k - 1)]?).getD 0 else
   0 := (by dsimp only [ν']; unfold writeMemBatch; rw [sA0, Pi.add_apply]); have wbR {i : Fin k} (h0
  : k - 1 ≤ i.val) (hi : i.val < k') : addrEquiv n k ν' i = gh[i.val - (k -
  1)]'(Nat.sub_lt_left_of_lt_add h0 hi) := (by
  have sl := Nat.sub_lt_left_of_lt_add h0 hi; rw [ws, hval.2.2.2 i h0, zero_add, iL0 h0,
  List.getElem?_eq_getElem sl, Option.getD_some]);
  have hm0 : memSeen n k (memPrefix k k') ν' = mS mP ν ∪
   gh.toFinset := (by ext y; dsimp only [mS, mP]; simp only [memSeen, memPrefix, mem_image,
  mem_filter, mem_univ, true_and, mem_union, mem_toFinset]; exact ⟨fun ⟨i, hi, e⟩ ↦ if h : i.val < k
  - 1 then Or.inl ⟨i, h, by rw [← e, ws, iR0 (not_le.mpr h), add_zero]⟩ else Or.inr (by
  rw [← e, wbR (le_of_not_gt h) hi]; exact List.getElem_mem _), fun o ↦ o.elim (fun ⟨i, h, e⟩ ↦ ⟨i,
  lt_of_lt_of_le h (Nat.le_add_right _ _), by rw [ws, iR0 (not_le.mpr h), add_zero, e]⟩) fun hy ↦
  (by rcases List.mem_iff_getElem.mp hy with ⟨j, hj, rfl⟩; have a1 := Nat.add_lt_add_left hj (k -
  1); exact ⟨⟨(k - 1) + j, lt_of_lt_of_le a1 ln⟩, a1, (wbR (Nat.le_add_right _ _) a1).trans (by
  simp)⟩)⟩); have sd : S \ memSeen n k (memPrefix k k') ν' = R' \ (gH o).toFinset := (by
  dsimp only [gh] at hm0; rw [hm0]; ext y; simp only [R', mem_sdiff, mem_union]; tauto); have ie :
   (lowHighEquiv W M).symm (0,
   (addrEquiv n k).symm (addrEquiv n k ν + batchDelta (k - 1) gH o)) = workMemIdx
   n m k 0 ν' := rfl; have hθ := hΘ k' (τ.subst res (Int.ofNat k')) ν' ln (by simp) hv'; rw [ie, cn,
  hθ, sd] } }; { rw [← Equiv.sum_comp pM]; dsimp only [pM]; simp_rw [hpI]; rw [← (groupSplitEquiv
  hb1).symm.sum_comp]; refine sum_congr rfl fun zs _ ↦ ?_; congr 1; unfold zoomProdState; dsimp only
                  [nsq]; simp_rw [← gA0 hb1, sA0, map_prod, Complex.ofReal_prod] } }; {
  let jL := pf xL; let s₀ : Fin m := midpMidPref hp hm h2p (perm xL); have hif : (Lp ∩ R'.image
  pf).Nonempty ↔ jL ∈ Lp := (by dsimp only [jL]; rw [hxL, Finset.image_singleton]; exact ⟨fun ⟨_, h⟩
  ↦ (mem_singleton.1 (mem_inter.1 h).2) ▸ (mem_inter.1 h).1, fun h ↦ ⟨pf xL, mem_inter.2 ⟨h,
  Finset.mem_singleton_self _⟩⟩⟩); have hrs (s) := midpSlotGroverVec_readout_singleton hp hm h2p
   perm hLn xL s kZoom; have hso (s : Fin m) (hn : ¬ (jL ∈ Lp ∧ s₀ = s)) (z) (hz : ξ s z ≠ 0) :
   firstMarkedAddr n 1 (p1 z) = none := (by dsimp only [p1]; rw [hxL]; exact (hrs s).2.1 hn z (by
  simpa [ξ, midpZoomSlotState, Lp, Lr, hxL] using hz)); let fH (z) : Bool := (firstMarkedAddr n 1
  (p1 z)).isSome; let wV (z) : ℂ := if fH z then (Ψ ∅ : ℂ) else (Ψ R' : ℂ); have hc (zs : Fin m → _)
   : (∏ s, nsq (ξ s (zs s))) * (Ψ (R' \ (gH (pM ((groupSplitEquiv hb1).symm zs))).toFinset) : ℂ) =
   (∏ s, nsq (ξ s (zs s))) * wV (zs s₀) := (by
  by_cases z0 : (∏ s, nsq (ξ s (zs s))) = 0; { rw [z0, zero_mul, zero_mul] }; {
  have nz (s) : ξ s (zs s) ≠ 0 := fun h0 ↦ z0 (prod_eq_zero (mem_univ s) (by
  dsimp only [nsq]; rw [h0, normSq_zero, ofReal_zero])); let w := (groupSplitEquiv hb1).symm zs; set
   o := pM w; have gw (s) : (groupReg hb1 s).extractIndex w = zs s := (by rw [← gA0 hb1, sA0]); have
   xo (s) : (groupReg hb1 s).extractIndex o = p1 (zs s) := (by
  dsimp only [o, pM, p1]; rw [extractIndex_groupReg_parallelMarkPerm, gw]); have fl (s) : ((addrReg
  n 1).basisSplitEquiv ((groupReg hb1 s).extractIndex w)).2 = 0 := gw s ▸ fZ0 _ R' kZoom (nz s);
  have sR : (gH o).toFinset ⊆ R' := fun y hy ↦ mem_of_mem_groupHits_parallelMarkPerm hb1 fl
   (mem_toFinset.1 hy); dsimp only [wV]; rcases Option.casesOn (motive := fun q ↦ q = none ∨ ∃ y, q
  = some y) (firstMarkedAddr n 1 (p1 (zs s₀))) (Or.inl rfl) (fun y ↦ Or.inr ⟨y, rfl⟩) with f0 | ⟨y,
  f0⟩; { rw [iR0 (by dsimp only [fH]; rw [f0]; intro h; cases h)]; have em : (gH o).toFinset = ∅ :=
          Finset.eq_empty_iff_forall_notMem.2 fun y hy ↦ (by
  have l0 := mem_toFinset.1 hy; dsimp only [gH] at l0; unfold groupHits at l0; rcases
   List.mem_filterMap.1 (List.mem_dedup.1 l0) with ⟨s, _, hs⟩; rw [xo s] at hs; obtain rfl | s0 :=
   eq_or_ne s s₀; { rw [f0] at hs; cases hs }; {
  rw [hso s (mt And.right s0.symm) (zs s) (nz s)] at hs; cases hs }); rw [em, Finset.sdiff_empty] };
  { rw [iL0 (by dsimp only [fH]; rw [f0]; rfl)]; have ym : y ∈ (gH o).toFinset := (by
  rw [mem_toFinset]; dsimp only [gH]; unfold groupHits; rw [List.mem_dedup, List.mem_filterMap];
  exact ⟨s₀, mem_finRange s₀, by rw [xo s₀, f0]⟩); rw [hxL] at sR ⊢; rw [mem_singleton.mp (sR ym)]
     at ym; rw [Finset.Subset.antisymm sR (Finset.singleton_subset_iff.mpr ym), Finset.sdiff_self] }
  }); simp_rw [hc]; let g (s : Fin m) (z) : ℂ := nsq (ξ s z) * if s = s₀ then wV z else 1; have gp
   (zs : Fin m → _) : (∏ s, nsq (ξ s (zs s))) * wV (zs s₀) = ∏ s, g s (zs s) := (by
  dsimp only [g]; rw [Finset.prod_mul_distrib]; congr 1; rw [Finset.prod_eq_single s₀ (fun s _ hs ↦
  iR0 hs) (by simp), iL0 rfl]); simp_rw [gp, ← Fintype.prod_sum g]; rw [Finset.prod_eq_single s₀
  (fun s _ hs ↦ by dsimp only [g, nsq]; simp_rw [iR0 hs, mul_one]; rw [← ofReal_sum, hξ s,
  Complex.ofReal_one]) (by simp)]; simp_rw [(show ∀ z, g s₀ z = nsq (ξ s₀ z) * wV z from fun z ↦ by
  dsimp only [g]; rw [iL0 rfl])]; by_cases hj : jL ∈ Lp; {
  rw [iL0 (hif.mpr hj)]; let pZ := sin ((2 * (kZoom : ℝ) + 1) * arcsin (1 / √(((r - 1) * 2 ^ (n - 2
  * p) : ℕ) : ℝ))) ^ 2; have hp : (∑ z, if fH z then normSq (ξ s₀ z) else 0) = pZ := (by
  have h1 := (hrs s₀).2.2 ⟨hj, rfl⟩; rw [hLc] at h1; dsimp only [fH, p1, ξ, midpZoomSlotState, Lp,
  Lr, mS]; simp_rw [hxL]; exact h1); have hw (z) : nsq (ξ s₀ z) * wV z = nsq (ξ s₀ z) * (Ψ R' : ℂ) +
   ((if fH z then normSq (ξ s₀ z) else 0 : ℝ) : ℂ) * ((Ψ ∅ - Ψ R' : ℝ) : ℂ) := (by
  (by_cases hf : fH z = true <;> dsimp only [wV, nsq] <;> simp [hf]); ring); simp_rw [hw]; dsimp
   only [nsq]; rw [sum_add_distrib, ← sum_mul, ← sum_mul, ← ofReal_sum, ← ofReal_sum, hξ s₀, hp];
  dsimp only [pZ, R', mS, mP]; push_cast; ring }; {
  rw [iR0 (mt hif.mp hj)]; have h0 (z) : nsq (ξ s₀ z) * wV z = nsq (ξ s₀ z) * (Ψ R' : ℂ) := if hz :
   ξ s₀ z = 0 then (by simp [nsq, hz]) else (by dsimp only [wV, fH]; simp [hso s₀ (fun h ↦ hj h.1) z
  hz]); simp_rw [h0]; dsimp only [nsq]; rw [← sum_mul, ← ofReal_sum, hξ s₀]; simp } }
/-- Unconditional real upper bound on `ghMidPZoomRound` diagonal expectation whenever `Ψ ∅ ≤
  Ψ R'`,
  holding for EVERY collision fiber without `L_raw.card = r - 1` side conditions (`L_raw ⊆
  L_pad`). -/
lemma ghMidP_wp_zoomRound_workMemIdx_le {Var : Type} [DecidableEq Var] (res : Var) {n p m k active r
  : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm :
  Equiv.Perm (Fin (2 ^ n))) (hr_eq : r = k - active) (hr2 : 2 ≤ r) (hrm : r - 1 ≤ m) (kZoom : ℕ) {S
  : Finset (Fin (2 ^ n))} (hcard : S.card = k) {ν : Fin (2 ^ (k * n))} (hval : MemPrefixValid S (k -
  1) ν) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ
    : ∀ (s
  : ℕ) (τ : Store Var) (ν' : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν' →
  (Θ τ).1.1 (workMemIdx n m k 0 ν') (workMemIdx n m k 0 ν') = (Ψ (S \ memSeen n k (memPrefix k s)
  ν') : ℂ)) (hΨ : Ψ ∅ ≤ Ψ (S \ memSeen n k (memPrefix k (k - 1)) ν)) (τ : Store Var) :
  let R' := S \ memSeen n k (memPrefix k (k - 1)) ν; let pref x := subcubePref hp hm (perm x)
  let L_raw := midpRawPrefixes hp hm perm active ν
  let θZoom := Real.arcsin (1 / √(((r - 1) * 2 ^ (n - 2 * p) : ℕ) : ℝ))
  let pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2; (((wp ((ghMidPZoomRound res hm1 hkN hp
  hm h2p perm active kZoom).compile qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx
  n m k 0 ν) (workMemIdx n m k 0 ν)).re ≤ if (L_raw ∩ R'.image pref).Nonempty then pZoom * Ψ ∅ + (1
  - pZoom) * Ψ R' else Ψ R' := by
  dsimp only; rw [ghMidP_wp_zoomRound_workMemIdx res hm1 hkN hp hm h2p perm hr_eq hr2 hrm kZoom
  hcard hval Θ Ψ hΘ τ];
  set I := (S \ memSeen n k (memPrefix k (k - 1)) ν).image fun x ↦ subcubePref hp hm
   (perm x); by_cases hr : (midpRawPrefixes hp hm perm active ν ∩ I).Nonempty; {
  have hp0 : (midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν) ∩ I).Nonempty
   := (by rcases hr with ⟨j, hj⟩; rcases mem_inter.mp hj with ⟨h1, h2⟩; exact ⟨j, mem_inter.mpr
  ⟨subset_midpPadPrefixes _ _ h1, h2⟩⟩); rw [iL0 hp0, iL0 hr, ofReal_re] }; {
  rw [iR0 hr]; split_ifs; { rw [ofReal_re]; nlinarith [sq_nonneg (sin ((2 * (kZoom : ℝ) + 1) *
  arcsin (1 / √(((r - 1) * 2 ^ (n - 2 * p) : ℕ) : ℝ))))] }; { rw [ofReal_re] } }
/- ## 6. Prefix-Projector Preservation, `IsWpTop`, and `(32, 4)` (`r - 1 = 3`) Instantiation -/
/-- Equality of two operators on basis indices satisfying `D`. -/
def ghMidPAgreeOnD {d : ℕ} (D : Fin d → Prop) (A B : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ z₁ z₂, D z₁ → D z₂ → A z₁ z₂ = B z₁ z₂
/-- Block-diagonality of `K` with respect to predicate `D`. -/
def ghMidPBlockDiag {d : ℕ} (D : Fin d → Prop) (K : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ z₁ z₂, K z₁ z₂ ≠ 0 → (D z₁ ↔ D z₂)
lemma ghMidPAgreeOnD_conj_of_blockDiag {d : ℕ} {D : Fin d → Prop} {K A B : Matrix (Fin d) (Fin d) ℂ}
  (hK : ghMidPBlockDiag D K) (hAB : ghMidPAgreeOnD D A B) : ghMidPAgreeOnD D (Kᴴ * A * K) (Kᴴ * B *
  K) := fun a b ha hb ↦ by
  simp only [mul_apply, conjTranspose_apply, sum_mul]; exact sum_congr rfl fun u _ ↦ sum_congr rfl
   fun v _ ↦ if p : K v a = 0 then (by simp [p]) else if q : K u b = 0 then (by simp [q]) else (by
  rw [hAB v u ((hK v a p).mpr ha) ((hK u b q).mpr hb)])
lemma ghMidPAgreeOnD_sum {ι : Type*} {d : ℕ} {D : Fin d → Prop} (s : Finset ι) {A B : ι → Matrix
  (Fin d) (Fin d) ℂ} (h : ∀ i ∈ s, ghMidPAgreeOnD D (A i) (B i)) : ghMidPAgreeOnD D (∑ i ∈ s, A i)
  (∑ i ∈ s, B i) := fun z₁ z₂ hz₁ hz₂ ↦ by
  simp only [Matrix.sum_apply]; exact sum_congr rfl fun i hi ↦ h i hi z₁ z₂ hz₁ hz₂
/-- Weakest-precondition preservation of `ghMidPAgreeOnD D` across an oracle circuit `C`. -/
def ghMidPPreservesAgreeOnD {Var : Type} [DecidableEq Var] {Q O : ℕ}
    (D : Fin (2 ^ Q) → Prop) (C : OracleCirc Var Q O) (oracle : Unitary (2 ^ O)) : Prop :=
  ∀ (Θ₁ Θ₂ : CQAssertion (Store Var) (2 ^ Q)), (∀ τ, ghMidPAgreeOnD D (Θ₁ τ).1.1 (Θ₂ τ).1.1) →
    ∀ τ, ghMidPAgreeOnD D ((wp (C.compile qAssign oracle) Θ₁) τ).1.1
      ((wp (C.compile qAssign oracle) Θ₂) τ).1.1
lemma ghMidPPreservesAgreeOnD_skip {Var : Type} [DecidableEq Var] {Q O : ℕ} (D : Fin (2 ^ Q) → Prop)
  (oracle : Unitary (2 ^ O)) : ghMidPPreservesAgreeOnD D (.skip : OracleCirc Var Q O) oracle := fun
  _ _ h ↦ h
lemma ghMidPPreservesAgreeOnD_seq {Var : Type} [DecidableEq Var] {Q O : ℕ} {D : Fin (2 ^ Q) → Prop}
  {oracle : Unitary (2 ^ O)} {c₁ c₂ : OracleCirc Var Q O} (h₁ : ghMidPPreservesAgreeOnD D c₁ oracle)
  (h₂ : ghMidPPreservesAgreeOnD D c₂ oracle) : ghMidPPreservesAgreeOnD D (.seq c₁ c₂) oracle := fun
  Θ₁ Θ₂ hΘ τ ↦ by dsimp only [compile]; rw [wp_qSeq, wp_qSeq]; exact h₁ _ _ (h₂ Θ₁ Θ₂ hΘ) τ
lemma ghMidPPreservesAgreeOnD_sequence {Var : Type} [DecidableEq Var] {Q O : ℕ} {D : Fin (2 ^ Q) →
  Prop} {oracle : Unitary (2 ^ O)} (l : List (OracleCirc Var Q O)) (hl : ∀ c ∈ l,
  ghMidPPreservesAgreeOnD D c oracle) : ghMidPPreservesAgreeOnD D (OracleDynamicCircuit.sequence l)
  oracle := by refine List.rec (fun _ ↦ ghMidPPreservesAgreeOnD_skip D oracle) (fun c _ ih h ↦ ?_) l
                hl; rw [sequence_cons]; exact ghMidPPreservesAgreeOnD_seq (h c mem_cons_self) (ih
  fun x u ↦ h x (List.mem_cons_of_mem c u))
lemma ghMidPPreservesAgreeOnD_step_phaseTag {Var : Type} [DecidableEq Var] {Q O : ℕ} {D : Fin (2 ^
  Q) → Prop} (oracle : Unitary (2 ^ O)) {U : Unitary (2 ^ Q)} (hU : ghMidPBlockDiag D U.1) :
  ghMidPPreservesAgreeOnD D (.step (phaseTag U) : OracleCirc Var Q O) oracle := fun _ _ hΘ τ ↦ by
  simp only [compile, wp_qAssign, wp_phaseTag, qhlQAssign_val]; exact
   ghMidPAgreeOnD_conj_of_blockDiag hU (hΘ τ)
lemma ghMidPPreservesAgreeOnD_oracle {Var : Type} [DecidableEq Var] {Q O : ℕ} {D : Fin (2 ^ Q) →
  Prop} (oracle : Unitary (2 ^ O)) (r : QRegister O Q) (hr : ghMidPBlockDiag D (r.embedUnitary
  oracle).1) : ghMidPPreservesAgreeOnD D (.oracle r : OracleCirc Var Q O) oracle := fun _ _ hΘ τ ↦
  by simp only [compile, wp_qAssign, qhlQAssign_val]; exact
      ghMidPAgreeOnD_conj_of_blockDiag hr (hΘ τ)
/-- Agreement of the first `act_bound` classical memory slots with `μ`. -/
def ghMidPMemPrefixAgree {n k W : ℕ} (act_bound : ℕ) (μ : Fin (2 ^ (k * n)))
    (z : Fin (2 ^ (W + k * n))) : Prop :=
  ∀ i : Fin k, i.val < act_bound → addrEquiv n k (lowHighEquiv W (k * n) z).2 i = addrEquiv n k μ i
lemma ghMidPBlockDiag_embedMatrix_lowBlock {n k W : ℕ} (act_bound : ℕ) (μ : Fin (2 ^ (k * n))) (A :
  Matrix (Fin (2 ^ W)) (Fin (2 ^ W)) ℂ) : ghMidPBlockDiag (ghMidPMemPrefixAgree act_bound μ)
  ((lowBlock W (k * n)).embedMatrix A) := fun a b e ↦ by
  unfold ghMidPMemPrefixAgree; simp_rw [(agreeOutside_lowBlock_iff W (k * n) a b).mp (by
  by_contra h; exact e (by rw [QRegister.embedMatrix_apply_of_agreeOutside, iR0 h, mul_zero]))]
lemma ghMidPBlockDiag_wtR1MemCtrlWorkUnitary {n k W : ℕ} (act_bound : ℕ) (μ : Fin (2 ^ (k * n))) (U
  : Fin (2 ^ (k * n)) → Unitary (2 ^ W)) : ghMidPBlockDiag (ghMidPMemPrefixAgree act_bound μ)
  (wtR1MemCtrlWorkUnitary U).1 := fun a b e ↦ by
  have s : (lowHighEquiv W (k * n) a).2 = (lowHighEquiv W (k * n) b).2 := (
  by by_contra h; exact e (by
  change wtR1MemCtrlWorkMat (fun ν ↦ (U ν).1) a b = 0; unfold wtR1MemCtrlWorkMat; rw [iR0 h]));
  unfold ghMidPMemPrefixAgree; simp_rw [s]
lemma ghMidPPreservesAgreeOnD_setCountAndResetWork {Var : Type} [DecidableEq Var] (res : Var) {n k W
  O : ℕ} (act_bound : ℕ) (μ : Fin (2 ^ (k * n))) (oracle : Unitary (2 ^ O)) (g : Fin (2 ^ W) → Fin
  (2 ^ W)) : ghMidPPreservesAgreeOnD (ghMidPMemPrefixAgree act_bound μ) (setCountAndResetWork (Var
  := Var) (M := k * n) (O := O) res g) oracle := fun _ _ hΘ τ ↦ by
  rw [wp_setCountAndResetWork, wp_setCountAndResetWork]; exact ghMidPAgreeOnD_sum Finset.univ fun _
   _ ↦ ghMidPAgreeOnD_conj_of_blockDiag (ghMidPBlockDiag_embedMatrix_lowBlock act_bound μ _) (hΘ _)
/-- `ghMidPZoomRound` preserves `ghMidPMemPrefixAgree act_bound μ` for every `act_bound ≤ k
  - 1`. -/
lemma ghMidPPreservesAgreeOnD_zoomRound {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
  (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm : Equiv.Perm
  (Fin (2 ^ n))) (active kZoom act_bound : ℕ) (hact_le : act_bound ≤ k - 1) (μ : Fin (2 ^ (k * n)))
  (oracle : Unitary (2 ^ ((n + 1) * m))) : ghMidPPreservesAgreeOnD (ghMidPMemPrefixAgree (W := m *
  (n + 1)) act_bound μ) (ghMidPZoomRound res hm1 hkN hp hm h2p perm active kZoom) oracle := by
  let W := m * (n + 1); let M := k * n; let D := ghMidPMemPrefixAgree (W := W) act_bound μ; let P
   (C) := ghMidPPreservesAgreeOnD (Var := Var) (O := (n + 1) * m) D C oracle;
   let mP := memPrefix k (k -
  1); have pt {U} (h : ghMidPBlockDiag D U.1) : P (.step (phaseTag U)) :=
   ghMidPPreservesAgreeOnD_step_phaseTag oracle h; have q {c₁ c₂} (h₁ : P c₁) (h₂ : P c₂) : P (.seq
  c₁ c₂) := ghMidPPreservesAgreeOnD_seq h₁ h₂; have bL (A) := ghMidPBlockDiag_embedMatrix_lowBlock
   (n := n) (k := k) (W := W) act_bound μ A; have bW (U) := ghMidPBlockDiag_wtR1MemCtrlWorkUnitary
   (n := n) (k := k) (W := W) act_bound μ U; have hb (σ : Equiv.Perm (Fin (2 ^ (W + M)))) (h : ∀ z,
  D (σ z) ↔ D z) : ghMidPBlockDiag D (permutationUnitary σ).1 := fun z₁ z₂ hnz ↦ (by
  obtain rfl : z₁ = σ z₂ := (by by_contra hne; exact hnz (by rw [permutationUnitary_apply, iR0
  hne])); exact h z₂); have hw := hb (memWriteBatchPerm (k - 1) (groupHits (Nat.mul_one m))) fun z ↦
   (by unfold D ghMidPMemPrefixAgree; refine forall_congr' fun i ↦ imp_congr_right fun hi ↦ ?_; rw
        [memWriteBatchPerm, lowHighEquiv_memAddPerm, sA0, Pi.add_apply, batchDelta, iR0 (not_le.mpr
  (lt_of_lt_of_le hi hact_le)), add_zero]); have hr : P (deflatedOracle (Var := Var) (n := n) (m :=
  m) (k := k) le_rfl mP) := (by unfold deflatedOracle; rw [(by
  ext i; simp [workMemReg]; rfl : workMemReg n m k (W + M) le_rfl = QRegister.whole (W + M))]; exact
                                 q (ghMidPPreservesAgreeOnD_oracle oracle _ (by
  rw [workFullReg_embedUnitary_eq, embedUnitary_val]; exact bL _)) (pt (by
  rw [QRegister.whole_embedUnitary]; exact hb (unmarkPerm n m k mP) fun z ↦ (by
  dsimp only [D, ghMidPMemPrefixAgree, W, M]; simp only [lowHighEquiv_unmarkPerm])))); have hf := pt
   (U := (lowBlock W M).embedUnitary (flagConj n m)) (by rw [embedUnitary_val]; exact bL _); have p0
   : P (deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k) le_rfl mP) := (by
  unfold deflatedPhaseStep; exact q hf (q hr hf)); have hl := ghMidPPreservesAgreeOnD_sequence
   (replicate kZoom (ghMidPZoomGroverStep (Var := Var) (k := k) hp hm h2p perm active)) fun c hc ↦
   (by rw [(List.mem_replicate.mp hc).2]; unfold ghMidPZoomGroverStep; exact q p0 (pt (bW _)));
  unfold ghMidPZoomRound ghMidPZoomPrefix wdReadoutWrite; exact q (q (pt (bW _)) (q hl hr)) (q (pt
  hw) (ghMidPPreservesAgreeOnD_setCountAndResetWork res act_bound μ oracle _))
/-- Losslessness (`wp... ⊤ = ⊤`) for any oracle unitary. -/
def ghMidPIsWpTop {Var : Type} [DecidableEq Var] {Q O : ℕ} (C : OracleCirc Var Q O) : Prop :=
  ∀ oracle : Unitary (2 ^ O), wp (C.compile qAssign oracle) (⊤ : CQAssertion (Store Var) (2 ^ Q)) =
    ⊤
lemma ghMidPIsWpTop_skip {Var : Type} [DecidableEq Var] {Q O : ℕ} : ghMidPIsWpTop (.skip :
  OracleCirc Var Q O) := fun _ ↦ rfl
lemma ghMidPIsWpTop_step {Var : Type} [DecidableEq Var] {Q O : ℕ} (U : Unitary (2 ^ Q)) :
  ghMidPIsWpTop (.step U : OracleCirc Var Q O) := fun _ ↦ by funext σ; simp [compile]
lemma ghMidPIsWpTop_oracle {Var : Type} [DecidableEq Var] {Q O : ℕ} (r : QRegister O Q) :
  ghMidPIsWpTop (.oracle r : OracleCirc Var Q O) := fun _ ↦ by funext σ; simp [compile]
lemma ghMidPIsWpTop_seq {Var : Type} [DecidableEq Var] {Q O : ℕ} {c₁ c₂ : OracleCirc Var Q O} (h₁ :
  ghMidPIsWpTop c₁) (h₂ : ghMidPIsWpTop c₂) : ghMidPIsWpTop (.seq c₁ c₂) := fun o ↦ by
  dsimp only [compile]; rw [wp_qSeq, h₂ o, h₁ o]
lemma ghMidPIsWpTop_sequence {Var : Type} [DecidableEq Var] {Q O : ℕ} (l : List (OracleCirc Var Q
  O)) (hl : ∀ c ∈ l, ghMidPIsWpTop c) : ghMidPIsWpTop (OracleDynamicCircuit.sequence l) := by
  refine List.rec (fun _ ↦ ghMidPIsWpTop_skip) (fun c _ ih h ↦ ?_) l hl; rw [sequence_cons]; exact
   ghMidPIsWpTop_seq (h c mem_cons_self) (ih fun x u ↦ h x (List.mem_cons_of_mem c u))
lemma ghMidPIsWpTop_setCountAndResetWork {Var : Type} [DecidableEq Var] (res : Var) {W M O : ℕ} (g :
  Fin (2 ^ W) → Fin (2 ^ W)) : ghMidPIsWpTop (setCountAndResetWork (Var := Var) (M := M) (O := O)
  res g) := fun _ ↦ by
  funext σ; apply Subtype.ext; apply HermitianMat.ext; rw [← HermitianMat.val_eq_coe,
  wp_setCountAndResetWork]; have p (o) : ((lowBlock W M).embedMatrix (Matrix.single 0 o 1))ᴴ * ((⊤ :
  CQAssertion (Store Var) (2 ^ (W + M))) (Store.subst σ res (Int.ofNat (g o).val))).1.1 * (lowBlock
    W
  M).embedMatrix (Matrix.single 0 o 1) = (lowBlock W M).basisOutcomeProjector o := (by
  change _ * 1 * _ = _; rw [Matrix.mul_one, ← QRegister.embedMatrix_conjTranspose, ←
  QRegister.embedMatrix_mul, (show (Matrix.single (0 : Fin (2 ^ W)) o (1 : ℂ))ᴴ * Matrix.single 0 o
  1 = compProj o by ext i j; rw [mul_apply, compProj, sum_eq_single 0 (fun x hx ↦ by
  simp [hx.symm])]; simp only [conjTranspose_apply, Matrix.single_apply]; exact if u : o = i then
                     (by subst u; by_cases v : o = j <;> simp [v]) else (by simp [u])),
  QRegister.basisOutcomeProjector]); simp_rw [p]; exact (lowBlock W M).sum_basisOutcomeProjector
/-- `ghMidPZoomRound` is lossless (`wp... ⊤ = ⊤`). -/
lemma ghMidPIsWpTop_zoomRound {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hm1 : 1 ≤ m)
  (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (perm : Equiv.Perm (Fin (2 ^
  n))) (active kZoom : ℕ) : ghMidPIsWpTop (ghMidPZoomRound (Var := Var) res hm1 hkN hp hm h2p perm
  active kZoom) := by
  let P := ghMidPIsWpTop (Var := Var) (Q := m * (n + 1) + k * n) (O := (n + 1) * m); have s (U) : P
   (.step U) := ghMidPIsWpTop_step U; have q {c₁ c₂} (h₁ : P c₁) (h₂ : P c₂) : P (.seq c₁ c₂) :=
   ghMidPIsWpTop_seq h₁ h₂; have hr : P (deflatedOracle (Var := Var) (n := n) (m := m) (k := k)
  le_rfl (memPrefix k (k - 1))) := q (ghMidPIsWpTop_oracle _) (s _);
  have hp0 : P (deflatedPhaseStep (Var
  := Var) (n := n) (m := m) (k := k) le_rfl (memPrefix k (k - 1))) := q (s _) (q hr (s _));
  have hl :=
   ghMidPIsWpTop_sequence (replicate kZoom (ghMidPZoomGroverStep (Var := Var) (k := k) hp hm h2p
  perm active)) fun _ hc ↦ (by rw [(List.mem_replicate.mp hc).2]; exact q hp0 (s _)); unfold
   ghMidPZoomRound ghMidPZoomPrefix wdReadoutWrite; exact q (q (s _) (q hl hr)) (q (s _)
  (ghMidPIsWpTop_setCountAndResetWork res _))
/-- Concrete `(32, 4)` (`m = 32`, `p = 5`, `k = 4`, `r - 1 = 3`) middle-`p` zoom circuit. -/
noncomputable def ghMidPZoomRoundM32K4 {Var : Type} (res : Var) {n : ℕ} (hkN : 4 ≤ 2 ^ n)
    (h10 : 10 ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (kZoom : ℕ) :
    OracleCirc Var (32 * (n + 1) + 4 * n) ((n + 1) * 32) :=
  ghMidPZoomRound (k := 4) res (by decide : 1 ≤ 32) hkN (Nat.le_trans (by decide : 5 ≤ 10) h10)
    (by decide : 32 = 2 ^ 5) (Nat.le_trans (by decide : 2 * 5 ≤ 10) h10) perm 0 kZoom
/-- `(32, 4)` middle-`p` zoom round uses at most `kZoom + 1` oracle queries. -/
theorem ghMidPZoomRoundM32K4_costBound {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ} (hkN : 4 ≤
  2 ^ n) (h10 : 10 ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (kZoom : ℕ) (S : Finset (Fin (2 ^ n))) :
  CostBound (Var := Var) (CostModel.ofEmbeddedOracle (n := 32 * (n + 1) + 4 * n)
  (groverParallelMarkingOracle 32 S)) ((ghMidPZoomRoundM32K4 res hkN h10 perm kZoom).compile qAssign
  (groverParallelMarkingOracle 32 S)) ((kZoom + 1 : ℕ) : ℝ≥0) := by
  rw [ghMidPZoomRoundM32K4]; exact ghMidP_costBound_zoomRound _ _ hkN _ _ _ perm 0 kZoom S
/-- `(32, 4)` (`r = 4`, `r - 1 = 3`) unconditional QHL upper bound over `3 * 2 ^ (n - 10)`. -/
theorem ghMidPZoomRoundM32K4_wp_le {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ} (hkN : 4 ≤ 2 ^
  n) (h10 : 10 ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (kZoom : ℕ) {S : Finset (Fin (2 ^ n))} (hcard
  : S.card = 4) {ν : Fin (2 ^ (4 * n))} (hval : MemPrefixValid S 3 ν) (Θ : CQAssertion (Store Var)
    (2 ^ (32
  * (n + 1) + 4 * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν' : Fin (2 ^
  (4 * n))), s ≤ 4 → τ res = (s : ℤ) → MemPrefixValid S s ν' → (Θ τ).1.1 (workMemIdx n 32 4 0 ν')
  (workMemIdx n 32 4 0 ν') = (Ψ (S \ memSeen n 4 (memPrefix 4 s) ν') : ℂ)) (hΨ : Ψ ∅ ≤ Ψ (S \
  memSeen n 4 (memPrefix 4 3) ν)) (τ : Store Var) :
  let hp5 : 5 ≤ n := Nat.le_trans (by decide : 5 ≤ 10) h10; let hm32 : 32 = 2 ^ 5 := by decide
  let R' := S \ memSeen n 4 (memPrefix 4 3) ν; let pref := fun x ↦ subcubePref hp5 hm32 (perm x)
  let L_raw := midpRawPrefixes hp5 hm32 perm 0 ν
  let θZoom := Real.arcsin (1 / √((3 * 2 ^ (n - 10) : ℕ) : ℝ))
  let pZoom := Real.sin ((2 * (kZoom : ℝ) + 1) * θZoom) ^ 2; (((wp ((ghMidPZoomRoundM32K4 res hkN
  h10 perm kZoom).compile qAssign (groverParallelMarkingOracle 32 S)) Θ) τ).1.1 (workMemIdx n 32 4 0
  ν) (workMemIdx n 32 4 0 ν)).re ≤ if (L_raw ∩ R'.image pref).Nonempty then pZoom * Ψ ∅ + (1 -
  pZoom) * Ψ R' else Ψ R' := by
  dsimp only; rw [ghMidPZoomRoundM32K4]; exact ghMidP_wp_zoomRound_workMemIdx_le _ _ hkN _ _ _ perm
   rfl (by omega) (by omega) kZoom hcard hval Θ Ψ hΘ hΨ τ
end
end QuantumComputation.Specs.DickeSol
end GHMidPZoomQHLInlined

section GHMidPZoomDeflatedQHL
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val tensorState)
open Matrix (diagonal mulVec_mulVec mulVec_diagonal)
open Complex (normSq)
open List (finRange map_cons mem_finRange prod_cons)
open Fintype (sum_eq_single sum_prod_type)
open Pi (single)
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QProg.Notation QHLExpectation
@[expose] public section
/- ## 1. Arbitrary-Collision Slot/Product Helpers & `ghMidPAmpState` Evolution -/
private lemma extractIndex_wdCast1nReg_midp {n q : ℕ} (hq : q ≤ n) (u : Fin (2 ^ (1 * n))) :
  (wdCast1nReg hq).extractIndex u = zoomCast1nEquiv hq u := by
  apply (basisBits ((n - q) + q)).injective; funext r; rw [basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]; simp [wdCast1nReg, zoomCast1nEquiv]
private lemma agreeOutside_wdCast1nReg_midp {n q : ℕ} (hq : q ≤ n) (i j : Fin (2 ^ (1 * n))) :
    (wdCast1nReg hq).AgreeOutside i j := fun r hr ↦
  False.elim (hr ⟨⟨r.val, by omega⟩, Fin.ext (by simp [wdCast1nReg])⟩)
private lemma embedMatrix_wdCast1nReg_mulVec_comp_midp {n q : ℕ} (hq : q ≤ n) (B : Operator (2 ^ ((n
  - q) + q))) (ψ : Fin (2 ^ ((n - q) + q)) → ℂ) : (wdCast1nReg hq).embedMatrix B *ᵥ (ψ ∘
  zoomCast1nEquiv hq) = (B *ᵥ ψ) ∘ zoomCast1nEquiv hq := by
  funext i; rw [Matrix.mulVec, dotProduct]; simp_rw [QRegister.embedMatrix_apply_of_agreeOutside,
    extractIndex_wdCast1nReg_midp, agreeOutside_wdCast1nReg_midp, ite_true, mul_one]
  exact (zoomCast1nEquiv hq).sum_comp (fun y ↦ B (zoomCast1nEquiv hq i) y * ψ y)
private lemma subcubeSplit_addrEquiv_one_midp {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q) (u :
  Fin (2 ^ (1 * n))) : subcubeSplit hq hM (addrEquiv n 1 u 0) = ((lowHighEquiv (n - q) q
  (zoomCast1nEquiv hq u)).1, finCongr hM.symm (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).2) :=
  by
  have hcast : finCongr (by congr 1; omega) (addrEquiv n 1 u 0) = zoomCast1nEquiv hq u := by
    ext; rw [finCongr_apply, Fin.val_cast, addrEquiv_eq_div_pow_mod]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, finCongr_apply, Fin.val_cast]
    exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using u.isLt)
  unfold subcubeSplit; rw [Equiv.trans_apply, Equiv.trans_apply, hcast]; rfl
private lemma mem_oddSet_one_iff_midp {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) : u
  ∈ oddSet n 1 S ↔ addrEquiv n 1 u 0 ∈ S := by
  rw [oddSet, Finset.mem_filter]; simp only [Finset.mem_univ, true_and, Fin.prod_univ_one]
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h1 ↦ absurd h1 (by norm_num), fun hm ↦ absurd hm h⟩
private lemma firstTupleHit_one_eq_midp {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) :
  firstTupleHit n 1 S u = if addrEquiv n 1 u 0 ∈ S then some (addrEquiv n 1 u 0) else none := by
  unfold firstTupleHit; by_cases hu : u ∈ oddSet n 1 S
  · have hmem : addrEquiv n 1 u 0 ∈ S := (mem_oddSet_one_iff_midp S u).mp hu; rw [dite_eq_left hu,
      ite_eq_left hmem]
    exact congrArg (fun j : Fin 1 ↦ some (addrEquiv n 1 u j)) (Subsingleton.elim _ _)
  · have hnmem : addrEquiv n 1 u 0 ∉ S := mt (mem_oddSet_one_iff_midp S u).mpr hu; rw [dite_eq_right
      hu, ite_eq_right hnmem]
private lemma wdPerm1n_symm_midp {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) : (wdPerm1n perm).symm =
  wdPerm1n perm.symm := by ext u; simp [wdPerm1n]
private lemma addrEquiv_wdPerm1n_zero_midp {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) (u : Fin (2 ^
  (1 * n))) : addrEquiv n 1 (wdPerm1n perm u) 0 = perm (addrEquiv n 1 u 0) := by
  have he1n (v : Fin (2 ^ (1 * n))) : addrEquiv n 1 v 0 = finCongr (by rw [Nat.one_mul]) v := by
    ext; rw [addrEquiv_eq_div_pow_mod, finCongr_apply, Fin.val_cast]
    simp only [Fin.val_zero, pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using v.isLt)
  rw [he1n, he1n]; simp [wdPerm1n]
private lemma permUnitary_mulVec_comp_midp {d : ℕ} (σ : Equiv.Perm (Fin d)) (ψ : Fin d → ℂ) :
  (permutationUnitary σ).1 *ᵥ ψ = ψ ∘ σ.symm := by
  funext i
  rw [Matrix.mulVec, dotProduct,
    sum_eq_single (σ.symm i) (fun j hj ↦ by
      have hne : i ≠ σ j := fun h ↦ hj ((σ.symm_apply_eq).mpr h).symm
      rw [permutationUnitary_apply, ite_eq_right hne, zero_mul])]
  rw [permutationUnitary_apply, ite_eq_left (σ.apply_symm_apply i).symm, one_mul]; rfl
private lemma permUnitary_parallelMarkPerm_mulVec_apply_midp {n m : ℕ} (R : Finset (Fin (2 ^ n))) (ψ
  : Fin (2 ^ (m * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ((permutationUnitary
  (parallelMarkPerm n m R)).1 *ᵥ ψ) w = ψ (parallelMarkPerm n m R w) := by
  rw [permUnitary_mulVec_comp_midp]; dsimp only [Function.comp_apply]
  congr 1; exact Equiv.symm_apply_eq _ |>.mpr (parallelMarkPerm_involutive R w).symm
private lemma zoomSlotWrap_eq_linear_midp {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q) (perm :
  Equiv.Perm (Fin (2 ^ n))) (j_sub : Fin M_sub) (c s : ℂ) (φ₀ φ₁ : Fin (2 ^ (n - q)) → ℂ) (z : Fin
  (2 ^ (1 * (n + 1)))) : zoomSlotWrap hq hM perm j_sub (c • φ₀ + s • φ₁) z = c * zoomSlotWrap hq hM
  perm j_sub φ₀ z + s * zoomSlotWrap hq hM perm j_sub φ₁ z := by
  dsimp only [zoomSlotWrap, tensorState, workMemState, Function.comp_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]; ring
private lemma prod_groupReg_embedMatrix_mulVec_midp {n m b g : ℕ} (hbg : b * g = m) (A : Fin b →
  Matrix (Fin (2 ^ (g * (n + 1)))) (Fin (2 ^ (g * (n + 1)))) ℂ) (f : Fin b → Fin (2 ^ (g * (n + 1)))
  → ℂ) : ((finRange b).map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod *ᵥ (fun w ↦ ∏ c : Fin b,
  f c ((groupReg hbg c).extractIndex w)) = fun w ↦ ∏ c : Fin b, (A c *ᵥ f c) ((groupReg hbg
  c).extractIndex w) := by
  suffices ∀ l : List (Fin b), l.Nodup → ((l.map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod)
    *ᵥ (fun w ↦ ∏ c : Fin b, f c ((groupReg hbg c).extractIndex w)) = fun w ↦ ∏ c : Fin b, (if c ∈ l
    then A c *ᵥ f c else f c) ((groupReg hbg c).extractIndex w) by
    rw [this (finRange b) (List.nodup_finRange b)]; funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_left (mem_finRange c)]
  intro l hl
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]; funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_right List.not_mem_nil]
  | cons c₀ l ih =>
    rcases List.nodup_cons.mp hl with ⟨hc₀, hl'⟩; rw [map_cons, prod_cons, ← mulVec_mulVec, ih hl',
      embedMatrix_groupReg_mulVec_prod]; funext w; refine Finset.prod_congr rfl fun c _ ↦ ?_
    by_cases h : c = c₀
    · subst h; rw [ite_eq_left rfl, ite_eq_right hc₀, ite_eq_left List.mem_cons_self]
    · have hmem : c ∈ c₀ :: l ↔ c ∈ l := (by simp [List.mem_cons, h]); by_cases hl_mem : c ∈ l
      · rw [ite_eq_left (hmem.mpr hl_mem), ite_eq_right h, ite_eq_left hl_mem]
      · rw [ite_eq_right (mt hmem.mp hl_mem), ite_eq_right h, ite_eq_right hl_mem]
private lemma wdPrepUnitary_mulVec_workMemIdx_midp {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm
  : Equiv.Perm (Fin (2 ^ n))) (μ : Fin (2 ^ (k * n))) : (lowBlock (m * (n + 1)) (k * n)).embedMatrix
  (wdPrepUnitary hp hm perm).1 *ᵥ single (workMemIdx n m k 0 μ) 1 = workMemState (zoomProdState fun
  j ↦ zoomSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0 1)) (single μ 1) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hex0 : (addrReg n 1).extractIndex 0 = 0 :=
    (by apply (basisBits (1 * n)).injective; funext r; simp [basisBits_extractIndex])
  have henv0 : ((addrReg n 1).basisSplitEquiv 0).2 = 0 :=
    (by funext e; simp [QRegister.basisSplitEquiv])
  have hzero_comp : (single (0 : Fin (2 ^ (1 * n))) (1 : ℂ)) = workMemState (single (0 : Fin (2 ^ (n
    - p))) 1) (single (0 : Fin (2 ^ p)) 1) ∘ zoomCast1nEquiv hp := by
    rw [workMemState_zero]; funext u; dsimp only [Function.comp_apply]; by_cases hu : u = 0
    · subst hu; have hc0 : zoomCast1nEquiv hp 0 = 0 := Fin.ext (by simp [zoomCast1nEquiv]); rw [hc0,
        Pi.single_eq_same, Pi.single_eq_same]
    · have hcne : zoomCast1nEquiv hp u ≠ 0 := fun h ↦ hu ((zoomCast1nEquiv hp).injective (h.trans
        (Fin.ext (by simp [zoomCast1nEquiv])).symm)); rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne
        hcne]
  have hprep_slot (j : Fin m) : (wdSlotPrep hp hm perm j).1 *ᵥ single (0 : Fin (2 ^ (1 * (n + 1))))
    1 = zoomSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0 1) := by
    unfold wdSlotPrep zoomSlotWrap; rw [Submonoid.coe_mul, embedUnitary_val, embedUnitary_val, ←
      mulVec_mulVec, QRegister.embedMatrix_mulVec_single_factors, hex0, henv0, embedUnitary_val,
      Submonoid.coe_mul, embedUnitary_val, embedUnitary_val, hzero_comp,
      embedMatrix_wdCast1nReg_mulVec_comp_midp, ← mulVec_mulVec,
      embedMatrix_highBlock_mulVec_workMemState, permutationUnitary_mulVec_single,
      Equiv.swap_apply_left, embedMatrix_lowBlock_mulVec_workMemState,
      QRegister.embedMatrix_mulVec_tensorState, permUnitary_mulVec_comp_midp, wdPerm1n_symm_midp,
      Equiv.symm_symm]; rfl
  have hsub0 : zoomProdState (n := n) (fun _ : Fin m ↦ single 0 1) = single 0 1 := by
    have hex_g0 (c : Fin m) : (groupReg (n := n) hbg1 c).extractIndex 0 = 0 :=
      (by apply (basisBits (1 * (n + 1))).injective; funext r; simp [basisBits_extractIndex])
    funext w; unfold zoomProdState; by_cases hw : w = 0
    · subst hw; simp [hex_g0]
    · rw [Pi.single_eq_of_ne hw]
      have hne : ∃ c : Fin m, (groupReg hbg1 c).extractIndex w ≠ 0 := by
        by_contra hall; apply hw; apply (groupSplitEquiv hbg1).injective; funext c
        have hc0 : (groupReg hbg1 c).extractIndex w = 0 := (by by_contra hnc; exact hall ⟨c, hnc⟩)
        rw [groupSplitEquiv_apply, groupSplitEquiv_apply, hc0, hex_g0 c]
      obtain ⟨c, hc⟩ := hne; exact Finset.prod_eq_zero (Finset.mem_univ c) (Pi.single_eq_of_ne hc 1)
  rw [workMemIdx, ← workMemState_single, embedMatrix_lowBlock_mulVec_workMemState, ← hsub0]
  have hcoe : (wdPrepUnitary hp hm perm).1 = ((finRange m).map fun j ↦ (groupReg hbg1 j).embedMatrix
    (wdSlotPrep hp hm perm j).1).prod := by
    unfold wdPrepUnitary; rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  unfold zoomProdState; rw [hcoe, prod_groupReg_embedMatrix_mulVec_midp hbg1 _ (fun _ ↦ single 0 1)]
  simp_rw [hprep_slot]
private lemma oracleMat_oddSet_one_mulVec_wdPerm1n_midp {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) (R
  : Finset (Fin (2 ^ n))) (ψ : Fin (2 ^ (1 * n)) → ℂ) : oracleMat (oddSet n 1 R) *ᵥ (ψ ∘ wdPerm1n
  perm) = (oracleMat (oddSet n 1 (R.image perm)) *ᵥ ψ) ∘ wdPerm1n perm := by
  funext u; rw [oracleMat, mulVec_diagonal]; dsimp only [Function.comp_apply]; rw [oracleMat,
    mulVec_diagonal]
  have hiff : u ∈ oddSet n 1 R ↔ wdPerm1n perm u ∈ oddSet n 1 (R.image perm) := by
    rw [mem_oddSet_one_iff_midp, mem_oddSet_one_iff_midp, addrEquiv_wdPerm1n_zero_midp]
    refine ⟨Finset.mem_image_of_mem perm, fun h ↦ ?_⟩; rcases Finset.mem_image.mp h with ⟨y, hy,
      heq⟩; rwa [← perm.injective heq]
  rw [if_congr hiff rfl rfl]
private lemma oracleMat_oddSet_one_mulVec_subcube_midp {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2
  ^ q) (T : Finset (Fin (2 ^ n))) (j_sub : Fin M_sub) (ψ : Fin (2 ^ (n - q)) → ℂ) : oracleMat
  (oddSet n 1 T) *ᵥ (workMemState ψ (single (finCongr hM j_sub) 1) ∘ zoomCast1nEquiv hq) =
  workMemState (oracleMat (subcubeLocalSet hq hM T j_sub) *ᵥ ψ) (single (finCongr hM j_sub) 1) ∘
  zoomCast1nEquiv hq := by
  funext u; rw [oracleMat, mulVec_diagonal]; dsimp only [Function.comp_apply, workMemState]
  rw [oracleMat, mulVec_diagonal]; by_cases hj : (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).2 =
    finCongr hM j_sub
  · have hsp := subcubeSplit_addrEquiv_one_midp hq hM u; have hfc : finCongr hM.symm (finCongr hM
      j_sub) = j_sub := (by ext; simp); rw [hj, hfc] at hsp
    have hiff : u ∈ oddSet n 1 T ↔ (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).1 ∈
      subcubeLocalSet hq hM T j_sub :=
      (by rw [mem_oddSet_one_iff_midp, mem_subcubeLocalSet_iff, ← hsp, Equiv.symm_apply_apply])
    rw [hj, Pi.single_eq_same, mul_one, mul_one, if_congr hiff rfl rfl]
  · rw [Pi.single_eq_of_ne hj]; ring
private lemma wdDiffuser_mulVec_sDiagM_zoomProdState_midp {n q M_sub m : ℕ} (hq : q ≤ n) (hM : M_sub
  = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (jSub : Fin m → Fin M_sub)
  (φ : Fin m → Fin (2 ^ (n - q)) → ℂ) : (wdDiffuserUnitary (m := m) hq perm).1 *ᵥ (sDiagM n m R *ᵥ
  zoomProdState (fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂) (φ j₂))) = zoomProdState (fun j₂ ↦
  zoomSlotWrap hq hM perm (jSub j₂) (Grover.diffuserMatrix *ᵥ (oracleMat (subcubeLocalSet hq hM
  (R.image perm) (jSub j₂)) *ᵥ φ j₂))) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hdiff_coe : (wdDiffuserUnitary (m := m) hq perm).1 = ((finRange m).map fun j₂ ↦ (groupReg
    hbg1 j₂).embedMatrix (wdSlotDiffuser hq perm).1).prod := by
    unfold wdDiffuserUnitary; rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  rw [sDiagM_eq_prod_groupReg hbg1 R]; unfold zoomProdState
  rw [prod_groupReg_embedMatrix_mulVec_midp hbg1]
  have hslot_p (j₂ : Fin m) : sDiagM n 1 R *ᵥ zoomSlotWrap hq hM perm (jSub j₂) (φ j₂) = (addrReg n
    1).tensorState ((workMemState (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ
    j₂) (single (finCongr hM (jSub j₂)) 1) ∘ zoomCast1nEquiv hq) ∘ wdPerm1n perm) (single 0 1) := by
    unfold zoomSlotWrap; rw [sDiagM_mulVec_tensorState_zero,
      oracleMat_oddSet_one_mulVec_wdPerm1n_midp, oracleMat_oddSet_one_mulVec_subcube_midp]
  simp_rw [hslot_p]; rw [hdiff_coe, prod_groupReg_embedMatrix_mulVec_midp hbg1]
  have hslot_d (j₂ : Fin m) : (wdSlotDiffuser hq perm).1 *ᵥ (addrReg n 1).tensorState ((workMemState
    (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂) (single (finCongr hM (jSub
    j₂)) 1) ∘ zoomCast1nEquiv hq) ∘ wdPerm1n perm) (single 0 1) = zoomSlotWrap hq hM perm (jSub j₂)
    (Grover.diffuserMatrix *ᵥ (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂))
    := by
    unfold wdSlotDiffuser zoomSlotWrap; rw [Submonoid.coe_mul, Submonoid.coe_mul, (addrReg n
      1).embedUnitary_val, (addrReg n 1).embedUnitary_val, (addrReg n 1).embedUnitary_val,
      Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, QRegister.embedMatrix_mulVec_tensorState,
      permUnitary_mulVec_comp_midp]; have hcancel : (((workMemState (oracleMat (subcubeLocalSet hq
      hM (R.image perm) (jSub j₂)) *ᵥ φ j₂) (single (finCongr hM (jSub j₂)) 1) ∘ zoomCast1nEquiv hq)
      ∘ wdPerm1n perm) ∘ (wdPerm1n perm).symm) = workMemState (oracleMat (subcubeLocalSet hq hM
      (R.image perm) (jSub j₂)) *ᵥ φ j₂) (single (finCongr hM (jSub j₂)) 1) ∘ zoomCast1nEquiv hq :=
      (by funext v; simp); rw [hcancel, QRegister.embedMatrix_mulVec_tensorState, embedUnitary_val,
      embedMatrix_wdCast1nReg_mulVec_comp_midp, embedUnitary_val,
      embedMatrix_lowBlock_mulVec_workMemState, QRegister.embedMatrix_mulVec_tensorState,
      permUnitary_mulVec_comp_midp, wdPerm1n_symm_midp, Equiv.symm_symm]; rfl
  simp_rw [hslot_d]
private lemma ghDeflatedGrover_iter_zoomProdState_midp {n q M_sub m k : ℕ} (hq : q ≤ n) (hM : M_sub
  = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^
  (k * n))} (hsub : memSeen n k (memPrefix k active) μ ⊆ S) (jSub : Fin m → Fin M_sub) (φ : Fin m →
  Fin (2 ^ (n - q)) → ℂ) (t : ℕ) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hq perm).1
    ((diffOp * phaseOp) ^ t) *ᵥ workMemState (zoomProdState fun j₂ ↦ zoomSlotWrap hq hM perm (jSub
      j₂) (φ j₂)) (single μ 1) = workMemState (zoomProdState fun j₂ ↦ zoomSlotWrap hq hM perm (jSub
      j₂) ((fun ψ ↦ Grover.diffuserMatrix *ᵥ (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub
      j₂)) *ᵥ ψ))^[t] (φ j₂))) (single μ 1) := by
  intro W M R fc orac unm phaseOp diffOp
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, ih]
    have hp_step : phaseOp *ᵥ workMemState (zoomProdState fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂)
      ((fun ψ ↦ Grover.diffuserMatrix *ᵥ (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂))
      *ᵥ ψ))^[t] (φ j₂))) (single μ 1) = workMemState (sDiagM n m R *ᵥ zoomProdState fun j₂ ↦
      zoomSlotWrap hq hM perm (jSub j₂) ((fun ψ ↦ Grover.diffuserMatrix *ᵥ (oracleMat
      (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ ψ))^[t] (φ j₂))) (single μ 1) := by
      simpa [phaseOp, fc, unm, orac, R, Matrix.mul_assoc] using deflatedPhaseMat_mulVec_workMemState
        (memPrefix k active) _ μ hsub
    rw [hp_step]; dsimp only [diffOp]; rw [embedMatrix_lowBlock_mulVec_workMemState,
      wdDiffuser_mulVec_sDiagM_zoomProdState_midp]; simp only [Function.iterate_succ_apply']
private lemma zoomSlotWrap_support_firstMarkedAddr_midp {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2
  ^ q) (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (j_sub : Fin M_sub) (φ : Fin (2
  ^ (n - q)) → ℂ) (z : Fin (2 ^ (1 * (n + 1)))) (hz : zoomSlotWrap hq hM perm j_sub φ z ≠ 0) :
    let u := (addrReg n 1).extractIndex z
    let w_loc := (lowHighEquiv (n - q) q (zoomCast1nEquiv hq (wdPerm1n perm u))).1
    ((addrReg n 1).basisSplitEquiv z).2 = 0 ∧ φ w_loc ≠ 0 ∧ (lowHighEquiv (n - q) q (zoomCast1nEquiv
      hq (wdPerm1n perm u))).2 = finCongr hM j_sub ∧ firstMarkedAddr n 1 (parallelMarkPerm n 1 R z)
      = if w_loc ∈ subcubeLocalSet hq hM (R.image perm) j_sub then some (perm.symm ((subcubeSplit hq
      hM).symm (w_loc, j_sub))) else none := by
  intro u w_loc
  have hE : ((addrReg n 1).basisSplitEquiv z).2 = 0 := by
    by_contra hne
    apply hz; dsimp only [zoomSlotWrap, tensorState]; rw [Pi.single_eq_of_ne hne, mul_zero]
  have hy : (lowHighEquiv (n - q) q (zoomCast1nEquiv hq (wdPerm1n perm u))).2 = finCongr hM j_sub
    := by
    by_contra hne
    apply hz; dsimp only [zoomSlotWrap, tensorState, workMemState, Function.comp_apply]
    rw [Pi.single_eq_of_ne hne, mul_zero, zero_mul]
  have hφ : φ w_loc ≠ 0 := by
    intro h0; apply hz; dsimp only [zoomSlotWrap, tensorState, workMemState, Function.comp_apply]
    rw [h0, zero_mul, zero_mul]
  refine ⟨hE, hφ, hy, ?_⟩; rw [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R z hE,
    firstTupleHit_one_eq_midp]; set v := wdPerm1n perm u; have hu_eq : u = (wdPerm1n perm).symm v :=
    (Equiv.symm_apply_apply _ u).symm; have hsp := subcubeSplit_addrEquiv_one_midp hq hM v
  have hfc : finCongr hM.symm (finCongr hM j_sub) = j_sub := (by ext; simp); rw [hy, hfc] at hsp
  have hv_addr : addrEquiv n 1 v 0 = (subcubeSplit hq hM).symm (w_loc, j_sub) :=
    (by rw [← hsp, Equiv.symm_apply_apply])
  have hu_addr : addrEquiv n 1 u 0 = perm.symm ((subcubeSplit hq hM).symm (w_loc, j_sub)) :=
    (by rw [hu_eq, wdPerm1n_symm_midp, addrEquiv_wdPerm1n_zero_midp, hv_addr])
  have hmem_iff : addrEquiv n 1 u 0 ∈ R ↔ w_loc ∈ subcubeLocalSet hq hM (R.image perm) j_sub := by
    rw [hu_addr, mem_subcubeLocalSet_iff]; refine ⟨fun hxR ↦
      by simpa using Finset.mem_image_of_mem perm hxR, fun himg ↦ ?_⟩
    rcases Finset.mem_image.mp himg with ⟨x, hxR, hx_perm⟩; have hxeq : x = perm.symm ((subcubeSplit
      hq hM).symm (w_loc, j_sub)) := (by rw [← hx_perm, Equiv.symm_apply_apply])
    rwa [← hxeq]
  rw [if_congr hmem_iff rfl rfl, hu_addr]
private lemma groupHits_of_zoomSlotWrap_midp {n q M_sub m : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
  (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (jSub : Fin m → Fin M_sub) (φ : Fin m
  → Fin (2 ^ (n - q)) → ℂ) (o : Fin (2 ^ (m * (n + 1)))) (hslot_nz : ∀ j₂ : Fin m, zoomSlotWrap hq
  hM perm (jSub j₂) (φ j₂) ((groupReg (Nat.mul_one m) j₂).extractIndex (parallelMarkPerm n m R o)) ≠
  0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∀ (j₂ : Fin m) (x : Fin (2 ^ n)), firstMarkedAddr n 1 ((groupReg hbg1 j₂).extractIndex o) =
      some x → x ∈ R ∧ subcubePref hq hM (perm x) = jSub j₂) ∧ (groupHits hbg1 o).toFinset =
      ((finRange m).filterMap fun j₂ ↦ firstMarkedAddr n 1 ((groupReg hbg1 j₂).extractIndex
      o)).toFinset := by
  intro hbg1
  have hmem_sub (j₂ : Fin m) (x : Fin (2 ^ n)) (hx : firstMarkedAddr n 1 ((groupReg hbg1
    j₂).extractIndex o) = some x) : x ∈ R ∧ subcubePref hq hM (perm x) = jSub j₂ := by
    set w := parallelMarkPerm n m R o; have ho_eq : o = parallelMarkPerm n m R w :=
      (parallelMarkPerm_involutive R o).symm
    have hsp := zoomSlotWrap_support_firstMarkedAddr_midp hq hM perm R (jSub j₂) (φ j₂) _ (hslot_nz
      j₂); have hex_o : (groupReg hbg1 j₂).extractIndex o = parallelMarkPerm n 1 R ((groupReg hbg1
      j₂).extractIndex w) := (by rw [ho_eq, extractIndex_groupReg_parallelMarkPerm]); rw [hex_o,
      hsp.2.2.2] at hx; set w_loc := (lowHighEquiv (n - q) q (zoomCast1nEquiv hq (wdPerm1n perm
      ((addrReg n 1).extractIndex ((groupReg hbg1 j₂).extractIndex w))))).1
    by_cases hmem : w_loc ∈ subcubeLocalSet hq hM (R.image perm) (jSub j₂)
    · rw [ite_eq_left hmem, Option.some.injEq] at hx; subst hx; have h_perm :=
        (mem_subcubeLocalSet_iff hq hM (R.image perm) (jSub j₂) w_loc).mp hmem
      rcases Finset.mem_image.mp h_perm with ⟨y, hyR, hy_perm⟩
      have hyeq : y = perm.symm ((subcubeSplit hq hM).symm (w_loc, jSub j₂)) :=
        (by rw [← hy_perm, Equiv.symm_apply_apply]); refine ⟨hyeq ▸ hyR, ?_⟩
      dsimp only [subcubePref]; rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · rw [ite_eq_right hmem] at hx; cases hx
  refine ⟨hmem_sub, ?_⟩; unfold groupHits; exact List.toFinset_dedup
private lemma groupHits_eq_filterMap_of_zoomSlotWrap_midp {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
  (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (φ : Fin m → Fin (2 ^ (n - p)) → ℂ)
  (o : Fin (2 ^ (m * (n + 1)))) (hslot_nz : ∀ j : Fin m, zoomSlotWrap hp hm perm j (φ j) ((groupReg
  (Nat.mul_one m) j).extractIndex (parallelMarkPerm n m R o)) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∀ (j : Fin m) (x : Fin (2 ^ n)), firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) = some
      x → x ∈ R ∧ subcubePref hp hm (perm x) = j) ∧ groupHits hbg1 o = (finRange m).filterMap fun j
      ↦ firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) := by
  intro hbg1; have hhit_sub := (groupHits_of_zoomSlotWrap_midp hp hm perm R id φ o hslot_nz).1
  have hfm_nodup : ∀ (l : List (Fin m)), l.Nodup → (l.filterMap fun j ↦ firstMarkedAddr n 1
    ((groupReg hbg1 j).extractIndex o)).Nodup := by
    intro l hl
    induction l with
    | nil => exact List.nodup_nil
    | cons j js ih =>
      rcases List.nodup_cons.mp hl with ⟨hj_not, hjs_nd⟩
      cases hfa : firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) with
      | none => simp only [List.filterMap_cons, hfa]; exact ih hjs_nd
      | some x =>
        simp only [List.filterMap_cons, hfa, List.nodup_cons]; refine ⟨fun hmem ↦ ?_, ih hjs_nd⟩
        rcases List.mem_filterMap.mp hmem with ⟨j', hj'mem, hj'eq⟩; have hjeq : j = j' := (hhit_sub
          j x hfa).2.symm.trans (hhit_sub j' x hj'eq).2; exact hj_not (hjeq ▸ hj'mem)
  refine ⟨hhit_sub, ?_⟩; unfold groupHits; exact List.dedup_eq_self.mpr (hfm_nodup (finRange m)
    (List.nodup_finRange m))
private lemma sum_normSq_zoomSlotWrap_of_norm_midp {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
  (perm : Equiv.Perm (Fin (2 ^ n))) (j_sub : Fin M_sub) (φ : Fin (2 ^ (n - q)) → ℂ) (S_norm : ℝ) (hφ
  : (∑ u : Fin (2 ^ (n - q)), normSq (φ u)) = S_norm) : (∑ z : Fin (2 ^ (1 * (n + 1))), normSq
  (zoomSlotWrap hq hM perm j_sub φ z)) = S_norm := by
  rw [← (addrReg n 1).basisSplitEquiv.symm.sum_comp, sum_prod_type]
  have hflag (u : Fin (2 ^ (1 * n))) : (∑ e, normSq (zoomSlotWrap hq hM perm j_sub φ ((addrReg n
    1).basisSplitEquiv.symm (u, e)))) = normSq (((workMemState φ (single (finCongr hM j_sub) 1) ∘
    zoomCast1nEquiv hq) ∘ wdPerm1n perm) u) := by
    rw [sum_eq_single 0 (fun e he ↦ by
      dsimp only [zoomSlotWrap, tensorState]; rw [← QRegister.basisSplitEquiv_apply_fst,
        Equiv.apply_symm_apply]; dsimp only
      rw [Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero])]
    dsimp only [zoomSlotWrap, tensorState]; rw [← QRegister.basisSplitEquiv_apply_fst,
      Equiv.apply_symm_apply]; dsimp only; rw [Pi.single_eq_same, mul_one]
  simp_rw [hflag]; rw [← (wdPerm1n perm).symm.sum_comp]; simp only [Function.comp_apply,
    Equiv.apply_symm_apply]; rw [← (zoomCast1nEquiv hq).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]; rw [← (lowHighEquiv (n - q) q).symm.sum_comp, sum_prod_type]
  have hhigh (w_loc : Fin (2 ^ (n - q))) : (∑ y : Fin (2 ^ q), normSq (workMemState φ (single
    (finCongr hM j_sub) 1) ((lowHighEquiv (n - q) q).symm (w_loc, y)))) = normSq (φ w_loc) := by
    rw [sum_eq_single (finCongr hM j_sub) (fun y hy ↦ by
      dsimp only [workMemState]; rw [Equiv.apply_symm_apply]; dsimp only
      rw [Pi.single_eq_of_ne hy, mul_zero, Complex.normSq_zero])]
    dsimp only [workMemState]; rw [Equiv.apply_symm_apply]; dsimp only; rw [Pi.single_eq_same,
      mul_one]
  simp_rw [hhigh]; exact hφ
private lemma sum_normSq_zoomProdState_midp {n m : ℕ} (ξ : Fin m → Fin (2 ^ (1 * (n + 1))) → ℂ) : (∑
  w : Fin (2 ^ (m * (n + 1))), normSq (zoomProdState ξ w)) = ∏ j : Fin m, ∑ z : Fin (2 ^ (1 * (n +
  1))), normSq (ξ j z) := by
  let hbg1 : m * 1 = m := Nat.mul_one m; rw [← (groupSplitEquiv hbg1).symm.sum_comp]
  have hex (g : Fin m → Fin (2 ^ (1 * (n + 1)))) : normSq (zoomProdState ξ ((groupSplitEquiv
    hbg1).symm g)) = ∏ j : Fin m, normSq (ξ j (g j)) := by
    unfold zoomProdState; rw [map_prod]; refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
  simp_rw [hex]; exact (Fintype.prod_sum fun j z ↦ normSq (ξ j z)).symm
private lemma card_subcubeLocalSet_image_perm_midp {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (j : Fin m) : (subcubeLocalSet hp hm (R.image
  perm) j).card = ghMidPOcc (fun x ↦ subcubePref hp hm (perm x)) R j := by
  rw [card_subcubeLocalSet_eq, ghMidPOcc]
  have himg : ((R.image perm).filter fun y ↦ subcubePref hp hm y = j) = (R.filter fun x ↦
    subcubePref hp hm (perm x) = j).image perm := by
    ext y; simp only [Finset.mem_filter, Finset.mem_image]; exact ⟨fun ⟨⟨x, hxR, hxp⟩, hj⟩ ↦ ⟨x,
      ⟨hxR, hxp ▸ hj⟩, hxp⟩, fun ⟨x, ⟨hxR, hj⟩, hxp⟩ ↦ ⟨⟨x, hxR, hxp⟩, hxp ▸ hj⟩⟩
  rw [himg, Finset.card_image_of_injective _ perm.injective]
private lemma gh_length_filterMap_fin_eq_length_filter {m d : ℕ} (p : Fin m → Option (Fin d)) (l :
  List (Fin m)) : (l.filterMap p).length = (l.filter fun a ↦ (p a).isSome).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hpa : p a <;> simp [List.filterMap_cons_none, List.filterMap_cons_some, hpa, ih]
private lemma ghBasisVec_support_props_midp {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) {A : Finset (Fin m)} (hA : A ⊆ R.image fun x
  ↦ subcubePref hp hm (perm x)) (o : Fin (2 ^ (m * (n + 1)))) (hamp : ghBasisVec hp hm perm R A
  (parallelMarkPerm n m R o) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m; let pref := fun x ↦ subcubePref hp hm (perm x)
    (∀ j : Fin m, ((addrReg n 1).basisSplitEquiv ((groupReg hbg1 j).extractIndex (parallelMarkPerm n
      m R o))).2 = 0) ∧ (∀ j : Fin m, (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex
      o)).isSome = (if j ∈ A then true else false)) ∧ (∀ x ∈ groupHits hbg1 o, x ∈ R) ∧
      (groupHits hbg1 o).toFinset.image pref = A ∧ wdHitCount n m o = A.card := by
  intro hbg1 pref; set w := parallelMarkPerm n m R o; have ho_eq : o = parallelMarkPerm n m R w :=
    (parallelMarkPerm_involutive R o).symm
  have hslot_nz (j : Fin m) : zoomSlotWrap hp hm perm j (if j ∈ R.image pref then if j ∈ A then
    grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1 else grover2DVec (subcubeLocalSet hp hm
    (R.image perm) j) 1 0 else groverMultiState ∅ 0) ((groupReg hbg1 j).extractIndex w) ≠ 0 := fun
    h0 ↦ hamp (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  have hflags (j : Fin m) : ((addrReg n 1).basisSplitEquiv ((groupReg hbg1 j).extractIndex w)).2 = 0
    := (zoomSlotWrap_support_firstMarkedAddr_midp hp hm perm R j _ _ (hslot_nz j)).1
  have hisSome (j : Fin m) : (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome =
    (if j ∈ A then true else false) := by
    have hsp := zoomSlotWrap_support_firstMarkedAddr_midp hp hm perm R j _ _ (hslot_nz j)
    have hex_o : (groupReg hbg1 j).extractIndex o = parallelMarkPerm n 1 R ((groupReg hbg1
      j).extractIndex w) := (by rw [ho_eq, extractIndex_groupReg_parallelMarkPerm]); rw [hex_o,
      hsp.2.2.2]; have hφ := hsp.2.1; set w_loc := (lowHighEquiv (n - p) p (zoomCast1nEquiv hp
      (wdPerm1n perm ((addrReg n 1).extractIndex ((groupReg hbg1 j).extractIndex w))))).1
    change _ ≠ 0 at hφ; by_cases hjA : j ∈ A
    · have hjR : j ∈ R.image pref := hA hjA; rw [ite_eq_left hjR, ite_eq_left hjA] at hφ
      have hw_mem : w_loc ∈ subcubeLocalSet hp hm (R.image perm) j := by
        by_contra hnot; apply hφ
        unfold grover2DVec; rw [ite_eq_right hnot, zero_div, Complex.ofReal_zero]
      rw [ite_eq_left hw_mem, ite_eq_left hjA]; rfl
    · by_cases hjR : j ∈ R.image pref
      · rw [ite_eq_left hjR, ite_eq_right hjA] at hφ
        have hw_not : w_loc ∉ subcubeLocalSet hp hm (R.image perm) j := by
          intro hmem; apply hφ; unfold grover2DVec; rw [ite_eq_left hmem, zero_div,
            Complex.ofReal_zero]
        rw [ite_eq_right hw_not, ite_eq_right hjA]; rfl
      · have hc0 : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
          rw [card_subcubeLocalSet_image_perm_midp, ghMidPOcc, Finset.card_eq_zero,
            Finset.filter_eq_empty_iff]; intro x hxR heq; exact hjR (heq ▸ Finset.mem_image_of_mem _
            hxR)
        have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0
        rw [hemp, ite_eq_right (Finset.notMem_empty w_loc), ite_eq_right hjA]; rfl
  have hnew : ∀ x ∈ groupHits hbg1 o, x ∈ R :=
    (by intro x hx; rw [ho_eq] at hx; exact mem_of_mem_groupHits_parallelMarkPerm hbg1 hflags hx)
  rcases groupHits_eq_filterMap_of_zoomSlotWrap_midp hp hm perm R _ o hslot_nz with ⟨hhit_sub,
    hgh_eq⟩
  have himg_A : (groupHits hbg1 o).toFinset.image pref = A := by
    ext j; simp only [Finset.mem_image, List.mem_toFinset]; constructor
    · rintro ⟨x, hx_gh, rfl⟩; rw [hgh_eq, List.mem_filterMap] at hx_gh; rcases hx_gh with ⟨j', _,
        hj'eq⟩
      have hpx := (hhit_sub j' x hj'eq).2; have hsome_j' :
          (firstMarkedAddr n 1 ((groupReg hbg1 j').extractIndex o)).isSome = true := by
        rw [hj'eq]; rfl
      have hj'A : j' ∈ A := by
        by_contra hn; rw [hisSome j', ite_eq_right hn] at hsome_j'; cases hsome_j'
      dsimp only [pref]; exact hpx ▸ hj'A
    · intro hjA; have hsome_j : (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome =
        true := (by rw [hisSome j, ite_eq_left hjA])
      rcases Option.isSome_iff_exists.mp hsome_j with ⟨x, hx_eq⟩; refine ⟨x, ?_, (hhit_sub j x
        hx_eq).2⟩; rw [hgh_eq, List.mem_filterMap]; exact ⟨j, mem_finRange j, hx_eq⟩
  have hhit_card : wdHitCount n m o = A.card := by
    unfold wdHitCount; change (groupHits hbg1 o).length = A.card; rw [hgh_eq,
      gh_length_filterMap_fin_eq_length_filter]; have hfilt_eq : ((finRange m).filter fun j ↦
      (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome) = (finRange m).filter (fun j
      ↦ (if j ∈ A then true else false)) := List.filter_congr fun j _ ↦ hisSome j
    rw [hfilt_eq, ← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
    congr 1; ext j; by_cases hj : j ∈ A <;> simp [hj]
  exact ⟨hflags, hisSome, hnew, himg_A, hhit_card⟩
private lemma ghBasisVec_mul_eq_zero_of_ne_midp {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) {A₁ A₂ : Finset (Fin m)} (hA₁ : A₁ ⊆ R.image
  fun x ↦ subcubePref hp hm (perm x)) (hA₂ : A₂ ⊆ R.image fun x ↦ subcubePref hp hm (perm x)) (hne :
  A₁ ≠ A₂) (w : Fin (2 ^ (m * (n + 1)))) : ghBasisVec hp hm perm R A₁ w = 0 ∨ ghBasisVec hp hm perm
  R A₂ w = 0 := by
  by_contra hboth
  rcases not_or.mp hboth with ⟨h1_nz, h2_nz⟩; set o := parallelMarkPerm n m R w; have hw : w =
    parallelMarkPerm n m R o := (parallelMarkPerm_involutive R w).symm
  rw [hw] at h1_nz h2_nz; have h1 := (ghBasisVec_support_props_midp hp hm perm R hA₁ o h1_nz).2.1
  have h2 := (ghBasisVec_support_props_midp hp hm perm R hA₂ o h2_nz).2.1; apply hne; ext j
  have heq := (h1 j).symm.trans (h2 j)
  by_cases hj1 : j ∈ A₁ <;> by_cases hj2 : j ∈ A₂ <;> simp [hj1, hj2] at heq ⊢
private lemma ghMidPOcc_pos_and_lt {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin
  (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hR_lt : R.card < 2 ^ (n - p)) {j : Fin m} (hj : j ∈ R.image
  fun x ↦ subcubePref hp hm (perm x)) : 0 < (subcubeLocalSet hp hm (R.image perm) j).card ∧
  (subcubeLocalSet hp hm (R.image perm) j).card < 2 ^ (n - p) := by
  rw [card_subcubeLocalSet_image_perm_midp]; rcases Finset.mem_image.mp hj with ⟨x, hxR, hxj⟩
  have hpos : 0 < ghMidPOcc (fun y ↦ subcubePref hp hm (perm y)) R j := Finset.card_pos.mpr ⟨x,
    Finset.mem_filter.mpr ⟨hxR, hxj⟩⟩
  have hle : ghMidPOcc (fun y ↦ subcubePref hp hm (perm y)) R j ≤ R.card := Finset.card_filter_le _
    _; exact ⟨hpos, lt_of_le_of_lt hle hR_lt⟩
private lemma sum_normSq_ghBasisVec_midp {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hR_lt : R.card < 2 ^ (n - p)) (A : Finset
  (Fin m)) : (∑ w : Fin (2 ^ (m * (n + 1))), normSq (ghBasisVec hp hm perm R A w)) = 1 := by
  unfold ghBasisVec; rw [sum_normSq_zoomProdState_midp]
  refine Finset.prod_eq_one fun j _ ↦ sum_normSq_zoomSlotWrap_of_norm_midp hp hm perm j _ 1 ?_
  by_cases hj : j ∈ R.image (fun x ↦ subcubePref hp hm (perm x))
  · rw [ite_eq_left hj]; rcases ghMidPOcc_pos_and_lt hp hm perm hR_lt hj with ⟨h0, hlt⟩
    by_cases hjA : j ∈ A
    · rw [ite_eq_left hjA]; exact sum_normSq_grover2DVec_zero_one _ h0
    · rw [ite_eq_right hjA]; exact sum_normSq_grover2DVec_one_zero _ hlt
  · rw [ite_eq_right hj]; exact sum_normSq_groverMultiState_eq_one ∅ 0
/-- Arbitrary-collision superposition of disjoint-support `ghBasisVec` states over
  `J.powerset`. -/
private noncomputable def ghMidPAmpState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n)))
    (coeff : Finset (Fin m) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  let pref := fun x ↦ subcubePref hp hm (perm x)
  ∑ A ∈ (R.image pref).powerset, coeff A * ghBasisVec hp hm perm R A w
private lemma ghMidP_prod_univ_ite_eq {m : ℕ} (J : Finset (Fin m)) (f z : Fin m → ℂ) : (∏ j : Fin m,
  if j ∈ J then f j else z j) = (∏ j ∈ Finset.univ \ J, z j) * (∏ j ∈ J, f j) := by
  rw [← Finset.prod_sdiff (Finset.subset_univ J)]; congr 1
  · exact Finset.prod_congr rfl fun j hj ↦ ite_eq_right (Finset.mem_sdiff.mp hj).2
  · exact Finset.prod_congr rfl fun j hj ↦ ite_eq_left hj
private lemma ghBasisVec_eq_prod_sdiff_midp {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (B : Finset (Fin m)) (w : Fin (2 ^ (m * (n +
  1)))) :
    let pref := fun x ↦ subcubePref hp hm (perm x); let J := R.image pref
    ghBasisVec hp hm perm R B w = (∏ j ∈ Finset.univ \ J, zoomSlotWrap hp hm perm j
      (groverMultiState ∅ 0) ((groupReg (Nat.mul_one m) j).extractIndex w)) * (∏ j ∈ J, if j ∈ B
      then zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1)
      ((groupReg (Nat.mul_one m) j).extractIndex w) else zoomSlotWrap hp hm perm j (grover2DVec
      (subcubeLocalSet hp hm (R.image perm) j) 1 0) ((groupReg (Nat.mul_one m) j).extractIndex w))
      := by
  intro pref J; unfold ghBasisVec zoomProdState; rw [← ghMidP_prod_univ_ite_eq J]
  refine Finset.prod_congr rfl fun j _ ↦ ?_; dsimp only [J, pref]; by_cases hjJ : j ∈ R.image (fun x
    ↦ subcubePref hp hm (perm x))
  · rw [ite_eq_left hjJ, ite_eq_left hjJ]; by_cases hjB : j ∈ B
    · rw [ite_eq_left hjB, ite_eq_left hjB]
    · rw [ite_eq_right hjB, ite_eq_right hjB]
  · rw [ite_eq_right hjJ, ite_eq_right hjJ]
private lemma ghPrep_grover_eq_ghMidPAmpState {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^ (k * n))} (hsub :
  memSeen n k (memPrefix k active) μ ⊆ S) (hR_lt : (S \ memSeen n k (memPrefix k active) μ).card < 2
  ^ (n - p)) (kInit : ℕ) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let pref := fun x ↦ subcubePref hp hm (perm x)
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let prepOp := (lowBlock W M).embedMatrix (wdPrepUnitary hp hm perm).1
    ((diffOp * phaseOp) ^ kInit) *ᵥ (prepOp *ᵥ single (workMemIdx n m k 0 μ) 1) = workMemState
      (ghMidPAmpState hp hm perm R (ghMidPInitCoeff (n - p) pref R kInit)) (single μ 1) := by
  dsimp only; rw [wdPrepUnitary_mulVec_workMemIdx_midp hp hm perm μ,
    ghDeflatedGrover_iter_zoomProdState_midp hp hm perm hsub (fun j ↦ j) _ kInit]
  set R := S \ memSeen n k (memPrefix k active) μ; let pref := fun x ↦ subcubePref hp hm (perm x)
  let J := R.image pref; congr 1; funext w
  let cr (j : Fin m) : ℝ := Real.cos ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta (n - p) pref R j)
  let sr (j : Fin m) : ℝ := Real.sin ((2 * (kInit : ℝ) + 1) * ghMidPSlotTheta (n - p) pref R j)
  let x₀ (j : Fin m) : ℂ := zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image
    perm) j) 1 0) ((groupReg (Nat.mul_one m) j).extractIndex w)
  let x₁ (j : Fin m) : ℂ := zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image
    perm) j) 0 1) ((groupReg (Nat.mul_one m) j).extractIndex w)
  let z (j : Fin m) : ℂ :=
    zoomSlotWrap hp hm perm j (groverMultiState ∅ 0) ((groupReg (Nat.mul_one m) j).extractIndex w)
  have hprod_lhs : zoomProdState (fun j ↦ zoomSlotWrap hp hm perm j ((fun ψ ↦ Grover.diffuserMatrix
    *ᵥ (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ ψ))^[kInit] (hadamardMatrix (n - p) *ᵥ
    single 0 1))) w = ∏ j : Fin m, if j ∈ J then (cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j else z j
    := by
    unfold zoomProdState; refine Finset.prod_congr rfl fun j _ ↦ ?_; dsimp only; by_cases hj : j ∈ J
    · rw [ite_eq_left hj]; rcases ghMidPOcc_pos_and_lt hp hm perm hR_lt hj with ⟨h0, hlt⟩
      have hθ : Real.arcsin (√(((subcubeLocalSet hp hm (R.image perm) j).card : ℝ) / (2 ^ (n - p) :
        ℝ))) = ghMidPSlotTheta (n - p) pref R j :=
        (by unfold ghMidPSlotTheta; rw [card_subcubeLocalSet_image_perm_midp]); have hinit :=
        hadamard_zero_eq_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0 hlt
      have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0 hlt
        kInit (Real.cos (ghMidPSlotTheta (n - p) pref R j)) (Real.sin (ghMidPSlotTheta (n - p) pref
        R j)); have hc_add : Real.cos (2 * (kInit : ℝ) * ghMidPSlotTheta (n - p) pref R j) *
        Real.cos (ghMidPSlotTheta (n - p) pref R j) - Real.sin (2 * (kInit : ℝ) * ghMidPSlotTheta (n
        - p) pref R j) * Real.sin (ghMidPSlotTheta (n - p) pref R j) = cr j :=
        (by dsimp only [cr]; rw [← Real.cos_add]; exact congrArg Real.cos (by ring))
      have hs_add : Real.sin (2 * (kInit : ℝ) * ghMidPSlotTheta (n - p) pref R j) * Real.cos
        (ghMidPSlotTheta (n - p) pref R j) + Real.cos (2 * (kInit : ℝ) * ghMidPSlotTheta (n - p)
        pref R j) * Real.sin (ghMidPSlotTheta (n - p) pref R j) = sr j :=
        (by dsimp only [sr]; rw [← Real.sin_add]; exact congrArg Real.sin (by ring))
      rw [hθ] at hinit hiter; dsimp only at hinit hiter; rw [hc_add, hs_add] at hiter; rw [hinit,
        hiter, grover2DVec_linear, zoomSlotWrap_eq_linear_midp]
    · rw [ite_eq_right hj]
      have hc0 : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
        rw [card_subcubeLocalSet_image_perm_midp, ghMidPOcc, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]; intro x hxR heq; exact hj (heq ▸ Finset.mem_image_of_mem _
          hxR)
      have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0
      rw [hemp, ← groverMultiState_zero_eq_hadamard_mulVec ∅, Function.iterate_fixed
        diffuser_oracle_empty_groverMultiState_zero]
  let coeff0 : Finset (Fin m) → ℂ := fun A ↦ if A = ∅ then 1 else 0
  have hrot_J : (∏ j ∈ J, ((cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) = ∑ B ∈ J.powerset,
    ghMidPInitCoeff (n - p) pref R kInit B * ∏ j ∈ J, (if j ∈ B then x₁ j else x₀ j) := by
    have hlhs0 : (∏ j ∈ J, ((cr j : ℂ) * x₀ j + (sr j : ℂ) * x₁ j)) = ∑ A ∈ J.powerset, coeff0 A * ∏
      j ∈ J, (if j ∈ A then -(sr j : ℂ) * x₀ j + (cr j : ℂ) * x₁ j else (cr j : ℂ) * x₀ j + (sr j :
      ℂ) * x₁ j) := by
      rw [Finset.sum_eq_single ∅ (fun A _ hne ↦ by simp [coeff0, hne]) (fun hnot ↦ absurd
        (Finset.empty_mem_powerset J) hnot)]; simp [coeff0]
    rw [hlhs0, ghMidPSlotRot_mul_prod_eq J cr sr coeff0 x₀ x₁]
    refine Finset.sum_congr rfl fun B _ ↦ ?_; congr 1; unfold ghMidPSlotRot ghMidPInitCoeff
    rw [Finset.sum_eq_single ∅ (fun A _ hne ↦ by simp [coeff0, hne]) (fun hnot ↦ absurd
      (Finset.empty_mem_powerset J) hnot)]; dsimp only [coeff0, J, cr, sr]; rw [ite_eq_left rfl,
      one_mul]; refine Finset.prod_congr rfl fun j _ ↦ ?_; by_cases hjB : j ∈ B <;> simp [hjB]
  rw [hprod_lhs, ghMidP_prod_univ_ite_eq J, hrot_J, Finset.mul_sum]; unfold ghMidPAmpState
  dsimp only [J, pref, x₀, x₁, z]; refine Finset.sum_congr rfl fun B _ ↦ ?_
  rw [ghBasisVec_eq_prod_sdiff_midp hp hm perm R B w]; ring
private lemma ghGrover_iter_ghMidPAmpState {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^ (k * n))} (hsub :
  memSeen n k (memPrefix k active) μ ⊆ S) (hR_lt : (S \ memSeen n k (memPrefix k active) μ).card < 2
  ^ (n - p)) (coeff : Finset (Fin m) → ℂ) (kNext : ℕ) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let pref := fun x ↦ subcubePref hp hm (perm x)
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let coeffNext := ghMidPSlotRot (R.image pref) (fun j ↦ Real.cos (2 * (kNext : ℝ) *
      ghMidPSlotTheta (n - p) pref R j)) (fun j ↦ Real.sin (2 * (kNext : ℝ) * ghMidPSlotTheta (n -
      p) pref R j)) coeff
    ((diffOp * phaseOp) ^ kNext) *ᵥ workMemState (ghMidPAmpState hp hm perm R coeff) (single μ 1) =
      workMemState (ghMidPAmpState hp hm perm R coeffNext) (single μ 1) := by
  dsimp only; let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
  let pref := fun x ↦ subcubePref hp hm (perm x); let J := R.image pref
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1; let orac := (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
  let ck (j : Fin m) : ℝ := Real.cos (2 * (kNext : ℝ) * ghMidPSlotTheta (n - p) pref R j)
  let sk (j : Fin m) : ℝ := Real.sin (2 * (kNext : ℝ) * ghMidPSlotTheta (n - p) pref R j)
  have hlin_ws (F : Finset (Fin m) → Fin (2 ^ W) → ℂ) : workMemState (W := W) (M := M) (fun w ↦ ∑ A
    ∈ J.powerset, F A w) (single μ 1) = ∑ A ∈ J.powerset, workMemState (W := W) (M := M) (F A)
    (single μ 1) :=
    (by funext z; rw [Finset.sum_apply]; dsimp only [workMemState]; rw [Finset.sum_mul])
  have hlin_smul (c : ℂ) (v : Fin (2 ^ W) → ℂ) : workMemState (fun w ↦ c * v w) (single μ 1) = c •
    workMemState v (single μ 1) :=
    (by funext z; dsimp only [workMemState, Pi.smul_apply, smul_eq_mul]; ring); change ((diffOp *
    phaseOp) ^ kNext) *ᵥ workMemState (W := W) (M := M) (fun w ↦ ∑ A ∈ J.powerset, coeff A *
    ghBasisVec hp hm perm R A w) (single μ 1) = _; rw [hlin_ws (fun A w ↦ coeff A * ghBasisVec hp hm
    perm R A w), Matrix.mulVec_sum]
  let slotAfter (A : Finset (Fin m)) (w : Fin (2 ^ W)) (j : Fin m) : ℂ := if j ∈ J then if j ∈ A
    then -(sk j : ℂ) * zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image
    perm) j) 1 0) ((groupReg (Nat.mul_one m) j).extractIndex w) + (ck j : ℂ) * zoomSlotWrap hp hm
    perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1) ((groupReg (Nat.mul_one m)
    j).extractIndex w) else (ck j : ℂ) * zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet
    hp hm (R.image perm) j) 1 0) ((groupReg (Nat.mul_one m) j).extractIndex w) + (sk j : ℂ) *
    zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1)
    ((groupReg (Nat.mul_one m) j).extractIndex w) else zoomSlotWrap hp hm perm j (groverMultiState
    ∅ 0) ((groupReg (Nat.mul_one m) j).extractIndex w)
  have h_sub_sum (A : Finset (Fin m)) : ((diffOp * phaseOp) ^ kNext) *ᵥ workMemState (W := W) (M :=
    M) (fun w ↦ coeff A * ghBasisVec hp hm perm R A w) (single μ 1) = workMemState (W := W) (M := M)
    (fun w ↦ coeff A * ∏ j : Fin m, slotAfter A w j) (single μ 1) := by
    dsimp only [slotAfter, W, M, R, fc, orac, unm, phaseOp, diffOp]; rw [hlin_smul (coeff A) _,
      Matrix.mulVec_smul]; unfold ghBasisVec; rw [ghDeflatedGrover_iter_zoomProdState_midp hp hm
      perm hsub (fun j ↦ j) _ kNext, ← hlin_smul (coeff A) _]
    congr 1; funext w; congr 1; unfold zoomProdState; refine Finset.prod_congr rfl fun j _ ↦ ?_
    dsimp only; by_cases hj : j ∈ J
    · dsimp only [J, pref, R] at hj ⊢; rw [ite_eq_left hj, ite_eq_left hj]
      rcases ghMidPOcc_pos_and_lt hp hm perm hR_lt hj with ⟨h0, hlt⟩
      have hθ : Real.arcsin (√(((subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active)
        μ).image perm) j).card : ℝ) / (2 ^ (n - p) : ℝ))) = ghMidPSlotTheta (n - p) pref R j :=
        (by unfold ghMidPSlotTheta; rw [card_subcubeLocalSet_image_perm_midp]); by_cases hjA : j ∈ A
      · rw [ite_eq_left hjA, ite_eq_left hjA]
        have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm ((S \ memSeen n k
          (memPrefix k active) μ).image perm) j) h0 hlt kNext 0 1
        rw [hθ] at hiter; dsimp only at hiter; have hc_tr : Real.cos (2 * (kNext : ℝ) *
          ghMidPSlotTheta (n - p) pref R j) * 0 - Real.sin (2 * (kNext : ℝ) * ghMidPSlotTheta (n -
          p) pref R j) * 1 = -sk j := (by dsimp only [sk]; ring); have hs_tr : Real.sin (2 * (kNext
          : ℝ) * ghMidPSlotTheta (n - p) pref R j) * 0 + Real.cos (2 * (kNext : ℝ) * ghMidPSlotTheta
          (n - p) pref R j) * 1 = ck j := (by dsimp only [ck]; ring); rw [hc_tr, hs_tr] at hiter
        rw [hiter, grover2DVec_linear, zoomSlotWrap_eq_linear_midp, Complex.ofReal_neg]
      · rw [ite_eq_right hjA, ite_eq_right hjA]
        have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm ((S \ memSeen n k
          (memPrefix k active) μ).image perm) j) h0 hlt kNext 1 0
        rw [hθ] at hiter; dsimp only at hiter; have hc_tr : Real.cos (2 * (kNext : ℝ) *
          ghMidPSlotTheta (n - p) pref R j) * 1 - Real.sin (2 * (kNext : ℝ) * ghMidPSlotTheta (n -
          p) pref R j) * 0 = ck j := (by dsimp only [ck]; ring); have hs_tr : Real.sin (2 * (kNext :
          ℝ) * ghMidPSlotTheta (n - p) pref R j) * 1 + Real.cos (2 * (kNext : ℝ) * ghMidPSlotTheta
          (n - p) pref R j) * 0 = sk j := (by dsimp only [sk]; ring)
        rw [hc_tr, hs_tr] at hiter; rw [hiter, grover2DVec_linear, zoomSlotWrap_eq_linear_midp]
    · dsimp only [J, pref, R] at hj ⊢; rw [ite_eq_right hj, ite_eq_right hj]
      have hc0 : (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm)
        j).card = 0 := by
        rw [card_subcubeLocalSet_image_perm_midp, ghMidPOcc, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]; intro x hxR heq; exact hj (heq ▸ Finset.mem_image_of_mem _
          hxR)
      have hemp : subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm) j = ∅
        := Finset.card_eq_zero.mp hc0; rw [hemp, Function.iterate_fixed
        diffuser_oracle_empty_groverMultiState_zero]
  simp_rw [h_sub_sum]; rw [← hlin_ws (fun A w ↦ coeff A * ∏ j : Fin m, slotAfter A w j)]; congr 1;
    funext w
  let x₀ (j : Fin m) : ℂ := zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image
    perm) j) 1 0) ((groupReg (Nat.mul_one m) j).extractIndex w)
  let x₁ (j : Fin m) : ℂ := zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image
    perm) j) 0 1) ((groupReg (Nat.mul_one m) j).extractIndex w)
  let z (j : Fin m) : ℂ :=
    zoomSlotWrap hp hm perm j (groverMultiState ∅ 0) ((groupReg (Nat.mul_one m) j).extractIndex w)
  have hfact (A : Finset (Fin m)) : coeff A * (∏ j : Fin m, slotAfter A w j) = (∏ j ∈ Finset.univ \
    J, z j) * (coeff A * ∏ j ∈ J, (if j ∈ A then -(sk j : ℂ) * x₀ j + (ck j : ℂ) * x₁ j else (ck j :
    ℂ) * x₀ j + (sk j : ℂ) * x₁ j)) :=
    (by dsimp only [slotAfter]; rw [ghMidP_prod_univ_ite_eq J _ z]; ring); simp_rw [hfact]
  rw [← Finset.mul_sum, ghMidPSlotRot_mul_prod_eq J ck sk coeff x₀ x₁, Finset.mul_sum]
  unfold ghMidPAmpState; dsimp only [J, pref, R, ck, sk, x₀, x₁, z]
  refine Finset.sum_congr rfl fun B _ ↦ ?_; rw [ghBasisVec_eq_prod_sdiff_midp hp hm perm (S \
    memSeen n k (memPrefix k active) μ) B w]; ring
private lemma ghDamp_and_click_marked_ghMidPAmpState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm
  : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (pr : GHMidPProbe) (coeff : Finset (Fin m)
  → ℂ) :
    let pref := fun x ↦ subcubePref hp hm (perm x)
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    ghDampVec n m (ghMidPWSpec R.card pr) (P_R *ᵥ ghMidPAmpState hp hm perm R coeff) = P_R *ᵥ
      ghMidPAmpState hp hm perm R (ghMidPDampCoeff R.card pr coeff) ∧ ghClickVec n m (ghMidPWSpec
      R.card pr) (P_R *ᵥ ghMidPAmpState hp hm perm R coeff) = if 1 ≤ R.card ∧ (R.image pref).card =
      R.card then (((pr.rotTop.sVal : ℂ) * (pr.phases.getD (R.card - 1) gaussOne).val * coeff
      (R.image pref)) • (P_R *ᵥ ghBasisVec hp hm perm R (R.image pref))) else 0 := by
  intro pref P_R; let J := R.image pref
  have hsVal_zero {b : ℕ} (hb : ¬ (1 ≤ R.card ∧ b = R.card)) : (ghMidPWSpec R.card pr b).2.sVal = 0
    := by
    unfold ghMidPWSpec; by_cases hb0 : b = 0
    · simp [hb0, pythOne, PythPair.sVal]
    · by_cases hlt : b < R.card
      · simp [hb0, hlt, pythOne, PythPair.sVal]
      · by_cases heq : b = R.card
        · exfalso; exact hb ⟨Nat.pos_of_ne_zero (heq ▸ hb0), heq⟩
        · simp [hb0, hlt, heq, pythOne, PythPair.sVal]
  constructor
  · funext o; dsimp only [ghDampVec, P_R]; rw [permUnitary_parallelMarkPerm_mulVec_apply_midp,
      permUnitary_parallelMarkPerm_mulVec_apply_midp]
    unfold ghMidPAmpState ghMidPDampCoeff; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    by_cases hnz : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
    · simp [hnz]
    · have hcardA := (ghBasisVec_support_props_midp hp hm perm R (Finset.mem_powerset.mp hA) o
        hnz).2.2.2.2; rw [hcardA]; ring
  · by_cases hall : 1 ≤ R.card ∧ J.card = R.card
    · rw [ite_eq_left hall]; rcases hall with ⟨hr1, hJ_card⟩; have hr0 : R.card ≠ 0 := (by omega)
      funext o; dsimp only [ghClickVec, P_R, Pi.smul_apply, smul_eq_mul]
      rw [permUnitary_parallelMarkPerm_mulVec_apply_midp,
        permUnitary_parallelMarkPerm_mulVec_apply_midp]
      unfold ghMidPAmpState; by_cases hhit : wdHitCount n m o = R.card
      · rw [hhit, Finset.mul_sum, Finset.sum_eq_single J (fun A hA hne ↦ ?_) (fun hnot ↦ absurd
          (Finset.mem_powerset_self J) hnot)]
        · unfold ghMidPWSpec; simp only [hr0, lt_irrefl, ↓reduceIte]; ring
        · by_cases hnz : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
          · simp [hnz]
          · have hcardA := (ghBasisVec_support_props_midp hp hm perm R (Finset.mem_powerset.mp hA) o
              hnz).2.2.2.2
            have hAJ : A = J := Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hA)
              (by rw [hJ_card, ← hhit, hcardA]); exact absurd hAJ hne
      · have hrhs0 : (((pr.rotTop.sVal : ℂ) * (pr.phases.getD (R.card - 1) gaussOne).val * coeff J)
          * ghBasisVec hp hm perm R J (parallelMarkPerm n m R o)) = 0 := by
          by_cases hnz : ghBasisVec hp hm perm R J (parallelMarkPerm n m R o) = 0
          · dsimp only [J] at hnz; rw [hnz, mul_zero]
          · have hcardJ := (ghBasisVec_support_props_midp hp hm perm R Finset.Subset.rfl o
              hnz).2.2.2.2; exact absurd (hcardJ.trans hJ_card) hhit
        dsimp only [J] at hrhs0 ⊢; rw [hrhs0, Finset.mul_sum]
        refine Finset.sum_eq_zero fun A _ ↦ ?_; rw [hsVal_zero (fun h ↦ hhit h.2)]; simp
    · rw [ite_eq_right hall]; funext o; dsimp only [ghClickVec, P_R, Pi.zero_apply]
      rw [permUnitary_parallelMarkPerm_mulVec_apply_midp]; unfold ghMidPAmpState
      rw [Finset.mul_sum]; refine Finset.sum_eq_zero fun A hA ↦ ?_
      by_cases hnz : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
      · simp [hnz]
      · have hcardA := (ghBasisVec_support_props_midp hp hm perm R (Finset.mem_powerset.mp hA) o
          hnz).2.2.2.2; have hle_J : A.card ≤ J.card := Finset.card_le_card (Finset.mem_powerset.mp
          hA); have hle_R : J.card ≤ R.card := Finset.card_image_le
        have hnot_eq : ¬ (1 ≤ R.card ∧ wdHitCount n m o = R.card) :=
          (by rintro ⟨hr1, hcnt⟩; apply hall; exact ⟨hr1, le_antisymm hle_R (by omega)⟩)
        rw [hsVal_zero hnot_eq]; simp
private lemma sum_normSq_ghBasisVec_readout_choices {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm
  : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hR_lt : R.card < 2 ^ (n - p)) {A : Finset
  (Fin m)} (hA : A ⊆ R.image fun x ↦ subcubePref hp hm (perm x)) (Φ : Finset (Fin (2 ^ n)) → ℂ) :
    let pref := fun x ↦ subcubePref hp hm (perm x)
    (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (ghBasisVec hp hm perm R A (parallelMarkPerm n m R o)) :
      ℂ) * Φ (R \ (groupHits (Nat.mul_one m) o).toFinset)) = ∑ c ∈ ghMidPHitChoices pref R A,
      (ghMidPChoiceWeight pref R A : ℂ) * Φ (R \ ghMidPChoiceSet c) := by
  intro pref; let hbg1 : m * 1 = m := Nat.mul_one m
  let ξ (j : Fin m) : Fin (2 ^ (1 * (n + 1))) → ℂ := zoomSlotWrap hp hm perm j (if j ∈ R.image
    pref then if j ∈ A then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1 else
    grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0 else groverMultiState ∅ 0)
  let hitSlot (_ : Fin m) (z : Fin (2 ^ (1 * (n + 1)))) : Option (Fin (2 ^ n)) :=
    firstMarkedAddr n 1 (parallelMarkPerm n 1 R z)
  let hitVec (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) : Fin m → Option (Fin (2 ^ n)) :=
    fun j ↦ hitSlot j (zs j)
  have hsum_zs : (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (ghBasisVec hp hm perm R A
    (parallelMarkPerm n m R o)) : ℂ) * Φ (R \ (groupHits hbg1 o).toFinset)) = ∑ zs : Fin m → Fin (2
    ^ (1 * (n + 1))), (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) * Φ (R \ (groupHits hbg1
    (parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs))).toFinset) := by
    rw [← Equiv.sum_comp (parallelMarkPerm n m R)]; simp_rw [parallelMarkPerm_involutive R]
    rw [← (groupSplitEquiv hbg1).symm.sum_comp]; refine Finset.sum_congr rfl fun zs _ ↦ ?_; congr 1;
      unfold ghBasisVec zoomProdState; dsimp only [ξ, pref]; simp_rw [← groupSplitEquiv_apply hbg1,
      Equiv.apply_symm_apply, map_prod, Complex.ofReal_prod]
  rw [hsum_zs]
  have hpoint (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) : (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) * Φ
    (R \ (groupHits hbg1 (parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs))).toFinset) = ∑ c
    ∈ ghMidPHitChoices pref R A, (if hitVec zs = c then ∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ) else
    0) * Φ (R \ ghMidPChoiceSet c) := by
    by_cases hzero : (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) = 0
    · rw [hzero]; simp
    · set w := (groupSplitEquiv hbg1).symm zs; set o := parallelMarkPerm n m R w; have hw_eq : w =
        parallelMarkPerm n m R o := (parallelMarkPerm_involutive R w).symm
      have hamp : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) ≠ 0 := by
        rw [← hw_eq]; unfold ghBasisVec zoomProdState; dsimp only [w, ξ, pref]; simp_rw [←
          groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]; intro hp0; apply hzero
        rw [← Complex.ofReal_prod, ← map_prod, hp0, Complex.normSq_zero, Complex.ofReal_zero]
      have hslot_nz (j : Fin m) : ξ j ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o)) ≠
        0 := fun h0 ↦ hamp (Finset.prod_eq_zero (Finset.mem_univ j) h0)
      have hex_o (j : Fin m) : (groupReg hbg1 j).extractIndex o = parallelMarkPerm n 1 R (zs j)
        := by
        dsimp only [o, w]; rw [extractIndex_groupReg_parallelMarkPerm, ← groupSplitEquiv_apply hbg1,
          Equiv.apply_symm_apply]
      rcases groupHits_of_zoomSlotWrap_midp hp hm perm R id (fun j ↦ if j ∈ R.image pref then if j ∈
        A then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1 else grover2DVec
        (subcubeLocalSet hp hm (R.image perm) j) 1 0 else groverMultiState ∅ 0) o hslot_nz with
        ⟨hhit_sub, htf_eq⟩; have hisSome := (ghBasisVec_support_props_midp hp hm perm R hA o
        hamp).2.1
      have hmem_c : hitVec zs ∈ ghMidPHitChoices pref R A := by
        refine Fintype.mem_piFinset.mpr fun j ↦ ?_; have hsj := hisSome j; rw [hex_o j] at hsj;
          by_cases hjA : j ∈ A
        · rw [ite_eq_left hjA, Finset.mem_image]; rw [ite_eq_left hjA] at hsj
          rcases Option.isSome_iff_exists.mp hsj with ⟨x, hx_eq⟩
          have hx_o : firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) = some x :=
            (by rwa [hex_o j]); rcases hhit_sub j x hx_o with ⟨hxR, hpx⟩; exact ⟨x,
            Finset.mem_filter.mpr ⟨hxR, hpx⟩, hx_eq.symm⟩
        · rw [ite_eq_right hjA, Finset.mem_singleton]; rw [ite_eq_right hjA] at hsj
          exact Option.not_isSome_iff_eq_none.mp (by simpa using hsj)
      have hcs_eq : (groupHits hbg1 o).toFinset = ghMidPChoiceSet (hitVec zs) := by
        rw [htf_eq]; ext x; simp only [List.mem_toFinset, List.mem_filterMap, ghMidPChoiceSet,
          Finset.mem_biUnion, Finset.mem_univ, true_and]; constructor
        · rintro ⟨j, _, hj_eq⟩; rw [hex_o j] at hj_eq; refine ⟨j, ?_⟩; dsimp only [hitVec, hitSlot];
            rw [hj_eq]; exact Finset.mem_singleton_self x
        · rintro ⟨j, hj_mem⟩; refine ⟨j, mem_finRange j, ?_⟩; rw [hex_o j]; dsimp only [hitVec,
            hitSlot] at hj_mem
          cases hfa : firstMarkedAddr n 1 (parallelMarkPerm n 1 R (zs j)) with
          | none => rw [hfa] at hj_mem; exact False.elim (Finset.notMem_empty x hj_mem)
          | some y => rw [hfa, Finset.mem_singleton] at hj_mem; rw [hj_mem]
      rw [Finset.sum_eq_single (hitVec zs) (fun c _ hne ↦ by rw [ite_eq_right hne.symm, zero_mul])
        (fun hnot ↦ absurd hmem_c hnot), ite_eq_left rfl, hcs_eq]
  simp_rw [hpoint]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [← Finset.sum_mul]; congr 1; have hprod_ite (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) :
      (if hitVec zs = c then ∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ) else 0) =
        ∏ j : Fin m, if hitSlot j (zs j) = c j then (normSq (ξ j (zs j)) : ℂ) else 0 := by
    by_cases heq : hitVec zs = c
    · rw [ite_eq_left heq]; refine Finset.prod_congr rfl fun j _ ↦ ?_; have hj : hitSlot j (zs j) =
        c j := congrFun heq j; rw [ite_eq_left hj]
    · rw [ite_eq_right heq]
      have hex : ∃ j : Fin m, hitSlot j (zs j) ≠ c j := by
        by_contra hall; apply heq; funext j; by_contra hne_j; exact hall ⟨j, hne_j⟩
      rcases hex with ⟨j₀, hj₀⟩; symm; exact Finset.prod_eq_zero (Finset.mem_univ j₀) (ite_eq_right
        hj₀)
  simp_rw [hprod_ite]; rw [← Fintype.prod_sum (fun (j : Fin m) (z : Fin (2 ^ (1 * (n + 1)))) ↦ if
    hitSlot j z = c j then (normSq (ξ j z) : ℂ) else 0)]; have hc_pi := Fintype.mem_piFinset.mp hc
  have hslot_val (j : Fin m) : (∑ z : Fin (2 ^ (1 * (n + 1))), if hitSlot j z = c j then (normSq (ξ
    j z) : ℂ) else 0) = if j ∈ A then ((1 / (ghMidPOcc pref R j : ℝ) : ℝ) : ℂ) else 1 := by
    have hmj := hc_pi j; by_cases hjA : j ∈ A
    · rw [ite_eq_left hjA] at hmj ⊢; rcases Finset.mem_image.mp hmj with ⟨x₀, hx₀f, hcx₀⟩
      rcases Finset.mem_filter.mp hx₀f with ⟨hx₀R, hpx₀⟩
      have hcj : c j = some x₀ := hcx₀.symm; rw [hcj]; have hjR : j ∈ R.image pref := hA hjA
      let w₀ : Fin (2 ^ (n - p)) := (subcubeSplit hp hm (perm x₀)).1
      let z₀ : Fin (2 ^ (1 * (n + 1))) := (addrReg n 1).basisSplitEquiv.symm ((wdPerm1n perm).symm
        ((zoomCast1nEquiv hp).symm ((lowHighEquiv (n - p) p).symm (w₀, finCongr hm j))), 0)
      have hw₀_mem : w₀ ∈ subcubeLocalSet hp hm (R.image perm) j := by
        rw [mem_subcubeLocalSet_iff]; have hpair : (w₀, j) = subcubeSplit hp hm (perm x₀) :=
          Prod.ext rfl hpx₀.symm
        rw [hpair, Equiv.symm_apply_apply]; exact Finset.mem_image_of_mem perm hx₀R
      rw [sum_eq_single z₀ (fun z hz_ne ↦ ?_)]
      · have hξ_z₀ : ξ j z₀ = grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1 w₀ := by
          dsimp only [ξ, z₀]; rw [ite_eq_left hjR, ite_eq_left hjA]; dsimp only [zoomSlotWrap,
            tensorState, workMemState, Function.comp_apply]
          rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]; dsimp only
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
            Pi.single_eq_same, Pi.single_eq_same, mul_one, mul_one]
        have hnz_z₀ : ξ j z₀ ≠ 0 := by
          rw [hξ_z₀]; unfold grover2DVec; rw [ite_eq_left hw₀_mem]
          rcases ghMidPOcc_pos_and_lt hp hm perm hR_lt hjR with ⟨h0, _⟩
          have hpos : (0 : ℝ) < 1 / √((subcubeLocalSet hp hm (R.image perm) j).card : ℝ) :=
            one_div_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr h0))
          exact Complex.ofReal_ne_zero.mpr hpos.ne'
        have hsp₀ := zoomSlotWrap_support_firstMarkedAddr_midp hp hm perm R j _ z₀
          (by simpa only [ξ] using hnz_z₀)
        have hhit_z₀ : hitSlot j z₀ = some x₀ := by
          dsimp only [hitSlot]; rw [hsp₀.2.2.2]
          have hloc_eq : (lowHighEquiv (n - p) p (zoomCast1nEquiv hp (wdPerm1n perm ((addrReg n
            1).extractIndex z₀)))).1 = w₀ := by
            dsimp only [z₀]; rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
            dsimp only; rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          rw [hloc_eq, ite_eq_left hw₀_mem]; congr 1
          have hpair : (w₀, j) = subcubeSplit hp hm (perm x₀) := Prod.ext rfl hpx₀.symm; rw [hpair,
            Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rw [ite_eq_left hhit_z₀, hξ_z₀]; unfold grover2DVec; rw [ite_eq_left hw₀_mem,
          Complex.normSq_ofReal]; have hcard_nn : (0 : ℝ) ≤ ((subcubeLocalSet hp hm (R.image perm)
          j).card : ℝ) := Nat.cast_nonneg _
        have hsq : (1 / √((subcubeLocalSet hp hm (R.image perm) j).card : ℝ)) * (1 /
          √((subcubeLocalSet hp hm (R.image perm) j).card : ℝ)) = 1 / (ghMidPOcc pref R j : ℝ) := by
          rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt hcard_nn,
            card_subcubeLocalSet_image_perm_midp]
        rw [hsq]
      · by_cases hnz_z : ξ j z = 0
        · simp [hnz_z]
        · have hsp := zoomSlotWrap_support_firstMarkedAddr_midp hp hm perm R j _ z
            (by simpa only [ξ] using hnz_z)
          have hne_hit : hitSlot j z ≠ some x₀ := by
            intro hhit; apply hz_ne; dsimp only [hitSlot] at hhit; rw [hsp.2.2.2] at hhit
            set w_loc := (lowHighEquiv (n - p) p (zoomCast1nEquiv hp (wdPerm1n perm ((addrReg n
              1).extractIndex z)))).1
            by_cases hmem : w_loc ∈ subcubeLocalSet hp hm (R.image perm) j
            · rw [ite_eq_left hmem, Option.some.injEq] at hhit; have hperm_eq : (subcubeSplit hp
                hm).symm (w_loc, j) = perm x₀ := (by rw [← hhit, Equiv.apply_symm_apply])
              have hw_eq : w_loc = w₀ := by
                have hp_eq := congrArg (subcubeSplit hp hm) hperm_eq
                rw [Equiv.apply_symm_apply] at hp_eq; exact congrArg Prod.fst hp_eq
              have hlow_eq : lowHighEquiv (n - p) p (zoomCast1nEquiv hp (wdPerm1n perm ((addrReg n
                1).extractIndex z))) = (w₀, finCongr hm j) := Prod.ext hw_eq hsp.2.2.1
              have hu_eq : (addrReg n 1).extractIndex z = (wdPerm1n perm).symm ((zoomCast1nEquiv
                hp).symm ((lowHighEquiv (n - p) p).symm (w₀, finCongr hm j))) := by
                rw [← hlow_eq, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
                  Equiv.symm_apply_apply]
              have hbs_eq : (addrReg n 1).basisSplitEquiv z = ((wdPerm1n perm).symm
                ((zoomCast1nEquiv hp).symm ((lowHighEquiv (n - p) p).symm (w₀, finCongr hm j))), 0)
                := Prod.ext (by rw [QRegister.basisSplitEquiv_apply_fst, hu_eq]) hsp.1
              dsimp only [z₀]; rw [← hbs_eq, Equiv.symm_apply_apply]
            · rw [ite_eq_right hmem] at hhit; cases hhit
          rw [ite_eq_right hne_hit]
    · rw [ite_eq_right hjA] at hmj ⊢; have hcj : c j = none := Finset.mem_singleton.mp hmj; rw [hcj]
      have hterm_none (z : Fin (2 ^ (1 * (n + 1)))) : (if hitSlot j z = none then (normSq (ξ j z) :
        ℂ) else 0) = (normSq (ξ j z) : ℂ) := by
        by_cases hnz_z : ξ j z = 0
        · simp [hnz_z]
        · have hsp := zoomSlotWrap_support_firstMarkedAddr_midp hp hm perm R j _ z
            (by simpa only [ξ] using hnz_z); have hφ := hsp.2.1; set w_loc := (lowHighEquiv (n - p)
            p (zoomCast1nEquiv hp (wdPerm1n perm ((addrReg n 1).extractIndex z)))).1
          change _ ≠ 0 at hφ
          have hnone : hitSlot j z = none := by
            dsimp only [hitSlot]; rw [hsp.2.2.2]; by_cases hjR : j ∈ R.image pref
            · rw [ite_eq_left hjR, ite_eq_right hjA] at hφ
              have hw_not : w_loc ∉ subcubeLocalSet hp hm (R.image perm) j := by
                intro hm_loc; apply hφ; unfold grover2DVec; rw [ite_eq_left hm_loc, zero_div,
                  Complex.ofReal_zero]
              exact ite_eq_right hw_not
            · have hc0 : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
                rw [card_subcubeLocalSet_image_perm_midp, ghMidPOcc, Finset.card_eq_zero,
                  Finset.filter_eq_empty_iff]; intro x hxR heq; exact hjR (heq ▸
                  Finset.mem_image_of_mem _ hxR)
              have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0
              rw [hemp]; exact ite_eq_right (Finset.notMem_empty w_loc)
          exact ite_eq_left hnone
      simp_rw [hterm_none]; rw [← Complex.ofReal_sum]
      have hnorm1 : (∑ z : Fin (2 ^ (1 * (n + 1))), normSq (ξ j z)) = 1 := by
        dsimp only [ξ]; refine sum_normSq_zoomSlotWrap_of_norm_midp hp hm perm j _ 1 ?_
        by_cases hjR : j ∈ R.image pref
        · rw [ite_eq_left hjR, ite_eq_right hjA]
          exact sum_normSq_grover2DVec_one_zero _ (ghMidPOcc_pos_and_lt hp hm perm hR_lt hjR).2
        · rw [ite_eq_right hjR]; exact sum_normSq_groverMultiState_eq_one ∅ 0
      rw [hnorm1, Complex.ofReal_one]
  simp_rw [hslot_val]
  have hp_sub : (∏ j : Fin m, if j ∈ A then ((1 / (ghMidPOcc pref R j : ℝ) : ℝ) : ℂ) else 1) = ∏ j ∈
    A, ((1 / (ghMidPOcc pref R j : ℝ) : ℝ) : ℂ) := by
    rw [← Finset.prod_subset (Finset.subset_univ A) fun j _ hj ↦ ite_eq_right hj]
    exact Finset.prod_congr rfl fun j hj ↦ ite_eq_left hj
  rw [hp_sub, ← Complex.ofReal_prod]; rfl
private lemma sum_normSq_ghMidPAmpState_readout {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hR_lt : R.card < 2 ^ (n - p)) (coeff :
  Finset (Fin m) → ℂ) (Φ : Finset (Fin (2 ^ n)) → ℂ) :
    let pref := fun x ↦ subcubePref hp hm (perm x)
    (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (ghMidPAmpState hp hm perm R coeff (parallelMarkPerm n m
      R o)) : ℂ) * Φ (R \ (groupHits (Nat.mul_one m) o).toFinset)) = ∑ A ∈ (R.image pref).powerset,
      (normSq (coeff A) : ℂ) * ∑ c ∈ ghMidPHitChoices pref R A, (ghMidPChoiceWeight pref R A : ℂ) *
      Φ (R \ ghMidPChoiceSet c) := by
  intro pref; let J := R.image pref
  have hpt (o : Fin (2 ^ (m * (n + 1)))) : (normSq (ghMidPAmpState hp hm perm R coeff
    (parallelMarkPerm n m R o)) : ℂ) = ∑ A ∈ J.powerset, (normSq (coeff A) : ℂ) * (normSq
    (ghBasisVec hp hm perm R A (parallelMarkPerm n m R o)) : ℂ) := by
    unfold ghMidPAmpState; set w := parallelMarkPerm n m R o; by_cases hex : ∃ A₀ ∈ J.powerset,
      ghBasisVec hp hm perm R A₀ w ≠ 0
    · rcases hex with ⟨A₀, hA₀, hnz⟩
      have hzero (A : Finset (Fin m)) (hA : A ∈ J.powerset) (hne : A ≠ A₀) : ghBasisVec hp hm perm R
        A w = 0 := by
        rcases ghBasisVec_mul_eq_zero_of_ne_midp hp hm perm R (Finset.mem_powerset.mp hA)
          (Finset.mem_powerset.mp hA₀) hne w with h1 | h2
        · exact h1
        · exact absurd h2 hnz
      rw [Finset.sum_eq_single A₀ (fun A hA hne ↦ by rw [hzero A hA hne, mul_zero])
          (fun hnot ↦ absurd hA₀ hnot),
        Finset.sum_eq_single A₀ (fun A hA hne ↦ by
          rw [hzero A hA hne, Complex.normSq_zero, Complex.ofReal_zero, mul_zero])
          (fun hnot ↦ absurd hA₀ hnot),
        map_mul, Complex.ofReal_mul]
    · simp only [not_exists, not_and, not_not] at hex
      rw [Finset.sum_eq_zero (fun A hA ↦ by rw [hex A hA, mul_zero]),
        Complex.normSq_zero, Complex.ofReal_zero,
        Finset.sum_eq_zero (fun A hA ↦ by
          rw [hex A hA, Complex.normSq_zero, Complex.ofReal_zero, mul_zero])]
  simp_rw [hpt, Finset.sum_mul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun A hA ↦ ?_
  simp_rw [mul_assoc]; rw [← Finset.mul_sum, sum_normSq_ghBasisVec_readout_choices hp hm perm hR_lt
    (Finset.mem_powerset.mp hA) Φ]
private lemma sum_normSq_ghMidPAmpState_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hR_lt : R.card < 2 ^ (n - p)) (coeff :
  Finset (Fin m) → ℂ) :
    let pref := fun x ↦ subcubePref hp hm (perm x)
    (∑ w : Fin (2 ^ (m * (n + 1))), (normSq (ghMidPAmpState hp hm perm R coeff w) : ℂ)) = ∑ A ∈
      (R.image pref).powerset, (normSq (coeff A) : ℂ) := by
  intro pref
  have hcomp : (∑ w : Fin (2 ^ (m * (n + 1))), (normSq (ghMidPAmpState hp hm perm R coeff w) : ℂ)) =
    ∑ o : Fin (2 ^ (m * (n + 1))), (normSq (ghMidPAmpState hp hm perm R coeff (parallelMarkPerm n m
    R o)) : ℂ) * (1 : ℂ) := by
    simp_rw [mul_one]; exact (Equiv.sum_comp (parallelMarkPerm n m R) (fun w ↦ (normSq
      (ghMidPAmpState hp hm perm R coeff w) : ℂ))).symm
  rw [hcomp, sum_normSq_ghMidPAmpState_readout hp hm perm hR_lt coeff (fun _ ↦ 1)]
  refine Finset.sum_congr rfl fun A hA ↦ ?_; dsimp only [pref] at hA ⊢; simp only [mul_one]
  rw [← Complex.ofReal_sum, ghMidPHitChoices_sum_weight (fun x ↦ subcubePref hp hm (perm x)) R
    (Finset.mem_powerset.mp hA), Complex.ofReal_one, mul_one]
/- ## 2. QHL, `ScaledCostRel`, and Arbitrary-Collision `ghDeflatedRound` Semantics -/
private lemma gh_constAssertion_mono_midp {Var : Type} {d : ℕ} {α₁ α₂ : ℝ} (h0 : 0 ≤ α₁) (h : α₁ ≤
  α₂) (h1 : α₂ ≤ 1) : (constAssertion α₁ : CQAssertion (Store Var) d) ≤ constAssertion α₂ := fun σ ↦
    by
  apply Subtype.coe_le_coe.mp
  rw [constAssertion_apply_of_bounds α₁ h0 (h.trans h1),
    constAssertion_apply_of_bounds α₂ (h0.trans h) h1]
  exact smul_le_smul_of_nonneg_right h (by simp)
private lemma gh_wp_constAssertion_le_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] (P :
  QProg Var d) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : wp P (constAssertion α) ≤ constAssertion α :=
  by
  induction P with
  | «skip» => exact le_rfl | «abort» => exact bot_le | assign _ _ => exact fun _ ↦ le_rfl
  | qMeasure x ℳ =>
    intro σ; apply Subtype.coe_le_coe.mp; rw [wp_qMeasure, CQAssertion.qMeasure_coe,
      constAssertion_apply_of_bounds α hα0 hα1]
    have hsum : (∑ o : Fin _, HermitianMat.conj (ℳ.1 o)ᴴ (((constAssertion α : CQAssertion (Store
      Var) d)
      (σ.subst x ↑o.1)).1)) = α • ∑ o : Fin _, HermitianMat.conj (ℳ.1 o)ᴴ 1 := by
      rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun o _ ↦ ?_
      rw [constAssertion_apply_of_bounds α hα0 hα1]; apply HermitianMat.ext
      simp [HermitianMat.conj_apply_mat]
    rw [hsum]; exact smul_le_smul_of_nonneg_left (ℳ.sum_conj_le_one fun _ ↦ le_rfl) hα0
  | qSet =>
    intro σ; apply Subtype.coe_le_coe.mp; rw [wp_qSet, constAssertion_apply_of_bounds α hα0 hα1]
    have h00 : ((constAssertion α : CQAssertion (Store Var) d) σ).1.1 0 0 = (α : ℂ) :=
      (by rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1]; simp)
    refine le_of_eq ?_; apply HermitianMat.ext; rw [← HermitianMat.val_eq_coe,
      qhlQSet_val, h00]; simp [HermitianMat.mat_smul, HermitianMat.mat_one]
  | qAssign U =>
    intro σ; apply Subtype.coe_le_coe.mp; refine le_of_eq ?_; apply HermitianMat.ext
    have hmat : ∀ τ : Store Var, ((constAssertion α : CQAssertion (Store Var) d) τ).1.1 = (α : ℂ) •
      (1 :
      Matrix (Fin d) (Fin d) ℂ) := fun τ ↦ by
      rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1, HermitianMat.mat_smul,
        HermitianMat.mat_one]; ext i j; simp [Complex.real_smul]
    rw [wp_qAssign, ← HermitianMat.val_eq_coe, qhlQAssign_val, hmat σ, ←
      HermitianMat.val_eq_coe, hmat σ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ←
      Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp U.2]
  | qSeq c₁ _ ih₁ ih₂ => exact (wp_mono c₁ ih₂).trans ih₁
  | qIf _ _ _ ih₁ ih₂ =>
    intro σ; dsimp [wp]; split_ifs
    · exact ih₁ σ
    · exact ih₂ σ
  | qWhile b c ih =>
    have hrec : ∀ t, whileRecWP (wp c) b t (constAssertion α) ≤ constAssertion α := by
      intro t
      induction t with
      | zero => exact bot_le
      | succ _ iht =>
        intro σ; dsimp [whileRecWP]; split_ifs
        · exact ((wp_mono c iht).trans ih) σ
        · exact le_rfl
    intro σ; rw [wp_qWhile]; exact OmegaCompletePartialOrder.ωSup_le
      (whileRecWP.chain (wp c) (wp_mono c) b (constAssertion α)) (constAssertion α) hrec σ
private lemma gh_expect_constAssertion_midp {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) {α : ℝ}
    (hα0 :
  0 ≤ α) (hα1 : α ≤ 1) : 𝔼[Δ, constAssertion α] = α * Δ.trace := by
  rw [expect_eq_mul_of_apply_eq_smul Δ (Ψ := ⊤) α (fun σ ↦ by
    rw [constAssertion_apply_of_bounds α hα0 hα1]
    rfl), expect_top]
private lemma gh_expect_nonneg_midp {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) (θ :
    CQAssertion (Store Var) d)
  : 0 ≤ 𝔼[Δ, θ] := by simpa using expect_mono (le_rfl : Δ ≤ Δ) (bot_le : ⊥ ≤ θ)
private lemma ghScaledCostRel_of_zero_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model
  : CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d} (hP : CostBound (Var := Var) model P 0) :
  ScaledCostRel model B P ⊥ 0 := by
  refine ⟨le_rfl, hB.le, bot_le, fun Δ ↦ ?_⟩; have h0 := hP Δ; simp only [ENNReal.coe_zero,
    mul_zero, nonpos_iff_eq_zero] at h0; simp [h0]
private lemma ghScaledCostRel_of_costBound_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
  {model : CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d} {k_cost : ℝ≥0} (hP : CostBound (Var
  := Var) model P k_cost) (hkB : (k_cost : ℝ) ≤ B) : ScaledCostRel model B P (constAssertion
  ((k_cost : ℝ) / B)) (k_cost : ℝ) := by
  have hc0 : 0 ≤ (k_cost : ℝ) := NNReal.coe_nonneg k_cost; have hdiv0 : 0 ≤ (k_cost : ℝ) / B :=
    div_nonneg hc0 hB.le; have hdiv1 : (k_cost : ℝ) / B ≤ 1 := (div_le_one hB).mpr hkB; refine ⟨hc0,
    hkB, le_rfl, fun Δ ↦ (hP Δ).trans ?_⟩; rw [gh_expect_constAssertion_midp Δ hdiv0 hdiv1, ←
    mul_assoc, mul_div_cancel₀ _ hB.ne', mul_comm (k_cost : ℝ) Δ.trace, ENNReal.ofReal_mul
    Δ.trace.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
private lemma ghScaledCostRel_qIf_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) (b : Store Var → Prop) [DecidablePred b] {P₁ P₂ : QProg Var d}
  {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ} (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ :
    ScaledCostRel
  model B P₂ θ₂ c₂) : ScaledCostRel model B (.qIf b P₁ P₂) (fun σ ↦ if b σ then θ₁ σ else θ₂ σ) (max
  c₁ c₂) := by
  have hmB : max c₁ c₂ ≤ B := max_le h₁.2.1 h₂.2.1; refine ⟨le_max_of_le_left h₁.1, hmB, fun σ ↦ ?_,
    fun Δ ↦ ?_⟩
  · dsimp only; split_ifs
    · exact (h₁.2.2.1 σ).trans (gh_constAssertion_mono_midp (div_nonneg h₁.1 hB.le)
        (div_le_div_of_nonneg_right (le_max_left c₁ c₂) hB.le) ((div_le_one hB).mpr hmB) σ)
    · exact (h₂.2.2.1 σ).trans (gh_constAssertion_mono_midp (div_nonneg h₂.1 hB.le)
        (div_le_div_of_nonneg_right (le_max_right c₁ c₂) hB.le) ((div_le_one hB).mpr hmB) σ)
  · simp only [expectedCost]
    have hnn1 : 0 ≤ B * 𝔼[Δ.wdTrueSt b, θ₁] := mul_nonneg hB.le (gh_expect_nonneg_midp _ _)
    have hnn2 : 0 ≤ B * 𝔼[Δ.wdFalseSt b, θ₂] := mul_nonneg hB.le (gh_expect_nonneg_midp _ _)
    calc expectedCost model P₁ (Δ.wdTrueSt b) + expectedCost model P₂ (Δ.wdFalseSt b)
        ≤ ENNReal.ofReal (B * 𝔼[Δ.wdTrueSt b, θ₁]) + ENNReal.ofReal (B * 𝔼[Δ.wdFalseSt b, θ₂]) :=
          add_le_add (h₁.2.2.2 _) (h₂.2.2.2 _)
      _ = ENNReal.ofReal (B * 𝔼[Δ, fun σ ↦ if b σ then θ₁ σ else θ₂ σ]) := by
          rw [← ENNReal.ofReal_add hnn1 hnn2, ← mul_add, ← wdExpectItePartition]
private theorem ghScaledCostRel_add_le_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model
  : CostModel d} {B : ℝ} (hB : 0 < B) {P₁ P₂ : QProg Var d} {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁
    c₂ : ℝ}
  (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel model B P₂ θ₂ c₂) (hc_sum : c₁ + c₂ ≤ B)
  (σ : Store Var) : (θ₁ σ).1 + ((wp P₁ θ₂) σ).1 ≤ 1 := by
  have h_wp_le : wp P₁ θ₂ ≤ constAssertion (c₂ / B) := (wp_mono P₁ h₂.2.2.1).trans
    (gh_wp_constAssertion_le_midp P₁ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1))
  have ha : (θ₁ σ).1 ≤ (c₁ / B) • 1 := by
    have h := Subtype.coe_le_coe.mpr (h₁.2.2.1 σ)
    rwa [constAssertion_apply_of_bounds _ (div_nonneg h₁.1 hB.le) ((div_le_one hB).mpr h₁.2.1)] at h
  have hb : ((wp P₁ θ₂) σ).1 ≤ (c₂ / B) • 1 := by
    have h := Subtype.coe_le_coe.mpr (h_wp_le σ)
    rwa [constAssertion_apply_of_bounds _ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1)] at h
  calc (θ₁ σ).1 + ((wp P₁ θ₂) σ).1 ≤ (c₁ / B) • 1 + (c₂ / B) • 1 := add_le_add ha hb
    _ = ((c₁ + c₂) / B) • 1 := by rw [add_div, add_smul]
    _ ≤ (1 : ℝ) • (1 : HermitianMat (Fin d) ℂ) :=
        smul_le_smul_of_nonneg_right ((div_le_one hB).mpr hc_sum) (by simp)
    _ = 1 := one_smul _ _
private lemma ghScaledCostRel_seq_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) {P₁ P₂ : QProg Var d} {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁ c₂
    : ℝ}
  (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel model B P₂ θ₂ c₂) (hc_sum : c₁ + c₂ ≤ B)
  : ScaledCostRel model B (P₁ ;; P₂) (θ₁.add (wp P₁ θ₂) (ghScaledCostRel_add_le_midp hB h₁ h₂
  hc_sum)) (c₁ + c₂) := by
  have h_wp_le : wp P₁ θ₂ ≤ constAssertion (c₂ / B) := (wp_mono P₁ h₂.2.2.1).trans
    (gh_wp_constAssertion_le_midp P₁ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1))
  refine ⟨add_nonneg h₁.1 h₂.1, hc_sum, fun σ ↦ ?_, fun Δ ↦ ?_⟩
  · apply Subtype.coe_le_coe.mp; rw [CQAssertion.add_apply, Observable.add_coe,
      constAssertion_apply_of_bounds _ (div_nonneg (add_nonneg h₁.1 h₂.1) hB.le) ((div_le_one
      hB).mpr hc_sum)]
    have ha : (θ₁ σ).1 ≤ (c₁ / B) • 1 := by
      have h := Subtype.coe_le_coe.mpr (h₁.2.2.1 σ)
      rwa [constAssertion_apply_of_bounds _ (div_nonneg h₁.1 hB.le)
        ((div_le_one hB).mpr h₁.2.1)] at h
    have hb : ((wp P₁ θ₂) σ).1 ≤ (c₂ / B) • 1 := by
      have h := Subtype.coe_le_coe.mpr (h_wp_le σ)
      rwa [constAssertion_apply_of_bounds _ (div_nonneg h₂.1 hB.le)
        ((div_le_one hB).mpr h₂.2.1)] at h
    calc (θ₁ σ).1 + ((wp P₁ θ₂) σ).1 ≤ (c₁ / B) • 1 + (c₂ / B) • 1 := add_le_add ha hb
      _ = ((c₁ + c₂) / B) • 1 := by rw [add_div, add_smul]
  · rw [expectedCost_qSeq]; have hnn1 : 0 ≤ B * 𝔼[Δ, θ₁] := mul_nonneg hB.le (gh_expect_nonneg_midp
      _ _)
    have hnn2 : 0 ≤ B * 𝔼[(interp P₁).toStateFun Δ, θ₂] := mul_nonneg hB.le (gh_expect_nonneg_midp _
      _)
    calc expectedCost model P₁ Δ + expectedCost model P₂ ((interp P₁).toStateFun Δ)
        ≤ ENNReal.ofReal (B * 𝔼[Δ, θ₁]) + ENNReal.ofReal (B * 𝔼[(interp P₁).toStateFun Δ, θ₂]) :=
          add_le_add (h₁.2.2.2 Δ) (h₂.2.2.2 _)
      _ = ENNReal.ofReal (B * 𝔼[Δ, θ₁.add (wp P₁ θ₂)
          (ghScaledCostRel_add_le_midp hB h₁ h₂ hc_sum)]) := by
          rw [← ENNReal.ofReal_add hnn1 hnn2, ← wp_expectation_eq P₁ Δ θ₂, ← mul_add, ←
            expect_assertion_add]
private lemma ghScaledCostRel_mono_c_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d} {θ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ} (h
    :
  ScaledCostRel model B P θ c₁) (hc : c₁ ≤ c₂) (hcB : c₂ ≤ B) : ScaledCostRel model B P θ c₂ :=
  ⟨h.1.trans hc, hcB, h.2.2.1.trans (gh_constAssertion_mono_midp (div_nonneg h.1 hB.le)
    (div_le_div_of_nonneg_right hc hB.le) ((div_le_one hB).mpr hcB)), h.2.2.2⟩
private lemma ghScaledCostRel_seq_zero_left_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
  {model : CostModel d} {B : ℝ} (hB : 0 < B) {P₁ P₂ : QProg Var d} {θ₂ : CQAssertion (Store Var) d}
    {c₂ : ℝ}
  (h₁ : CostBound (Var := Var) model P₁ 0) (h₂ : ScaledCostRel model B P₂ θ₂ c₂) : ScaledCostRel
  model B (P₁ ;; P₂) (wp P₁ θ₂) c₂ := by
  refine ⟨h₂.1, h₂.2.1, (wp_mono P₁ h₂.2.2.1).trans (gh_wp_constAssertion_le_midp P₁ (div_nonneg
    h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1)), fun Δ ↦ ?_⟩
  have h0 := h₁ Δ; simp only [ENNReal.coe_zero, mul_zero, nonpos_iff_eq_zero] at h0
  rw [expectedCost_qSeq, h0, zero_add]
  exact (h₂.2.2.2 ((interp P₁).toStateFun Δ)).trans_eq (by rw [wp_expectation_eq])
private lemma gh_cqAssertion_add_mat_midp {Var : Type} {d : ℕ} (θ₁ θ₂ : CQAssertion (Store Var) d)
    (h : ∀ σ,
  (θ₁ σ).1 + (θ₂ σ).1 ≤ 1) (σ : Store Var) : ((θ₁.add θ₂ h) σ).1.1 = (θ₁ σ).1.1 + (θ₂ σ).1.1 := by
  simp only [HermitianMat.val_eq_coe, CQAssertion.add_apply, Observable.add_coe,
    HermitianMat.mat_add]
private noncomputable def ghQuadForm_midp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) : ℂ := star v ⬝ᵥ (A *ᵥ v)
private lemma ghQuadForm_zero_mat_midp {d : ℕ} (v : Fin d → ℂ) : ghQuadForm_midp (0 : Matrix (Fin d)
  (Fin d) ℂ) v = 0 := by unfold ghQuadForm_midp; simp
private lemma ghQuadForm_bot_apply_midp {Var : Type} {d : ℕ} (σ : Store Var) (v : Fin d → ℂ) :
  ghQuadForm_midp ((⊥ : CQAssertion (Store Var) d) σ).1.1 v = 0 := ghQuadForm_zero_mat_midp v
private lemma ghQuadForm_zero_vec_midp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ghQuadForm_midp A (0
  : Fin d → ℂ) = 0 := by unfold ghQuadForm_midp; simp
private lemma ghQuadForm_add_mat_midp {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
  ghQuadForm_midp (A + B) v = ghQuadForm_midp A v + ghQuadForm_midp B v := by
  unfold ghQuadForm_midp; rw [Matrix.add_mulVec, dotProduct_add]
private lemma ghQuadForm_single_midp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (idx : Fin d) :
  ghQuadForm_midp A (single idx 1) = A idx idx := (diag_eq_star_single_dotProduct_mulVec A idx).symm
private lemma ghQuadForm_smul_vec_midp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (v : Fin d →
  ℂ) : ghQuadForm_midp A (c • v) = (normSq c : ℂ) * ghQuadForm_midp A v := by
  unfold ghQuadForm_midp; rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
private lemma ghQuadForm_unitaryEffect_midp {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {P :
  QProg Var d} {U : Matrix (Fin d) (Fin d) ℂ} (hU : UnitaryEffect P U) (Θ : CQAssertion (Store Var)
    d) (σ :
  Store Var) (v : Fin d → ℂ) : ghQuadForm_midp ((wp P Θ) σ).1.1 v = ghQuadForm_midp (Θ σ).1.1 (U *ᵥ
  v) := by
  unfold ghQuadForm_midp; rw [unitaryEffect_apply hU Θ σ, Matrix.mul_assoc, ← mulVec_mulVec, ←
    mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
private lemma ghQuadForm_wp_measureRegister_midp {Var : Type} [DecidableEq Var] (x : Var) {w Q : ℕ}
  (r : QRegister w Q) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (v : Fin (2 ^ Q) → ℂ) :
  ghQuadForm_midp ((wp (measureRegister x r) Θ) σ).1.1 v = ∑ o : Fin (2 ^ w), ghQuadForm_midp ((Θ
  (Store.subst σ x (Int.ofNat o.val))).1.1) (r.basisOutcomeProjector o *ᵥ v) := by
  unfold ghQuadForm_midp; rw [wp_measureRegister, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_; rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.vecMul_conjTranspose, star_star, QRegister.basisOutcomeProjector_conjTranspose]
private lemma ghQuadForm_constAssertion_workMemState_midp {Var : Type} {W M : ℕ} {α : ℝ} (hα0 : 0 ≤
  α) (hα1 : α ≤ 1) (τ : Store Var) (ξ : Fin (2 ^ W) → ℂ) (μ : Fin (2 ^ M)) : ghQuadForm_midp
  ((constAssertion α : CQAssertion (Store Var) (2 ^ (W + M))) τ).1.1 (workMemState ξ (single μ 1)) =
    (α : ℂ)
  * ∑ w : Fin (2 ^ W), (normSq (ξ w) : ℂ) := by
  have hmat : ((constAssertion α : CQAssertion (Store Var) (2 ^ (W + M))) τ).1.1 = (α : ℂ) • (1 :
    Matrix
    (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ) := by
    rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1, HermitianMat.mat_smul,
      HermitianMat.mat_one]; ext i j; simp [Complex.real_smul]
  rw [hmat]; unfold ghQuadForm_midp; rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]; congr 1; rw [dotProduct]
  let f (z : Fin (2 ^ (W + M))) : ℂ := star (workMemState ξ (single μ 1) z) * workMemState ξ (single
    μ 1) z; change ∑ z, f z = _; rw [← (lowHighEquiv W M).symm.sum_comp f, sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [sum_eq_single μ (fun ν hν ↦ by
    dsimp only [f, workMemState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hν, mul_zero, mul_zero])]
  dsimp only [f, workMemState]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one,
    RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
private lemma memSeen_writeMemBatch_midp {n k active : ℕ} {S : Finset (Fin (2 ^ n))} {μ : Fin (2 ^
  (k * n))} (hval : MemPrefixValid S active μ) (L : List (Fin (2 ^ n))) (hlen : active + L.length ≤
  k) : memSeen n k (memPrefix k (active + L.length)) (writeMemBatch active L μ) = memSeen n k
  (memPrefix k active) μ ∪ L.toFinset := by
  have hslot_lt (i : Fin k) (hi : i.val < active) : addrEquiv n k (writeMemBatch active L μ) i =
    addrEquiv n k μ i := by
    unfold writeMemBatch; rw [Equiv.apply_symm_apply, Pi.add_apply, ite_eq_right (not_le_of_gt hi),
      add_zero]
  have hslot_ge (i : Fin k) (hge : active ≤ i.val) (hlt : i.val < active + L.length) : addrEquiv n k
    (writeMemBatch active L μ) i = L[i.val - active]'(by omega) := by
    unfold writeMemBatch; have hzero : addrEquiv n k μ i = 0 := hval.2.2.2 i hge
    have hsub : i.val - active < L.length := (by omega); rw [Equiv.apply_symm_apply, Pi.add_apply,
      hzero, zero_add, ite_eq_left hge]; simp [List.getElem?_eq_getElem hsub]
  ext x; simp only [memSeen, memPrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, List.mem_toFinset]; constructor
  · rintro ⟨i, hi, rfl⟩; rcases lt_or_ge i.val active with hlt | hge
    · exact Or.inl ⟨i, hlt, (hslot_lt i hlt).symm⟩
    · right; rw [hslot_ge i hge hi]; exact List.getElem_mem _
  · rintro (⟨i, hi, rfl⟩ | hxL)
    · exact ⟨i, by omega, hslot_lt i hi⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hxL; let idx : Fin k := ⟨active + a, by omega⟩
      refine ⟨idx, by dsimp [idx]; omega, ?_⟩; have hge : active ≤ idx.val :=
        (by dsimp [idx]; omega); have hlt : idx.val < active + L.length := (by dsimp [idx]; omega)
      rw [hslot_ge idx hge hlt]; simp [idx]
private lemma ghQuadForm_wp_wdReadoutWrite_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k
  active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin
  (2 ^ n))) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {μ : Fin (2 ^ (k * n))} (hval :
  MemPrefixValid S active μ) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset
    (Fin (2 ^
  n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) →
  MemPrefixValid S s ν → (∀ i : Fin k, i.val < active → addrEquiv n k ν i = addrEquiv n k μ i) →
  ((((S \ memSeen n k (memPrefix k active) μ) \ (S \ memSeen n k (memPrefix k s) ν)).image (fun x ↦
  subcubePref hp hm (perm x))).card = s - active) → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m
  k 0 ν) = (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ)) (σ : Store Var) (φ : Fin (2 ^ (m * (n + 1)))
  → ℂ) (hsupp : ∀ o : Fin (2 ^ (m * (n + 1))), φ (parallelMarkPerm n m (S \ memSeen n k (memPrefix k
  active) μ) o) ≠ 0 → (∀ x ∈ groupHits (Nat.mul_one m) o, x ∈ S \ memSeen n k (memPrefix k active)
  μ) ∧ ((groupHits (Nat.mul_one m) o).toFinset.image (fun x ↦ subcubePref hp hm (perm x))).card =
  (groupHits (Nat.mul_one m) o).length) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    ghQuadForm_midp ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign
      (groverParallelMarkingOracle m S)) Θ) σ).1.1 (workMemState (P_R *ᵥ φ) (single μ 1)) = ∑ o :
      Fin (2 ^ (m * (n + 1))), (normSq (φ (parallelMarkPerm n m R o)) : ℂ) * (Ψ (R \ (groupHits
      (Nat.mul_one m) o).toFinset) : ℂ) := by
  intro R P_R; let hbg1 : m * 1 = m := Nat.mul_one m; unfold wdReadoutWrite; dsimp only [compile]
  rw [wp_qSeq, ghQuadForm_unitaryEffect_midp (unitaryEffect_phaseTag _)]; unfold ghQuadForm_midp
  rw [wp_setCountAndResetWork, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_; rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star,
    krausLowBlock_mulVec_memAddPerm]; change ghQuadForm_midp _ ((P_R *ᵥ φ) o • single (workMemIdx n
    m k 0 (writeMemBatch active (groupHits hbg1 o) μ)) 1) = _; rw [ghQuadForm_smul_vec_midp,
    ghQuadForm_single_midp]; dsimp only [P_R]; rw [permUnitary_parallelMarkPerm_mulVec_apply_midp]
  by_cases hnz : φ (parallelMarkPerm n m R o) = 0
  · simp [hnz]
  · rcases hsupp o hnz with ⟨hmem_R, himg_len⟩
    obtain ⟨hlen, hval'⟩ := memPrefixValid_writeMemBatch hcard hval (nodup_groupHits hbg1 o) hmem_R
    have hag (i : Fin k) (hi : i.val < active) : addrEquiv n k (writeMemBatch active (groupHits hbg1
      o) μ) i = addrEquiv n k μ i := by
      unfold writeMemBatch; rw [Equiv.apply_symm_apply, Pi.add_apply, ite_eq_right (not_le_of_gt
        hi), add_zero]
    have hcnt : (batchNextCount hm1 hkN hbg1 active o).val = active + (groupHits hbg1 o).length :=
      (by simp [batchNextCount, Nat.min_eq_right hlen])
    have hsdiff : S \ memSeen n k (memPrefix k (active + (groupHits hbg1 o).length)) (writeMemBatch
      active (groupHits hbg1 o) μ) = R \ (groupHits hbg1 o).toFinset := by
      rw [memSeen_writeMemBatch_midp hval (groupHits hbg1 o) hlen]; ext x; simp only [R,
        Finset.mem_sdiff, Finset.mem_union]
      tauto
    have hsdiff2 : R \ (R \ (groupHits hbg1 o).toFinset) = (groupHits hbg1 o).toFinset := by
      ext x; simp only [Finset.mem_sdiff, List.mem_toFinset]; exact ⟨fun ⟨hxR, hn⟩ ↦ by_contra fun
        hx ↦ hn ⟨hxR, hx⟩, fun hx ↦ ⟨hmem_R x hx, fun h ↦ h.2 hx⟩⟩
    have hcard_img : (((S \ memSeen n k (memPrefix k active) μ) \ (S \ memSeen n k (memPrefix k
      (active + (groupHits hbg1 o).length)) (writeMemBatch active (groupHits hbg1 o) μ))).image (fun
      x ↦ subcubePref hp hm (perm x))).card = (active + (groupHits hbg1 o).length) - active := by
      change ((R \ _).image _).card = _; rw [hsdiff, hsdiff2, himg_len, Nat.add_sub_cancel_left]
    rw [hcnt, hΘ (active + (groupHits hbg1 o).length) _ _ hlen (by simp [Store.subst]) hval' hag
      hcard_img, hsdiff]
private lemma ghQuadForm_wp_topAncProbe_midp {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
  (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (active : ℕ) (wSpec : ℕ → GaussPyth × PythPair)
  (noClickCirc : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (S : Finset (Fin (2 ^ n))) (Θ :
  CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) (ψ : Fin (2 ^ (m * (n + 1)))
    → ℂ) {μ
  : Fin (2 ^ (k * n))} (hμ : μ.val < 2 ^ (k * n - 1)) :
    let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
    let probeCirc : OracleCirc Var (W + M) ((n + 1) * m) :=
      .seq (.step (phaseTag (gaussianHammingAllHitUnitary n m M hM wSpec))) (.seq (.measure res
        (topAncReg W M hM)) (.qIf (fun τ ↦ τ res = 1) (wdClickCleanup res hm1 hkN hM active)
        noClickCirc))
    ghQuadForm_midp ((wp (probeCirc.compile qAssign oracle) Θ) σ).1.1 (workMemState ψ (single μ
      1)) = ghQuadForm_midp ((wp (noClickCirc.compile qAssign oracle) Θ) (Store.subst σ res
      0)).1.1 (workMemState (ghDampVec n m wSpec ψ) (single μ 1)) + ghQuadForm_midp ((wp
      ((wdReadoutWrite res hm1 hkN active).compile qAssign oracle) Θ) (Store.subst σ res 1)).1.1
      (workMemState (ghClickVec n m wSpec ψ) (single μ 1)) := by
  intro W M oracle probeCirc; dsimp only [probeCirc, compile]
  rw [wp_qSeq, wp_qSeq, ghQuadForm_unitaryEffect_midp (unitaryEffect_phaseTag _), show
    (gaussianHammingAllHitUnitary n m M hM wSpec).1 = gaussianHammingAllHitMat n m M hM wSpec from
    rfl, gaussianHammingAllHitMat_mulVec_workMemState hM wSpec ψ hμ,
    ghQuadForm_wp_measureRegister_midp]; refine (Fin.sum_univ_two _).trans ?_
  have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) res ≠ 1 := by simp [Store.subst]
  have hs1 : (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) res = 1 := by simp [Store.subst]
  let branchProg := QProg.qIf (fun τ ↦ τ res = 1) ((wdClickCleanup res hm1 hkN hM active).compile
    qAssign oracle) (noClickCirc.compile qAssign oracle)
  have hwp0 : wp branchProg Θ (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) = wp
    (noClickCirc.compile qAssign oracle) Θ (Store.subst σ res 0) := by
    rw [wp_qIf]; dsimp only; rw [ite_eq_right hs0]; rfl
  have hwp1 : wp branchProg Θ (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) = wp
    ((wdClickCleanup res hm1 hkN hM active).compile qAssign oracle) Θ (Store.subst σ res 1) := by
    rw [wp_qIf]; dsimp only; rw [ite_eq_left hs1]; rfl
  congr 1
  · change ghQuadForm_midp ((wp branchProg Θ (Store.subst σ res (Int.ofNat (0 : Fin (2 ^
      1)).val))).1.1) _ = _; rw [hwp0, topAncReg_projector_zero_mulVec hM _ _ hμ]
  · change ghQuadForm_midp
        ((wp branchProg Θ (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val))).1.1) _ = _
    rw [hwp1, topAncReg_projector_one_mulVec hM _ _ hμ]; unfold wdClickCleanup; dsimp only [compile]
    rw [wp_qSeq, ghQuadForm_unitaryEffect_midp (unitaryEffect_phaseTag _),
      topAncReg_flip_mulVec_one hM _ hμ]
private lemma deflatedRead_mulVec_workMemState_midp {n m k active : ℕ} {S : Finset (Fin (2 ^ n))} {μ
  : Fin (2 ^ (k * n))} (hsub : memSeen n k (memPrefix k active) μ ⊆ S) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    (∀ ξ : Fin (2 ^ W) → ℂ, (unm * orac) *ᵥ workMemState ξ (single μ 1) = workMemState (P_R *ᵥ ξ)
      (single μ 1)) ∧ (∀ ξ : Fin (2 ^ W) → ℂ, P_R *ᵥ (P_R *ᵥ ξ) = ξ) := by
  intro W M R orac unm P_R; constructor
  · intro ξ; rw [← mulVec_mulVec, unmark_mul_parallelOracle_workMemState (memPrefix k active) ξ μ
      hsub, show S \ memSeen n k (memPrefix k active) μ = R from rfl,
      fullReg_embedUnitary_eq_permutationUnitary R]
  · intro ξ; funext w; rw [permUnitary_parallelMarkPerm_mulVec_apply_midp,
      permUnitary_parallelMarkPerm_mulVec_apply_midp, parallelMarkPerm_involutive]
private lemma unitaryEffect_wdPrepAndNoClick_midp {Var : Type} [DecidableEq Var] {n p m k : ℕ} (hp :
  p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) (active : ℕ)
  :
    let W := m * (n + 1); let M := k * n; let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let prepOp := (lowBlock W M).embedMatrix (wdPrepUnitary hp hm perm).1
    (∀ kInit : ℕ, UnitaryEffect ((wdPrepAndLoop (Var := Var) (k := k) hp hm perm active
      kInit).compile qAssign (groverParallelMarkingOracle m S)) ((unm * orac) * ((diffOp * phaseOp)
      ^ kInit) * prepOp)) ∧ (∀ kNext : ℕ, UnitaryEffect ((wdNoClickStep (Var := Var) (k := k) hp
      perm active kNext).compile qAssign (groverParallelMarkingOracle m S)) ((unm * orac) * ((diffOp
      * phaseOp) ^ kNext) * (unm * orac))) := by
  intro W M fc orac unm phaseOp diffOp prepOp; have hwwhole : workMemReg n m k (W + M) le_rfl =
    QRegister.whole (W + M) := (by ext i; simp [workMemReg]; rfl)
  have hwlow : workReg n m (W + M) (by omega) = lowBlock W M := rfl
  have hread : UnitaryEffect ((deflatedOracle (Var := Var) (m := m) (k := k) le_rfl (memPrefix k
    active)).compile qAssign (groverParallelMarkingOracle m S)) (unm * orac) := by
    unfold deflatedOracle; dsimp only [compile]; rw [hwwhole, QRegister.whole_embedUnitary]
    have h1 := unitaryEffect_qAssign (Var := Var) ((workFullReg n m (W + M) (by omega)).embedUnitary
      (groverParallelMarkingOracle m S))
    rw [workFullReg_embedUnitary_eq] at h1; exact unitaryEffect_seq h1 (unitaryEffect_phaseTag _)
  have hphase : UnitaryEffect ((deflatedPhaseStep (Var := Var) (m := m) (k := k) le_rfl (memPrefix k
    active)).compile qAssign (groverParallelMarkingOracle m S)) phaseOp := by
    unfold deflatedPhaseStep; dsimp only [compile]; rw [hwlow]
    have hfc := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (flagConj n m))
    rw [embedUnitary_val] at hfc
    simpa only [phaseOp, Matrix.mul_assoc] using unitaryEffect_seq hfc (unitaryEffect_seq hread hfc)
  have hloop (t : ℕ) : UnitaryEffect ((wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp perm
    active t).compile qAssign (groverParallelMarkingOracle m S)) ((diffOp * phaseOp) ^ t) := by
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using unitaryEffect_skip (Var := Var) (d := 2 ^ (W + M))
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]; unfold wdDeflatedGroverStep; dsimp only [compile]
      have hdiff := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary
        (wdDiffuserUnitary (m := m) hp perm)); rw [embedUnitary_val] at hdiff; rw [pow_succ]
      exact unitaryEffect_seq (unitaryEffect_seq hphase hdiff) ih
  constructor
  · intro kInit; unfold wdPrepAndLoop; dsimp only [compile]
    have hprep := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (wdPrepUnitary hp
      hm perm))
    rw [embedUnitary_val] at hprep; simpa only [Matrix.mul_assoc] using
      unitaryEffect_seq hprep (unitaryEffect_seq (hloop kInit) hread)
  · intro kNext; unfold wdNoClickStep; dsimp only [compile]; simpa only [Matrix.mul_assoc] using
      unitaryEffect_seq hread (unitaryEffect_seq (hloop kNext) hread)
private lemma costBounds_ghPieces_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hm1
  : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin
  (2 ^ n))) (S : Finset (Fin (2 ^ n))) (active : ℕ) :
    let model := CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)
    (∀ kInit : ℕ, CostBound (Var := Var) model ((wdPrepAndLoop (k := k) hp hm perm active
      kInit).compile qAssign (groverParallelMarkingOracle m S)) (kInit + 1)) ∧ (∀ kNext : ℕ,
      CostBound (Var := Var) model ((wdNoClickStep (k := k) hp perm active kNext).compile qAssign
      (groverParallelMarkingOracle m S)) (kNext + 2)) ∧ CostBound (Var := Var) model
      ((wdReadoutWrite (k := k) res hm1 hkN active).compile qAssign (groverParallelMarkingOracle m
      S)) 0 ∧ CostBound (Var := Var) model ((wdClickCleanup (k := k) res hm1 hkN hM active).compile
      qAssign (groverParallelMarkingOracle m S)) 0 := by
  intro model; let W := m * (n + 1); let M := k * n; have hor :=
    isRealMatrix_groverParallelMarkingOracle m S; have hread := costBound_deflatedOracle (Var :=
    Var) (m := m) (k := k) le_rfl (memPrefix k active) S
  have hloop (t : ℕ) : CostBound (Var := Var) model ((wdDeflatedGroverLoop (Var := Var) (m := m) (k
    := k) hp perm active t).compile qAssign (groverParallelMarkingOracle m S)) t := by
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using CostBound.skip_zero (Var := Var) model
    | succ _ ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]; unfold wdDeflatedGroverStep; dsimp only [compile]
      have hstep : CostBound (Var := Var) model ((deflatedPhaseStep (m := m) (k := k) le_rfl
        (memPrefix k active)).compile qAssign (groverParallelMarkingOracle m S) ;; .qAssign
        (phaseTag ((lowBlock W M).embedUnitary (wdDiffuserUnitary (m := m) hp perm)))) 1 := by
        simpa using (costBound_deflatedPhaseStep le_rfl (memPrefix k active) S).seq
          (costBound_qAssign_phaseTag (Var := Var) hor _)
      exact (hstep.seq ih).mono (by rw [← NNReal.coe_le_coe]; push_cast; linarith)
  have hrw : CostBound (Var := Var) model ((wdReadoutWrite (Var := Var) (k := k) res hm1 hkN
    active).compile qAssign (groverParallelMarkingOracle m S)) 0 := by
    unfold wdReadoutWrite; dsimp only [compile]; exact ((costBound_qAssign_phaseTag (Var := Var) hor
      _).seq (costBound_setCountAndResetWork (Var := Var) (M := M) res (batchNextCount hm1 hkN
      (Nat.mul_one m) active) hor)).mono (by simp)
  refine ⟨fun kInit ↦ ?_, fun kNext ↦ ?_, hrw, ?_⟩
  · unfold wdPrepAndLoop; dsimp only [compile]; exact ((costBound_qAssign_phaseTag (Var := Var) hor
      _).seq ((hloop kInit).seq hread)).mono (by simp)
  · unfold wdNoClickStep; dsimp only [compile]
    exact (hread.seq ((hloop kNext).seq hread)).mono (le_of_eq (by ring))
  · unfold wdClickCleanup; dsimp only [compile]; exact ((costBound_qAssign_phaseTag (Var := Var) hor
      _).seq hrw).mono (by simp)
private lemma ghQuadForm_wp_ghProbeChain_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k
  active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {μ : Fin (2 ^ (k * n))}
  (hval : MemPrefixValid S active μ) (hμ : μ.val < 2 ^ (k * n - 1)) (hR_lt : (S \ memSeen n k
  (memPrefix k active) μ).card < 2 ^ (n - p)) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k *
    n))) (Ψ :
  Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res =
  (s : ℤ) → MemPrefixValid S s ν → (∀ i : Fin k, i.val < active → addrEquiv n k ν i = addrEquiv n k
  μ i) → ((((S \ memSeen n k (memPrefix k active) μ) \ (S \ memSeen n k (memPrefix k s) ν)).image
  (fun x ↦ subcubePref hp hm (perm x))).card = s - active) → (Θ τ).1.1 (workMemIdx n m k 0 ν)
  (workMemIdx n m k 0 ν) = (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ)) (probes : List GHMidPProbe)
  (coeff : Finset (Fin m) → ℂ) (σ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    let pref := fun x ↦ subcubePref hp hm (perm x)
    let cf := ghMidPChainFinalCoeff (n - p) pref R probes coeff
    ghQuadForm_midp ((wp ((ghProbeChain res hm1 hkN hM hp perm active (ghMidPWSpec (k - active))
      (fun pr ↦ pr.kNext) probes).compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1
      (workMemState (P_R *ᵥ ghMidPAmpState hp hm perm R coeff) (single μ 1)) =
      ((ghMidPChainClickProb (n - p) pref R probes coeff * Ψ ∅ + ∑ A ∈ (R.image pref).powerset,
      normSq (cf A) * ∑ c ∈ ghMidPHitChoices pref R A, ghMidPChoiceWeight pref R A * Ψ (R \
      ghMidPChoiceSet c) : ℝ) : ℂ) := by
  intro R P_R pref; let hbg1 : m * 1 = m := Nat.mul_one m; have hseen :=
    card_memSeen_of_memPrefixValid hval; have hadd := Finset.card_sdiff_add_card_eq_card hseen.2
  have hR_eq : R.card = k - active := (by dsimp only [R]; omega)
  have hsupp_amp (c' : Finset (Fin m) → ℂ) (o : Fin (2 ^ (m * (n + 1)))) (hnz : ghMidPAmpState hp hm
    perm R c' (parallelMarkPerm n m R o) ≠ 0) : (∀ x ∈ groupHits hbg1 o, x ∈ R) ∧ ((groupHits hbg1
    o).toFinset.image pref).card = (groupHits hbg1 o).length := by
    unfold ghMidPAmpState at hnz; obtain ⟨A, hA, hAnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    have hAb : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) ≠ 0 := fun h0 ↦ hAnz
      (by rw [h0, mul_zero])
    rcases ghBasisVec_support_props_midp hp hm perm R (Finset.mem_powerset.mp hA) o hAb with ⟨_, _,
      hnew, himg, hcnt⟩; exact ⟨hnew, by rw [himg]; exact hcnt.symm⟩
  induction probes generalizing coeff σ with
  | nil =>
    dsimp only [ghProbeChain, ghMidPChainClickProb, ghMidPChainFinalCoeff]
    rw [ghQuadForm_wp_wdReadoutWrite_midp res hm1 hkN hp hm perm hcard hval Θ Ψ hΘ σ _ (hsupp_amp
      coeff), sum_normSq_ghMidPAmpState_readout hp hm perm hR_lt coeff (fun X ↦ (Ψ X : ℂ))]
    push_cast; ring
  | cons pr rest ih =>
    dsimp only [ghProbeChain]; have hw_eq : ghMidPWSpec (k - active) pr = ghMidPWSpec R.card pr :=
      (by rw [hR_eq]); rw [ghQuadForm_wp_topAncProbe_midp res hm1 hkN hM active (ghMidPWSpec (k -
      active) pr) _ S Θ σ _ hμ, hw_eq]
    rcases ghDamp_and_click_marked_ghMidPAmpState hp hm perm R pr coeff with ⟨hdamp, hclick⟩
    let J := R.image pref; have hsmul_ws (c : ℂ) (v : Fin (2 ^ (m * (n + 1))) → ℂ) :
        workMemState (c • v) (single μ 1) = c • workMemState v (single μ 1) := by
      funext idx; simp [workMemState, mul_assoc]
    have hsupp_J (o : Fin (2 ^ (m * (n + 1)))) (hnz : ghBasisVec hp hm perm R J (parallelMarkPerm n
      m R o) ≠ 0) : (∀ x ∈ groupHits hbg1 o, x ∈ R) ∧ ((groupHits hbg1 o).toFinset.image pref).card
      = (groupHits hbg1 o).length := by
      rcases ghBasisVec_support_props_midp hp hm perm R Finset.Subset.rfl o hnz with ⟨_, _, hnew,
        himg, hcnt⟩; exact ⟨hnew, by rw [himg]; exact hcnt.symm⟩
    have hclick_tot : ghQuadForm_midp ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign
      (groverParallelMarkingOracle m S)) Θ) (Store.subst σ res 1)).1.1 (workMemState (ghClickVec n m
      (ghMidPWSpec R.card pr) (P_R *ᵥ ghMidPAmpState hp hm perm R coeff)) (single μ 1)) = (((if 1 ≤
      R.card ∧ (R.image pref).card = R.card then (pr.rotTop.sVal : ℝ) ^ 2 * normSq (coeff (R.image
      pref)) else 0) * Ψ ∅ : ℝ) : ℂ) := by
      rw [hclick]; by_cases hall : 1 ≤ R.card ∧ (R.image pref).card = R.card
      · rw [ite_eq_left hall, ite_eq_left hall, hsmul_ws, ghQuadForm_smul_vec_midp,
          ghQuadForm_wp_wdReadoutWrite_midp res hm1 hkN hp hm perm hcard hval Θ Ψ hΘ _ _ hsupp_J]
        have h_click_o (o : Fin (2 ^ (m * (n + 1)))) : (normSq (ghBasisVec hp hm perm R J
          (parallelMarkPerm n m R o)) : ℂ) * (Ψ (R \ (groupHits hbg1 o).toFinset) : ℂ) = (normSq
          (ghBasisVec hp hm perm R J (parallelMarkPerm n m R o)) : ℂ) * (Ψ ∅ : ℂ) := by
          by_cases hnz : ghBasisVec hp hm perm R J (parallelMarkPerm n m R o) = 0
          · simp [hnz]
          · rcases ghBasisVec_support_props_midp hp hm perm R Finset.Subset.rfl o hnz with ⟨_, _,
              hnew, himg, _⟩
            have hsub_tf : (groupHits hbg1 o).toFinset ⊆ R := fun x hx ↦ hnew x
              (List.mem_toFinset.mp hx)
            have hcard_ge : R.card ≤ (groupHits hbg1 o).toFinset.card :=
              (by rw [← hall.2, ← himg]; exact Finset.card_image_le)
            rw [Finset.eq_of_subset_of_card_le hsub_tf hcard_ge, Finset.sdiff_self]
        rw [Finset.sum_congr rfl fun o _ ↦ h_click_o o, ← Finset.sum_mul, ← Complex.ofReal_sum,
          Equiv.sum_comp (parallelMarkPerm n m R) (fun w ↦ normSq (ghBasisVec hp hm perm R J w)),
          sum_normSq_ghBasisVec_midp hp hm perm hR_lt J]; rw [map_mul, map_mul,
          Complex.normSq_ofReal, GaussPyth.normSq_val]; push_cast; ring
      · rw [ite_eq_right hall, ite_eq_right hall]; have hws0 : workMemState (0 : Fin (2 ^ (m * (n +
          1))) → ℂ) (single μ 1) = 0 := (by funext idx; simp [workMemState]); rw [hws0,
          ghQuadForm_zero_vec_midp]; simp
    rcases deflatedRead_mulVec_workMemState_midp (m := m) hseen.2 with ⟨hread_mul, hPR_inv⟩
    have hue := (unitaryEffect_wdPrepAndNoClick_midp (Var := Var) (k := k) hp hm perm S active).2
      pr.kNext
    have hnoclick_vec :
        let W := m * (n + 1); let M := k * n; let fc := (lowBlock W M).embedMatrix (flagConj n m).1
        let orac := (lowBlock W M).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
        let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
        let phaseOp := fc * unm * orac * fc
        let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
        ((unm * orac) * ((diffOp * phaseOp) ^ pr.kNext) * (unm * orac)) *ᵥ
            workMemState (P_R *ᵥ ghMidPAmpState hp hm perm R (ghMidPDampCoeff R.card pr coeff))
              (single μ 1) =
          workMemState
            (P_R *ᵥ ghMidPAmpState hp hm perm R (ghMidPProbeNextCoeff (n - p) pref R pr coeff))
            (single μ 1) := by
      intro W M fc orac unm phaseOp diffOp; dsimp only [W, M, fc, orac, unm, phaseOp, diffOp]; rw [←
        mulVec_mulVec, ← mulVec_mulVec, hread_mul, hPR_inv, ghGrover_iter_ghMidPAmpState hp hm perm
        hseen.2 hR_lt _ pr.kNext, hread_mul]; rfl
    dsimp only [compile]; rw [hdamp, hclick_tot, wp_qSeq, ghQuadForm_unitaryEffect_midp hue,
      hnoclick_vec, ih]; dsimp only [ghMidPChainClickProb, ghMidPChainFinalCoeff]; push_cast; ring
private lemma wp_ghDeflatedRound_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k active :
  ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
  (perm : Equiv.Perm (Fin (2 ^ n))) (kInit : ℕ) (probes : List GHMidPProbe) {S : Finset (Fin (2 ^
  n))} (hcard : S.card = k) (hact : active < k) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S
  active μ) (hR_lt : (S \ memSeen n k (memPrefix k active) μ).card < 2 ^ (n - p)) (Θ : CQAssertion
  (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store
    Var) (ν
  : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν → (∀ i : Fin k, i.val <
  active → addrEquiv n k ν i = addrEquiv n k μ i) → ((((S \ memSeen n k (memPrefix k active) μ) \ (S
  \ memSeen n k (memPrefix k s) ν)).image (fun x ↦ subcubePref hp hm (perm x))).card = s - active) →
  (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (Ψ (S \ memSeen n k (memPrefix k s) ν) :
  ℂ)) (τ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ; let pref := fun x ↦ subcubePref hp hm (perm x)
    ((wp ((ghDeflatedRound res hm1 hkN hM hp hm perm active kInit (ghMidPWSpec (k - active)) (fun pr
      ↦ pr.kNext) probes).compile qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n
      m k 0 μ) (workMemIdx n m k 0 μ) = (ghMidPBaseStep (n - p) pref false kInit probes Ψ R : ℂ) :=
      by
  dsimp only; set R := S \ memSeen n k (memPrefix k active) μ
  let pref := fun x ↦ subcubePref hp hm (perm x); have hk1 : 1 ≤ k := (by omega)
  have hseen := card_memSeen_of_memPrefixValid hval; have hμ : μ.val < 2 ^ (k * n - 1) :=
    memPrefixValid_lt_half hn hk1 hval hact; refine (ghQuadForm_single_midp _ (workMemIdx n m k 0
    μ)).symm.trans ?_; have hue := (unitaryEffect_wdPrepAndNoClick_midp (Var := Var) (k := k) hp hm
    perm S active).1 kInit; unfold ghDeflatedRound; dsimp only [compile]; rw [wp_qSeq,
    ghQuadForm_unitaryEffect_midp hue]
  rcases deflatedRead_mulVec_workMemState_midp (m := m) hseen.2 with ⟨hread_mul, _⟩; rw [←
    mulVec_mulVec, ← mulVec_mulVec, ghPrep_grover_eq_ghMidPAmpState hp hm perm hseen.2 hR_lt kInit,
    hread_mul, ghQuadForm_wp_ghProbeChain_midp res hm1 hkN hM hp hm perm hcard hval hμ hR_lt Θ Ψ hΘ
    probes _ τ]; unfold ghMidPBaseStep; simp only [Bool.false_eq_true, ↓reduceIte, zero_add]; rfl
private def ghMidPProbesMaxQ (probes : List GHMidPProbe) : ℕ :=
  (probes.map fun pr ↦ pr.kNext + 2).sum
private lemma scaledCostRel_ghProbeChain_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k
  active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) (probes : List GHMidPProbe) {B : ℝ} (hB : 0 <
  B) (hcB : (ghMidPProbesMaxQ probes : ℝ) ≤ B) :
    let R := fun μ ↦ S \ memSeen n k (memPrefix k active) μ
    let P_R := fun μ ↦ (permutationUnitary (parallelMarkPerm n m (R μ))).1
    let pref := fun x ↦ subcubePref hp hm (perm x)
    ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)), ScaledCostRel
      (CostModel.ofEmbeddedOracle
      (groverParallelMarkingOracle m S)) B ((ghProbeChain res hm1 hkN hM hp perm active (ghMidPWSpec
      (k - active)) (fun pr ↦ pr.kNext) probes).compile qAssign (groverParallelMarkingOracle m S)) θ
      (ghMidPProbesMaxQ probes) ∧ (∀ (μ : Fin (2 ^ (k * n))) (σ : Store Var), 1 ≤ n → S.card = k →
      active < k → MemPrefixValid S active μ → (R μ).card < 2 ^ (n - p) → ∀ coeff : Finset (Fin m) →
      ℂ, ghQuadForm_midp (θ σ).1.1 (workMemState (P_R μ *ᵥ ghMidPAmpState hp hm perm (R μ) coeff)
      (single μ 1)) = ((ghMidPChainExtraQ (n - p) pref (R μ) probes coeff / B : ℝ) : ℂ)) := by
  intro R P_R pref; let W := m * (n + 1); let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  have hor := isRealMatrix_groverParallelMarkingOracle m S; rcases costBounds_ghPieces_midp (Var :=
    Var) res hm1 hkN hM hp hm perm S active with ⟨_, hcb_noclick, hcb_rw, hcb_click⟩
  induction probes with
  | nil =>
    refine ⟨⊥, ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_of_zero_midp hB hcb_rw)
      (by simp [ghMidPProbesMaxQ]) hcB, ?_⟩
    intro μ σ _ _ _ _ _ coeff; dsimp only [ghMidPChainExtraQ, ghMidPProbesMaxQ]
    change ghQuadForm_midp 0 _ = _; rw [ghQuadForm_zero_mat_midp]; simp
  | cons pr rest ih =>
    have hfin2 (f : Fin (2 ^ 1) → ℂ) : (∑ o : Fin (2 ^ 1), f o) = f 0 + f 1 := Fin.sum_univ_two f
    have hc_eq : (ghMidPProbesMaxQ (pr :: rest) : ℝ) = (pr.kNext : ℝ) + 2 + (ghMidPProbesMaxQ rest :
      ℝ) := (by simp [ghMidPProbesMaxQ]); have hc_rest_le : (ghMidPProbesMaxQ rest : ℝ) ≤ B :=
      (by have : (0 : ℝ) ≤ (pr.kNext : ℝ) + 2 := (by positivity); linarith)
    rcases ih hc_rest_le with ⟨θ_rest, hrel_rest, heval_rest⟩; have hcb_step : CostBound (Var :=
      Var) model (.qAssign (phaseTag (gaussianHammingAllHitUnitary n m M hM (ghMidPWSpec (k -
      active) pr)))) 0 := costBound_qAssign_phaseTag (Var := Var) hor _
    have hcb_meas : CostBound (Var := Var) model (measureRegister res (topAncReg W M hM)) 0 := by
      simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using CostBound.qMeasure (Var :=
        Var) model res ((topAncReg W M hM).computationalBasisMeasurement : Measurement (2 ^ (W + M))
        (2 ^ 1))
    have hkNext_le : (((pr.kNext + 2 : ℕ) : ℝ≥0) : ℝ) ≤ B :=
      (by have : (0 : ℝ) ≤ (ghMidPProbesMaxQ rest : ℝ) := Nat.cast_nonneg _; push_cast; linarith)
    have hrel_nc0 := ghScaledCostRel_of_costBound_midp hB (k_cost := (pr.kNext + 2 : ℕ))
      (by simpa [Nat.cast_add] using hcb_noclick pr.kNext) hkNext_le; have hsum_le : (((pr.kNext + 2
      : ℕ) : ℝ≥0) : ℝ) + (ghMidPProbesMaxQ rest : ℝ) ≤ B := (by push_cast; linarith)
    have hrel_false := ghScaledCostRel_seq_midp hB hrel_nc0 hrel_rest hsum_le; have hrel_true :=
      ghScaledCostRel_of_zero_midp hB hcb_click; have hmax_eq : max (0 : ℝ) ((((pr.kNext + 2 : ℕ) :
      ℝ≥0) : ℝ) + (ghMidPProbesMaxQ rest : ℝ)) = (ghMidPProbesMaxQ (pr :: rest) : ℝ) :=
      (by rw [max_eq_right (by positivity)]; push_cast; linarith); have hrel_if :=
      ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_qIf_midp hB (fun τ ↦ τ res = 1) hrel_true
      hrel_false) (le_of_eq hmax_eq) hcB
    have hrel_tot := ghScaledCostRel_seq_zero_left_midp hB hcb_step
      (ghScaledCostRel_seq_zero_left_midp hB hcb_meas hrel_if); refine ⟨_, hrel_tot, fun μ σ hn
      hcard hact hval hR_lt coeff ↦ ?_⟩; have hk1 : 1 ≤ k := (by omega); have hμ : μ.val < 2 ^ (k *
      n - 1) := memPrefixValid_lt_half hn hk1 hval hact; have hseen :=
      card_memSeen_of_memPrefixValid hval; have hadd := Finset.card_sdiff_add_card_eq_card hseen.2
    have hR_eq : (R μ).card = k - active := (by dsimp only [R]; omega); have hw_eq : ghMidPWSpec (k
      - active) pr = ghMidPWSpec (R μ).card pr := (by rw [hR_eq])
    have hstep_vec : (gaussianHammingAllHitUnitary n m M hM (ghMidPWSpec (k - active) pr)).1 *ᵥ
      workMemState (P_R μ *ᵥ ghMidPAmpState hp hm perm (R μ) coeff) (single μ 1) = workMemState
      (ghDampVec n m (ghMidPWSpec (R μ).card pr) (P_R μ *ᵥ ghMidPAmpState hp hm perm (R μ) coeff))
      (single μ 1) + workMemState (ghClickVec n m (ghMidPWSpec (R μ).card pr) (P_R μ *ᵥ
      ghMidPAmpState hp hm perm (R μ) coeff)) (single (memWithTopOne hM μ hμ) 1) :=
      (by rw [hw_eq]; exact gaussianHammingAllHitMat_mulVec_workMemState hM _ _ hμ)
    rw [ghQuadForm_unitaryEffect_midp (unitaryEffect_phaseTag _), hstep_vec,
      ghQuadForm_wp_measureRegister_midp, hfin2]; have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin
      (2 ^ 1)).val)) res ≠ 1 := (by simp [Store.subst]); have hs1 : (Store.subst σ res (Int.ofNat (1
      : Fin (2 ^ 1)).val)) res = 1 := (by simp [Store.subst]); rw [topAncReg_projector_zero_mulVec
      hM _ _ hμ, topAncReg_projector_one_mulVec hM _ _ hμ, ite_eq_right hs0, ite_eq_left hs1,
      ghQuadForm_bot_apply_midp, add_zero]
    rcases ghDamp_and_click_marked_ghMidPAmpState hp hm perm (R μ) pr coeff with ⟨hdamp, _⟩
    rw [hdamp, gh_cqAssertion_add_mat_midp, ghQuadForm_add_mat_midp]; have hdiv0 : 0 ≤ (((pr.kNext +
      2 : ℕ) : ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le; have hdiv1 : (((pr.kNext + 2 : ℕ)
      : ℝ≥0) : ℝ) / B ≤ 1 := (div_le_one hB).mpr hkNext_le
    rw [ghQuadForm_constAssertion_workMemState_midp hdiv0 hdiv1]; set cD := ghMidPDampCoeff (R
      μ).card pr coeff
    have hnorm_damp : (∑ o : Fin (2 ^ W), (normSq ((P_R μ *ᵥ ghMidPAmpState hp hm perm (R μ) cD) o)
      : ℂ)) = ∑ A ∈ ((R μ).image pref).powerset, (normSq (cD A) : ℂ) := by
      dsimp only [P_R]; simp_rw [permUnitary_parallelMarkPerm_mulVec_apply_midp]; rw [Equiv.sum_comp
        (parallelMarkPerm n m (R μ)) (fun w ↦ (normSq (ghMidPAmpState hp hm perm (R μ) cD w) : ℂ))];
        exact sum_normSq_ghMidPAmpState_eq hp hm perm hR_lt cD
    rcases deflatedRead_mulVec_workMemState_midp (m := m) hseen.2 with ⟨hread_mul, hPR_inv⟩
    have hue := (unitaryEffect_wdPrepAndNoClick_midp (Var := Var) (k := k) hp hm perm S active).2
      pr.kNext; rw [hnorm_damp, ghQuadForm_unitaryEffect_midp hue, ← mulVec_mulVec, ← mulVec_mulVec,
      hread_mul, hPR_inv, ghGrover_iter_ghMidPAmpState hp hm perm hseen.2 hR_lt cD pr.kNext, show S
      \ memSeen n k (memPrefix k active) μ = R μ from rfl, show ghMidPSlotRot ((R μ).image pref)
      (fun j ↦ Real.cos (2 * (pr.kNext : ℝ) * ghMidPSlotTheta (n - p) pref (R μ) j)) (fun j ↦
      Real.sin (2 * (pr.kNext : ℝ) * ghMidPSlotTheta (n - p) pref (R μ) j)) cD =
      ghMidPProbeNextCoeff (n - p) pref (R μ) pr coeff from rfl, hread_mul, heval_rest μ _ hn hcard
      hact hval hR_lt]; dsimp only [ghMidPChainExtraQ, cD]; push_cast; ring
private lemma scaledCostRel_ghDeflatedRound_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m
    k active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) (kInit : ℕ) (probes : List
    GHMidPProbe) {B : ℝ} (hB : 0 < B) (hcB : (ghMidPPreMaxQueries kInit probes : ℝ) ≤ B) : ∃ θ :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)), ScaledCostRel (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) B ((ghDeflatedRound res hm1 hkN hM hp hm perm active kInit
    (ghMidPWSpec (k - active)) (fun pr ↦ pr.kNext) probes).compile qAssign
    (groverParallelMarkingOracle m S)) θ (ghMidPPreMaxQueries kInit probes) ∧ (∀ (μ : Fin (2 ^
    (k * n))) (τ : Store Var), 1 ≤ n → S.card = k → active < k → MemPrefixValid S active μ → (S \
    memSeen n k (memPrefix k active) μ).card < 2 ^ (n - p) → (θ τ).1.1 (workMemIdx n m k 0 μ)
    (workMemIdx n m k 0 μ) =
            let R := S \ memSeen n k (memPrefix k active) μ
            let pref := fun x ↦ subcubePref hp hm (perm x)
            let c0 := ghMidPInitCoeff (n - p) pref R kInit
            ((((kInit + 1 : ℕ) : ℝ) + ghMidPChainExtraQ (n - p) pref R probes c0) / B : ℂ)) := by
  have hmax_eq : (ghMidPPreMaxQueries kInit probes : ℝ) = (kInit : ℝ) + 1 + (ghMidPProbesMaxQ probes
    : ℝ) := (by unfold ghMidPPreMaxQueries ghMidPProbesMaxQ; push_cast; ring)
  have hc_probes : (ghMidPProbesMaxQ probes : ℝ) ≤ B :=
    (by have : (0 : ℝ) ≤ (kInit : ℝ) + 1 := (by positivity); linarith)
  have hc_init : (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) ≤ B :=
    (by have : (0 : ℝ) ≤ (ghMidPProbesMaxQ probes : ℝ) := Nat.cast_nonneg _; push_cast; linarith)
  rcases costBounds_ghPieces_midp (Var := Var) res hm1 hkN hM hp hm perm S active with ⟨hcb_prep, _,
    _, _⟩
  rcases scaledCostRel_ghProbeChain_midp (Var := Var) res hm1 hkN hM hp hm perm S probes hB
    hc_probes with ⟨θ_ch, hrel_ch, heval_ch⟩
  have hrel_init := ghScaledCostRel_of_costBound_midp hB (k_cost := (kInit + 1 : ℕ))
    (by simpa [Nat.cast_add] using hcb_prep kInit) hc_init; have hsum_le : (((kInit + 1 : ℕ) : ℝ≥0)
    : ℝ) + (ghMidPProbesMaxQ probes : ℝ) ≤ B := (by push_cast; linarith); have hrel_tot :=
    ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_seq_midp hB hrel_init hrel_ch hsum_le) (le_of_eq
    (by push_cast; linarith)) hcB; refine ⟨_, hrel_tot, fun μ τ hn hcard hact hval hR_lt ↦ ?_⟩
  dsimp only; have hseen := card_memSeen_of_memPrefixValid hval; refine (ghQuadForm_single_midp _
    (workMemIdx n m k 0 μ)).symm.trans ?_; rw [gh_cqAssertion_add_mat_midp, ghQuadForm_add_mat_midp,
    ghQuadForm_single_midp]
  have hdiv0 : 0 ≤ (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le
  have hdiv1 : (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B ≤ 1 := (div_le_one hB).mpr hc_init
  have hconst_diag : ((constAssertion ((((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B) : CQAssertion (Store Var)
    (2 ^ (m
    * (n + 1) + k * n))) τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = ((((kInit + 1 : ℕ) :
    ℝ) / B : ℝ) : ℂ) := by
    rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds _ hdiv0 hdiv1,
      HermitianMat.mat_smul, HermitianMat.mat_one]; simp [Complex.real_smul]
  have hue := (unitaryEffect_wdPrepAndNoClick_midp (Var := Var) (k := k) hp hm perm S active).1
    kInit; rcases deflatedRead_mulVec_workMemState_midp (m := m) hseen.2 with ⟨hread_mul, _⟩
  rw [hconst_diag, ghQuadForm_unitaryEffect_midp hue, ← mulVec_mulVec, ← mulVec_mulVec,
    ghPrep_grover_eq_ghMidPAmpState hp hm perm hseen.2 hR_lt kInit, hread_mul, heval_ch μ τ hn hcard
    hact hval hR_lt]; push_cast; ring
/- ## 3. Multi-Active-Count Middle-`p` Sweeps & `ghMidPMultiSweepPre` QHL / Cost Bridge -/
/-- Single-active-count Gaussian-Hamming middle-`p` deflated + `wt = r - 1` zoom round. -/
noncomputable def ghMidPActiveRound {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ) (spec : GHMidPSpec) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  match spec with
  | none => .skip
  | some (kInit, probes, kZoom) =>
      if 2 ≤ k - active ∧ k - active ≤ 16 ∧ (k - active) - 1 < m then
        .seq
          (ghDeflatedRound res hm1 hkN hM hp hm perm active kInit
            (ghMidPWSpec (k - active)) (fun pr ↦ pr.kNext) probes)
          (.qIf (fun σ ↦ σ res = ((k - 1 : ℕ) : ℤ))
            (ghMidPZoomRound res hm1 hkN hp hm h2p perm active kZoom)
            .skip)
      else .skip
/-- Auxiliary `0.. u` active-count dispatch ladder for one middle-`p` pass. -/
noncomputable def ghMidPPassAux {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHMidPSpec) :
    ℕ → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | 0 =>
      .qIf (fun σ ↦ σ res = ((0 : ℕ) : ℤ))
        (ghMidPActiveRound res hm1 hkN hM hp hm h2p perm 0 (spec_fn (k - 0)))
        .skip
  | u + 1 =>
      .qIf (fun σ ↦ σ res = ((u + 1 : ℕ) : ℤ))
        (ghMidPActiveRound res hm1 hkN hM hp hm h2p perm (u + 1) (spec_fn (k - (u + 1))))
        (ghMidPPassAux res hm1 hkN hM hp hm h2p perm spec_fn u)
/-- One full `0.. k` active-count middle-`p` Collision-Zoom pass. -/
noncomputable def ghMidPOnePass {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHMidPSpec) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  ghMidPPassAux res hm1 hkN hM hp hm h2p perm spec_fn k
/-- Sequential execution of `ghMidPOnePass` across a list of `(perm, spec_fn)` passes. -/
noncomputable def ghMidPSweeps {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)) →
      OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | (perm, spec_fn) :: rest =>
      .seq (ghMidPOnePass res hm1 hkN hM hp hm h2p perm spec_fn)
        (ghMidPSweeps res hm1 hkN hM hp hm h2p rest)
/-- Multi-sweep prefix initializing `res` via computational-basis measurement before
  `ghMidPSweeps`. -/
noncomputable def ghMidPMultiSweepPre {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec))) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (.measure res (QRegister.whole (m * (n + 1) + k * n)))
    (.qIf (fun σ ↦ σ res = 0)
      (ghMidPSweeps res hm1 hkN hM hp hm h2p passes)
      .skip)
/-- Instantiate `passes` along rotated bit-slices `0.. W - 1` at subcube exponent `n - p`. -/
noncomputable def ghMidPPermPasses {n p m W : ℕ}
    (hs : (n - W * p) + W * p = n) (hm : m = 2 ^ p)
    (passes : List GHMidPPassFn) (hW_eq : passes.length = W) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)) :=
  (List.finRange W).map fun i ↦
    (rotatedSliceSwapPerm hs hm (Nat.zero_lt_of_lt i.isLt) i,
      (passes[i.val]'(by rw [hW_eq]; exact i.isLt)) (n - p))
/-- Worst-case oracle query bound of a single `GHMidPSpec` round. -/
def ghMidPRoundMaxQ : GHMidPSpec → ℕ
  | none => 0
  | some (kInit, probes, kZoom) => ghMidPMaxQueries kInit probes kZoom
private lemma ghMidPIsWpTop_measure_midp {Var : Type} [DecidableEq Var] {w Q O : ℕ}
    (x : Var) (r : QRegister w Q) :
    ghMidPIsWpTop (.measure x r : OracleCirc Var Q O) := fun _ ↦ by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  dsimp only [compile]; rw [← HermitianMat.val_eq_coe, wp_measureRegister]
  have hidem (o : Fin (2 ^ w)) :
      r.basisOutcomeProjector o *
          ((⊤ : CQAssertion (Store Var) (2 ^ Q)) (Store.subst σ x (Int.ofNat o.val))).1.1 *
          r.basisOutcomeProjector o =
        r.basisOutcomeProjector o := by
    change r.basisOutcomeProjector o * (1 : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) *
      r.basisOutcomeProjector o = _; rw [Matrix.mul_one,
      QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]; ext z₁ z₂;
      by_cases hz : z₁ = z₂
    · subst hz; by_cases h : r.extractIndex z₁ = o <;> simp [h]
    · simp [hz]
  simp_rw [hidem]; exact r.sum_basisOutcomeProjector
private lemma ghMidPIsWpTop_qIf_midp {Var : Type} [DecidableEq Var] {Q O : ℕ} (b : Store Var → Prop)
  [DecidablePred b] {c₁ c₂ : OracleCirc Var Q O} (h₁ : ghMidPIsWpTop c₁) (h₂ : ghMidPIsWpTop c₂) :
  ghMidPIsWpTop (.qIf b c₁ c₂) := fun oracle ↦ by
  funext σ; dsimp only [compile]; rw [wp_qIf]; dsimp only
  split_ifs <;> simp [h₁ oracle, h₂ oracle]
private lemma ghMidPIsWpTop_ghDeflatedRound_midp {P : Type*} {Var : Type} [DecidableEq Var] (res :
  Var) {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
  (perm : Equiv.Perm (Fin (2 ^ n))) (active kInit : ℕ) (wSpecOf : P → ℕ → GaussPyth × PythPair)
  (stepsOf : P → ℕ) (probes : List P) : ghMidPIsWpTop (ghDeflatedRound (Var := Var) res hm1 hkN hM
  hp hm perm active kInit wSpecOf stepsOf probes) := by
  have hread : ghMidPIsWpTop (deflatedOracle (Var := Var) (n := n) (m := m) (k := k) le_rfl
    (memPrefix k active)) := ghMidPIsWpTop_seq (ghMidPIsWpTop_oracle _) (ghMidPIsWpTop_step _)
  have hloop (t : ℕ) : ghMidPIsWpTop (wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp perm
    active t) := ghMidPIsWpTop_sequence _ fun c hc ↦ by
      rw [List.mem_replicate] at hc; rcases hc with ⟨_, rfl⟩
      exact ghMidPIsWpTop_seq (ghMidPIsWpTop_seq (ghMidPIsWpTop_step _) (ghMidPIsWpTop_seq hread
        (ghMidPIsWpTop_step _))) (ghMidPIsWpTop_step _)
  have hprep : ghMidPIsWpTop (wdPrepAndLoop (Var := Var) (k := k) hp hm perm active kInit) :=
    ghMidPIsWpTop_seq (ghMidPIsWpTop_step _) (ghMidPIsWpTop_seq (hloop kInit) hread)
  have hrw : ghMidPIsWpTop (wdReadoutWrite (Var := Var) (k := k) res hm1 hkN active) :=
    ghMidPIsWpTop_seq (ghMidPIsWpTop_step _) (ghMidPIsWpTop_setCountAndResetWork res _)
  have hclean : ghMidPIsWpTop (wdClickCleanup (Var := Var) (k := k) res hm1 hkN hM active) :=
    ghMidPIsWpTop_seq (ghMidPIsWpTop_step _) hrw
  have hnoclick (t : ℕ) : ghMidPIsWpTop (wdNoClickStep (Var := Var) (k := k) hp perm active t) :=
    ghMidPIsWpTop_seq hread (ghMidPIsWpTop_seq (hloop t) hread)
  have hchain : ∀ l : List P, ghMidPIsWpTop (ghProbeChain (Var := Var) res hm1 hkN hM hp perm active
    wSpecOf stepsOf l) := by
    intro l
    induction l with
    | nil => exact hrw
    | cons pr rest ih =>
      exact ghMidPIsWpTop_seq (ghMidPIsWpTop_step _) (ghMidPIsWpTop_seq (ghMidPIsWpTop_measure_midp
        _ _) (ghMidPIsWpTop_qIf_midp _ hclean (ghMidPIsWpTop_seq (hnoclick (stepsOf pr)) ih)))
  exact ghMidPIsWpTop_seq hprep (hchain probes)
private lemma ghMidPIsWpTop_activeRound_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k :
  ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤
  n) (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ) (spec : GHMidPSpec) : ghMidPIsWpTop
  (ghMidPActiveRound (Var := Var) res hm1 hkN hM hp hm h2p perm active spec) := by
  unfold ghMidPActiveRound
  cases spec with
  | none => exact ghMidPIsWpTop_skip
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩; dsimp only; split_ifs
    · exact ghMidPIsWpTop_seq (ghMidPIsWpTop_ghDeflatedRound_midp res hm1 hkN hM hp hm perm active
        kInit _ _ probes) (ghMidPIsWpTop_qIf_midp _ (ghMidPIsWpTop_zoomRound res hm1 hkN hp hm h2p
        perm active kZoom) ghMidPIsWpTop_skip)
    · exact ghMidPIsWpTop_skip
private lemma ghMidPIsWpTop_passAux_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
  (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
  (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHMidPSpec) (u : ℕ) : ghMidPIsWpTop
  (ghMidPPassAux (Var := Var) res hm1 hkN hM hp hm h2p perm spec_fn u) := by
  induction u with
  | zero =>
    exact ghMidPIsWpTop_qIf_midp _ (ghMidPIsWpTop_activeRound_midp res hm1 hkN hM hp hm h2p perm 0
      _) ghMidPIsWpTop_skip
  | succ v ih =>
    exact ghMidPIsWpTop_qIf_midp _ (ghMidPIsWpTop_activeRound_midp res hm1 hkN hM hp hm h2p perm (v
      + 1) _) ih
private lemma ghMidPIsWpTop_sweeps_midp {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
  (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
  (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec))) : ghMidPIsWpTop (ghMidPSweeps (Var
  := Var) res hm1 hkN hM hp hm h2p passes) := by
  induction passes with
  | nil => exact ghMidPIsWpTop_skip
  | cons ps rest ih =>
    rcases ps with ⟨perm, spec_fn⟩; exact ghMidPIsWpTop_seq
      (ghMidPIsWpTop_passAux_midp res hm1 hkN hM hp hm h2p perm spec_fn k) ih
private lemma wp_ghMidPActiveRound {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hn : 1
  ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤
  n) (hk_sub : k < 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHMidPSpec) {S :
  Finset (Fin (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k *
    n))) (Ψ :
  Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res =
  (s : ℤ) → MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (Ψ (S \
  memSeen n k (memPrefix k s) ν) : ℂ)) {active : ℕ} (hact : active ≤ k) {τ : Store Var} (hτ : τ res
  = (active : ℤ)) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) : ((wp
  ((ghMidPActiveRound res hm1 hkN hM hp hm h2p perm active (spec_fn (k - active))).compile qAssign
  (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
  (ghMidPSubsetStep (n - p) p (fun x ↦ subcubePref hp hm (perm x)) false spec_fn Ψ (S \ memSeen n k
  (memPrefix k active) μ) : ℂ) := by
  set R := S \ memSeen n k (memPrefix k active) μ; let pref := fun x ↦ subcubePref hp hm (perm x)
  have hseen := card_memSeen_of_memPrefixValid hval
  have hadd := Finset.card_sdiff_add_card_eq_card hseen.2; have hR_card : R.card = k - active :=
    (by dsimp only [R]; omega); unfold ghMidPActiveRound ghMidPSubsetStep; rw [hR_card]
  cases spec_fn (k - active) with
  | none => dsimp only [compile, wp]; exact hΘ active τ μ hact hτ hval
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩; dsimp only; by_cases hguard : 2 ≤ k - active ∧ k -
      active ≤ 16 ∧ (k - active) - 1 < m
    · rw [ite_eq_left hguard, ite_eq_left hguard]; dsimp only [compile]; rw [wp_qSeq]
      have hact_lt : active < k := (by omega); have hact_le1 : active ≤ k - 1 := (by omega)
      have hrm : (k - active) - 1 ≤ m := (by omega); have hR_lt : R.card < 2 ^ (n - p) :=
        (by rw [hR_card]; omega)
      let postCirc : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) := .qIf (fun σ ↦ σ res =
        ((k - 1 : ℕ) : ℤ)) (ghMidPZoomRound res hm1 hkN hp hm h2p perm active kZoom) .skip
      have hΘ_post : ∀ (s : ℕ) (τ' : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ' res = (s : ℤ) →
        MemPrefixValid S s ν → (∀ i : Fin k, i.val < active → addrEquiv n k ν i = addrEquiv n k μ i)
        → (((R \ (S \ memSeen n k (memPrefix k s) ν)).image pref).card = s - active) → ((wp
        (postCirc.compile qAssign (groverParallelMarkingOracle m S)) Θ) τ').1.1 (workMemIdx n m k 0
        ν) (workMemIdx n m k 0 ν) = (ghMidPZoomPost ((k - active) - 1) ((n - p) - p) kZoom false
        pref R Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ) := by
        intro s τ' ν hs hτ' hval' hag himg_card; set R' := S \ memSeen n k (memPrefix k s) ν
        have hseen' := card_memSeen_of_memPrefixValid hval'; have hadd' :=
          Finset.card_sdiff_add_card_eq_card hseen'.2; dsimp only [postCirc, compile]; rw [wp_qIf];
          dsimp only; by_cases hs_k1 : s = k - 1
        · subst hs_k1; have hτ'_k1 : τ' res = ((k - 1 : ℕ) : ℤ) := hτ'; have hR'1 : R'.card = 1 :=
            (by dsimp only [R']; omega)
          have hzoom := ghMidP_wp_zoomRound_workMemIdx res hm1 hkN hp hm h2p perm rfl hguard.1 hrm
            kZoom hcard hval' Θ Ψ hΘ τ'; dsimp only at hzoom; rw [ite_eq_left hτ'_k1, hzoom]
          have hraw_eq : midpRawPrefixes hp hm perm active ν = (R \ R').image pref :=
            midpRawPrefixes_eq_image_sdiff hp hm perm hact_le1 hval' hag
          have hraw_card : (midpRawPrefixes hp hm perm active ν).card = (k - 1) - active :=
            (by rw [hraw_eq]; exact himg_card); have hwt_m : (k - 1) - active ≤ m := (by omega)
          have hpad_eq : midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν) =
            (R \ R').image pref := by
            have hsub := subset_midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm
              active ν); have hce := card_midpPadPrefixes (le_of_eq hraw_card) hwt_m
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hce, hraw_card])).symm.trans hraw_eq
          unfold ghMidPZoomPost; rw [ite_eq_left hR'1, midp_sub_sub_eq n p]
          dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, zero_add]; by_cases hne : ((R \
            R').image pref ∩ R'.image pref).Nonempty
          · have hne' : (midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν) ∩
              R'.image pref).Nonempty := (by rwa [hpad_eq]); rw [ite_eq_left hne', ite_eq_left hne]
          · have hne' : ¬ (midpPadPrefixes ((k - 1) - active) (midpRawPrefixes hp hm perm active ν)
              ∩ R'.image pref).Nonempty := (by rwa [hpad_eq]); rw [ite_eq_right hne', ite_eq_right
              hne]
        · have hτ'_ne : τ' res ≠ ((k - 1 : ℕ) : ℤ) := (by rw [hτ']; omega)
          have hR'_ne1 : R'.card ≠ 1 := (by dsimp only [R']; omega)
          rw [ite_eq_right hτ'_ne]; dsimp only [wp]
          rw [hΘ s τ' ν hs hτ' hval']; unfold ghMidPZoomPost; rw [ite_eq_right hR'_ne1]
      have hmain := wp_ghDeflatedRound_midp res hn hm1 hkN hM hp hm perm kInit probes hcard hact_lt
        hval hR_lt (wp (postCirc.compile qAssign (groverParallelMarkingOracle m S)) Θ)
        (ghMidPZoomPost ((k - active) - 1) ((n - p) - p) kZoom false pref R Ψ) hΘ_post τ
      dsimp only [postCirc, compile] at hmain; exact hmain
    · rw [ite_eq_right hguard, ite_eq_right hguard]; dsimp only [compile, wp]
      exact hΘ active τ μ hact hτ hval
private lemma wp_ghMidPPassAux {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hn : 1 ≤ n)
  (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
  (hk_sub : k < 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHMidPSpec) {S :
  Finset (Fin (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k *
    n))) (Ψ :
  Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res =
  (s : ℤ) → MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (Ψ (S \
  memSeen n k (memPrefix k s) ν) : ℂ)) (u : ℕ) (hu : u ≤ k) {active : ℕ} (hact_u : active ≤ u) {τ :
  Store Var} (hτ : τ res = (active : ℤ)) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
  : ((wp ((ghMidPPassAux res hm1 hkN hM hp hm h2p perm spec_fn u).compile qAssign
  (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
  (ghMidPSubsetStep (n - p) p (fun x ↦ subcubePref hp hm (perm x)) false spec_fn Ψ (S \ memSeen n k
  (memPrefix k active) μ) : ℂ) := by
  induction u with
  | zero =>
    have ha0 : active = 0 := Nat.eq_zero_of_le_zero hact_u; subst ha0; dsimp only [ghMidPPassAux,
      compile]; rw [wp_qIf]; dsimp only; rw [ite_eq_left hτ]
    exact wp_ghMidPActiveRound res hn hm1 hkN hM hp hm h2p hk_sub perm spec_fn hcard Θ Ψ hΘ
      (Nat.zero_le k) hτ hval
  | succ v ih =>
    dsimp only [ghMidPPassAux, compile]; rw [wp_qIf]; dsimp only; by_cases ha_eq : active = v + 1
    · subst ha_eq; rw [ite_eq_left hτ]
      exact wp_ghMidPActiveRound res hn hm1 hkN hM hp hm h2p hk_sub perm spec_fn hcard Θ Ψ hΘ hu hτ
        hval
    · have hτ_ne : τ res ≠ ((v + 1 : ℕ) : ℤ) := (by rw [hτ]; omega); rw [ite_eq_right hτ_ne]
      exact ih (by omega) (by omega)
private lemma wp_ghMidPSweeps {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hn : 1 ≤ n)
  (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n)
  (hk_sub : k < 2 ^ (n - p)) (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec))) {S :
  Finset (Fin (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k *
    n))) (Ψ :
  Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res =
  (s : ℤ) → MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (Ψ (S \
  memSeen n k (memPrefix k s) ν) : ℂ)) {active : ℕ} (hact : active ≤ k) {τ : Store Var} (hτ : τ res
  = (active : ℤ)) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) : ((wp ((ghMidPSweeps
  res hm1 hkN hM hp hm h2p passes).compile qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1
  (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (ghMidPCircDP hp hm false passes Ψ (S \ memSeen n
  k (memPrefix k active) μ) : ℂ) := by
  induction passes generalizing active τ μ with
  | nil => exact hΘ active τ μ hact hτ hval
  | cons ps rest ih =>
    rcases ps with ⟨perm, spec_fn⟩; dsimp only [ghMidPSweeps, ghMidPOnePass, ghMidPCircDP, compile];
      rw [wp_qSeq]
    exact wp_ghMidPPassAux res hn hm1 hkN hM hp hm h2p hk_sub perm spec_fn hcard (wp ((ghMidPSweeps
      res hm1 hkN hM hp hm h2p rest).compile qAssign (groverParallelMarkingOracle m S)) Θ)
      (ghMidPCircDP hp hm false rest Ψ) (fun s τ' ν hs hτ' hval' ↦ ih hs hτ' hval') k le_rfl hact hτ
      hval
private lemma wp_qSet_measure_whole_apply_mat_midp {Var : Type} [DecidableEq Var] (res : Var) (Q :
  ℕ) (Φ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) : ((wp (.qSet ;; measureRegister res
  (QRegister.whole Q)) Φ) σ).1.1 = ((Φ (Store.subst σ res 0)).1.1 0 0) • (1 : Operator (2 ^ Q)) :=
  by
  rw [wp_qSeq, wp_qSet, qhlQSet_val, wp_measureRegister]; congr 1
  have hsum : (∑ o : Fin (2 ^ Q), (QRegister.whole Q).basisOutcomeProjector o * (Φ (Store.subst σ
    res (Int.ofNat o.val))).1.1 * (QRegister.whole Q).basisOutcomeProjector o) = ∑ o : Fin (2 ^ Q),
    ((Φ (Store.subst σ res (Int.ofNat o.val))).1.1 o o) • compProj o := by
    refine Finset.sum_congr rfl fun o _ ↦ ?_; rw [QRegister.basisOutcomeProjector,
      QRegister.whole_embedMatrix, compProj_mul_mul]
  rw [hsum, Matrix.sum_apply, sum_eq_single (0 : Fin (2 ^ Q)) (fun o ho ↦
    by simp [compProj_apply, ho.symm])]; simp [compProj_apply]
private lemma wp_qSet_measure_lowBlock_apply_mat_midp {Var : Type} [DecidableEq Var] (res : Var) (W
  M : ℕ) (Φ : CQAssertion (Store Var) (2 ^ (W + M))) (σ : Store Var) : ((wp (.qSet ;;
    measureRegister res
  (lowBlock W M)) Φ) σ).1.1 = ((Φ (Store.subst σ res 0)).1.1 0 0) • (1 : Operator (2 ^ (W + M))) :=
  by
  rw [wp_qSeq, wp_qSet, qhlQSet_val, wp_measureRegister]; congr 1
  refine (diag_eq_star_single_dotProduct_mulVec _ 0).trans ?_; rw [Matrix.sum_mulVec,
    dotProduct_sum]
  have hproj (o : Fin (2 ^ W)) : (lowBlock W M).basisOutcomeProjector o *ᵥ single (0 : Fin (2 ^ (W +
    M))) 1 = if o = 0 then single 0 1 else 0 := by
    rw [QRegister.basisOutcomeProjector, ← workMemState_zero W M,
      embedMatrix_lowBlock_mulVec_workMemState, compProj_mulVec]; by_cases ho : o = 0
    · subst ho; rw [ite_eq_left rfl, Pi.single_eq_same, workMemState_zero]
    · rw [ite_eq_right ho, Pi.single_eq_of_ne ho, Pi.single_zero]; funext z; simp [workMemState]
  rw [sum_eq_single 0 (fun o ho ↦ by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj o, ite_eq_right ho,
      Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero])]
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj 0, ite_eq_left rfl,
    Matrix.dotProduct_mulVec, ← QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.vecMul_conjTranspose, star_star, hproj 0, ite_eq_left rfl]
  refine (diag_eq_star_single_dotProduct_mulVec _ 0).symm.trans ?_; simp [HermitianMat.val_eq_coe]
/-- Exact `wp` scalar identity for `.qSet;; ghMidPMultiSweepPre` under an active-count
  invariant postcondition `Θ`. -/
theorem ghMidP_wp_qSet_multiSweepPre {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hn :
  1 ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p
  ≤ n) (hk_sub : k < 2 ^ (n - p)) (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec))) {S :
  Finset (Fin (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k *
    n))) (f :
  ℕ → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) →
  MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (f s : ℂ)) (σ :
  Store Var) : ((wp (.qSet ;; (ghMidPMultiSweepPre res hm1 hkN hM hp hm h2p passes).compile qAssign
  (groverParallelMarkingOracle m S)) Θ) σ).1.1 = (ghMidPCircDP hp hm false passes (fun R ↦ f (k -
  R.card)) S : ℂ) • (1 : Operator (2 ^ (m * (n + 1) + k * n))) := by
  dsimp only [ghMidPMultiSweepPre, compile]; have hassoc : wp (.qSet ;; (measureRegister res
    (QRegister.whole (m * (n + 1) + k * n)) ;; .qIf (fun σ ↦ σ res = 0) ((ghMidPSweeps res hm1 hkN
    hM hp hm h2p passes).compile qAssign (groverParallelMarkingOracle m S)) .skip)) Θ = wp (.qSet ;;
    measureRegister res (QRegister.whole (m * (n + 1) + k * n))) (wp (.qIf (fun σ ↦ σ res = 0)
    ((ghMidPSweeps res hm1 hkN hM hp hm h2p passes).compile qAssign (groverParallelMarkingOracle m
    S)) .skip) Θ) := (by simp only [wp_qSeq]); have hs0 : (Store.subst σ res 0) res = 0 :=
    (by simp [Store.subst]); have hif0 : wp (.qIf (fun τ ↦ τ res = 0) ((ghMidPSweeps res hm1 hkN hM
    hp hm h2p passes).compile qAssign (groverParallelMarkingOracle m S)) .skip) Θ (Store.subst σ res
    0) = wp ((ghMidPSweeps res hm1 hkN hM hp hm h2p passes).compile qAssign
    (groverParallelMarkingOracle m S)) Θ (Store.subst σ res 0) :=
    (by rw [wp_qIf]; exact ite_eq_left hs0)
  have hΘ_fin : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) →
    MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (f (k - (S \
    memSeen n k (memPrefix k s) ν).card) : ℂ) := by
    intro s τ ν hs hτ hval; have hseen := (card_memSeen_of_memPrefixValid hval).1; have hadd :=
      Finset.card_sdiff_add_card_eq_card (card_memSeen_of_memPrefixValid hval).2; have hsub_eq : k -
      (S \ memSeen n k (memPrefix k s) ν).card = s := (by omega)
    rw [hsub_eq]; exact hΘ s τ ν hs hτ hval
  have hseen0 : memSeen n k (memPrefix k 0) (0 : Fin (2 ^ (k * n))) = ∅ :=
    (by ext x; simp [memSeen, memPrefix]); rw [hassoc, wp_qSet_measure_whole_apply_mat_midp, hif0, ←
    workMemIdx_zero n m k, wp_ghMidPSweeps res hn hm1 hkN hM hp hm h2p hk_sub passes hcard Θ (fun R
    ↦ f (k - R.card)) hΘ_fin (Nat.zero_le k) hs0 (memPrefixValid_zero S), hseen0,
    Finset.sdiff_empty]
/-- Output active-count probability law of `ghMidPMultiSweepPre` on target set `S`. -/
noncomputable def ghMidPOccLaw {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec)))
    (S : Finset (Fin (2 ^ n))) (s : ℕ) : ℝ :=
  ghMidPCircDP hp hm false passes (fun R ↦ if k - R.card = s then 1 else 0) S
/-- Nonnegativity, normalization, and expectation decomposition for `ghMidPOccLaw`. -/
theorem ghMidPOccLaw_props {n p m k : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k *
  n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p : 2 * p ≤ n) (hk_sub : k < 2 ^ (n - p)) (passes : List
  (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHMidPSpec))) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
  (∀ s, 0 ≤ ghMidPOccLaw (k := k) hp hm passes S s) ∧ (∑ s ∈ Finset.range (k + 1), ghMidPOccLaw (k
  := k) hp hm passes S s = 1) ∧ (∀ f : ℕ → ℝ, (∑ s ∈ Finset.range (k + 1), ghMidPOccLaw (k := k) hp
  hm passes S s * f s) = ghMidPCircDP hp hm false passes (fun R ↦ f (k - R.card)) S) := by
  have hnn : ∀ s, 0 ≤ ghMidPOccLaw (k := k) hp hm passes S s := fun s ↦
    ghMidPCircDP_nonneg hp hm false passes fun _ _ ↦ by split_ifs <;> norm_num
  have hexp : ∀ f : ℕ → ℝ, (∑ s ∈ Finset.range (k + 1), ghMidPOccLaw (k := k) hp hm passes S s * f
    s) = ghMidPCircDP hp hm false passes (fun R ↦ f (k - R.card)) S := by
    intro f
    have h_occ_s (s : ℕ) : ghMidPOccLaw (k := k) hp hm passes S s * f s = ghMidPCircDP hp hm false
      passes (fun R ↦ f s * (if k - R.card = s then 1 else 0)) S :=
      (by unfold ghMidPOccLaw; rw [mul_comm, ← ghMidPCircDP_false_mul]); simp_rw [h_occ_s, ←
      ghMidPCircDP_false_sum]
    have hfun : (fun R : Finset (Fin (2 ^ n)) ↦ ∑ x ∈ Finset.range (k + 1), f x * if k - R.card = x
      then 1 else 0) = fun R ↦ f (k - R.card) := by
      funext R; have hmem : k - R.card ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (k - R.card) (fun s _ hne ↦ by rw [ite_eq_right hne.symm, mul_zero])
        (fun hnot ↦ absurd hmem hnot)]; simp
    rw [hfun]
  refine ⟨hnn, ?_, hexp⟩
  rw [show (∑ s ∈ Finset.range (k + 1), ghMidPOccLaw (k := k) hp hm passes S s) =
      ∑ s ∈ Finset.range (k + 1), ghMidPOccLaw (k := k) hp hm passes S s * 1 by simp,
    hexp (fun _ ↦ 1)]
  have htop := ghMidP_wp_qSet_multiSweepPre (Var := Unit) () hn hm1 hkN hM hp hm h2p hk_sub passes
    hcard ⊤ (fun _ ↦ 1) (fun _ _ _ _ _ _ ↦ by simp [HermitianMat.val_eq_coe]) (fun _ ↦ 0)
  have hwp_top : wp (.qSet ;; (ghMidPMultiSweepPre () hm1 hkN hM hp hm h2p passes).compile qAssign
    (groverParallelMarkingOracle m S)) (⊤ : CQAssertion (Store Unit) (2 ^ (m * (n + 1) + k * n))) =
      ⊤ := by
    have hpre_top : ghMidPIsWpTop (ghMidPMultiSweepPre (Var := Unit) () hm1 hkN hM hp hm h2p passes)
      := ghMidPIsWpTop_seq (ghMidPIsWpTop_measure_midp _ _) (ghMidPIsWpTop_qIf_midp _
      (ghMidPIsWpTop_sweeps_midp () hm1 hkN hM hp hm h2p passes) ghMidPIsWpTop_skip); rw [wp_qSeq,
      hpre_top (groverParallelMarkingOracle m S)]; funext σ
    apply Subtype.ext; apply HermitianMat.ext; rw [wp_qSet, ← HermitianMat.val_eq_coe,
      qhlQSet_val]; simp [HermitianMat.val_eq_coe]
  rw [hwp_top] at htop; have h00 := congrFun (congrFun htop 0) 0
  simp only [HermitianMat.val_eq_coe, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
    mul_one] at h00; exact Complex.ofReal_injective h00.symm
private lemma scaledCostRel_ghMidPActiveRound {Var : Type} [DecidableEq Var] (res : Var) {n p m k :
  ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
  (h2p : 2 * p ≤ n) (hk_sub : k < 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ →
  GHMidPSpec) (active : ℕ) (S : Finset (Fin (2 ^ n))) {M_step B : ℝ} (hM_step : 0 ≤ M_step) (hB : 0
  < B) (hcB : M_step ≤ B) (hspec_le : ∀ r ≤ k, (ghMidPRoundMaxQ (spec_fn r) : ℝ) ≤ M_step) : ∃ θ :
  CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)), ScaledCostRel (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle m S)) B ((ghMidPActiveRound res hm1 hkN hM hp hm h2p perm active
  (spec_fn (k - active))).compile qAssign (groverParallelMarkingOracle m S)) θ M_step ∧ (∀ (τ :
  Store Var) (μ : Fin (2 ^ (k * n))), S.card = k → active ≤ k → MemPrefixValid S active μ → (θ
  τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = ((ghMidPSubsetStep (n - p) p (fun x ↦
  subcubePref hp hm (perm x)) true spec_fn (fun _ ↦ 0) (S \ memSeen n k (memPrefix k active) μ) / B
  : ℝ) : ℂ)) := by
  let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hrel_skip : ScaledCostRel model B ((OracleDynamicCircuit.skip : OracleCirc Var (W + M) ((n +
    1) * m)).compile qAssign oracle) ⊥ M_step := ghScaledCostRel_mono_c_midp hB
    (ghScaledCostRel_of_zero_midp hB (CostBound.skip_zero model)) hM_step hcB
  unfold ghMidPActiveRound ghMidPSubsetStep
  cases hsp : spec_fn (k - active) with
  | none =>
    refine ⟨⊥, hrel_skip, fun _ μ hcard _ hval ↦ ?_⟩
    have hseen := card_memSeen_of_memPrefixValid hval; have hadd :=
      Finset.card_sdiff_add_card_eq_card hseen.2; have hR_card : (S \ memSeen n k (memPrefix k
      active) μ).card = k - active := (by omega); rw [hR_card, hsp]; simp [HermitianMat.val_eq_coe]
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩; dsimp only; by_cases hguard : 2 ≤ k - active ∧ k -
      active ≤ 16 ∧ (k - active) - 1 < m
    · rw [ite_eq_left hguard]
      have hmax_le : ((ghMidPMaxQueries kInit probes kZoom : ℕ) : ℝ) ≤ M_step :=
        (by simpa [ghMidPRoundMaxQ, hsp] using hspec_le (k - active) (Nat.sub_le k active))
      let c₁ : ℝ := (ghMidPPreMaxQueries kInit probes : ℝ); let c₂ : ℝ := ((kZoom + 1 : ℕ) : ℝ)
      have hc₁_nn : 0 ≤ c₁ := Nat.cast_nonneg _; have hc₂_nn : 0 ≤ c₂ := Nat.cast_nonneg _
      have hc₁₂_eq : c₁ + c₂ = ((ghMidPMaxQueries kInit probes kZoom : ℕ) : ℝ) :=
        (by dsimp only [c₁, c₂, ghMidPMaxQueries]; push_cast; ring)
      have hc₁₂_M : c₁ + c₂ ≤ M_step := hc₁₂_eq.trans_le hmax_le; have hc₁₂_B : c₁ + c₂ ≤ B :=
        hc₁₂_M.trans hcB; have hc₁_B : c₁ ≤ B := (by linarith); have hc₂_B : c₂ ≤ B := (by linarith)
      rcases scaledCostRel_ghDeflatedRound_midp (Var := Var) res hm1 hkN hM hp hm perm S kInit
        probes hB hc₁_B with ⟨θ₁, hrel₁_0, hdiag₁⟩
      have hrel₁ : ScaledCostRel model B ((ghDeflatedRound res hm1 hkN hM hp hm perm active kInit
        (ghMidPWSpec (k - active)) (fun pr ↦ pr.kNext) probes).compile qAssign oracle) θ₁ c₁ :=
        ghScaledCostRel_mono_c_midp hB hrel₁_0 le_rfl hc₁_B; have hcb_zoom :=
        ghMidP_costBound_zoomRound (Var := Var) res hm1 hkN hp hm h2p perm active kZoom S
      have hrel_zoom : ScaledCostRel model B ((ghMidPZoomRound res hm1 hkN hp hm h2p perm active
        kZoom).compile qAssign oracle) (constAssertion (c₂ / B)) c₂ := by
        simpa [c₂] using ghScaledCostRel_of_costBound_midp hB hcb_zoom (by simpa [c₂] using hc₂_B)
      let postCirc : OracleCirc Var (W + M) ((n + 1) * m) := .qIf (fun σ ↦ σ res = ((k - 1 : ℕ) :
        ℤ)) (ghMidPZoomRound res hm1 hkN hp hm h2p perm active kZoom) .skip
      let θ_post : CQAssertion (Store Var) (2 ^ (W + M)) :=
        fun σ ↦ if σ res = ((k - 1 : ℕ) : ℤ) then constAssertion (c₂ / B) σ else ⊥
      have hrel_post : ScaledCostRel model B (postCirc.compile qAssign oracle) θ_post c₂ :=
        ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_qIf_midp hB (fun σ ↦ σ res = ((k - 1 : ℕ) :
        ℤ)) hrel_zoom (ghScaledCostRel_of_zero_midp hB (CostBound.skip_zero model))) (le_of_eq
        (max_eq_left hc₂_nn)) hc₂_B
      have hrel_then := ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_seq_midp hB hrel₁ hrel_post
        hc₁₂_B) hc₁₂_M hcB; refine ⟨_, hrel_then, fun τ μ hcard _ hval ↦ ?_⟩
      set R := S \ memSeen n k (memPrefix k active) μ
      have hseen := card_memSeen_of_memPrefixValid hval; have hadd :=
        Finset.card_sdiff_add_card_eq_card hseen.2; have hR_card : R.card = k - active :=
        (by dsimp only [R]; omega); have hact_lt : active < k := (by omega)
      have hR_lt : R.card < 2 ^ (n - p) := (by rw [hR_card]; omega); rw [hR_card, hsp]; dsimp only
      rw [ite_eq_left hguard, gh_cqAssertion_add_mat_midp, Matrix.add_apply, hdiag₁ μ τ hn hcard
        hact_lt hval hR_lt]; dsimp only
      have hΘ_post : ∀ (s' : ℕ) (τ' : Store Var) (ν : Fin (2 ^ (k * n))), s' ≤ k → τ' res = (s' : ℤ)
        → MemPrefixValid S s' ν → (∀ i : Fin k, i.val < active → addrEquiv n k ν i = addrEquiv n k μ
        i) → (((R \ (S \ memSeen n k (memPrefix k s') ν)).image pref).card = s' - active) → (θ_post
        τ').1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = ((ghMidPZoomPost ((k - active) - 1)
        ((n - p) - p) kZoom true pref R (fun _ ↦ 0) (S \ memSeen n k (memPrefix k s') ν) / B : ℝ) :
        ℂ) := by
        intro s' τ' ν hs' hτ' hval' _ _; set R' := S \ memSeen n k (memPrefix k s') ν
        have hseen' := card_memSeen_of_memPrefixValid hval'; have hadd' :=
          Finset.card_sdiff_add_card_eq_card hseen'.2; dsimp only [θ_post]
        by_cases hs_k1 : s' = k - 1
        · subst hs_k1; have hτ'_k1 : τ' res = ((k - 1 : ℕ) : ℤ) := hτ'; have hR'1 : R'.card = 1 :=
            (by dsimp only [R']; omega); rw [ite_eq_left hτ'_k1, HermitianMat.val_eq_coe,
            constAssertion_apply_of_bounds (c₂ / B) (div_nonneg hc₂_nn hB.le) ((div_le_one hB).mpr
            hc₂_B)]; unfold ghMidPZoomPost; rw [ite_eq_left hR'1]; dsimp only; rw [ite_eq_left (rfl
            : (true : Bool) = true)]
          split_ifs <;> simp [c₂, Complex.real_smul]
        · have hτ'_ne : τ' res ≠ ((k - 1 : ℕ) : ℤ) := (by rw [hτ']; omega)
          have hR'_ne1 : R'.card ≠ 1 := (by dsimp only [R']; omega); rw [ite_eq_right hτ'_ne];
            unfold ghMidPZoomPost; rw [ite_eq_right hR'_ne1]; simp [HermitianMat.val_eq_coe]
      have hwp_post := wp_ghDeflatedRound_midp res hn hm1 hkN hM hp hm perm kInit probes hcard
        hact_lt hval hR_lt θ_post (fun R' ↦ ghMidPZoomPost ((k - active) - 1) ((n - p) - p) kZoom
        true pref R (fun _ ↦ 0) R' / B) hΘ_post τ; dsimp only at hwp_post; rw [hwp_post]
      have hdiv_step : ghMidPBaseStep (n - p) pref false kInit probes (fun R' ↦ ghMidPZoomPost ((k -
        active) - 1) ((n - p) - p) kZoom true pref R (fun _ ↦ 0) R' / B) R = ghMidPBaseStep (n - p)
        pref false kInit probes (ghMidPZoomPost ((k - active) - 1) ((n - p) - p) kZoom true pref R
        (fun _ ↦ 0)) R / B := by
        simpa [div_eq_inv_mul] using ghMidPBaseStep_false_mul (n - p) pref kInit probes (1 / B)
          (ghMidPZoomPost ((k - active) - 1) ((n - p) - p) kZoom true pref R (fun _ ↦ 0)) R
      have hbase0 : ghMidPBaseStep (n - p) pref true kInit probes (fun _ ↦ 0) R = ((kInit + 1 : ℕ) :
        ℝ) + ghMidPChainExtraQ (n - p) pref R probes (ghMidPInitCoeff (n - p) pref R kInit) :=
        (by unfold ghMidPBaseStep; simp); dsimp only [R, pref] at hdiv_step hbase0 ⊢; rw [hdiv_step,
        ghMidPBaseStep_true_eq_cost_add_false, hbase0]; push_cast; ring
    · rw [ite_eq_right hguard]; refine ⟨⊥, hrel_skip, fun _ μ hcard _ hval ↦ ?_⟩; have hseen :=
        card_memSeen_of_memPrefixValid hval; have hadd := Finset.card_sdiff_add_card_eq_card hseen.2
      have hR_card : (S \ memSeen n k (memPrefix k active) μ).card = k - active := (by omega)
      rw [hR_card, hsp]; dsimp only; rw [ite_eq_right hguard]; simp [HermitianMat.val_eq_coe]
private lemma scaledCostRel_ghMidPPassAux {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
  (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p :
  2 * p ≤ n) (hk_sub : k < 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHMidPSpec)
  (S : Finset (Fin (2 ^ n))) {M_step B : ℝ} (hM_step : 0 ≤ M_step) (hB : 0 < B) (hcB : M_step ≤ B)
  (hspec_le : ∀ r ≤ k, (ghMidPRoundMaxQ (spec_fn r) : ℝ) ≤ M_step) (u : ℕ) (hu : u ≤ k) : ∃ θ :
  CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)), ScaledCostRel (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle m S)) B ((ghMidPPassAux res hm1 hkN hM hp hm h2p perm spec_fn
  u).compile qAssign (groverParallelMarkingOracle m S)) θ M_step ∧ (∀ (s : ℕ) (τ : Store Var) (μ :
  Fin (2 ^ (k * n))), S.card = k → s ≤ u → τ res = (s : ℤ) → MemPrefixValid S s μ → (θ τ).1.1
  (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = ((ghMidPSubsetStep (n - p) p (fun x ↦ subcubePref
  hp hm (perm x)) true spec_fn (fun _ ↦ 0) (S \ memSeen n k (memPrefix k s) μ) / B : ℝ) : ℂ)) := by
  let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  let diagAt (μ : Fin (2 ^ (k * n))) (o : Observable (Fin (2 ^ (W + M)))) : ℂ :=
    o.1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ)
  induction u with
  | zero =>
    rcases scaledCostRel_ghMidPActiveRound (Var := Var) res hn hm1 hkN hM hp hm h2p hk_sub perm
      spec_fn 0 S hM_step hB hcB hspec_le with ⟨θ₀, hrel₀, hdiag₀⟩
    have hrel_skip : ScaledCostRel model B ((OracleDynamicCircuit.skip : OracleCirc Var (W + M) ((n
      + 1) * m)).compile qAssign oracle) ⊥ M_step := ghScaledCostRel_mono_c_midp hB
      (ghScaledCostRel_of_zero_midp hB (CostBound.skip_zero model)) hM_step hcB; have hrel_if :=
      ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_qIf_midp hB (fun σ ↦ σ res = ((0 : ℕ) : ℤ))
      hrel₀ hrel_skip) (le_of_eq (max_self M_step)) hcB; refine ⟨_, hrel_if, fun s τ μ hcard hs0 hτ
      hval ↦ ?_⟩; have hs_eq : s = 0 := Nat.eq_zero_of_le_zero hs0; subst hs_eq; exact (congrArg
      (diagAt μ) (ite_eq_left hτ)).trans (hdiag₀ τ μ hcard (Nat.zero_le k) hval)
  | succ v ih =>
    rcases ih (by omega) with ⟨θ_v, hrel_v, hdiag_v⟩; rcases scaledCostRel_ghMidPActiveRound (Var :=
      Var) res hn hm1 hkN hM hp hm h2p hk_sub perm spec_fn (v + 1) S hM_step hB hcB hspec_le with
      ⟨θ_act, hrel_act, hdiag_act⟩
    have hrel_if := ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_qIf_midp hB (fun σ ↦ σ res = ((v
      + 1 : ℕ) : ℤ)) hrel_act hrel_v) (le_of_eq (max_self M_step)) hcB; refine ⟨_, hrel_if, fun s τ
      μ hcard hsv hτ hval ↦ ?_⟩; by_cases hs_eq : s = v + 1
    · subst hs_eq; exact (congrArg (diagAt μ) (ite_eq_left hτ)).trans (hdiag_act τ μ hcard hu hval)
    · have hτ_ne : τ res ≠ ((v + 1 : ℕ) : ℤ) := (by rw [hτ]; omega); exact (congrArg (diagAt μ)
        (ite_eq_right hτ_ne)).trans (hdiag_v s τ μ hcard (by omega) hτ hval)
private lemma scaledCostRel_ghMidPSweeps {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
  (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (h2p :
  2 * p ≤ n) (hk_sub : k < 2 ^ (n - p)) (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ →
  GHMidPSpec))) (S : Finset (Fin (2 ^ n))) {M_step B : ℝ} (hM_step : 0 ≤ M_step) (hB : 0 < B) (hcB :
  (passes.length : ℝ) * M_step ≤ B) (hspec_le : ∀ ps ∈ passes, ∀ r ≤ k, (ghMidPRoundMaxQ (ps.2 r) :
  ℝ) ≤ M_step) : ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)), ScaledCostRel
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B ((ghMidPSweeps res hm1 hkN hM hp
  hm h2p passes).compile qAssign (groverParallelMarkingOracle m S)) θ ((passes.length : ℝ) * M_step)
  ∧ (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))), S.card = k → s ≤ k → τ res = (s : ℤ) →
  MemPrefixValid S s μ → (θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = ((ghMidPCircDP hp
  hm true passes (fun _ ↦ 0) (S \ memSeen n k (memPrefix k s) μ) / B : ℝ) : ℂ)) := by
  let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  induction passes with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, zero_mul]; refine ⟨⊥, ghScaledCostRel_of_zero_midp hB
      (CostBound.skip_zero model), fun _ _ _ _ _ _ _ ↦ ?_⟩; simp [ghMidPCircDP,
      HermitianMat.val_eq_coe]
  | cons ps rest ih =>
    rcases ps with ⟨perm, spec_fn⟩; have hc_eq : (((perm, spec_fn) :: rest).length : ℝ) * M_step =
        M_step + (rest.length : ℝ) * M_step := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    have hc_rest_B : (rest.length : ℝ) * M_step ≤ B := (by linarith); have hc_head_B : M_step ≤ B :=
      (by have : 0 ≤ (rest.length : ℝ) * M_step := mul_nonneg (Nat.cast_nonneg _) hM_step; linarith)
    rcases ih hc_rest_B (fun q hq r hr ↦ hspec_le q (List.mem_cons_of_mem _ hq) r hr) with ⟨θ_rest,
      hrel_rest, hdiag_rest⟩
    rcases scaledCostRel_ghMidPPassAux (Var := Var) res hn hm1 hkN hM hp hm h2p hk_sub perm spec_fn
      S hM_step hB hc_head_B (hspec_le (perm, spec_fn) List.mem_cons_self) k le_rfl with ⟨θ_sw,
      hrel_sw, hdiag_sw⟩; have hsum_B : M_step + (rest.length : ℝ) * M_step ≤ B := (by linarith)
    have hrel_tot := ghScaledCostRel_mono_c_midp hB (ghScaledCostRel_seq_midp hB hrel_sw hrel_rest
      hsum_B) (le_of_eq hc_eq.symm) hcB; refine ⟨_, hrel_tot, fun s τ μ hcard hs hτ hval ↦ ?_⟩
    rw [gh_cqAssertion_add_mat_midp, Matrix.add_apply, hdiag_sw s τ μ hcard hs hτ hval,
      wp_ghMidPPassAux res hn hm1 hkN hM hp hm h2p hk_sub perm spec_fn hcard θ_rest (fun R' ↦
      ghMidPCircDP hp hm true rest (fun _ ↦ 0) R' / B) (fun s' τ' ν hs' hτ' hval' ↦ hdiag_rest s' τ'
      ν hcard hs' hτ' hval') k le_rfl hs hτ hval]
    have hdiv_step : ghMidPSubsetStep (n - p) p (fun x ↦ subcubePref hp hm (perm x)) false spec_fn
      (fun R' ↦ ghMidPCircDP hp hm true rest (fun _ ↦ 0) R' / B) (S \ memSeen n k (memPrefix k s) μ)
      = ghMidPSubsetStep (n - p) p (fun x ↦ subcubePref hp hm (perm x)) false spec_fn (ghMidPCircDP
      hp hm true rest (fun _ ↦ 0)) (S \ memSeen n k (memPrefix k s) μ) / B := by
      simpa [div_eq_inv_mul] using ghMidPSubsetStep_false_mul (n - p) p (fun x ↦ subcubePref hp hm
        (perm x)) spec_fn (1 / B) (ghMidPCircDP hp hm true rest (fun _ ↦ 0)) (S \ memSeen n k
        (memPrefix k s) μ)
    rw [hdiv_step]; dsimp only [ghMidPCircDP]
    conv_rhs => rw [ghMidPSubsetStep_true_eq_cost_add_false]
    push_cast; ring
/-- Expected oracle query `CostBound` and worst-case `passes.length * M_step` upper bound
  for
  `ghMidPMultiSweepPre`. -/
theorem ghMidP_expectedCost_and_bound_multiSweepPre {Var : Type} [DecidableEq Var] (res : Var) {n p
  m k : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^
  p) (h2p : 2 * p ≤ n) (hk_sub : k < 2 ^ (n - p)) (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ →
  GHMidPSpec))) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {M_step : ℝ} (hM_pos : 0 < M_step)
  (hspec_le : ∀ ps ∈ passes, ∀ r ≤ k, (ghMidPRoundMaxQ (ps.2 r) : ℝ) ≤ M_step) : CostBound (Var :=
  Var) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) ((ghMidPMultiSweepPre res hm1
  hkN hM hp hm h2p passes).compile qAssign (groverParallelMarkingOracle m S)) (Real.toNNReal
  (ghMidPCircDP hp hm true passes (fun _ ↦ 0) S)) ∧ ghMidPCircDP hp hm true passes (fun _ ↦ 0) S ≤
  (passes.length : ℝ) * M_step := by
  let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  let c₀ := ghMidPCircDP hp hm true passes (fun _ ↦ 0) S
  have hc0_nn : 0 ≤ c₀ := ghMidPCircDP_nonneg hp hm true passes fun _ _ ↦ le_rfl
  have hseen0 : memSeen n k (memPrefix k 0) (0 : Fin (2 ^ (k * n))) = ∅ :=
    (by ext x; simp [memSeen, memPrefix])
  have hbnd_top : c₀ ≤ (passes.length : ℝ) * M_step := by
    by_cases hnil : passes = []
    · subst hnil; simp [c₀, ghMidPCircDP]
    · have hlen_pos : 0 < (passes.length : ℝ) := (by exact_mod_cast List.length_pos_iff.mpr hnil)
      set B2 : ℝ := (passes.length : ℝ) * M_step; have hB2 : 0 < B2 := mul_pos hlen_pos hM_pos
      rcases scaledCostRel_ghMidPSweeps (Var := Unit) () hn hm1 hkN hM hp hm h2p hk_sub passes S
        hM_pos.le hB2 le_rfl hspec_le with ⟨θ_sw2, _, hdiag_sw2⟩
      let O : Observable (Fin (2 ^ (W + M))) :=
        wp (.qSet ;; measureRegister () (lowBlock W M)) θ_sw2 (fun _ ↦ 0)
      have hO_mat : O.1.1 = diagonal (fun _ ↦ ((c₀ / B2 : ℝ) : ℂ)) := by
        dsimp only [O, c₀]; rw [wp_qSet_measure_lowBlock_apply_mat_midp, ← workMemIdx_zero n m k,
          hdiag_sw2 0 (Store.subst (fun _ ↦ 0) () 0) 0 hcard (Nat.zero_le k) (by simp [Store.subst])
          (memPrefixValid_zero S), hseen0, Finset.sdiff_empty]; ext z₁ z₂; by_cases hz : z₁ = z₂ <;>
          simp [hz]
      have hbnd := (observable_diag_real_bounds O _ hO_mat 0).2.2
      simp only [Complex.ofReal_re] at hbnd; exact (div_le_one hB2).mp hbnd
  refine ⟨fun Δ ↦ ?_, hbnd_top⟩
  have hmeas_cb : CostBound (Var := Var) model (measureRegister res (QRegister.whole (W + M))) 0
    := by
    simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using CostBound.qMeasure (Var := Var)
      model res ((QRegister.whole (W + M)).computationalBasisMeasurement : Measurement (2 ^ (W + M))
      (2 ^ (W + M)))
  set B1 : ℝ := (passes.length : ℝ) * M_step + 1; have hB1 : 0 < B1 := (by positivity)
  have hc0_B1 : c₀ ≤ B1 := (by dsimp [B1]; linarith)
  have hdiv0 : 0 ≤ c₀ / B1 := div_nonneg hc0_nn hB1.le; have hdiv1 : c₀ / B1 ≤ 1 := (div_le_one
    hB1).mpr hc0_B1
  rcases scaledCostRel_ghMidPSweeps (Var := Var) res hn hm1 hkN hM hp hm h2p hk_sub passes S
    hM_pos.le hB1 (by dsimp [B1]; linarith) hspec_le with ⟨θ_sw1, hrel_sw1, hdiag_sw1⟩
  have hrel_if := ghScaledCostRel_qIf_midp hB1 (fun τ ↦ τ res = 0) hrel_sw1
    (ghScaledCostRel_of_zero_midp hB1 (CostBound.skip_zero model)); have hrel_pre1 :=
    ghScaledCostRel_seq_zero_left_midp hB1 hmeas_cb hrel_if
  let θ_if : CQAssertion (Store Var) (2 ^ (W + M)) :=
    fun σ ↦ if σ res = 0 then θ_sw1 σ else (⊥ : CQAssertion (Store Var) (2 ^ (W + M))) σ
  have hθ_le : wp (measureRegister res (QRegister.whole (W + M))) θ_if ≤ constAssertion (c₀ / B1)
    := by
    intro σ; apply Subtype.coe_le_coe.mp; rw [constAssertion_apply_of_bounds _ hdiv0 hdiv1]
    let p0 : HermitianMat (Fin (2 ^ (W + M))) ℂ := ⟨compProj (0 : Fin (2 ^ (W + M))),
      compProj_isHermitian _⟩; have hp0_mat : p0.mat = compProj (0 : Fin (2 ^ (W + M))) := rfl
    have hθ_eq : ((wp (measureRegister res (QRegister.whole (W + M))) θ_if) σ).1 = (c₀ / B1) • p0
      := by
      apply HermitianMat.ext; rw [← HermitianMat.val_eq_coe, wp_measureRegister,
        HermitianMat.mat_smul, hp0_mat]
      have hsum : (∑ o : Fin (2 ^ (W + M)), (QRegister.whole (W + M)).basisOutcomeProjector o *
        (θ_if (Store.subst σ res (Int.ofNat o.val))).1.1 * (QRegister.whole (W +
        M)).basisOutcomeProjector o) = ((c₀ / B1 : ℝ) : ℂ) • compProj (0 : Fin (2 ^ (W + M))) := by
        rw [sum_eq_single (0 : Fin (2 ^ (W + M))) (fun o ho ↦ by
          have hv : (o.val : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.val_ne_of_ne ho)
          have ho_ne : (Store.subst σ res (Int.ofNat o.val)) res ≠ 0 :=
            (by simpa [Store.subst] using hv)
          dsimp only [θ_if]; rw [ite_eq_right ho_ne]; change _ * 0 * _ = 0
          simp)]
        have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ (W + M))).val)) res = 0 :=
          (by simp [Store.subst]); dsimp only [θ_if]; rw [ite_eq_left hs0,
          QRegister.basisOutcomeProjector, QRegister.whole_embedMatrix, compProj_mul_mul]
        have h0_eq : Store.subst σ res (Int.ofNat (0 : Fin (2 ^ (W + M))).val) = Store.subst σ res 0
          := rfl; rw [h0_eq, ← workMemIdx_zero n m k, hdiag_sw1 0 (Store.subst σ res 0) 0 hcard
          (Nat.zero_le k) (by simp [Store.subst]) (memPrefixValid_zero S), hseen0,
          Finset.sdiff_empty]
      rw [hsum]; ext i j; simp [Complex.real_smul]
    rw [hθ_eq]; have hp0_le : p0 ≤ 1 := compProj_le_one 0
    exact smul_le_smul_of_nonneg_left hp0_le hdiv0
  refine (hrel_pre1.2.2.2 Δ).trans ?_
  have hexp_le : 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if] ≤ (c₀ / B1) * Δ.trace
    := by
    calc 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if]
        ≤ 𝔼[Δ, constAssertion (c₀ / B1)] := expect_mono le_rfl hθ_le
      _ = (c₀ / B1) * Δ.trace := gh_expect_constAssertion_midp Δ hdiv0 hdiv1
  have hmul_le : B1 * 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if] ≤ Δ.trace * c₀
    := by
    calc B1 * 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if]
        ≤ B1 * ((c₀ / B1) * Δ.trace) := mul_le_mul_of_nonneg_left hexp_le hB1.le
      _ = Δ.trace * c₀ := by rw [← mul_assoc, mul_div_cancel₀ _ hB1.ne', mul_comm]
  refine (ENNReal.ofReal_le_ofReal hmul_le).trans ?_; rw [ENNReal.ofReal_mul Δ.trace.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ← Real.coe_toNNReal c₀ hc0_nn, ENNReal.ofReal_coe_nnreal]
end
end QuantumComputation.Specs.DickeSol
end GHMidPZoomDeflatedQHL
