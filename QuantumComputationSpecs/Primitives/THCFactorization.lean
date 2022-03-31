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

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.Registers.Embed

/-!
# Tensor Hypercontraction (THC) Block-Encoding Specification

Given a rank-`M` THC factorization of an `N`-spatial-orbital electronic Hamiltonian (`2 * N`
Jordan–Wigner qubits; Lee et al. use `N` for spin orbitals), block-encode
$$H_{\text{THC}} = \sum_{\sigma,p,q} h'_{pq} a_{p,\sigma}^\dagger a_{q,\sigma} +
  \frac{1}{2} \sum_{\sigma,\tau} \sum_{\mu,\nu} \zeta_{\mu\nu}
  \tilde{n}_{\mu,\sigma} \tilde{n}_{\nu,\tau}$$
up to an energy offset, agreeing with $H_{\text{THC}}$ on the `η`-electron sector within `εSynth`
(`thc_correctness`).

As in Lee et al. (2021), the THC data are already rounded to the `aleph`-bit state-preparation and
`beth`-bit rotation grids of their circuit (`THCFactorization.IsRounded`), so rounding counts as
classical factorization error, and the block encoding may use a phase-gradient register that it
returns intact (`RealizesCatalyticSubroutine`).

The cost target `thc_t_cost` bounds the total `T` count
$\lceil \pi \alpha / (2 \varepsilon_{\text{QPE}}) \rceil \cdot C_{\text{step}}$ of qubitized phase
estimation to accuracy `εQPE` by the claimed `thcTCost`, for all sizes, bit sizes, 1-norms and
tolerances, over Clifford + `T` with measurements; the logical-qubit count is the candidate's
`thcTotalLogicalQubits`. `TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T`
construction, such as `4` `T` gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87,
022328 (2013)). How `T` gates and qubits are traded off when ranking candidates is up to whoever
evaluates the spec. The docstring of `thcTCost` gives Lee et al.'s FeMoco numbers as a worked
example.

References: Lee et al., PRX Quantum 2, 030305 (2021); von Burg et al., Phys. Rev. Res. 3, 033055
(2021); Berry et al., Quantum 3, 208 (2019).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator Matrix Circuit
open scoped Matrix Real

/-!
## Part 1: Jordan–Wigner Operators, Electron Sector, Block Encodings & Catalysts
-/

/-- Jordan–Wigner annihilation operator $a_j = Z_0 \cdots Z_{j-1} (|0\rangle\langle 1|)_j$ on `k`
wires. -/
noncomputable def jwAnnihilate (k : ℕ) (j : Fin k) : Operator (2 ^ k) :=
  Matrix.diagonal (fun i ↦ (-1 : ℂ) ^ ∑ q ∈ Finset.univ.filter (· < j), (basisBits k i q).val) *
    (QRegister.singleton j).embedMatrix (Matrix.single (0 : Fin 2) (1 : Fin 2) 1)

/-- Spin-orbital wire `2 * p + σ` of spatial orbital `p` with spin `σ`. -/
def spinOrbital (N : ℕ) (p : Fin N) (σ : Fin 2) : Fin (2 * N) :=
  ⟨2 * p.val + σ.val, by omega⟩

/-- Number operator $\tilde{n}_{\chi,\sigma} = b_{\chi,\sigma}^\dagger b_{\chi,\sigma}$ of the
spatial orbital with real coefficients `χ`, where $b_{\chi,\sigma} = \sum_p \chi_p a_{p,\sigma}$. -/
noncomputable def orbitalNumberOp (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) : Operator (2 ^ (2 * N)) :=
  let b := ∑ p : Fin N, (χ p : ℂ) • jwAnnihilate (2 * N) (spinOrbital N p σ)
  bᴴ * b

/-- Projector onto the `η`-electron sector of `k` spin-orbital wires (basis states of Hamming
weight `η`). -/
noncomputable def electronSectorProjector (k η : ℕ) : Operator (2 ^ k) :=
  Matrix.diagonal fun i ↦ if ∑ q, (basisBits k i q).val = η then 1 else 0

open scoped Matrix.Norms.L2Operator in
/-- `A` preserves the `η`-electron sector and agrees with `B` there to spectral norm `ε`. This
admits symmetry-shifted factorizations, which change the Hamiltonian only outside that sector. -/
def AgreesOnElectronSector (N η : ℕ) (A B : Operator (2 ^ (2 * N))) (ε : ℝ) : Prop :=
  let P := electronSectorProjector (2 * N) η
  A * P = P * A ∧ ‖P * (A - B) * P‖ ≤ ε

/-- `U` is a self-inverse `(α, m)`-block-encoding of `A`: `Uᴴ = U`, so a qubitization walk step
$(2|0^m\rangle\langle 0^m| - I) U$ uses one query to `U`, and
$(\langle 0^m| \otimes I) U (|0^m\rangle \otimes I) = A / \alpha$. -/
def IsQubitizedBlockEncodingUnitary {k m : ℕ} (α : ℝ) (A : Operator (2 ^ k))
    (U : Unitary (2 ^ (k + m))) : Prop :=
  let P := (QRegister.block k m le_rfl : QRegister m (k + m)).basisOutcomeProjector 0
  let sysA := (QRegister.block 0 k (by omega) : QRegister k (k + m)).embedMatrix A
  0 < α ∧ U.1ᴴ = U.1 ∧ P * U.1 * P = (α : ℂ)⁻¹ • (P * sysA * P)

/-- Phase-gradient state $2^{-b/2} \sum_k e^{-2\pi i k / 2^b} |k\rangle$ on `b` qubits. Adding `j`
into it applies the phase $e^{2\pi i j / 2^b}$ and leaves the state intact, so it is a reusable
catalyst for rotations (Lee et al. 2021, Sec. III.C). -/
noncomputable def phaseGradientState (b : ℕ) : Fin (2 ^ b) → ℂ :=
  fun k ↦ (√(2 ^ b) : ℂ)⁻¹ * Complex.exp (-(2 * π * Complex.I * k.val) / 2 ^ b)

/-- `P` realizes `U` on `rTarget` with clean scratch `rScratch` and a catalyst `rCat` in the
phase-gradient state $|\phi_b\rangle$, which is restored:
$P (|\psi\rangle |0\rangle |\phi_b\rangle) = (U |\psi\rangle) |0\rangle |\phi_b\rangle$. Stated
as `RealizesCleanSubroutine` for $V^{-1} P V$, for any (uncounted) `V` preparing
$|\phi_b\rangle$ from $|0\rangle$. -/
def RealizesCatalyticSubroutine {Var : Type} [DecidableEq Var] {n k m b : ℕ}
    (rTarget : QRegister k n) (rScratch : QRegister m n) (rCat : QRegister b n)
    (hsc : rScratch.DisjointWires rCat) (hdisj : rTarget.DisjointWires (rScratch.concat rCat hsc))
    (U : Unitary (2 ^ k)) (P : QProg Var (2 ^ n)) : Prop :=
  ∀ V : Unitary (2 ^ b), (∀ i, V.1 i 0 = phaseGradientState b i) →
    RealizesCleanSubroutine rTarget (rScratch.concat rCat hsc) hdisj U
      (.qSeq (.qAssign (rCat.embedUnitary V)) (.qSeq P (.qAssign (rCat.embedUnitary V⁻¹))))

/-!
## Part 2: THC Factorization & Rounded Input
-/

/-- Rank-`M` Tensor Hypercontraction (THC) factorization of an `N`-spatial-orbital electronic
Hamiltonian: modified one-body matrix $h'_{pq}$ (intended to include the normal-ordering shift
$h_{pq} - \frac{1}{2}\sum_r V_{prrq}$), normalized leaf vectors $\chi^\mu$, and symmetric core
matrix $\zeta_{\mu\nu}$. -/
structure THCFactorization (N M : ℕ) where
  /-- Modified symmetric one-body matrix $h'_{pq}$. -/
  h1eMod : Matrix (Fin N) (Fin N) ℝ
  /-- Symmetry of $h'_{pq}$. -/
  h1eMod_symm : h1eMod.IsSymm
  /-- Leaf vectors $\chi^\mu \in \mathbb{R}^N$. -/
  chi : Fin M → Fin N → ℝ
  /-- Each leaf vector is normalized, so $\tilde{n}_{\mu,\sigma}$ has spectrum $\{0, 1\}$. -/
  chi_norm : ∀ μ, ∑ p, chi μ p ^ 2 = 1
  /-- Core matrix $\zeta_{\mu\nu}$. -/
  zeta : Matrix (Fin M) (Fin M) ℝ
  /-- Symmetry of $\zeta_{\mu\nu}$. -/
  zeta_symm : zeta.IsSymm

/-- One-body term $\sum_{\sigma,p,q} h_{pq} a_{p,\sigma}^\dagger a_{q,\sigma}$. -/
noncomputable def oneBodyHamiltonian {N : ℕ} (h : Matrix (Fin N) (Fin N) ℝ) :
    Operator (2 ^ (2 * N)) :=
  ∑ σ : Fin 2, ∑ p : Fin N, ∑ q : Fin N, (h p q : ℂ) •
    ((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ * jwAnnihilate (2 * N) (spinOrbital N q σ))

/-- THC Hamiltonian
$H_{\text{THC}} = \sum_{\sigma,p,q} h'_{pq} a_{p,\sigma}^\dagger a_{q,\sigma} +
\frac{1}{2} \sum_{\sigma,\tau} \sum_{\mu,\nu} \zeta_{\mu\nu}
\tilde{n}_{\mu,\sigma} \tilde{n}_{\nu,\tau}$
with $\tilde{n}_{\mu,\sigma} = \tilde{n}_{\chi^\mu,\sigma}$. -/
noncomputable def thcHamiltonian {N M : ℕ} (thc : THCFactorization N M) :
    Operator (2 ^ (2 * N)) :=
  oneBodyHamiltonian thc.h1eMod +
    (2 : ℂ)⁻¹ • ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin M, ∑ ν : Fin M,
      (thc.zeta μ ν : ℂ) • (orbitalNumberOp N (thc.chi μ) σ * orbitalNumberOp N (thc.chi ν) τ)

/-- Shifted one-body matrix
$T'_{pq} = h'_{pq} + \sum_{\mu,\nu} \zeta_{\mu\nu} \chi_p^\mu \chi_q^\mu$
obtained by centering $\tilde{n}_{\mu,\sigma}$ around $\frac{1}{2} I$ (Lee et al. 2021,
Eqs. 11–18). -/
noncomputable def thcShiftedOneBody {N M : ℕ} (thc : THCFactorization N M) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun p q ↦ thc.h1eMod p q + ∑ μ : Fin M, ∑ ν : Fin M, thc.zeta μ ν * thc.chi μ p * thc.chi μ q

/-- Unit vector reached from $e_0$ by Givens rotations in the planes $(p, p + 1)$, $p < N - 1$,
with angles on the `b`-bit grid $\theta_p = 2\pi k_p / 2^b$ of Lee et al. (2021), Eq. 50: entry
`p` is $(\prod_{q<p} \sin 2\theta_q) \cos 2\theta_p$, their Eq. 49 with $\theta_{N-1} = 0$. -/
noncomputable def givensLeaf {N : ℕ} (b : ℕ) (k : Fin N → ℤ) : Fin N → ℝ :=
  let θ := fun p ↦ 2 * π * k p / 2 ^ b
  fun p ↦ (∏ q ∈ Finset.univ.filter (· < p), Real.sin (2 * θ q)) *
    if p.val + 1 = N then 1 else Real.cos (2 * θ p)

open Real in
/-- A `givensLeaf` is a unit vector. -/
theorem givensLeaf_sum_sq {N : ℕ} [NeZero N] (b : ℕ) (k : Fin N → ℤ) :
    ∑ p, givensLeaf b k p ^ 2 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne N)).symm⟩
  let φ : ℕ → ℝ := fun q ↦ if h : q < n + 1 then 2 * (2 * π * k ⟨q, h⟩ / 2 ^ b) else 0
  let S : ℕ → ℝ := fun p ↦ ∏ q ∈ Finset.range p, sin (φ q)
  have hmap (p : Fin (n + 1)) :
      (Finset.univ.filter (· < p)).map Fin.valEmbedding = Finset.range p.val := by
    rw [Finset.filter_gt_eq_Iio, Fin.map_valEmbedding_Iio, Nat.Iio_eq_range]
  have hleaf : ∀ p : Fin (n + 1), givensLeaf b k p =
      S p * if p.val + 1 = n + 1 then 1 else Real.cos (φ p) := by
    intro p
    have hprod : ∏ q ∈ Finset.univ.filter (· < p), sin (2 * (2 * π * k q / 2 ^ b)) =
        S p := by
      simp only [S, ← hmap p, Finset.prod_map, Fin.valEmbedding_apply, φ, Fin.is_lt,
        ↓reduceDIte, Fin.eta]
    simp only [givensLeaf, hprod, φ, p.is_lt, ↓reduceDIte, Fin.eta]
  have hsum : ∑ p : Fin (n + 1), givensLeaf b k p ^ 2 =
      ∑ p ∈ Finset.range (n + 1), (S p * if p + 1 = n + 1 then 1 else Real.cos (φ p)) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun p _ ↦ by rw [hleaf p]
  rw [hsum, Finset.sum_range_succ]
  simp only [↓reduceIte, mul_one]
  have htel : ∀ p ∈ Finset.range n,
      (S p * if p + 1 = n + 1 then 1 else Real.cos (φ p)) ^ 2 = S p ^ 2 - S (p + 1) ^ 2 := by
    intro p hp
    have hne : p + 1 ≠ n + 1 := by
      have := Finset.mem_range.mp hp
      omega
    simp only [hne, ↓reduceIte, S, Finset.prod_range_succ]
    linear_combination (∏ q ∈ Finset.range p, sin (φ q)) ^ 2 * Real.sin_sq_add_cos_sq (φ p)
  rw [Finset.sum_congr rfl htel, Finset.sum_range_sub']
  simp [S]

/-- `thc` is rounded to the grids of the circuit of Lee et al. (2021, Secs. III.B–C), which then
implements `thcHamiltonian thc` exactly, with LCU 1-norm at most `lam`. Each leaf $\chi^\mu$, and
each leaf $u_\ell$ of the rounded eigendecomposition $T' = \sum_\ell t_\ell u_\ell u_\ell^T$ of
`thcShiftedOneBody thc`, is a `givensLeaf beth`. The alias-sampling weights $|t_\ell|$,
$|\zeta_{\mu\nu}|$ ($\mu < \nu$) and $|\zeta_{\mu\mu}| / 2$ are multiples of
$\lambda / (d \cdot 2^{\aleph})$, where $d = N + M(M+1)/2$ and
$\lambda = \sum_\ell |t_\ell| + \frac{1}{2} \sum_{\mu,\nu} |\zeta_{\mu\nu}| \le$ `lam`. For
orthonormal $u_\ell$, $\lambda$ is $\lambda_{\text{THC}}$ of Lee et al. (2021), Eq. 20. -/
def THCFactorization.IsRounded {N M : ℕ} (thc : THCFactorization N M) (aleph beth : ℕ)
    (lam : ℝ) : Prop :=
  (∀ μ, ∃ k, thc.chi μ = givensLeaf beth k) ∧
  ∃ (t : Fin N → ℝ) (k : Fin N → Fin N → ℤ),
    let u := fun ℓ ↦ givensLeaf beth (k ℓ)
    let lamRep := ∑ ℓ, |t ℓ| + 2⁻¹ * ∑ μ, ∑ ν, |thc.zeta μ ν|
    let q := lamRep / (((N + M * (M + 1) / 2 : ℕ) : ℝ) * 2 ^ aleph)
    thcShiftedOneBody thc = ∑ ℓ, t ℓ • vecMulVec (u ℓ) (u ℓ) ∧ lamRep ≤ lam ∧
      (∀ ℓ, ∃ j : ℕ, |t ℓ| = j * q) ∧ (∀ μ ν, μ < ν → ∃ j : ℕ, |thc.zeta μ ν| = j * q) ∧
      ∀ μ, ∃ j : ℕ, |thc.zeta μ μ| = 2 * j * q

/-!
## Part 3: Qubitized Phase Estimation Walk Steps
-/

/-- Number of qubitization walk queries $\lceil \pi \alpha / (2 \varepsilon_{\text{QPE}}) \rceil$
for Heisenberg-limited phase estimation at subnormalization `α` and energy accuracy `εQPE`. -/
noncomputable def qpeWalkSteps (α εQPE : ℝ) : ℕ :=
  Nat.ceil ((π * α) / (2 * εQPE))

/-!
## Part 4: Parameterized THC Block-Encoding Subroutine
-/

/-- By default we allow only a single variable. -/
inductive THCFactorization.Var where | v deriving DecidableEq, Inhabited

open THCFactorization (Var)
open THCFactorization.Var (v)

/-- Number of block-encoding ancilla qubits used by `thcCandidateProgram`. -/
def thcBlockAncillas (N M aleph beth : ℕ) (lamMax εSynth : ℝ) : ℕ := sorry

/-- Number of clean scratch ancilla qubits (e.g. for QROM outputs and adders), returned to `|0⟩`
at the end of each step, used by `thcCandidateProgram`. -/
def thcScratchAncillas (N M aleph beth : ℕ) (lamMax εSynth : ℝ) : ℕ := sorry

/-- Number of qubits `b` of the phase-gradient catalyst used by `thcCandidateProgram`. -/
def thcCatalystQubits (N M aleph beth : ℕ) (lamMax εSynth : ℝ) : ℕ := sorry

/-- Total logical qubits $2N + m_{\text{block}} + m_{\text{scratch}} + b$ of `thcCandidateProgram`.
Unlike Lee et al. (2021), Table III, this excludes the phase-estimation control register. -/
abbrev thcTotalLogicalQubits (N M aleph beth : ℕ) (lamMax εSynth : ℝ) : ℕ :=
  2 * N + thcBlockAncillas N M aleph beth lamMax εSynth +
    thcScratchAncillas N M aleph beth lamMax εSynth + thcCatalystQubits N M aleph beth lamMax εSynth

/-- Claimed subnormalization $\alpha$ of the block-encoding built by `thcCandidateProgram`. -/
noncomputable def thcCandidateAlpha {N M : ℕ} (thc : THCFactorization N M)
    (η aleph beth : ℕ) (lamMax εSynth : ℝ) : ℝ := sorry

/-- Claimed energy offset $c$ of the block-encoding built by `thcCandidateProgram`. -/
noncomputable def thcCandidateOffset {N M : ℕ} (thc : THCFactorization N M)
    (η aleph beth : ℕ) (lamMax εSynth : ℝ) : ℝ := sorry

/-- Candidate circuit for the self-inverse block-encoding unitary of `thc` on the active register
`rActive` (`2 * N` system qubits followed by the block-encoding ancillas), using clean scratch
ancillas `rScratch` and the phase-gradient catalyst `rCat`. -/
def thcCandidateProgram {N M n : ℕ} (thc : THCFactorization N M)
    (η aleph beth : ℕ) (lamMax εSynth : ℝ)
    (rActive : QRegister (2 * N + thcBlockAncillas N M aleph beth lamMax εSynth) n)
    (rScratch : QRegister (thcScratchAncillas N M aleph beth lamMax εSynth) n)
    (rCat : QRegister (thcCatalystQubits N M aleph beth lamMax εSynth) n) :
    DynamicCircuit Var n := sorry

/-- For any THC factorization rounded to `aleph`/`beth` bits with LCU 1-norm at most `lamMax`,
and `η ≤ 2 * N`, `thcCandidateProgram` realizes, with clean scratch and a restored phase-gradient
catalyst, a self-inverse unitary `U` block-encoding `(Heff - c • 1) / α`, with `α` and `c` given
by `thcCandidateAlpha` and `thcCandidateOffset`, where `Heff` preserves and agrees with
`thcHamiltonian thc` on the `η`-electron sector within `εSynth`. -/
theorem thc_correctness
    {N M : ℕ} (thc : THCFactorization N M) (η aleph beth : ℕ) (lamMax εSynth : ℝ)
    (hround : thc.IsRounded aleph beth lamMax) (hη : η ≤ 2 * N) (hεSynth : 0 < εSynth) :
    ∃ (U : Unitary (2 ^ (2 * N + thcBlockAncillas N M aleph beth lamMax εSynth)))
      (Heff : Operator (2 ^ (2 * N))),
      IsQubitizedBlockEncodingUnitary
        (thcCandidateAlpha thc η aleph beth lamMax εSynth)
        (Heff - (thcCandidateOffset thc η aleph beth lamMax εSynth : ℂ) •
          (1 : Operator (2 ^ (2 * N)))) U ∧
      AgreesOnElectronSector N η Heff (thcHamiltonian thc) εSynth ∧
      ∀ {n : ℕ}
        (rActive : QRegister (2 * N + thcBlockAncillas N M aleph beth lamMax εSynth) n)
        (rScratch : QRegister (thcScratchAncillas N M aleph beth lamMax εSynth) n)
        (rCat : QRegister (thcCatalystQubits N M aleph beth lamMax εSynth) n)
        (hsc : rScratch.DisjointWires rCat)
        (hdisj : rActive.DisjointWires (rScratch.concat rCat hsc)),
        RealizesCatalyticSubroutine rActive rScratch rCat hsc hdisj U
          (thcCandidateProgram thc η aleph beth lamMax εSynth rActive rScratch rCat).compile := by
  sorry

/-!
## Part 5: `T`-Count Cost Target
-/

/-- Claimed total `T` count of qubitized phase estimation to accuracy `εQPE` with
`thcCandidateProgram`, for `η` electrons and rank-`M` THC factorizations of `N` spatial orbitals
rounded to `aleph`/`beth` bits with LCU 1-norm at most `lamMax`, at synthesis tolerance `εSynth`.

Worked example (Lee et al. 2021, Table III, with `εQPE = 1e-3` Ha from their Eq. 25): their THC
circuit uses `5.3e9` Toffolis, i.e. `2.12e10` `T` gates at `4` `T` gates per Toffoli, and `2142`
logical qubits for the Reiher et al. FeMoco active space (`N = 54`, `η = 54`) with `M = 350`,
`aleph = 10`, `beth = 16` and `lamMax = 306.3` Ha, and `3.2e10` Toffolis (`1.28e11` `T` gates) and
`2196` qubits for the Li et al. one (`N = 76`, `η = 113`) with `M = 450`, `aleph = 10`,
`beth = 20` and `lamMax = 1201.5` Ha. Their qubit counts include the phase-estimation control
register, which `thcTotalLogicalQubits` excludes. -/
noncomputable def thcTCost (N M η aleph beth : ℕ) (lamMax εSynth εQPE : ℝ) : ℕ := sorry

/-- On every rank-`M` THC factorization rounded to `aleph`/`beth` bits with LCU 1-norm at most
`lamMax`, `thcCandidateProgram` uses no `TOFF` gates, and its `T` count over the `qpeWalkSteps`
walk steps of phase estimation to accuracy `εQPE` is at most `thcTCost`. -/
theorem thc_t_cost
    {N M : ℕ} (thc : THCFactorization N M) (η aleph beth : ℕ) (lamMax εSynth εQPE : ℝ)
    (hround : thc.IsRounded aleph beth lamMax) {n : ℕ}
    (rActive : QRegister (2 * N + thcBlockAncillas N M aleph beth lamMax εSynth) n)
    (rScratch : QRegister (thcScratchAncillas N M aleph beth lamMax εSynth) n)
    (rCat : QRegister (thcCatalystQubits N M aleph beth lamMax εSynth) n) :
    let P := thcCandidateProgram thc η aleph beth lamMax εSynth rActive rScratch rCat
    P.count PrimitiveGate.TOFF = 0 ∧
      qpeWalkSteps (thcCandidateAlpha thc η aleph beth lamMax εSynth) εQPE *
        P.count PrimitiveGate.T ≤ thcTCost N M η aleph beth lamMax εSynth εQPE := by
  sorry

end QuantumComputation.Specs
