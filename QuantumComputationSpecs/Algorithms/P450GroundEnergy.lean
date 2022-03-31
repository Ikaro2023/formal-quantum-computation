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

/-!
# Ground-State Energy of Cytochrome P450 Compound I

Specification of estimating the ground-state energy of compound I of cytochrome P450 to
`ε = 1` mHa, together with every other energy within `Δ = 0.1` Ha of it, for the rounded DFTHC
Hamiltonian `P450.dfthc` of Low et al. (Phys. Rev. X 2025) of active space `X` of Goings et al.
(PNAS 2022): `63` electrons in `58` spatial orbitals, i.e. `116` Jordan–Wigner qubits.
Energies are eigenvalues of `thcHamiltonian dfthc`. Its factorization error (about `0.28` mHa in
CCSD(T); Low et al., Table V) is a property of the instance and is not part of `ε`.

* `p450GroundEnergy_correctness`: the program, started with clean ancillas, realizes a unitary
  whose phase register, measured and decoded by `p450GroundEnergyDecoder`, gives the energy of
  every `63`-electron eigenstate within `Δ` of the ground state with root-mean-square error at most
  `ε`, the error measure behind the `⌈πλ / (2ε)⌉` walk steps of Babbush et al. (2018,
  Eqs. 21–23), and does not place a higher eigenstate below the top of that window by more than
  `ε`.
* `p450GroundEnergy_const_cost`: the program is over Clifford + `T` with measurements, and its
  spacetime volume (qubits × `T` count) is at most `p450GroundEnergyConstCost`. It has no `TOFF`
  gates, so each Toffoli is built from Clifford + `T` gates and the correctness proof covers that
  construction.

The program, its decoder, its ancilla count and its cost are computable `def`s, so none of them can
be defined from the eigenvalues being estimated. The decoder has the fixed phase-estimation form
`PhaseDecoder`, with the solution choosing the register and two coefficients.

The window `Δ` keeps the statement quantum: with `scale = 0` the decoder is a constant, which would
have to be within `ε` of the ground energy and, for the eigenstates above the window, at most `ε`
below its top, which needs `Δ ≤ 2ε`. The window also covers the low-lying spin states: CCSD(T)
places the quartet `73` mHa below the sextet. As in the literature, one run on an eigenstate is
costed; preparing it is not.

Baselines. Both use the circuit of Low et al. (2025), which block-encodes the sum-of-squares
form with spectral amplification, for `⌈πλ_eff / (2ε)⌉` walk steps, `λ_eff = √(E_gap (2Λ - E_gap))`
(their Eq. 11), where `E_gap` is the largest energy to be measured minus the sum-of-squares lower
bound. With `Λ = 97.3864` Ha, the lower bound `-134.887` Ha and the quartet ROHF energy
`-129.844` Ha bounding the ground energy from above (both for `thcHamiltonian dfthc`, which omits
a constant), `E_gap ≤ 5.143` Ha, `λ_eff ≤ 31.23` Ha and `49,056` steps. Reaching this step count
requires proving the upper bound on the ground energy in Lean, for example as the energy of an
explicit `63`-electron state. Both charge `4` `T` gates per Toffoli, the Toffoli of Jones (2013)
from `4` `T` gates, an ancilla, a measurement and a classically controlled `CZ`.

* Low et al. (2025), Table V: `9,535` Toffolis per walk step on `1150` qubits. Storing `13`
  instead of `15` bits for each of the `57` angles (the angle indices of `dfthc` are below `2¹³`)
  and adding a `16`-qubit phase-estimation register gives `1052` qubits, so `4.68 × 10⁸`
  Toffolis, `1.87 × 10⁹` `T` gates and spacetime `1.97 × 10¹²`. They quote `4.91 × 10⁸` Toffolis
  with their one-body term and a Hartree–Fock bound.
* The same circuit with the logical-circuit options of Low et al., *A Denser Planar Surface Code*
  (2026, App. E), minimising qubits × `T` count over those options. The `G`, `r`, `c`, spin and
  `b = B` registers are recomputed from `x_o` by comparators, and `19` of the `57` Givens angles
  (`13` bits each) are held at a time, loaded in `3` batches with `5` lookups per `SELECT` (both
  Givens networks need every angle). Three exact refinements are also applied: that paper's
  minimum-Toffoli comparator, controlled adders that skip the two always-zero addend bits (`27`
  Toffolis), and padding `C` rather than `R` in the `x_o` index. That gives `11,517` Toffolis per
  walk step on `481` qubits (`116` system, `16` phase estimation, `15` phase gradient, `247`
  angles, `87` other), including `32` Toffolis per step for controlling the walk from the phase
  register by comparing it with the step index around both reflections, so `2.26 × 10⁹` `T`
  gates and spacetime `1.09 × 10¹²`. Improvements are quoted against this baseline.

References:
* G. H. Low et al., *Fast quantum simulation of electronic structure by spectral amplification*,
  Phys. Rev. X 15, 041016 (2025), https://doi.org/10.1103/pb2g-j9cw,
  https://arxiv.org/abs/2502.15882; factors at https://doi.org/10.5281/zenodo.17066718.
* G. H. Low et al., *A Denser Planar Surface Code* (2026), https://arxiv.org/abs/2605.30455.
* J. J. Goings et al., *Reliably assessing the electronic structure of cytochrome P450 on today's
  classical computers and tomorrow's quantum computers*, PNAS 119(38), e2203533119 (2022),
  https://arxiv.org/abs/2202.01244.
* R. Babbush et al., *Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity*,
  Phys. Rev. X 8, 041015 (2018), https://arxiv.org/abs/1805.03662.
* C. Jones, *Low-overhead constructions for the fault-tolerant Toffoli gate*, Phys. Rev. A 87,
  022328 (2013).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator
open scoped Matrix

/-- Phase-estimation decoder of `m` ancillas, for a walk with eigenphases `±φ` that is applied
forwards or backwards depending on the phase register, so that the register `register` holds `y`,
an estimate of `±2φ`. With `θ = 2π y / 2 ^ bits` the decoded energy is
`offset + scale * |cos (θ / 2)|`. For the spectral-amplification walk of Low et al. (2025), with
`E = E_LB + Λ (1 + cos φ)` and `φ ∈ [π/2, π]` at low energy, `offset = E_LB + Λ` and
`scale = -Λ`. -/
structure PhaseDecoder (m : ℕ) where
  /-- Number of qubits of the phase register. -/
  bits : ℕ
  /-- The phase register, within the ancillas. -/
  register : QRegister bits m
  /-- Energy where the cosine is `0`. -/
  offset : ℝ
  /-- Energy per unit of the cosine. -/
  scale : ℝ

open Real in
/-- Energy that `d` decodes from the ancilla outcome `a`. -/
noncomputable def PhaseDecoder.energy {m : ℕ} (d : PhaseDecoder m) (a : Fin (2 ^ m)) : ℝ :=
  let θ := 2 * π * (d.register.extractIndex a).val / 2 ^ d.bits
  d.offset + d.scale * |cos (θ / 2)|

/-- `W` measures the energies of `H` within `Δ` of its ground-state energy on the `η`-electron
sector with root-mean-square error `ε`, decoded by `decoder`: for every `T` at most `Δ` above that
ground-state energy and every unit eigenvector `ψ` of `H` with `η` electrons and eigenvalue `E`,
measuring the ancillas of `W (ψ ⊗ |0⟩)` and decoding the outcome estimates `min E T` with mean
squared error at most `ε²` once the estimate is capped at `T`. For `E ≤ T` this bounds the error in
`E`; for `E > T` the estimate may not fall below `T` by more than `ε` in root mean square. -/
def MeasuresLowEnergies {k m : ℕ} (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (decoder : PhaseDecoder m) (W : Unitary (2 ^ (k + m))) : Prop :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  -- `ψ ≠ 0` is needed: without it every `E'` is an eigenvalue of `0`, no `T` qualifies and the
  -- predicate holds vacuously.
  let IsEigen (E : ℝ) (ψ : Fin (2 ^ k) → ℂ) :=
    H *ᵥ ψ = (E : ℂ) • ψ ∧ electronSectorProjector k η *ᵥ ψ = ψ ∧ ψ ≠ 0
  ∀ T : ℝ, (∀ E' φ, IsEigen E' φ → T ≤ E' + Δ) →
    ∀ E ψ, IsEigen E ψ → ∑ i, Complex.normSq (ψ i) = 1 →
    let out := W.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)
    ∑ a, anc.basisOutcomeProbability a out * (min (decoder.energy a) T - min E T) ^ 2 ≤ ε ^ 2

/-- Width `2N = 116` of the system register; wire `2p + σ` holds spin orbital `(p, σ)`. -/
abbrev P450.systemQubits : ℕ := 2 * 58

open P450

/-! ## Candidate Program & Correctness / Cost Theorems -/

/-- By default we allow only a single variable. -/
inductive P450GroundEnergy.Var where | v deriving DecidableEq, Inhabited

open P450GroundEnergy (Var)
open P450GroundEnergy.Var (v)

/-- Number of clean ancilla qubits `p450GroundEnergyProgram` uses, including the
phase-estimation register. -/
def p450GroundEnergyAncillas : ℕ := sorry

/-- Energy estimation circuit on system wires `rSys` and clean ancilla wires `rAnc`. -/
def p450GroundEnergyProgram {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister p450GroundEnergyAncillas n) : DynamicCircuit Var n :=
  sorry

/-- Decoder of the ancillas of `p450GroundEnergyProgram`. Fractions in it are written as
`((a / b : ℚ) : ℝ)`, since division in `ℝ` is noncomputable. -/
def p450GroundEnergyDecoder : PhaseDecoder p450GroundEnergyAncillas := sorry

/-- `p450GroundEnergyProgram`, started with clean ancillas, realizes a unitary from which
`p450GroundEnergyDecoder` decodes the energy of every `63`-electron eigenstate of
`thcHamiltonian dfthc` within `0.1` Ha of the ground state with root-mean-square error `10⁻³` Ha,
and places no higher eigenstate below that window. With no catalyst, phase-gradient states are
prepared within the run. -/
theorem p450GroundEnergy_correctness {n : ℕ}
    (rSys : QRegister systemQubits n) (rAnc : QRegister p450GroundEnergyAncillas n)
    (hdisj : rSys.DisjointWires rAnc) :
    ∃ W, MeasuresLowEnergies (thcHamiltonian dfthc) 63 0.1 0.001 p450GroundEnergyDecoder W ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W
        (p450GroundEnergyProgram rSys rAnc).compile := by sorry

/-- Claimed spacetime volume of `p450GroundEnergyProgram`. -/
def p450GroundEnergyConstCost : ℕ := sorry

/-- Over Clifford + `T` with measurements, the spacetime volume (qubits times `T` count) of
`p450GroundEnergyProgram` is at most `p450GroundEnergyConstCost`. `TOFF` gates are excluded, so
each Toffoli is costed by the Clifford + `T` construction the program uses, such as `4` `T` gates
with an ancilla and a measurement; measurements cost `0` and a `qIf` costs its worse branch. -/
theorem p450GroundEnergy_const_cost {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister p450GroundEnergyAncillas n) :
    (p450GroundEnergyProgram rSys rAnc).count PrimitiveGate.TOFF = 0 ∧
      (systemQubits + p450GroundEnergyAncillas) *
          (p450GroundEnergyProgram rSys rAnc).count PrimitiveGate.T ≤
        p450GroundEnergyConstCost := by sorry

end QuantumComputation.Specs
